import Base
import ./Text.bend as T
import ./Core.bend as C
import ./Lex.bend as L
import ./Path.bend as Pa
import ./Err.bend as E
import ./Parse.bend as Ps
import ./PHelp.bend as X

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Load: bend.ts's book_load: a file's import lines (Base, or a path with an
# alias), each loaded first and once, an import cycle refused, then the
# rest of the file parsed into the book with the import lines blanked.
# Base is parsed once a process and joins a book as a layer (Lex's Bk).

# Reading files
# -------------

type Sl is Type:
  Sl{f: File, acc: List<&2, U32>, more: Bool}

def slurp.res(g: File, x: Result<&1, &1, U32 & String, List<&2, U32>>, acc: List<&2, U32>) -> IO(Sl):
  match x:
    case Fail{(c, m)}:
      IO.pure(Sl, Sl{g, acc, False{}})
    case Done{+xs}:
      IO.pure(Sl, Sl{g, List.reverse.go(&2, U32, xs, acc), Bool.not(List.is_empty(&2, U32, xs))})

def slurp.got(acc: List<&2, U32>, r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Sl):
  (g, x) = r
  slurp.res(g, x, acc)

def slurp.step(s: Sl) -> IO(Sl):
  match s:
    case Sl{f, acc, m}:
      do IO<Sl>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 1048576)
        slurp.got(acc, r)

def slurp.go(fuel: Nat, s: Sl) -> IO(List<&2, U32>):
  match fuel s:
    case 1n+p Sl{f, acc, True{}}:
      IO.bind(Sl, List<&2, U32>, slurp.step(Sl{f, acc, True{}}), slurp.go(p))
    case _ Sl{f, acc, m}:
      do IO<List<&2, U32>>:
        File.close(f)
        return List.reverse(&2, U32, acc)

def slurp.opened(r: Result<&1, &1, U32 & String, File>) -> IO(Maybe<&2, List<&2, U32>>):
  match r:
    case Fail{e}:
      IO.pure(Maybe<&2, List<&2, U32>>, None{})
    case Done{f}:
      do IO<Maybe<&2, List<&2, U32>>>:
        xs : List<&2, U32> <- slurp.go(4096n, Sl{f, Nil{}, True{}})
        return Some{xs}

# a whole file's bytes, None when it cannot be opened
def slurp(path: String) -> IO(Maybe<&2, List<&2, U32>>):
  do IO<Maybe<&2, List<&2, U32>>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    slurp.opened(r)

# The loader's state
# ------------------

# a file loaded: its real path, namespace, aliases, declarations, and the
# text its spans point into (its import lines blanked); its id. Where Base
# joined the book (the first import of it), a mark: the path "", no text
type Fr is Data:
  Fr{path: String, ns: String, al: List<&2, L.Al>, ds: List<&2, C.Dcl>, txt: List<&2, U32>, fid: U32}

# a path seen: done, or still loading (an import of it is a cycle)
type Sn is Data:
  Sn{real: String, done: Bool}

type Ld is Data:
  Ld{bk: L.Bk, seen: List<&2, Sn>, files: List<&2, Fr>, fid: U32, base: String, lib: String}

type LR is Data:
  LOk{ld: Ld}
  LErr{e: C.Er}

def seen.find(ss: List<&2, Sn>, +r: String) -> Nat:
  match ss:
    case Nil{}:
      0n
    case Con{Sn{x, d}, t}:
      Bool.pick(Nat, String.eq(x, r), Bool.pick(Nat, d, 2n, 1n), seen.find(t, r))

def seen.done(ss: List<&2, Sn>, +r: String) -> List<&2, Sn>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{Sn{+x, d}, t}:
      Bool.pick(Sn, String.eq(x, r), Sn{x, True{}}, Sn{x, d}) <> seen.done(t, r)

def ld.seen(+r: String, +ld: Ld) -> Nat:
  match ld:
    case Ld{bk, seen, files, fid, base, lib}:
      seen.find(seen, r)

def ld.mark(r: String, ld: Ld) -> Ld:
  match ld:
    case Ld{bk, seen, files, fid, base, lib}:
      Ld{bk, Sn{r, False{}} <> seen, files, fid, base, lib}

def ld.finish(+r: String, ld: Ld) -> Ld:
  match ld:
    case Ld{bk, seen, files, fid, base, lib}:
      Ld{bk, seen.done(seen, r), files, fid, base, lib}

def ld.base(ld: Ld) -> String:
  match ld:
    case Ld{bk, seen, files, fid, base, lib}:
      base

def ld.bk(ld: Ld) -> L.Bk:
  match ld:
    case Ld{bk, seen, files, fid, base, lib}:
      bk

def ld.fid(ld: Ld) -> U32:
  match ld:
    case Ld{bk, seen, files, fid, base, lib}:
      fid

def ld.lib(ld: Ld) -> String:
  match ld:
    case Ld{bk, seen, files, fid, base, lib}:
      lib

# a mark where Base first joins the book
def base.place(on: Bool, files: List<&2, Fr>) -> List<&2, Fr>:
  match on:
    case True{}:
      files
    case False{}:
      Fr{"", "", Nil{}, Nil{}, Nil{}, 0} <> files

def bk.bon(b: L.Bk) -> Bool:
  match b:
    case L.Bk{tl, ct, btl, bct, bon, hols}:
      bon

# Base joins the book: its layer on, its path seen, its place marked
def ld.base_on(ld: Ld) -> Ld:
  match ld:
    case Ld{+bk, seen, files, fid, +base, lib}:
      Ld{L.bk.base_on(bk), Sn{base, True{}} <> seen, base.place(bk.bon(bk), files), fid, base, lib}

def ld.parsed(bk: L.Bk, f: Fr, ld: Ld) -> Ld:
  match ld:
    case Ld{o, seen, files, fid, base, lib}:
      Ld{bk, seen, f <> files, (fid + 1 : U32), base, lib}

def ld.files(ld: Ld) -> List<&2, Fr>:
  match ld:
    case Ld{bk, seen, files, fid, base, lib}:
      files

# Import lines
# ------------

def line.split(xs: List<&2, U32>, cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      List.reverse(&2, List<&2, U32>, List.reverse(&2, U32, cur) <> acc)
    case Con{10, t}:
      line.split(t, Nil{}, List.reverse(&2, U32, cur) <> acc)
    case Con{c, t}:
      line.split(t, c <> cur, acc)

# String.prototype.trim
def trim.start(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{+c, +t}:
      Bool.pick(List<&2, U32>, T.is_space(c), trim.start(t), Con{c, t})
    case Nil{}:
      Nil{}

def trim(+xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, trim.start(List.reverse(&2, U32, trim.start(xs))))

# a line's role before the first non-import: 0 skip (empty or #), 1 an
# import, 2 the end of the imports
def line.role.after(t: List<&2, U32>) -> Nat:
  match t:
    case Nil{}:
      1n
    case Con{+c, r}:
      Bool.pick(Nat, T.is_space(c), 1n, 2n)

def line.role(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{35, t}:
      0n
    case Con{105, Con{109, Con{112, Con{111, Con{114, Con{116, t}}}}}}:
      line.role.after(t)
    case _:
      2n

# /^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?\s*(?:#.*)?$/: the path and
# the alias, or none when the line is no import
type Im is Data:
  ImNo{}
  ImBase{}
  ImYes{path: List<&2, U32>, al: Maybe<&2, List<&2, U32>>}

def spaces(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{+c, +t}:
      Bool.pick(List<&2, U32>, T.is_space(c), spaces(t), Con{c, t})
    case Nil{}:
      Nil{}

def nonspace.run(xs: List<&2, U32>, on: Bool) -> Nat:
  match xs on:
    case _ False{}:
      0n
    case Nil{} True{}:
      0n
    case Con{+c, t} True{}:
      +z = Bool.not(T.is_space(c))
      Bool.pick(Nat, z, 1n+nonspace.run(t, z), 0n)

def word.run(xs: List<&2, U32>, on: Bool) -> Nat:
  match xs on:
    case _ False{}:
      0n
    case Nil{} True{}:
      0n
    case Con{+c, t} True{}:
      +z = T.is_word(c)
      Bool.pick(Nat, z, 1n+word.run(t, z), 0n)

# is a line terminator other than \n
def is.term(+c: U32) -> Bool:
  Bool.or(Bool.or(U32.is_eq(c, 13), U32.is_eq(c, 8232)), U32.is_eq(c, 8233))

def no.term(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Bool.and(Bool.not(is.term(c)), no.term(t))

# \s*(?:#.*)?$
def tail.end.go(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{35, t}:
      no.term(t)
    case _:
      False{}

def tail.end(+xs: List<&2, U32>) -> Bool:
  tail.end.go(spaces(xs))

def starts.space(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{+c, t}:
      T.is_space(c)
    case Nil{}:
      False{}

# (\s+as\s+([A-Za-z_]\w*))\s*(#.*)?$ on what follows the path: the alias
def tail.id(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Con{+c, +t}:
      +n : Nat = 1n+word.run(t, True{})
      Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(T.is_head(c), tail.end(List.drop(&2, U32, Con{c, t}, n))), Some{List.take(&2, U32, Con{c, t}, n)}, None{})
    case Nil{}:
      None{}

def tail.as(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Con{97, Con{115, +t}}:
      Bool.pick(Maybe<&2, List<&2, U32>>, starts.space(t), tail.id(spaces(t)), None{})
    case _:
      None{}

def tail.alias(+xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Bool.pick(Maybe<&2, List<&2, U32>>, starts.space(xs), tail.as(spaces(xs)), None{})

# the largest k < n with tok[k] == '#' and no line terminator after it
def hash.split(xs: List<&2, U32>, +i: Nat, best: Nat) -> Nat:
  match xs:
    case Nil{}:
      best
    case Con{35, +t}:
      hash.split(t, 1n+i, Bool.pick(Nat, Bool.and(Bool.not(Nat.is_eq(i, 0n)), no.term(t)), i, best))
    case Con{c, t}:
      hash.split(t, 1n+i, best)

def im.hash(+k: Nat, +r: List<&2, U32>) -> Im:
  Bool.pick(Im, Nat.is_eq(k, 0n), ImNo{}, ImYes{List.take(&2, U32, r, k), None{}})

def im.full(a: Maybe<&2, List<&2, U32>>, plain: Bool, +path: List<&2, U32>, +r: List<&2, U32>, +n: Nat) -> Im:
  match a:
    case Some{x}:
      ImYes{path, Some{x}}
    case None{}:
      Bool.pick(Im, plain, ImYes{path, None{}}, im.hash(hash.split(List.take(&2, U32, r, n), 0n, 0n), r))

def im.at(+r: List<&2, U32>, +n: Nat) -> Im:
  +after = List.drop(&2, U32, r, n)
  +path = List.take(&2, U32, r, n)
  im.full(tail.alias(after), tail.end(after), path, r, n)

# "import Base" (no alias) is Base
def im.base(im: Im) -> Im:
  match im:
    case ImYes{+m1, None{}}:
      Bool.pick(Im, T.eq(m1, T.units("Base")), ImBase{}, ImYes{m1, None{}})
    case im:
      im

# the trimmed line, past "import"
def im.match(xs: List<&2, U32>) -> Im:
  match xs:
    case Con{105, Con{109, Con{112, Con{111, Con{114, Con{116, +t}}}}}}:
      +r = spaces(t)
      Bool.pick(Im, Bool.and(starts.space(t), Bool.not(List.is_empty(&2, U32, r))), im.at(r, nonspace.run(r, True{})), ImNo{})
    case _:
      ImNo{}

# lines[i].indexOf(s): the offset of the units s in the line
def index.of.go(xs: List<&2, U32>, +s: List<&2, U32>, +n: U32) -> U32:
  match xs:
    case Nil{}:
      Bool.pick(U32, List.is_empty(&2, U32, s), n, 0)
    case Con{c, +t}:
      Bool.pick(U32, T.prefix(Con{c, t}, s), n, index.of.go(t, s, (n + 1 : U32)))

def q(s: String) -> String:
  "'" ++ s ++ "'"

def imp.err(exp: String, obs: Maybe<&2, String>, +txt: List<&2, U32>, +fid: U32, +beg: U32) -> C.Er:
  C.Er{exp, obs, C.Sp{fid, beg, beg}, txt, None{}}

# The loader
# ----------

# a file being read: its real path, dir (with its slash), the entry's dir,
# namespace, text (units), aliases, and the lines blanked so far
type Fc is Data:
  Fc{real: String, dir: String, top: String, ns: String, txt: List<&2, U32>, al: List<&2, L.Al>}

def fc.txt(f: Fc) -> List<&2, U32>:
  match f:
    case Fc{real, dir, top, ns, txt, al}:
      txt

def al.has(al: List<&2, L.Al>, +a: String) -> Bool:
  match al:
    case Nil{}:
      False{}
    case Con{L.Al{x, n}, t}:
      Bool.or(String.eq(x, a), al.has(t, a))

def join.lines(ls: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, Nil{}}:
      l
    case Con{l, t}:
      List.append(&2, U32, l, 10 <> join.lines(t))

def lerr(e: C.Er) -> IO(LR):
  IO.pure(LR, LErr{e})

def lok(ld: Ld) -> IO(LR):
  IO.pure(LR, LOk{ld})

# a book_file miss: no such file (at the importer's span, if any)
def nofile(+file: String, sp: Maybe<&2, C.Er>) -> C.Er:
  match sp:
    case Some{C.Er{e, o, s, txt, n}}:
      C.Er{"no such file: " ++ file, None{}, s, txt, None{}}
    case _:
      C.Er{"no such file: " ++ file, None{}, C.NoSp{}, Nil{}, None{}}

def cycle(+file: String, sp: Maybe<&2, C.Er>) -> C.Er:
  match sp:
    case Some{C.Er{e, o, s, txt, n}}:
      C.Er{"an import cycle through " ++ file, None{}, s, txt, None{}}
    case _:
      C.Er{"an import cycle through " ++ file, None{}, C.NoSp{}, Nil{}, None{}}

def lr.then(r: LR, k: Ld -> IO(LR)) -> IO(LR):
  match r:
    case LOk{ld}:
      k(ld)
    case LErr{e}:
      IO.pure(LR, LErr{e})

def parse.fin.env(st: L.St, fc: Fc, ld: Ld) -> LR:
  match st fc:
    case L.St{c, L.Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}} Fc{+real, d2, top, ns2, t2, al2}:
      LOk{ld.finish(real, ld.parsed(bk, Fr{real, ns, al, List.reverse(&2, C.Dcl, ds), txt, fid}, ld))}

def parse.fin(r: L.R<X.PV>, +fc: Fc, +ld: Ld) -> LR:
  match r:
    case L.RErr{e}:
      LErr{e}
    case L.ROk{v, st}:
      parse.fin.env(st, fc, ld)

def parse.file(+fc: Fc, +body: List<&2, U32>, +ld: Ld) -> LR:
  match fc:
    case Fc{real, dir, top, +ns, txt, +al}:
      parse.fin(Ps.parse.book(L.St{L.cur.of(body), L.Env{body, ld.fid(ld), ns, al, dir, 0, Nil{}, 0, Nil{}, ld.bk(ld), Nil{}}}), Fc{real, dir, top, ns, txt, al}, ld)

def fc.with_al(+a: String, +ns: String, f: Fc) -> Fc:
  match f:
    case Fc{real, dir, top, n, txt, al}:
      Fc{real, dir, top, n, txt, List.append(&2, L.Al, al, [L.Al{a, ns}])}

def fc.real(f: Fc) -> String:
  match f:
    case Fc{real, dir, top, ns, txt, al}:
      real

def fc.dir(f: Fc) -> String:
  match f:
    case Fc{real, dir, top, ns, txt, al}:
      dir

def fc.top(f: Fc) -> String:
  match f:
    case Fc{real, dir, top, ns, txt, al}:
      top

def fc.ns(f: Fc) -> String:
  match f:
    case Fc{real, dir, top, ns, txt, al}:
      ns

def fc.al(f: Fc) -> List<&2, L.Al>:
  match f:
    case Fc{real, dir, top, ns, txt, al}:
      al

# an import's checks before its file is read (bend.ts's order): a .bend
# path, a fresh alias, no name@version, plain names; the path to read
type Ic is Data:
  IcErr{e: C.Er}
  IcPath{path: String}

def BAD() -> String:
  "an import path of plain names (each starts with a letter or _, then letters, digits, _ and -)"

def at.slash(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{47, t}:
      True{}
    case Con{c, t}:
      at.slash(t)

def has.at.dir(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{47, t}:
      False{}
    case Con{64, t}:
      at.slash(t)
    case Con{c, t}:
      has.at.dir(t)

def sp.with(sp: C.Er, exp: String, obs: Maybe<&2, String>) -> C.Er:
  match sp:
    case C.Er{e, o, s, txt, n}:
      C.Er{exp, obs, s, txt, None{}}
    case e:
      e

def imp.check(+fc: Fc, +m1: String, +al: String, +line: String, +sp: C.Er) -> Ic:
  Bool.pick(Ic, Bool.not(Pa.p.ends_bend(m1)), IcErr{sp.with(sp, "an import of a .bend file", Some{q(m1)})},
  Bool.pick(Ic, al.has(fc.al(fc), al), IcErr{sp.with(sp, "a fresh alias (" ++ al ++ " names an earlier import)", Some{q(line)})},
  Bool.pick(Ic, has.at.dir(T.cps.of(m1)), IcErr{sp.with(sp, "bendbis: a <name>@<version> import (the hub is not read)", None{})},
  Bool.pick(Ic, Bool.not(Pa.p.ok(Pa.p.import_stem(m1))), IcErr{sp.with(sp, BAD(), Some{q(m1)})},
    IcPath{Pa.p.resolve(fc.dir(fc), Pa.p.normalize(m1))}))))

# after the read: the namespace (the path from the entry's dir, less
# .bend), checked again; the hub's store is not read
def imp.sub(+fc: Fc, +got: String, +m1: String, +sp: C.Er, +lib: String) -> Ic:
  +sub = Pa.p.unbend(Pa.p.relative(fc.top(fc), got))
  Bool.pick(Ic, Bool.or(Pa.p.starts(got, lib), Pa.p.is_hub(fc.ns(fc))), IcErr{sp.with(sp, "an import on its side of the hub (a hub file imports only hub files, and a local path stays out of the hub's store)", Some{q(m1)})},
  Bool.pick(Ic, Bool.not(Pa.p.ok(sub)), IcErr{sp.with(sp, BAD(), Some{q(m1) ++ " (resolves to '" ++ Pa.p.relative(fc.dir(fc), got) ++ "')"})},
    IcPath{sub}))

def ic.then(c: Ic, k: String -> IO(LR)) -> IO(LR):
  match c:
    case IcErr{e}:
      lerr(e)
    case IcPath{p}:
      k(p)

def mb.then(m: Maybe<&2, List<&2, U32>>, +e: C.Er, k: List<&2, U32> -> IO(LR)) -> IO(LR):
  match m:
    case None{}:
      lerr(e)
    case Some{xs}:
      k(xs)

def line.len(xs: List<&2, U32>) -> U32:
  U32.from_nat(List.length(&2, U32, xs))

# the loader's answer when a file imports Base and the entry was read
# with no Base layer (its caller reads Base, then the entry again)
def NEED_BASE() -> String:
  "bendbis: Base is needed"

type LJ is Data:
  LjRead{bytes: List<&2, U32>, file: String, ns: String, top: Maybe<&2, String>, sp: Maybe<&2, C.Er>}
  LjSeen{n: Nat, bytes: List<&2, U32>, file: String, ns: String, top: Maybe<&2, String>, sp: Maybe<&2, C.Er>}
  LjText{txt: List<&2, U32>, file: String, ns: String, top: Maybe<&2, String>, sp: Maybe<&2, C.Er>}
  LjLines{fc: Fc, ls: List<&2, List<&2, U32>>, at: U32, out: List<&2, List<&2, U32>>}
  LjLine{role: Nat, fc: Fc, l: List<&2, U32>, ls: List<&2, List<&2, U32>>, at: U32, out: List<&2, List<&2, U32>>}
  LjIm{im: Im, fc: Fc, l: List<&2, U32>, ls: List<&2, List<&2, U32>>, at: U32, out: List<&2, List<&2, U32>>}
  LjBase{none: Bool, fc: Fc, l: List<&2, U32>, ls: List<&2, List<&2, U32>>, at: U32, out: List<&2, List<&2, U32>>}

def ld.go(+fuel: Nat, j: LJ, +ld: Ld) -> IO(LR):
  match fuel j:
    case 0n _:
      lerr(C.ErRaw{"bendbis: the loader ran out of fuel"})

    # book_load, its file read: a cycle, a second import, or the lines
    case 1n+p LjRead{bytes, +file, ns, top, sp}:
      ld.go(p, LjSeen{ld.seen(file, ld), bytes, file, ns, top, sp}, ld)
    case 1n+p LjSeen{n, bytes, +file, +ns, top, sp}:
      match n:
        case 1n:
          lerr(cycle(file, sp))
        case 2n:
          lok(ld)
        case _:
          ld.go(p, LjText{T.of_bytes(bytes), file, ns, top, sp}, ld)
    case 1n+p LjText{+txt, +file, ns, top, sp}:
      +dir = Pa.p.dir(file)
      ld.go(p, LjLines{Fc{file, dir, Maybe.default(&2, String, top, dir), ns, txt, Nil{}}, line.split(txt, Nil{}, Nil{}), 0, Nil{}}, ld.mark(file, ld))

    case 1n+p LjLines{+fc, ls, +at, +out}:
      match ls:
        case Nil{}:
          IO.pure(LR, parse.file(fc, join.lines(List.reverse(&2, List<&2, U32>, out)), ld))
        case Con{+l, t}:
          ld.go(p, LjLine{line.role(trim(l)), fc, l, t, at, out}, ld)

    case 1n+p LjLine{role, +fc, +l, +ls, +at, +out}:
      match role:
        case 0n:
          ld.go(p, LjLines{fc, ls, ((at + line.len(l) : U32) + 1 : U32), l <> out}, ld)
        case 1n:
          ld.go(p, LjIm{im.base(im.match(trim(l))), fc, l, ls, at, out}, ld)
        case _:
          IO.pure(LR, parse.file(fc, join.lines(List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, out), l <> ls)), ld))

    # import Base: its layer on, or, when the entry was read without one,
    # the call for it (NEED_BASE)
    case 1n+p LjBase{none, +fc, +l, +ls, +at, +out}:
      match none:
        case True{}:
          lerr(C.ErRaw{NEED_BASE()})
        case False{}:
          ld.go(p, LjLines{fc, ls, ((at + line.len(l) : U32) + 1 : U32), Nil{} <> out}, ld.base_on(ld))

    case 1n+p LjIm{im, +fc, +l, +ls, +at, +out}:
      match im:
        case ImNo{}:
          +line = trim(l)
          lerr(imp.err("an import ('import Base', or 'import <path> as <Name>')", Some{q(T.str(line))}, fc.txt(fc), ld.fid(ld), (at + index.of.go(l, line, 0) : U32)))
        case ImBase{}:
          ld.go(p, LjBase{String.is_empty(ld.base(ld)), fc, l, ls, at, out}, ld)
        case ImYes{+m1, None{}}:
          +line = trim(l)
          lerr(imp.err("an import ('import Base', or 'import <path> as <Name>')", Some{q(T.str(line))}, fc.txt(fc), ld.fid(ld), (at + index.of.go(l, m1, 0) : U32)))
        case ImYes{+m1, Some{+a}}:
          +line = trim(l)
          +next = ((at + line.len(l) : U32) + 1 : U32)
          +ms = T.str(m1)
          +as = T.str(a)
          +sp = imp.err("", None{}, fc.txt(fc), ld.fid(ld), (at + index.of.go(l, m1, 0) : U32))
          ic.then(imp.check(fc, ms, as, T.str(line), sp), +path =>
            (do IO<LR>:
              mb : Maybe<&2, List<&2, U32>> <- slurp(path)
              mb.then(mb, sp.with(sp, "no such file: " ++ path, None{}), bytes =>
                ic.then(imp.sub(fc, path, ms, sp, ld.lib(ld)), +sub =>
                  (do IO<LR>:
                    r : LR <- ld.go(p, LjRead{bytes, path, sub, Some{fc.top(fc)}, Some{sp}}, ld)
                    lr.then(r, ld2 => ld.go(p, LjLines{fc.with_al(as, sub, fc), ls, next, Nil{} <> out}, ld2)))))))

# Base, parsed once: its tables become every book's Base layer
def base.mark(t: C.Tld) -> C.Tld:
  match t:
    case C.TlDef{n, x, v, b, f}:
      C.TlDef{n, x, v, True{}, f}
    case t:
      t

def base.tl.go(m: Map<&2, C.Tld>) -> Map<&2, C.Tld>:
  match m:
    case MTip{}:
      MTip{}
    case MLeaf{k, v}:
      MLeaf{k, base.mark(v)}
    case MNode{pos, lo, hi}:
      MNode{pos, base.tl.go(lo), base.tl.go(hi)}

def base.layer(bk: L.Bk) -> L.Bk:
  match bk:
    case L.Bk{tl, ct, btl, bct, bon, hols}:
      L.Bk{Map.new(&2, C.Tld), Map.new(&2, U32), base.tl.go(tl), ct, False{}, 0}

def ld.new(+base: String, bk: L.Bk, lib: String) -> Ld:
  Ld{bk, Nil{}, Nil{}, 0, base, lib}

# Base's file id: its spans point into it, not into an entry's files
def BASE_FID() -> U32:
  1000000

# load base.bend (at its real path) into an empty book: the Base layer
def base.load(+path: String, lib: String) -> IO(LR):
  do IO<LR>:
    mb : Maybe<&2, List<&2, U32>> <- slurp(path)
    mb.then(mb, C.ErRaw{"bendbis: cannot read Base at " ++ path}, bytes =>
      ld.go(4294967295n, LjRead{bytes, path, "", None{}, None{}}, Ld{L.bk.nil(), Nil{}, Nil{}, BASE_FID(), path, lib}))

# the loader state for a new entry over the Base layer
def ld.entry(+base: String, bk: L.Bk, lib: String) -> Ld:
  ld.new(base, base.layer(bk), lib)

# book_load(book, file, "", seen): file as given, real its real path
def load.entry(+file: String, +real: String, ld: Ld) -> IO(LR):
  do IO<LR>:
    mb : Maybe<&2, List<&2, U32>> <- slurp(real)
    mb.then(mb, C.Er{"no such file: " ++ file, None{}, C.NoSp{}, Nil{}, None{}}, bytes =>
      ld.go(4294967295n, LjRead{bytes, real, "", None{}, None{}}, ld))

# book_load of a text (UTF-16 units) as though it were the file at real:
# the round trip parses the printer's output where the file was
def load.text(+real: String, txt: List<&2, U32>, ld: Ld) -> IO(LR):
  ld.go(4294967295n, LjText{txt, real, "", None{}, None{}}, ld)

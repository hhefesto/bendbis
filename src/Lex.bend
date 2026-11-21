import Base
import ./Text.bend as T
import ./Core.bend as C

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Lex: the parser's state and monad, and bend.ts's lexical layer (parse_peek
# to parse_char). bend.ts's Parse record is St here: the cursor Cur (the
# units from pos on, pos, the column parse_col would compute, whether
# parse_nl holds, and the unit before pos) and the rest, Env. A P(A) runs
# on a St and answers A and the next St, or the Er bend.ts would throw.

# an import alias: a names the namespace ns
type Al is Data:
  Al{a: String, ns: String}

# a name in scope at index i (bend.ts's idx and stk, as one stack)
type Sc is Data:
  Sc{k: String, i: U32}

# the book's tables as the parser reads them: its own, and Base's once
# loaded (a layer, so Base is parsed once a process); the TODO count
type Bk is Data:
  Bk{tl: Map<&2, C.Tld>, ct: Map<&2, U32>, btl: Map<&2, C.Tld>, bct: Map<&2, U32>, bon: Bool, hols: U32}

type Env is Data:
  Env{txt: List<&2, U32>, fid: U32, ns: String, al: List<&2, Al>, dir: String, frs: U32, sc: List<&2, Sc>, dep: U32, ann: List<&2, U32>, bk: Bk, ds: List<&2, C.Dcl>}

type Cur is Data:
  Cur{rest: List<&2, U32>, pos: U32, col: U32, nl: Bool, prev: U32}

type St is Data:
  St{c: Cur, e: Env}

type R<-A: Type> is Type:
  ROk{v: A, st: St}
  RErr{e: C.Er}

def P(-A: Type) -> Type:
  St -> R<A>

def P.pure(-A: Type, x: A) -> P(A):
  st => ROk{x, st}

def P.bind.go(-A: Type, -B: Type, r: R<A>, f: A -> P(B)) -> R<B>:
  match r:
    case ROk{a, st}:
      f(a, st)
    case RErr{e}:
      RErr{e}

def P.bind(-A: Type, -B: Type, m: P(A), f: A -> P(B)) -> P(B):
  st => P.bind.go(A, B, m(st), f)

def P.throw(-A: Type, e: C.Er) -> P(A):
  st => RErr{e}

def P.st() -> P(St):
  +st => ROk{st, st}

def P.put(st: St) -> P(Unit):
  old => ROk{Unit{}, st}

def P.cur.go(st: St) -> R<Cur>:
  match st:
    case St{+c, e}:
      ROk{c, St{c, e}}

def P.cur() -> P(Cur):
  st => P.cur.go(st)

def P.set_cur.go(c: Cur, st: St) -> R<Unit>:
  match st:
    case St{o, e}:
      ROk{Unit{}, St{c, e}}

def P.set_cur(c: Cur) -> P(Unit):
  st => P.set_cur.go(c, st)

def P.env.go(st: St) -> R<Env>:
  match st:
    case St{c, +e}:
      ROk{e, St{c, e}}

def P.env() -> P(Env):
  st => P.env.go(st)

def P.set_env.go(e: Env, st: St) -> R<Unit>:
  match st:
    case St{c, o}:
      ROk{Unit{}, St{c, e}}

def P.set_env(e: Env) -> P(Unit):
  st => P.set_env.go(e, st)

# run f on the cursor
def P.mod_cur.go(f: Cur -> Cur, st: St) -> R<Unit>:
  match st:
    case St{c, e}:
      ROk{Unit{}, St{f(c), e}}

def P.mod_cur(f: Cur -> Cur) -> P(Unit):
  st => P.mod_cur.go(f, st)

def P.mod_env.go(f: Env -> Env, st: St) -> R<Unit>:
  match st:
    case St{c, e}:
      ROk{Unit{}, St{c, f(e)}}

def P.mod_env(f: Env -> Env) -> P(Unit):
  st => P.mod_env.go(f, st)

# Env fields
# ----------

def env.txt(e: Env) -> List<&2, U32>:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      txt

def env.fid(e: Env) -> U32:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      fid

def env.ns(e: Env) -> String:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      ns

def env.al(e: Env) -> List<&2, Al>:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      al

def env.dir(e: Env) -> String:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      dir

def env.frs(e: Env) -> U32:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      frs

def env.dep(e: Env) -> U32:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      dep

def env.bk(e: Env) -> Bk:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      bk

def env.ann(e: Env) -> List<&2, U32>:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      ann

def env.sc(e: Env) -> List<&2, Sc>:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      sc

def env.set_frs(n: U32, e: Env) -> Env:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      Env{txt, fid, ns, al, dir, n, sc, dep, ann, bk, ds}

def env.set_bk(b: Bk, e: Env) -> Env:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      Env{txt, fid, ns, al, dir, frs, sc, dep, ann, b, ds}

def env.set_ann(a: List<&2, U32>, e: Env) -> Env:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      Env{txt, fid, ns, al, dir, frs, sc, dep, a, bk, ds}

def env.push_d(d: C.Dcl, e: Env) -> Env:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, d <> ds}

# the scope: push k at i (parse_push); close down to n entries (parse_close)
def env.push(k: String, i: U32, e: Env) -> Env:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      Env{txt, fid, ns, al, dir, frs, Sc{k, i} <> sc, (dep + 1 : U32), ann, bk, ds}

def sc.drop(n: Nat, sc: List<&2, Sc>) -> List<&2, Sc>:
  match n sc:
    case 0n sc:
      sc
    case 1n+p Con{h, t}:
      sc.drop(p, t)
    case 1n+p Nil{}:
      Nil{}

def env.close(+n: U32, e: Env) -> Env:
  match e:
    case Env{txt, fid, ns, al, dir, frs, sc, +dep, ann, bk, ds}:
      Env{txt, fid, ns, al, dir, frs, sc.drop(Nat.sub(U32.to_nat(dep), U32.to_nat(n)), sc), U32.min(dep, n), ann, bk, ds}

# the innermost index bound to k, NONE when k is not in scope
def sc.find(sc: List<&2, Sc>, +k: String) -> U32:
  match sc:
    case Nil{}:
      C.NONE()
    case Con{Sc{j, +i}, t}:
      Bool.pick(U32, String.eq(j, k), i, sc.find(t, k))

# Book tables
# -----------

def bk.tld.base(b: Bool, btl: Map<&2, C.Tld>, k: String) -> C.Tld:
  match b:
    case True{}:
      C.mp.get(C.Tld, C.TlNone{}, btl, k)
    case False{}:
      C.TlNone{}

def bk.tld.or(+bon: Bool, btl: Map<&2, C.Tld>, +k: String, t: C.Tld) -> C.Tld:
  match t:
    case C.TlNone{}:
      bk.tld.base(bon, btl, k)
    case t:
      t

# book.tlds[k]
def bk.tld(b: Bk, +k: String) -> C.Tld:
  match b:
    case Bk{tl, ct, btl, bct, bon, hols}:
      bk.tld.or(bon, btl, k, C.mp.get(C.Tld, C.TlNone{}, tl, k))

def bk.ctr.base(b: Bool, bct: Map<&2, U32>, k: String) -> U32:
  match b:
    case True{}:
      C.mp.get(U32, C.NONE(), bct, k)
    case False{}:
      C.NONE()

def bk.ctr.or(+bon: Bool, bct: Map<&2, U32>, +k: String, +n: U32) -> U32:
  Bool.pick(U32, U32.is_eq(n, C.NONE()), bk.ctr.base(bon, bct, k), n)

# book.ctrs[k]: its field count, NONE when k is not a constructor
def bk.ctr(b: Bk, +k: String) -> U32:
  match b:
    case Bk{tl, ct, btl, bct, bon, hols}:
      bk.ctr.or(bon, bct, k, C.mp.get(U32, C.NONE(), ct, k))

def tld.is_none(t: C.Tld) -> Bool:
  match t:
    case C.TlNone{}:
      True{}
    case _:
      False{}

def bk.has_tld(b: Bk, k: String) -> Bool:
  Bool.not(tld.is_none(bk.tld(b, k)))

def bk.has_ctr(b: Bk, k: String) -> Bool:
  Bool.not(U32.is_eq(bk.ctr(b, k), C.NONE()))

def bk.set_tld(k: String, t: C.Tld, b: Bk) -> Bk:
  match b:
    case Bk{tl, ct, btl, bct, bon, hols}:
      Bk{Map.set(&2, C.Tld, tl, k, t), ct, btl, bct, bon, hols}

def bk.set_ctr(k: String, n: U32, b: Bk) -> Bk:
  match b:
    case Bk{tl, ct, btl, bct, bon, hols}:
      Bk{tl, Map.set(&2, U32, ct, k, n), btl, bct, bon, hols}

def bk.hols(b: Bk) -> U32:
  match b:
    case Bk{tl, ct, btl, bct, bon, hols}:
      hols

def bk.set_hols(n: U32, b: Bk) -> Bk:
  match b:
    case Bk{tl, ct, btl, bct, bon, hols}:
      Bk{tl, ct, btl, bct, bon, n}

def bk.add_hol(b: Bk) -> Bk:
  match b:
    case Bk{tl, ct, btl, bct, bon, hols}:
      Bk{tl, ct, btl, bct, bon, (hols + 1 : U32)}

def bk.base_on(b: Bk) -> Bk:
  match b:
    case Bk{tl, ct, btl, bct, bon, hols}:
      Bk{tl, ct, btl, bct, True{}, hols}

def bk.nil() -> Bk:
  Bk{Map.new(&2, C.Tld), Map.new(&2, U32), Map.new(&2, C.Tld), Map.new(&2, U32), False{}, 0}

# Cursor
# ------

def cur.of(xs: List<&2, U32>) -> Cur:
  Cur{xs, 0, 1, True{}, C.NONE()}

def cur.rest(c: Cur) -> List<&2, U32>:
  match c:
    case Cur{rest, pos, col, nl, prev}:
      rest

def cur.pos(c: Cur) -> U32:
  match c:
    case Cur{rest, pos, col, nl, prev}:
      pos

def cur.col(c: Cur) -> U32:
  match c:
    case Cur{rest, pos, col, nl, prev}:
      col

def cur.nl(c: Cur) -> Bool:
  match c:
    case Cur{rest, pos, col, nl, prev}:
      nl

def cur.prev(c: Cur) -> U32:
  match c:
    case Cur{rest, pos, col, nl, prev}:
      prev

def cur.peek.go(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      C.NONE()
    case Con{h, t}:
      h

def cur.peek2.go(xs: List<&2, U32>) -> U32:
  match xs:
    case Con{h, Con{g, t}}:
      g
    case _:
      C.NONE()

def cur.peek(c: Cur) -> U32:
  cur.peek.go(cur.rest(c))

# the unit n past pos
def cur.ahead(c: Cur, n: U32) -> U32:
  T.at(cur.rest(c), n)

# whether parse_nl holds after the unit c: a newline makes it, a space,
# carriage return or tab keeps it, anything else ends it
def nl.after(+c: U32, nl: Bool) -> Bool:
  match c:
    case 10:
      True{}
    case 32:
      nl
    case 13:
      nl
    case 9:
      nl
    case _:
      False{}

def col.after(+c: U32, col: U32) -> U32:
  match c:
    case 10:
      1
    case _:
      (col + 1 : U32)

# one unit forward (parse_bump past the end stays put but counts, as JS does)
def cur.bump(c: Cur) -> Cur:
  match c:
    case Cur{Nil{}, pos, col, nl, prev}:
      Cur{Nil{}, (pos + 1 : U32), (col + 1 : U32), False{}, C.NONE()}
    case Cur{Con{+h, t}, pos, col, nl, prev}:
      Cur{t, (pos + 1 : U32), col.after(h, col), nl.after(h, nl), h}

def cur.adv(n: Nat, c: Cur) -> Cur:
  match n:
    case 0n:
      c
    case 1n+p:
      cur.adv(p, cur.bump(c))

# parse_skip: spaces, newlines, carriage returns, tabs and # comments
def cur.skip.go(xs: List<&2, U32>, pos: U32, col: U32, nl: Bool, prev: U32, cm: Bool) -> Cur:
  match xs cm:
    case Nil{} _:
      Cur{Nil{}, pos, col, nl, prev}
    case Con{10, t} _:
      cur.skip.go(t, (pos + 1 : U32), 1, True{}, 10, False{})
    case Con{+h, t} True{}:
      cur.skip.go(t, (pos + 1 : U32), (col + 1 : U32), nl.after(h, nl), h, True{})
    case Con{32, t} False{}:
      cur.skip.go(t, (pos + 1 : U32), (col + 1 : U32), nl, 32, False{})
    case Con{13, t} False{}:
      cur.skip.go(t, (pos + 1 : U32), (col + 1 : U32), nl, 13, False{})
    case Con{9, t} False{}:
      cur.skip.go(t, (pos + 1 : U32), (col + 1 : U32), nl, 9, False{})
    case Con{35, t} False{}:
      cur.skip.go(t, (pos + 1 : U32), (col + 1 : U32), False{}, 35, True{})
    case Con{h, t} False{}:
      Cur{Con{h, t}, pos, col, nl, prev}

def cur.skip(c: Cur) -> Cur:
  match c:
    case Cur{rest, pos, col, nl, prev}:
      cur.skip.go(rest, pos, col, nl, prev, False{})

# the length of the run of name units at the head of xs
def name.run.go(xs: List<&2, U32>, n: Nat, on: Bool) -> Nat:
  match xs on:
    case _ False{}:
      n
    case Nil{} True{}:
      n
    case Con{+h, t} True{}:
      name.run.go(t, Nat.add(n, Bool.pick(Nat, T.is_name(h), 1n, 0n)), T.is_name(h))

def name.run(xs: List<&2, U32>) -> Nat:
  name.run.go(xs, 0n, True{})

# Failing
# -------

def quote(s: String) -> String:
  "'" ++ s ++ "'"

# parse_fail's observed text: the source between beg and end, else the
# unit at pos, else end of input
def fail.obs(+txt: List<&2, U32>, +beg: U32, +end: U32, +pos: U32) -> String:
  Bool.pick(String, U32.is_lt(beg, end), quote(T.str(T.slice(txt, beg, end))),
    Bool.pick(String, U32.is_lt(pos, U32.from_nat(T.len(txt))), quote(T.str(T.slice(txt, pos, (pos + 1 : U32)))), "end of input"))

def fail.mk(exp: String, +beg: U32, +end: U32, +pos: U32, +e: Env) -> C.Er:
  +txt = env.txt(e)
  C.Er{exp, Some{fail.obs(txt, beg, end, pos)}, C.Sp{env.fid(e), beg, end}, txt, None{}}

def fail.go(-A: Type, exp: String, beg: U32, end: U32, st: St) -> R<A>:
  match st:
    case St{c, e}:
      RErr{fail.mk(exp, beg, end, cur.pos(c), e)}

# parse_fail(p, exp, beg, end)
def P.fail.at(-A: Type, exp: String, beg: U32, end: U32) -> P(A):
  st => fail.go(A, exp, beg, end, st)

def fail.here(-A: Type, exp: String, st: St) -> R<A>:
  match st:
    case St{+c, e}:
      fail.go(A, exp, cur.pos(c), cur.pos(c), St{c, e})

# parse_fail(p, exp)
def P.fail(-A: Type, exp: String) -> P(A):
  st => fail.here(A, exp, st)

def fail.from(-A: Type, exp: String, beg: U32, st: St) -> R<A>:
  match st:
    case St{+c, e}:
      fail.go(A, exp, beg, cur.pos(c), St{c, e})

# parse_fail(p, exp, beg)
def P.fail.from(-A: Type, exp: String, beg: U32) -> P(A):
  st => fail.from(A, exp, beg, st)

def err.go(-A: Type, exp: String, obs: Maybe<&2, String>, s: C.Sp, st: St) -> R<A>:
  match st:
    case St{c, e}:
      RErr{C.Er{exp, obs, s, env.txt(e), None{}}}

# throw Err(book, ctx_nil(), exp, obs, s): an error at a term's span
def P.err(-A: Type, exp: String, obs: Maybe<&2, String>, s: C.Sp) -> P(A):
  st => err.go(A, exp, obs, s, st)

# Lexing
# ------

def P.peek() -> P(U32):
  do P<U32>:
    c : Cur <- P.cur()
    return cur.peek(c)

def P.ahead(n: U32) -> P(U32):
  do P<U32>:
    c : Cur <- P.cur()
    return cur.ahead(c, n)

def P.pos() -> P(U32):
  do P<U32>:
    c : Cur <- P.cur()
    return cur.pos(c)

def P.col() -> P(U32):
  do P<U32>:
    c : Cur <- P.cur()
    return cur.col(c)

def P.nl() -> P(Bool):
  do P<Bool>:
    c : Cur <- P.cur()
    return cur.nl(c)

def P.bump() -> P(Unit):
  P.mod_cur(cur.bump)

def P.skip() -> P(Unit):
  P.mod_cur(cur.skip)

# parse_at(p, s): the units of s are next
def P.at(s: List<&2, U32>) -> P(Bool):
  do P<Bool>:
    c : Cur <- P.cur()
    return T.prefix(cur.rest(c), s)

def take.if(z: Bool, n: Nat) -> P(Bool):
  match z:
    case True{}:
      do P<Bool>:
        P.mod_cur(cur.adv(n))
        return True{}
    case False{}:
      P.pure(Bool, False{})

# parse_take(p, s)
def P.take(+s: List<&2, U32>) -> P(Bool):
  do P<Bool>:
    c : Cur <- P.cur()
    take.if(T.prefix(cur.rest(c), s), T.len(s))

def eat.if(z: Bool, s: String) -> P(Unit):
  match z:
    case True{}:
      P.pure(Unit, Unit{})
    case False{}:
      P.fail(Unit, quote(s))

# parse_eat(p, s)
def P.eat(+s: String) -> P(Unit):
  do P<Unit>:
    P.skip()
    z : Bool <- P.take(T.units(s))
    eat.if(z, s)

# parse_at_word(p, w): skip, then w with no name unit after it
def P.at_word(+w: String) -> P(Bool):
  do P<Bool>:
    P.skip()
    +c : Cur <- P.cur()
    +u : List<&2, U32> = T.units(w)
    return Bool.and(T.prefix(cur.rest(c), u), Bool.not(T.is_name(cur.ahead(c, U32.from_nat(T.len(u))))))

# parse_word(p, w)
def P.word(+w: String) -> P(Bool):
  do P<Bool>:
    z : Bool <- P.at_word(w)
    take.if(z, T.len(T.units(w)))

def KEYWORDS() -> List<&2, String>:
  ["def", "type", "law", "match", "case", "do", "return", "for", "exs", "where", "is", "import", "Type", "Data", "Kind", "Quant"]

def is_keyword.go(ks: List<&2, String>, +k: String) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(String.eq(h, k), is_keyword.go(t, k))

def is_keyword(k: String) -> Bool:
  is_keyword.go(KEYWORDS(), k)

# a dot not followed by a letter or _ (the lexeme's /\.(?![A-Za-z_])/)
def bad_dot.next(t: List<&2, U32>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case Con{+h, r}:
      Bool.not(T.is_head(h))

def bad_dot(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{46, +t}:
      Bool.or(bad_dot.next(t), bad_dot(t))
    case Con{h, t}:
      bad_dot(t)

def lexeme.check(z: Bool, +k: String, beg: U32) -> P(String):
  match z:
    case True{}:
      P.fail.from(String, "a name (words joined by dots, got " ++ quote(k) ++ ")", beg)
    case False{}:
      P.pure(String, k)

def lexeme.fin(+xs: List<&2, U32>, +beg: U32) -> P(String):
  lexeme.check(bad_dot(xs), T.str(xs), beg)

def lexeme.go(z: Bool, +c: Cur) -> P(String):
  match z:
    case False{}:
      P.fail(String, "a name")
    case True{}:
      +n = name.run(cur.rest(c))
      do P<String>:
        P.mod_cur(cur.adv(n))
        lexeme.fin(T.take(cur.rest(c), n), cur.pos(c))

# parse_lexeme
def P.lexeme() -> P(String):
  do P<String>:
    P.skip()
    +c : Cur <- P.cur()
    lexeme.go(T.is_head(cur.peek(c)), c)

def name.check(z: Bool, +k: String) -> P(String):
  match z:
    case True{}:
      do P<String>:
        +pos : U32 <- P.pos()
        P.fail.from(String, "a name (got the keyword " ++ quote(k) ++ ")", (pos - U32.from_nat(String.length(k)) : U32))
    case False{}:
      P.pure(String, k)

# parse_name
def P.name() -> P(String):
  do P<String>:
    +k : String <- P.lexeme()
    name.check(is_keyword(k), k)

# \u{X} after a backslash: /^u\{([0-9a-f]+)\}/i over the next 11 units
def hex.digit(+c: U32) -> U32:
  Bool.pick(U32, T.is_digit(c), (c - 48 : U32),
    Bool.pick(U32, Bool.and(U32.is_le(97, c), U32.is_le(c, 102)), (c - 87 : U32),
      Bool.pick(U32, Bool.and(U32.is_le(65, c), U32.is_le(c, 70)), (c - 55 : U32), 16)))

def hex.run.go(xs: List<&2, U32>, n: Nat, on: Bool) -> Nat:
  match xs on:
    case _ False{}:
      n
    case Nil{} True{}:
      n
    case Con{+h, t} True{}:
      +d = U32.is_lt(hex.digit(h), 16)
      hex.run.go(t, Nat.add(n, Bool.pick(Nat, d, 1n, 0n)), d)

def hex.val(xs: List<&2, U32>, v: U32) -> U32:
  match xs:
    case Nil{}:
      v
    case Con{+h, t}:
      hex.val(t, ((v << 4n) .|. hex.digit(h) : U32))

def hex.close(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{125, t}:
      True{}
    case _:
      False{}

# after the backslash, the window w (11 units): the code and the units the
# escape takes past the backslash, or 0n when it is no \u{..}
def hex.esc.got(+ds: List<&2, U32>, +n: Nat) -> U32 & Nat:
  (hex.val(T.take(ds, n), 0), Nat.add(n, 3n))

def hex.esc.body(+ds: List<&2, U32>) -> U32 & Nat:
  +n = hex.run.go(ds, 0n, True{})
  Bool.pick(U32 & Nat, Bool.and(Bool.not(Nat.is_eq(n, 0n)), hex.close(T.drop(ds, n))), hex.esc.got(ds, n), (0, 0n))

def hex.esc(w: List<&2, U32>) -> U32 & Nat:
  match w:
    case Con{117, Con{123, ds}}:
      hex.esc.body(ds)
    case Con{85, Con{123, ds}}:
      hex.esc.body(ds)
    case _:
      (0, 0n)

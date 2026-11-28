import Base
import ./Text.bend as T
import ./PHelp.bend as X
import ../lib/F64.bend as F

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Lower: G, bendbis's additions lowered to upstream Bend (DESIGN.md, "bend
# and bendbis: the adjunction"). On a file's text (UTF-16 units, as the
# loader holds it):
#
# - a header line `import F64` (the bare import, which upstream refuses)
#   becomes `import REL as F64`, REL the path from the file's directory to
#   bendbis's lib/F64.bend: the type is F64.F64, the operations F64.add,
#   ..., the operators (a + b : F64.F64);
# - in such a file, past the header, a literal NUMBER.NUMBER[EXP]d (F32's
#   literal with a d after it, and no name character after the d) becomes
#   F64.lit(HI, LO), the nearest F64's bits (F64.of_dec); a literal past
#   the F64 range stays as written (upstream then reads an F32 literal
#   and a name). Comments, strings and chars are copied as they are.
#
# A file with no `import F64` is returned as it is: G is the identity on
# upstream's programs (the unit of the adjunction), and G(G(Q)) = G(Q)
# (G's output has no bare import left). The loader lowers every file it
# reads, so bendbis reads Q as it reads G(Q), and bendbis lower FILE prints
# G(FILE) for upstream bend.

def rev.onto(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{c, t}:
      rev.onto(t, c <> acc)

# The header
# ----------

# a line: the units before the first \n, and what follows that \n
def ln.take(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{10, t}:
      Nil{}
    case Con{c, t}:
      c <> ln.take(t)

def ln.rest(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      None{}
    case Con{10, t}:
      Some{t}
    case Con{c, t}:
      ln.rest(t)

# String.prototype.trim (Load's)
def trim.start(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{+c, +t}:
      Bool.pick(List<&2, U32>, T.is_space(c), trim.start(t), Con{c, t})
    case Nil{}:
      Nil{}

def trim(+xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, trim.start(List.reverse(&2, U32, trim.start(xs))))

def spaces(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{+c, +t}:
      Bool.pick(List<&2, U32>, T.is_space(c), spaces(t), Con{c, t})
    case Nil{}:
      Nil{}

# a line's role before the first non-import (Load's line.role): 0 skip
# (empty or #), 1 an import, 2 the end of the header
def ln.role.after(t: List<&2, U32>) -> Nat:
  match t:
    case Nil{}:
      1n
    case Con{+c, r}:
      Bool.pick(Nat, T.is_space(c), 1n, 2n)

def ln.role(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{35, t}:
      0n
    case Con{105, Con{109, Con{112, Con{111, Con{114, Con{116, t}}}}}}:
      ln.role.after(t)
    case _:
      2n

# is a line terminator other than \n (Load's)
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

# a trimmed line is `import F64`, then spaces and a comment at most: the
# path F64 and no alias, as Load's im.match reads it
def is.f64.end(a: List<&2, U32>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case Con{+c, +t}:
      Bool.and(T.is_space(c), tail.end(t))

def is.f64.p(r: List<&2, U32>) -> Bool:
  match r:
    case Con{70, Con{54, Con{52, a}}}:
      is.f64.end(a)
    case _:
      False{}

def is.f64.sp(t: List<&2, U32>) -> Bool:
  match t:
    case Con{+c, +r}:
      Bool.and(T.is_space(c), is.f64.p(spaces(r)))
    case Nil{}:
      False{}

def is.f64(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{105, Con{109, Con{112, Con{111, Con{114, Con{116, t}}}}}}:
      is.f64.sp(t)
    case _:
      False{}

def imp.line(+rel: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, T.units("import "), List.append(&2, U32, rel, T.units(" as F64")))

# the header, line by line: its pieces so far (each line with its \n,
# reversed), and whether a bare `import F64` was among them
type Hj is Data:
  HStart{xs: List<&2, U32>, acc: List<&2, List<&2, U32>>, hit: Bool}
  HRole{role: Nat, xs: List<&2, U32>, acc: List<&2, List<&2, U32>>, hit: Bool}
  HNext{r: Maybe<&2, List<&2, U32>>, l: List<&2, U32>, acc: List<&2, List<&2, U32>>, hit: Bool}

# the header's pieces (reversed), the rest of the text, the hit
type Hd is Data:
  Hd{acc: List<&2, List<&2, U32>>, rest: List<&2, U32>, hit: Bool}

def hd.go(fuel: Nat, +rel: List<&2, U32>, j: Hj) -> Hd:
  match fuel j:
    case 0n _:
      Hd{Nil{}, Nil{}, False{}}
    case 1n+p HStart{+xs, acc, hit}:
      hd.go(p, rel, HRole{ln.role(trim(ln.take(xs))), xs, acc, hit})
    case 1n+p HRole{role, +xs, acc, +hit}:
      match role:
        case 2n:
          Hd{acc, xs, hit}
        case _:
          +l = ln.take(xs)
          +f = is.f64(trim(l))
          hd.go(p, rel, HNext{ln.rest(xs), Bool.pick(List<&2, U32>, f, imp.line(rel), l), acc, Bool.or(hit, f)})
    case 1n+p HNext{r, l, acc, hit}:
      match r:
        case None{}:
          Hd{l <> acc, Nil{}, hit}
        case Some{t}:
          hd.go(p, rel, HStart{t, List.append(&2, U32, l, [10]) <> acc, hit})

# The body
# --------

# a unit's class in code: 0 other, 1 #, 2 a quote, 3 a name's head, 4 a digit
def bd.cls(+c: U32) -> Nat:
  Bool.pick(Nat, U32.is_eq(c, 35), 1n,
    Bool.pick(Nat, Bool.or(U32.is_eq(c, 34), U32.is_eq(c, 39)), 2n,
      Bool.pick(Nat, T.is_head(c), 3n,
        Bool.pick(Nat, T.is_digit(c), 4n, 0n))))

# an F32 literal's rest is a d and no name character
def bd.isd.t(t: List<&2, U32>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case Con{+c, r}:
      Bool.not(T.is_name(c))

def bd.isd.r(rest: List<&2, U32>) -> Bool:
  match rest:
    case Con{100, t}:
      bd.isd.t(t)
    case _:
      False{}

def bd.isd(kind: Nat, rest: List<&2, U32>) -> Bool:
  match kind:
    case 2n:
      bd.isd.r(rest)
    case _:
      False{}

def lit.units(+v: F.F64) -> List<&2, U32>:
  T.units("F64.lit(" ++ U32.show(F.bits.hi(v)) ++ ", " ++ U32.show(F.bits.lo(v)) ++ ")")

# the scan, the text out so far reversed in acc
type Bj is Data:
  BCode{xs: List<&2, U32>, acc: List<&2, U32>}
  BCls{k: Nat, c: U32, t: List<&2, U32>, acc: List<&2, U32>}
  BName{xs: List<&2, U32>, acc: List<&2, U32>}
  BCom{xs: List<&2, U32>, acc: List<&2, U32>}
  BStr{q: U32, xs: List<&2, U32>, acc: List<&2, U32>}
  BNum{nm: X.Nm, xs: List<&2, U32>, acc: List<&2, U32>}
  BLit{yes: Bool, nm: X.Nm, xs: List<&2, U32>, rest: List<&2, U32>, acc: List<&2, U32>}
  BFin{inf: Bool, v: F.F64, len: Nat, xs: List<&2, U32>, rest: List<&2, U32>, acc: List<&2, U32>}

def bd.go(fuel: Nat, j: Bj) -> List<&2, U32>:
  match fuel j:
    case 0n _:
      Nil{}
    case 1n+p BCode{Nil{}, acc}:
      acc
    case 1n+p BCode{Con{+c, t}, acc}:
      bd.go(p, BCls{bd.cls(c), c, t, acc})
    case 1n+p BCls{k, +c, t, acc}:
      match k:
        case 0n:
          bd.go(p, BCode{t, c <> acc})
        case 1n:
          bd.go(p, BCom{t, c <> acc})
        case 2n:
          bd.go(p, BStr{c, t, c <> acc})
        case 3n:
          bd.go(p, BName{t, c <> acc})
        case _:
          +xs : List<&2, U32> = Con{c, t}
          bd.go(p, BNum{X.num.read(xs), xs, acc})
    case 1n+p BName{Nil{}, acc}:
      acc
    case 1n+p BName{Con{+c, +t}, +acc}:
      bd.go(p, Bool.pick(Bj, T.is_name(c), BName{t, c <> acc}, BCode{Con{c, t}, acc}))
    case 1n+p BCom{Nil{}, acc}:
      acc
    case 1n+p BCom{Con{10, t}, acc}:
      bd.go(p, BCode{t, 10 <> acc})
    case 1n+p BCom{Con{c, t}, acc}:
      bd.go(p, BCom{t, c <> acc})
    case 1n+p BStr{q, Nil{}, acc}:
      acc
    case 1n+p BStr{q, Con{92, Con{c, t}}, acc}:
      bd.go(p, BStr{q, t, c <> 92 <> acc})
    case 1n+p BStr{+q, Con{+c, +t}, +acc}:
      bd.go(p, Bool.pick(Bj, U32.is_eq(c, q), BCode{t, c <> acc}, BStr{q, t, c <> acc}))
    case 1n+p BNum{+nm, +xs, acc}:
      match nm:
        case X.Nm{ds, kind, fs, neg, es, +len}:
          +rest = T.drop(xs, len)
          bd.go(p, BLit{bd.isd(kind, rest), nm, xs, rest, acc})
    case 1n+p BLit{yes, nm, +xs, rest, acc}:
      match yes nm:
        case True{} X.Nm{ds, kind, fs, neg, es, len}:
          +v = F.of_dec(ds, fs, neg, es)
          bd.go(p, BFin{F.is_inf(v), v, len, xs, rest, acc})
        case False{} X.Nm{ds, kind, fs, neg, es, len}:
          bd.go(p, BCode{rest, rev.onto(T.take(xs, len), acc)})
    case 1n+p BFin{inf, v, len, xs, rest, acc}:
      match inf:
        case True{}:
          bd.go(p, BCode{rest, rev.onto(T.take(xs, len), acc)})
        case False{}:
          bd.go(p, BCode{List.drop(&2, U32, rest, 1n), rev.onto(lit.units(v), acc)})

# G
# -

def lower.hd(h: Hd, txt: List<&2, U32>) -> List<&2, U32>:
  match h:
    case Hd{acc, rest, hit}:
      match hit:
        case True{}:
          List.append(&2, U32, List.concat(&2, U32, List.reverse(&2, List<&2, U32>, acc)), List.reverse(&2, U32, bd.go(4294967295n, BCode{rest, Nil{}})))
        case False{}:
          txt

# G on a file's text; rel the path from the file's directory to F64.bend
def lower(+txt: List<&2, U32>, +rel: List<&2, U32>) -> List<&2, U32>:
  lower.hd(hd.go(4294967295n, rel, HStart{txt, Nil{}, False{}}), txt)

# where F64.bend is: $BENDBIS_LIB/F64.bend, by default
# $HOME/src/bendbis/lib/F64.bend
def env.or(r: Result<&1, &1, U32 & String, String>, d: String) -> String:
  match r:
    case Done{v}:
      v
    case Fail{e}:
      d

def f64.path() -> IO(String):
  do IO<String>:
    h : Result<&1, &1, U32 & String, String> <- IO.get_env("HOME")
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("BENDBIS_LIB")
    return env.or(r, env.or(h, "/") ++ "/src/bendbis/lib") ++ "/F64.bend"

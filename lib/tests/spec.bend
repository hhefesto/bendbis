import Base
import ../F64.bend as F
import ../SPEC.bend as S

# lib/tests/spec.bend N: SPEC.bend's laws on inputs: the specials' table
# (every pair) and N pseudo-random pairs in each of three sections (random
# bits; exponents near each other; exponents at the ends of the range).
# Prints each input where F64.bend and the spec differ, then "C checks, D
# differ".

def xs(+x: U32) -> U32:
  +a = (x .^. (x << 13n : U32) : U32)
  +b = (a .^. (a >> 17n : U32) : U32)
  (b .^. (b << 5n : U32) : U32)

# x's 8 hex digits
def hx.go(k: Nat, +x: U32, acc: String) -> String:
  match k:
    case 0n:
      acc
    case 1n+p:
      +d = (x .&. 15 : U32)
      hx.go(p, (x >> 4n : U32), SCon{Chr{(d + 48 + Bool.to_u32((d > 9 : U32)) * 39 : U32)}, acc})

def hx(x: U32) -> String:
  hx.go(8n, x, SNil{})

def hf(+x: F.F64) -> String:
  hx(F.bits.hi(x)) ++ hx(F.bits.lo(x))

# A tally: checks, differences, and the lines of the differences
type T is Data:
  T{n: U32, d: U32, out: String}

def t.zero() -> T:
  T{0, 0, ""}

def t.one(name: String, +a: F.F64, +b: F.F64, ok: Bool) -> T:
  match ok:
    case True{}:
      T{1, 0, ""}
    case False{}:
      T{1, 1, name ++ " " ++ hf(a) ++ " " ++ hf(b) ++ "\n"}

def t.add(x: T, y: T) -> T:
  match x y:
    case T{n, d, o} T{m, e, p}:
      T{(n + m : U32), (d + e : U32), o ++ p}

def same(a: F.F64, b: F.F64) -> Bool:
  match a b:
    case F.F64{ah, al} F.F64{bh, bl}:
      Bool.and(U32.is_eq(ah, bh), U32.is_eq(al, bl))

def b.eq(a: Bool, b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

def pair(+a: F.F64, +b: F.F64) -> T:
  t.add(t.one("add", a, b, same(F.add(a, b), S.s.add(a, b))),
  t.add(t.one("sub", a, b, same(F.sub(a, b), S.s.sub(a, b))),
  t.add(t.one("mul", a, b, same(F.mul(a, b), S.s.mul(a, b))),
  t.add(t.one("div", a, b, same(F.div(a, b), S.s.div(a, b))),
  t.add(t.one("lt", a, b, b.eq(F.is_lt(a, b), S.s.lt(a, b))),
  t.add(t.one("eq", a, b, b.eq(F.is_eq(a, b), S.s.eq(a, b))),
  t.add(t.one("sqrt", a, b, same(F.sqrt(a), S.s.sqrt(a))),
        t.one("to_f32", a, b, U32.is_eq(F.f32.bits(F.to_f32(a)), S.s.to_f32(a))))))))))

def specials() -> List<&2, F.F64>:
  [F.lit(0, 0), F.lit(2147483648, 0), F.lit(0, 1), F.lit(1048575, 4294967295),
   F.lit(1048576, 0), F.lit(1072693248, 0), F.lit(3220176896, 0), F.lit(1072693248, 1),
   F.lit(1072693247, 4294967295), F.lit(2146435071, 4294967295), F.lit(2146435072, 0),
   F.lit(4293918720, 0), F.lit(2146959360, 0), F.lit(1073741824, 0), F.lit(1071644672, 0),
   F.lit(1017118720, 0), F.lit(1018167296, 0), F.lit(1127219200, 0), F.lit(1128267776, 0),
   F.lit(1074340347, 1413754136), F.lit(1069128089, 2576980378), F.lit(3221225472, 0),
   F.lit(2145386496, 0), F.lit(524288, 0), F.lit(2147483648, 1), F.lit(1073217536, 0),
   F.lit(2146435072, 1), F.lit(1070945621, 1431655765), F.lit(1048576, 1),
   F.lit(2146435071, 4294967294), F.lit(1206910975, 3758096384), F.lit(939524096, 0)]

def sp.in(+a: F.F64, ys: List<&2, F.F64>) -> T:
  match ys:
    case Nil{}:
      t.zero()
    case Con{+b, t}:
      t.add(pair(a, b), sp.in(a, t))

def sp.out(ws: List<&2, F.F64>, +all: List<&2, F.F64>) -> T:
  match ws:
    case Nil{}:
      t.zero()
    case Con{+a, t}:
      t.add(sp.in(a, all), sp.out(t, all))

def at(+r1: U32, +r2: U32, +ex: U32) -> F.F64:
  F.lit(((r1 .&. 2148532223 : U32) .|. ((ex .&. 2047 : U32) << 20n : U32) : U32), r2)

def ends(+r: U32) -> U32:
  Bool.pick(U32, U32.is_eq((r .&. 64 : U32), 0), (r .&. 63 : U32), (2046 - (r .&. 63 : U32) : U32))

# mode 0: random bits; 1: exponents near each other; 2: at the ends
def gen(mode: Nat, +s1: U32, +s2: U32, +s3: U32, +s4: U32) -> T:
  match mode:
    case 0n:
      pair(F.lit(s1, s2), F.lit(s3, s4))
    case 1n:
      pair(at(s1, s2, (1000 + (s4 .&. 63 : U32) : U32)),
        at(s3, s4, (((1000 + (s4 .&. 63 : U32) : U32) + ((s4 >> 8n : U32) .&. 127 : U32) : U32) - 63 : U32)))
    case _:
      pair(at(s1, s2, ends(s4)), at(s3, s4, ends((s4 >> 8n : U32))))

def rnd(+n: Nat, +mode: Nat, +s: U32) -> T:
  match n:
    case 0n:
      t.zero()
    case 1n+p:
      +s1 = xs(s)
      +s2 = xs(s1)
      +s3 = xs(s2)
      +s4 = xs(s3)
      t.add(gen(mode, s1, s2, s3, s4), rnd(p, mode, s4))

def go(+n: Nat) -> T:
  t.add(sp.out(specials(), specials()),
  t.add(rnd(n, 0n, 2463534242),
  t.add(rnd(n, 1n, 88172645), rnd(n, 2n, 521288629))))

def show(t: T) -> String:
  match t:
    case T{n, d, o}:
      o ++ U32.show(n) ++ " checks, " ++ U32.show(d) ++ " differ\n"

def arg(args: List<String>) -> Nat:
  match args:
    case Con{p, Con{a, t}}:
      U32.to_nat(Maybe.default(&2, U32, U32.read(a), 100))
    case _:
      100n

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.write(show(go(arg(args))))

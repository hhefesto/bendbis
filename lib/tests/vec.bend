import Base
import ../F64.bend as F

# lib/tests/vec.bend: F64.bend's answers on chosen and pseudo-random
# inputs, one line each: OP AHI ALO BHI BLO RHI RLO (hex), for Oracle.hs to
# hold against the machine's double. OP is add, sub, mul, div, sqrt (b 0),
# lt, le, eq (r 0 or 1), s2d (an F32's bits in alo, the F64 in r), d2s
# (the F32's bits in rlo). The argument is the count of random lines per
# section (decimal U32).

def xs(+x: U32) -> U32:
  +a = (x .^. (x << 13n : U32) : U32)
  +b = (a .^. (a >> 17n : U32) : U32)
  (b .^. (b << 5n : U32) : U32)

def b01(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

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

def ln(op: String, +ah: U32, +al: U32, +bh: U32, +bl: U32, +rh: U32, +rl: U32) -> String:
  op ++ " " ++ hx(ah) ++ " " ++ hx(al) ++ " " ++ hx(bh) ++ " " ++ hx(bl) ++ " " ++ hx(rh) ++ " " ++ hx(rl) ++ "\n"

def ln.f(op: String, +a: F.F64, +b: F.F64, +r: F.F64) -> String:
  ln(op, F.bits.hi(a), F.bits.lo(a), F.bits.hi(b), F.bits.lo(b), F.bits.hi(r), F.bits.lo(r))

def ln.b(op: String, +a: F.F64, +b: F.F64, r: Bool) -> String:
  ln(op, F.bits.hi(a), F.bits.lo(a), F.bits.hi(b), F.bits.lo(b), 0, b01(r))

def bin(+a: F.F64, +b: F.F64) -> String:
  ln.f("add", a, b, F.add(a, b)) ++ ln.f("sub", a, b, F.sub(a, b)) ++
  ln.f("mul", a, b, F.mul(a, b)) ++ ln.f("div", a, b, F.div(a, b)) ++
  ln.b("lt", a, b, F.is_lt(a, b)) ++ ln.b("le", a, b, F.is_le(a, b)) ++
  ln.b("eq", a, b, F.is_eq(a, b))

def un(+a: F.F64) -> String:
  ln.f("sqrt", a, F.zero(0), F.sqrt(a)) ++
  ln("d2s", F.bits.hi(a), F.bits.lo(a), 0, 0, 0, F.f32.bits(F.to_f32(a)))

def s2d(+u: U32) -> String:
  +d = F.from_f32(F.f32.of_bits(u))
  ln("s2d", 0, u, 0, 0, F.bits.hi(d), F.bits.lo(d))

def specials() -> List<&2, F.F64>:
  [F.lit(0, 0), F.lit(2147483648, 0), F.lit(0, 1), F.lit(1048575, 4294967295),
   F.lit(1048576, 0), F.lit(1072693248, 0), F.lit(3220176896, 0), F.lit(1072693248, 1),
   F.lit(1072693247, 4294967295), F.lit(2146435071, 4294967295), F.lit(2146435072, 0),
   F.lit(4293918720, 0), F.lit(2146959360, 0), F.lit(1073741824, 0), F.lit(1071644672, 0),
   F.lit(1017118720, 0), F.lit(1018167296, 0), F.lit(1127219200, 0), F.lit(1128267776, 0),
   F.lit(1074340347, 1413754136), F.lit(1069128089, 2576980378), F.lit(3221225472, 0),
   F.lit(2145386496, 0), F.lit(524288, 0), F.lit(2147483648, 1), F.lit(1073217536, 0),
   F.lit(2146435072, 1), F.lit(1070945621, 1431655765), F.lit(1048576, 1),
   F.lit(2146435071, 4294967294)]

def sp.in(+a: F.F64, ys: List<&2, F.F64>) -> String:
  match ys:
    case Nil{}:
      un(a)
    case Con{+b, t}:
      bin(a, b) ++ sp.in(a, t)

def sp.out(ws: List<&2, F.F64>, +all: List<&2, F.F64>) -> String:
  match ws:
    case Nil{}:
      ""
    case Con{+a, t}:
      sp.in(a, all) ++ sp.out(t, all)

# an F64 of random sign and mantissa, its exponent field ex
def at(+r1: U32, +r2: U32, +ex: U32) -> F.F64:
  F.lit(((r1 .&. 2148532223 : U32) .|. ((ex .&. 2047 : U32) << 20n : U32) : U32), r2)

# random bits
def rnd.bits(+n: Nat, +s: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      +s1 = xs(s)
      +s2 = xs(s1)
      +s3 = xs(s2)
      +s4 = xs(s3)
      bin(F.lit(s1, s2), F.lit(s3, s4)) ++ un(F.lit(s1, s2)) ++ s2d(s3) ++ rnd.bits(p, s4)

# exponents near each other (cancellation, rounding at every distance)
def rnd.near(+n: Nat, +s: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      +s1 = xs(s)
      +s2 = xs(s1)
      +s3 = xs(s2)
      +s4 = xs(s3)
      +e1 = (1000 + (s4 .&. 63 : U32) : U32)
      +e2 = ((e1 + ((s4 >> 8n : U32) .&. 127 : U32) : U32) - 63 : U32)
      bin(at(s1, s2, e1), at(s3, s4, e2)) ++ un(at(s3, s2, e2)) ++ rnd.near(p, s4)

# exponents at the ends of the range (overflow, underflow, subnormals),
# and around F32's range for d2s
def rnd.edge(+n: Nat, +s: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      +s1 = xs(s)
      +s2 = xs(s1)
      +s3 = xs(s2)
      +s4 = xs(s3)
      +e1 = Bool.pick(U32, U32.is_eq((s4 .&. 1 : U32), 0), ((s4 >> 1n : U32) .&. 63 : U32), (2046 - ((s4 >> 1n : U32) .&. 63 : U32) : U32))
      +e2 = Bool.pick(U32, U32.is_eq((s4 .&. 256 : U32), 0), ((s4 >> 9n : U32) .&. 63 : U32), (2046 - ((s4 >> 9n : U32) .&. 63 : U32) : U32))
      +e3 = (850 + ((s4 >> 16n : U32) .&. 351 : U32) : U32)
      bin(at(s1, s2, e1), at(s3, s4, e2)) ++ un(at(s1, s3, e3)) ++ rnd.edge(p, s4)

def go(+n: Nat) -> String:
  sp.out(specials(), specials()) ++ rnd.bits(n, 2463534242) ++ rnd.near(n, 88172645) ++ rnd.edge(n, 521288629)

def arg(args: List<String>) -> Nat:
  match args:
    case Con{p, Con{a, t}}:
      U32.to_nat(Maybe.default(&2, U32, U32.read(a), 100))
    case _:
      100n

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.write(go(arg(args)))

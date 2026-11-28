import Base
import ../F64.bend as F

# lib/tests/dec.bend: F64.bend's of_dec (a decimal literal's value) on
# chosen and pseudo-random decimals, one line each: dec I F X RHI RLO, the
# decimal I.F e X (F may be "-": none; X signed) and of_dec's bits (hex),
# for Oracle.hs to hold against the machine's reading of the same text.
# The argument is the count of random lines per section (decimal U32).
# Sections: random digits and exponents over the whole range and past it;
# the exact midpoints between neighbouring doubles (each must round to the
# even one) and the decimals one unit in the last digit below and above
# them (each must round to the near side), from random doubles, normal and
# subnormal; long decimals (40 and more digits).

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

def str.of(ds: List<&2, U32>) -> String:
  match ds:
    case Nil{}:
      SNil{}
    case Con{d, t}:
      SCon{Chr{d}, str.of(t)}

# a big natural's decimal digits (codes), most significant first: the
# loop's state, a natural still to spell or a division by 10 done
type Ds is Data:
  DIn{xs: List<&2, U32>, acc: List<&2, U32>}
  DQr{q: List<&2, U32>, r: U32, acc: List<&2, U32>}

# xs (most significant limb first) / 10: the quotient (least significant
# first) and the remainder
def d10.go(xs: List<&2, U32>, +rem: U32, q: List<&2, U32>, acc: List<&2, U32>) -> Ds:
  match xs:
    case Nil{}:
      DQr{q, rem, acc}
    case Con{+x, t}:
      +v = ((rem << 16n : U32) .|. x : U32)
      d10.go(t, (v % 10 : U32), (v / 10 : U32) <> q, acc)

def big.dec.go(fuel: Nat, st: Ds) -> List<&2, U32>:
  match fuel st:
    case 0n DIn{xs, acc}:
      acc
    case 0n DQr{q, r, acc}:
      acc
    case 1n+p DIn{Nil{}, acc}:
      acc
    case 1n+p DIn{xs, acc}:
      big.dec.go(p, d10.go(List.reverse(&2, U32, xs), 0, Nil{}, acc))
    case 1n+p DQr{q, r, acc}:
      big.dec.go(p, DIn{F.big.trim(q), (r + 48 : U32) <> acc})

def big.dec(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [48]
    case xs:
      big.dec.go(8000n, DIn{xs, Nil{}})

# an exponent: sign and digits
def ex.of(neg: Bool, +k: U32) -> String:
  match neg:
    case True{}:
      "-" ++ U32.show(k)
    case False{}:
      U32.show(k)

def u32.digits(+k: U32) -> List<&2, U32>:
  big.dec(F.big.of2(0, k))

def ln(+i: List<&2, U32>, +f: List<&2, U32>, +xneg: Bool, +k: U32) -> String:
  +r = F.of_dec(i, f, xneg, u32.digits(k))
  "dec " ++ str.of(i) ++ " " ++ Bool.pick(String, List.is_empty(&2, U32, f), "-", str.of(f)) ++ " " ++ ex.of(xneg, k) ++ " " ++ hx(F.bits.hi(r)) ++ " " ++ hx(F.bits.lo(r)) ++ "\n"

# a signed exponent e - 1000 as (negative, magnitude)
def sgn(+e: U32) -> Bool & U32:
  Bool.pick(Bool & U32, U32.is_lt(e, 1000), (True{}, (1000 - e : U32)), (False{}, (e - 1000 : U32)))

def ln.e(+i: List<&2, U32>, +f: List<&2, U32>, nk: Bool & U32) -> String:
  (neg, +k) = nk
  ln(i, f, neg, k)

# the chosen: zeros, the ends of the range, ties, long fractions
def chosen() -> String:
  ln([48], Nil{}, False{}, 0) ++ ln([48], [48, 48, 48], True{}, 5) ++
  ln([49], Nil{}, False{}, 0) ++ ln([48], [49], False{}, 0) ++ ln([49], [53], False{}, 0) ++
  ln([50], [53], False{}, 0) ++ ln([51], [49, 52, 49, 53, 57, 50, 54, 53, 51, 53, 56, 57, 55, 57, 51, 50, 51, 56, 52, 54, 50, 54, 52, 51, 51, 56, 51, 50, 55, 57, 53], False{}, 0) ++
  ln([49], [55, 57, 55, 54, 57, 51, 49, 51, 52, 56, 54, 50, 51, 49, 53, 55], False{}, 308) ++
  ln([49], [55, 57, 55, 54, 57, 51, 49, 51, 52, 56, 54, 50, 51, 49, 53, 56], False{}, 308) ++
  ln([49], [56], False{}, 308) ++ ln([49], Nil{}, False{}, 309) ++ ln([49], Nil{}, False{}, 400) ++
  ln([52], [57, 52, 48, 54, 53, 54, 52, 53, 56, 52, 49, 50, 52, 54, 53, 52, 52], True{}, 324) ++
  ln([50], [52, 55, 48, 51, 50, 56], True{}, 324) ++ ln([50], [52, 55, 48, 51, 50, 57], True{}, 324) ++
  ln([50], [52], True{}, 324) ++ ln([49], Nil{}, True{}, 324) ++ ln([49], Nil{}, True{}, 400) ++
  ln([50], [50, 50, 53, 48, 55, 51, 56, 53, 56, 53, 48, 55, 50, 48, 49, 51], True{}, 308) ++
  ln([57, 48, 48, 55, 49, 57, 57, 50, 53, 52, 55, 52, 48, 57, 57, 51, 51], Nil{}, False{}, 0) ++
  ln([57, 48, 48, 55, 49, 57, 57, 50, 53, 52, 55, 52, 48, 57, 57, 51, 53], Nil{}, False{}, 0) ++
  ln([49], Nil{}, False{}, 100000) ++ ln([49], Nil{}, True{}, 100000) ++
  ln([48], [48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49], False{}, 310) ++
  ln([49, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48], Nil{}, True{}, 334)

# random digits: a 1 to 10 digit integer part, a 0 to 9 digit fraction,
# an exponent in [-350, 330]
def rnd.dec(+n: Nat, +s: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      +s1 = xs(s)
      +s2 = xs(s1)
      +s3 = xs(s2)
      +i = u32.digits((s1 >> U32.to_nat((s3 .&. 31 : U32)) : U32))
      +f = Bool.pick(List<&2, U32>, U32.is_eq((s3 .&. 32 : U32), 0), Nil{}, u32.digits((s2 >> U32.to_nat(((s3 >> 6n : U32) .&. 31 : U32)) : U32)))
      ln.e(i, f, sgn((650 + ((s3 >> 11n : U32) % 681 : U32) : U32))) ++ rnd.dec(p, s3)

# m * 2^q, a random positive double's significand and ulp exponent (q
# signed, as q + 2000)
type Mq is Data:
  Mq{m: List<&2, U32>, q: U32}

def mq.of(+hi: U32, +lo: U32) -> Mq:
  +ex = ((hi >> 20n : U32) .&. 2047 : U32)
  +mh = (hi .&. 1048575 : U32)
  Bool.pick(Mq, U32.is_eq(ex, 0), Mq{F.big.of2(mh, lo), (2000 - 1074 : U32)},
    Mq{F.big.of2((mh .|. 1048576 : U32), lo), ((2000 + ex : U32) - 1075 : U32)})

# n * 2^t (t + 2000) as a decimal: digits and a signed exponent
type Dx is Data:
  Dx{ds: List<&2, U32>, neg: Bool, k: U32}

def dx.at(c: Bool, n: List<&2, U32>, +t: U32) -> Dx:
  match c:
    case True{}:
      Dx{big.dec(F.big.shl((t - 2000 : U32), n)), False{}, 0}
    case False{}:
      Dx{big.dec(F.big.mul(n, F.big.pow5(U32.to_nat((2000 - t : U32)), F.big.one()))), True{}, (2000 - t : U32)}

def dx.of(n: List<&2, U32>, +t: U32) -> Dx:
  dx.at(U32.is_ge(t, 2000), n, t)

def dec.big(ds: List<&2, U32>) -> List<&2, U32>:
  F.dec.big(ds, Nil{})

# a decimal and the two one unit of its last digit below and above it
def mid.dx(d: Dx) -> String:
  match d:
    case Dx{+ds, +neg, +k}:
      +b = dec.big(ds)
      ln(ds, Nil{}, neg, k) ++
      ln(big.dec(F.big.sub(b, F.big.one())), Nil{}, neg, k) ++
      ln(big.dec(F.big.add(b, F.big.one())), Nil{}, neg, k)

# the midpoint above m * 2^q: (2m + 1) * 2^(q - 1)
def mid.of(mq: Mq) -> String:
  match mq:
    case Mq{m, +q}:
      +n = F.big.add(F.big.shl(1, m), F.big.one())
      +t = (q - 1 : U32)
      mid.dx(dx.of(n, t))

def rnd.mid(+n: Nat, +s: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      +s1 = xs(s)
      +s2 = xs(s1)
      +s3 = xs(s2)
      +hi = Bool.pick(U32, U32.is_eq((s3 .&. 7 : U32), 0), (s1 .&. 1048575 : U32), (s1 .&. 2146435071 : U32))
      +hi2 = Bool.pick(U32, U32.is_eq(((hi >> 20n : U32) .&. 2047 : U32), 2047), (hi .&. 2145386495 : U32), hi)
      mid.of(mq.of(hi2, s2)) ++ rnd.mid(p, s3)

# long decimals: 4 random 9-digit groups, a fraction of 2, an exponent
def rnd.long(+n: Nat, +s: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      +s1 = xs(s)
      +s2 = xs(s1)
      +s3 = xs(s2)
      +s4 = xs(s3)
      +i = List.concat(&2, U32, [u32.digits((s1 % 1000000000 : U32)), u32.digits((s2 % 1000000000 + 1000000000 : U32)), u32.digits((s3 % 1000000000 + 1000000000 : U32))])
      +f = List.concat(&2, U32, [u32.digits((s4 % 1000000000 + 1000000000 : U32)), u32.digits((s1 % 1000000000 + 1000000000 : U32))])
      ln.e(i, f, sgn((650 + ((s4 >> 7n : U32) % 681 : U32) : U32))) ++ rnd.long(p, s4)

def go(+n: Nat) -> String:
  chosen() ++ rnd.dec(n, 2463534242) ++ rnd.mid(n, 88172645) ++ rnd.long(n, 521288629)

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

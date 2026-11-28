import Base
import ./F64.bend as F

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# SPEC: what F64.bend's operations are, stated as IEEE 754 states them,
# and the laws that delimit F64.bend by it: op(a, b) == spec.op(a, b) for
# every input. The spec is written to be read, not to be fast:
#
# - a finite F64 is the exact dyadic m * 2^(e - OFF) its bits encode;
# - a result is the exact real (a sum, a product, a quotient, a square
#   root) rounded by `near`: the F64 nearest to it, found by a binary
#   search over the positive bit patterns (whose order is their values'),
#   the midpoint compared exactly, a tie to the even pattern, and past the
#   greatest finite value plus half its ulp, infinity;
# - zeros, infinities and NaN by IEEE 754's tables (sections 6.1-6.3, 7).
#
# F64.bend computes the same results another way (the exact value shifted
# into 53 bits with a round and a sticky bit). OPEN.bend states the laws,
# op(a, b) == s.op(a, b) for every input, still open: tests/spec.bend
# holds them on chosen and pseudo-random inputs, and tests/run.zsh holds
# F64.bend against the machine's double. A proof for every input is still
# to come.

# Exact values
# ------------

# a nonnegative dyadic: m * 2^(e - OFF)
type Dy is Data:
  Dy{m: List<&2, U32>, e: U32}

# the magnitude of a finite F64, or of an F32 (bits in lo, hi 0)
def mag.go(+f32: Bool, +hi: U32, +lo: U32) -> Dy:
  match f32:
    case True{}:
      +ex = ((lo >> 23n : U32) .&. 255 : U32)
      +mt = (lo .&. 8388607 : U32)
      Bool.pick(Dy, U32.is_eq(ex, 0), Dy{F.big.of2(0, mt), (F.OFF() - 149 : U32)},
        Dy{F.big.of2(0, (mt .|. 8388608 : U32)), ((F.OFF() + ex : U32) - 150 : U32)})
    case False{}:
      +ex = ((hi >> 20n : U32) .&. 2047 : U32)
      +mh = (hi .&. 1048575 : U32)
      Bool.pick(Dy, U32.is_eq(ex, 0), Dy{F.big.of2(mh, lo), (F.OFF() - 1074 : U32)},
        Dy{F.big.of2((mh .|. 1048576 : U32), lo), ((F.OFF() + ex : U32) - 1075 : U32)})

def mag(f32: Bool, x: F.F64) -> Dy:
  match x:
    case F.F64{hi, lo}:
      mag.go(f32, hi, lo)

# m * 2^e against n * 2^f, exactly
def dy.cmp.go(c: Bool, +m: List<&2, U32>, +e: U32, +n: List<&2, U32>, +f: U32) -> Cmp:
  match c:
    case True{}:
      F.big.cmp(F.big.shl((e - f : U32), m), n)
    case False{}:
      F.big.cmp(m, F.big.shl((f - e : U32), n))

def dy.cmp(+m: List<&2, U32>, +e: U32, +n: List<&2, U32>, +f: U32) -> Cmp:
  dy.cmp.go(U32.is_ge(e, f), m, e, n, f)

# The reals a result rounds from: a dyadic, a quotient, a square root
type R is Data:
  RDy{d: Dy}
  RQ{n: Dy, d: Dy}
  RSqrt{a: Dy}

# r against m * 2^(e - OFF), exactly (every quantity is nonnegative)
def r.cmp(r: R, +m: List<&2, U32>, +e: U32) -> Cmp:
  match r:
    case RDy{Dy{n, f}}:
      dy.cmp(n, f, m, e)
    case RQ{Dy{nm, ne}, Dy{dm, de}}:
      dy.cmp(nm, ne, F.big.mul(m, dm), ((e + de : U32) - F.OFF() : U32))
    case RSqrt{Dy{am, ae}}:
      dy.cmp(am, ae, F.big.mul(m, m), ((e + e : U32) - F.OFF() : U32))

# Rounding by search
# ------------------

# A format: F32 or F64, and the bit pattern of its greatest finite value
def top(f32: Bool) -> List<&2, U32>:
  match f32:
    case True{}:
      F.big.of2(0, 2139095039)
    case False{}:
      F.big.of2(2146435071, 4294967295)

# a bit pattern (a big natural) as an F64 (an F32's in lo)
def pat(+b: List<&2, U32>) -> F.F64:
  F.lit(F.big.hi32(b), F.big.lo32(b))

def pat.mag(+f32: Bool, +b: List<&2, U32>) -> Dy:
  mag(f32, pat(b))

# r against the value of pattern b
def r.vs.d(r: R, d: Dy) -> Cmp:
  match d:
    case Dy{m, e}:
      r.cmp(r, m, e)

def r.vs(+f32: Bool, r: R, +b: List<&2, U32>) -> Cmp:
  r.vs.d(r, pat.mag(f32, b))

# the greatest pattern in [l, h] whose value is at most r (r >= value(l)):
# 64 halvings of the interval
type LH is Data:
  LH{l: List<&2, U32>, h: List<&2, U32>}

def srch.step(c: Cmp, l: List<&2, U32>, h: List<&2, U32>, +mid: List<&2, U32>) -> LH:
  match c:
    case LT{}:
      LH{l, F.big.sub(mid, F.big.one())}
    case _:
      LH{mid, h}

def srch.lh(+f32: Bool, +r: R, lh: LH) -> LH:
  match lh:
    case LH{+l, +h}:
      +mid = F.big.shr.m(1, F.big.add(F.big.add(l, h), F.big.one()))
      srch.step(r.vs(f32, r, mid), l, h, mid)

def srch.l(lh: LH) -> List<&2, U32>:
  match lh:
    case LH{l, h}:
      l

def srch.go(+k: Nat, +f32: Bool, +r: R, lh: LH) -> List<&2, U32>:
  match k:
    case 0n:
      srch.l(lh)
    case 1n+p:
      srch.go(p, f32, r, srch.lh(f32, r, lh))

# the nearest pattern to r, ties to even; b the greatest at most r
def near.tie(+b: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, F.big.is_odd(b), F.big.add(b, F.big.one()), b)

def near.mid(c: Cmp, +b: List<&2, U32>) -> List<&2, U32>:
  match c:
    case LT{}:
      b
    case GT{}:
      F.big.add(b, F.big.one())
    case EQ{}:
      near.tie(b)

# the midpoint of b and the next pattern, as a dyadic, against r: the
# next past the greatest finite is 2^(emax + 1) (a value no format has)
# r against the midpoint of m * 2^e and n * 2^f
def dy.cmp.half(c: Bool, r: R, m: List<&2, U32>, +e: U32, n: List<&2, U32>, +f: U32) -> Cmp:
  match c:
    case True{}:
      r.cmp(r, F.big.add(m, F.big.shl((f - e : U32), n)), (e - 1 : U32))
    case False{}:
      r.cmp(r, F.big.add(F.big.shl((e - f : U32), m), n), (f - 1 : U32))

def dy.half(r: R, x: Dy, y: Dy) -> Cmp:
  match x y:
    case Dy{m, +e} Dy{n, +f}:
      dy.cmp.half(U32.is_le(e, f), r, m, e, n, f)

def near.half(+f32: Bool, r: R, +b: List<&2, U32>) -> Cmp:
  dy.half(r, pat.mag(f32, b), pat.mag(f32, F.big.add(b, F.big.one())))

# the greatest finite pattern's next, as a dyadic: 2^(emax + 1)
def over(f32: Bool) -> Dy:
  match f32:
    case True{}:
      Dy{F.big.one(), (F.OFF() + 128 : U32)}
    case False{}:
      Dy{F.big.one(), (F.OFF() + 1024 : U32)}

def near.top(+f32: Bool, r: R, +b: List<&2, U32>) -> Cmp:
  dy.half(r, pat.mag(f32, b), over(f32))

# past the greatest finite value: below the midpoint to 2^(emax+1) it is
# that value, at or above it infinity (the tie goes to the even 2^(emax+1))
def near.max(c: Cmp, f32: Bool) -> List<&2, U32>:
  match c:
    case LT{}:
      top(f32)
    case _:
      F.big.add(top(f32), F.big.one())

def near.at(c: Cmp, +f32: Bool, +r: R, +b: List<&2, U32>) -> List<&2, U32>:
  match c:
    case EQ{}:
      b
    case _:
      Bool.pick(List<&2, U32>, Cmp.is_eq(F.big.cmp(b, top(f32))),
        near.max(near.top(f32, r, b), f32),
        near.mid(near.half(f32, r, b), b))

# the pattern of the format's value nearest to r (r >= 0)
def near(+f32: Bool, +r: R) -> List<&2, U32>:
  +b = srch.go(64n, f32, r, LH{Nil{}, top(f32)})
  near.at(r.vs(f32, r, b), f32, r, b)

# with a sign (0 or 2^31), as an F64
def signed(+s: U32, x: F.F64) -> F.F64:
  match x:
    case F.F64{hi, lo}:
      F.lit((hi .|. s : U32), lo)

def near64(+s: U32, r: R) -> F.F64:
  signed(s, pat(near(False{}, r)))

# IEEE 754's operations
# ---------------------

def cls.nan(x: F.F64) -> Bool:
  match x:
    case F.F64{+hi, +lo}:
      Bool.and(U32.is_eq(((hi >> 20n : U32) .&. 2047 : U32), 2047), U32.is_ne(((hi .&. 1048575 : U32) .|. lo : U32), 0))

def cls.inf(x: F.F64) -> Bool:
  match x:
    case F.F64{+hi, +lo}:
      Bool.and(U32.is_eq((hi .&. 2147483647 : U32), 2146435072), U32.is_eq(lo, 0))

def cls.zero(x: F.F64) -> Bool:
  match x:
    case F.F64{+hi, +lo}:
      U32.is_eq(((hi .&. 2147483647 : U32) .|. lo : U32), 0)

def sgn(x: F.F64) -> U32:
  match x:
    case F.F64{hi, lo}:
      (hi .&. 2147483648 : U32)

# a sum of two finite values, by their signs and magnitudes
def s.sum.d(c: Cmp, +s: U32, +t: U32, +a: List<&2, U32>, +b: List<&2, U32>, +e: U32) -> F.F64:
  match c:
    case EQ{}:
      F.zero(0)
    case GT{}:
      near64(s, RDy{Dy{F.big.sub(a, b), e}})
    case LT{}:
      near64(t, RDy{Dy{F.big.sub(b, a), e}})

def s.sum.al(+s: U32, +t: U32, +a: List<&2, U32>, +b: List<&2, U32>, +e: U32) -> F.F64:
  Bool.pick(F.F64, U32.is_eq(s, t), near64(s, RDy{Dy{F.big.add(a, b), e}}), s.sum.d(F.big.cmp(a, b), s, t, a, b, e))

def s.sum.go(c: Bool, +s: U32, m: List<&2, U32>, +e: U32, +t: U32, n: List<&2, U32>, +f: U32) -> F.F64:
  match c:
    case True{}:
      s.sum.al(s, t, F.big.shl((e - f : U32), m), n, f)
    case False{}:
      s.sum.al(s, t, m, F.big.shl((f - e : U32), n), e)

def s.sum(+s: U32, x: Dy, +t: U32, y: Dy) -> F.F64:
  match x y:
    case Dy{m, +e} Dy{n, +f}:
      s.sum.go(U32.is_ge(e, f), s, m, e, t, n, f)

# a + b: NaN if either is, or inf + -inf; an infinity wins; two zeros sum
# to -0 only if both are -0; a zero adds nothing; x + -x is +0
def s.add(+a: F.F64, +b: F.F64) -> F.F64:
  Bool.pick(F.F64, Bool.or(cls.nan(a), cls.nan(b)), F.nan(),
  Bool.pick(F.F64, Bool.and(cls.inf(a), cls.inf(b)), Bool.pick(F.F64, U32.is_eq(sgn(a), sgn(b)), a, F.nan()),
  Bool.pick(F.F64, cls.inf(a), a,
  Bool.pick(F.F64, cls.inf(b), b,
  Bool.pick(F.F64, Bool.and(cls.zero(a), cls.zero(b)), F.zero((sgn(a) .&. sgn(b) : U32)),
  Bool.pick(F.F64, cls.zero(a), b,
  Bool.pick(F.F64, cls.zero(b), a,
  s.sum(sgn(a), mag(False{}, a), sgn(b), mag(False{}, b)))))))))

def s.sub(a: F.F64, b: F.F64) -> F.F64:
  s.add(a, F.neg(b))

def s.mul.fin(+s: U32, x: Dy, y: Dy) -> F.F64:
  match x y:
    case Dy{m, e} Dy{n, f}:
      near64(s, RDy{Dy{F.big.mul(m, n), ((e + f : U32) - F.OFF() : U32)}})

# a * b: NaN if either is, or 0 * inf; else the signs' product, inf if
# either is, 0 if either is
def s.mul(+a: F.F64, +b: F.F64) -> F.F64:
  +s = (sgn(a) .^. sgn(b) : U32)
  Bool.pick(F.F64, Bool.or(cls.nan(a), cls.nan(b)), F.nan(),
  Bool.pick(F.F64, Bool.or(Bool.and(cls.inf(a), cls.zero(b)), Bool.and(cls.zero(a), cls.inf(b))), F.nan(),
  Bool.pick(F.F64, Bool.or(cls.inf(a), cls.inf(b)), F.inf(s),
  Bool.pick(F.F64, Bool.or(cls.zero(a), cls.zero(b)), F.zero(s),
  s.mul.fin(s, mag(False{}, a), mag(False{}, b))))))

# a / b: NaN if either is, or 0/0, or inf/inf; inf / x and x / 0 are
# infinite, x / inf and 0 / x zero, all of the signs' product
def s.div(+a: F.F64, +b: F.F64) -> F.F64:
  +s = (sgn(a) .^. sgn(b) : U32)
  Bool.pick(F.F64, Bool.or(cls.nan(a), cls.nan(b)), F.nan(),
  Bool.pick(F.F64, Bool.or(Bool.and(cls.inf(a), cls.inf(b)), Bool.and(cls.zero(a), cls.zero(b))), F.nan(),
  Bool.pick(F.F64, Bool.or(cls.inf(a), cls.zero(b)), F.inf(s),
  Bool.pick(F.F64, Bool.or(cls.zero(a), cls.inf(b)), F.zero(s),
  near64(s, RQ{mag(False{}, a), mag(False{}, b)})))))

# sqrt(a): NaN for a NaN and below zero; +-0 and +inf are themselves
def s.sqrt(+a: F.F64) -> F.F64:
  Bool.pick(F.F64, cls.nan(a), F.nan(),
  Bool.pick(F.F64, cls.zero(a), a,
  Bool.pick(F.F64, U32.is_ne(sgn(a), 0), F.nan(),
  Bool.pick(F.F64, cls.inf(a), a,
  near64(0, RSqrt{mag(False{}, a)})))))

# to F32: NaN to F32's quiet NaN; infinities and zeros keep their sign;
# else the nearest F32 (its bits in lo)
def s.to_f32(+a: F.F64) -> U32:
  Bool.pick(U32, cls.nan(a), 2143289344,
  Bool.pick(U32, cls.inf(a), (sgn(a) .|. 2139095040 : U32),
  Bool.pick(U32, cls.zero(a), sgn(a),
  (sgn(a) .|. F.big.lo32(near(True{}, RDy{mag(False{}, a)})) : U32))))

# a < b, a == b: unordered when either is NaN; the zeros are equal; else
# by value, the signs first
def s.lt.c(s0: Bool, c: Cmp) -> Bool:
  match s0:
    case True{}:
      Cmp.is_lt(c)
    case False{}:
      Cmp.is_gt(c)

def s.lt.mag(+s: U32, x: Dy, y: Dy) -> Bool:
  match x y:
    case Dy{m, e} Dy{n, f}:
      s.lt.c(U32.is_eq(s, 0), dy.cmp(m, e, n, f))

def s.lt.fin(+a: F.F64, +b: F.F64) -> Bool:
  Bool.pick(Bool, Bool.and(cls.zero(a), cls.zero(b)), False{},
  Bool.pick(Bool, U32.is_ne(sgn(a), sgn(b)), U32.is_ne(sgn(a), 0),
  s.lt.mag(sgn(a), mag(False{}, a), mag(False{}, b))))

def s.lt(+a: F.F64, +b: F.F64) -> Bool:
  Bool.pick(Bool, Bool.or(cls.nan(a), cls.nan(b)), False{},
  Bool.pick(Bool, Bool.and(cls.inf(a), cls.inf(b)), Bool.and(U32.is_ne(sgn(a), 0), U32.is_eq(sgn(b), 0)),
  Bool.pick(Bool, cls.inf(a), U32.is_ne(sgn(a), 0),
  Bool.pick(Bool, cls.inf(b), U32.is_eq(sgn(b), 0),
  s.lt.fin(a, b)))))

def s.eq(+a: F.F64, +b: F.F64) -> Bool:
  Bool.and(Bool.not(Bool.or(cls.nan(a), cls.nan(b))), Bool.and(Bool.not(s.lt(a, b)), Bool.not(s.lt(b, a))))

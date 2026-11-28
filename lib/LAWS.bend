import Base
import ./F64.bend as F

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# LAWS: what F64.bend satisfies, proven in Bend (`bend lib/LAWS.bend
# --verdict`). Two kinds:
#
# - for every input: the definitional laws (sub is add of the negation,
#   is_ne is not is_eq), and the bit laws (neg and abs);
# - IEEE 754's rule table at named inputs, each proven by computing it:
#   signed zeros, infinities, NaN, ties to even, overflow, gradual
#   underflow, and the F32 conversions. These pin what no universal law
#   above says yet.
#
# The law that delimits each operation, op(a, b) is the F64 nearest to
# the exact result (ties to even), is SPEC.bend's: stated there for every
# input, held against the machine's double by tests/run.zsh, not yet
# proven for every input.

# Named values (their bits)
# -------------------------

def pz() -> F.F64:
  F.lit(0, 0)

def nz() -> F.F64:
  F.lit(2147483648, 0)

def one() -> F.F64:
  F.lit(1072693248, 0)

def mone() -> F.F64:
  F.lit(3220176896, 0)

def two() -> F.F64:
  F.lit(1073741824, 0)

def four() -> F.F64:
  F.lit(1074790400, 0)

def half() -> F.F64:
  F.lit(1071644672, 0)

# 1 + 2^-52, 1 + 2^-51: the two values above 1
def one.u() -> F.F64:
  F.lit(1072693248, 1)

def one.uu() -> F.F64:
  F.lit(1072693248, 2)

# 2^-53, half an ulp of 1
def hulp() -> F.F64:
  F.lit(1017118720, 0)

def max() -> F.F64:
  F.lit(2146435071, 4294967295)

def pinf() -> F.F64:
  F.lit(2146435072, 0)

def ninf() -> F.F64:
  F.lit(4293918720, 0)

def minn() -> F.F64:
  F.lit(1048576, 0)

# 2^-1023 and 2^-1074, subnormal
def sub.half() -> F.F64:
  F.lit(524288, 0)

def sub.min() -> F.F64:
  F.lit(0, 1)

# For every input
# ---------------

law sub.def:
  for a: F.F64
  for b: F.F64
  {F.sub(a, b) == F.add(a, F.neg(b)) : F.F64}

def sub.def(a, b):
  {==}

law is_ne.def:
  for a: F.F64
  for b: F.F64
  {F.is_ne(a, b) == Bool.not(F.is_eq(a, b)) : Bool}

def is_ne.def(a, b):
  {==}

# the bit laws: xor with b twice is the identity, and with b is idempotent
law w.xor_xor:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.xor(n, Word.xor(n, a, b), b) == a : Word(n)}

def w.xor_xor(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.xor(p, Word.xor(p, at, bt), bt), at, w.xor_xor(p, at, bt))
        case WCon{False{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.xor(p, Word.xor(p, at, bt), bt), at, w.xor_xor(p, at, bt))
        case WCon{True{}, at} WCon{False{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.xor(p, Word.xor(p, at, bt), bt), at, w.xor_xor(p, at, bt))
        case WCon{True{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.xor(p, Word.xor(p, at, bt), bt), at, w.xor_xor(p, at, bt))

law w.and_idem:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.and(n, Word.and(n, a, b), b) == Word.and(n, a, b) : Word(n)}

def w.and_idem(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.and(p, Word.and(p, at, bt), bt), Word.and(p, at, bt), w.and_idem(p, at, bt))
        case WCon{False{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.and(p, Word.and(p, at, bt), bt), Word.and(p, at, bt), w.and_idem(p, at, bt))
        case WCon{True{}, at} WCon{False{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.and(p, Word.and(p, at, bt), bt), Word.and(p, at, bt), w.and_idem(p, at, bt))
        case WCon{True{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.and(p, Word.and(p, at, bt), bt), Word.and(p, at, bt), w.and_idem(p, at, bt))

law u.xor_xor:
  for a: U32
  for b: U32
  {U32.xor(U32.xor(a, b), b) == a : U32}

def u.xor_xor(a, b):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, v => U32{v}, Word.xor(32n, Word.xor(32n, x, y), y), x,
        w.xor_xor(32n, x, y))

law u.and_idem:
  for a: U32
  for b: U32
  {U32.and(U32.and(a, b), b) == U32.and(a, b) : U32}

def u.and_idem(a, b):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, v => U32{v}, Word.and(32n, Word.and(32n, x, y), y),
        Word.and(32n, x, y), w.and_idem(32n, x, y))

# neg flips the sign bit: twice is the identity, NaN included
law neg_neg:
  for x: F.F64
  {F.neg(F.neg(x)) == x : F.F64}

def neg_neg(x):
  match x:
    case F.F64{hi, lo}:
      Equal.cong(U32, F.F64, v => F.F64{v, lo},
        U32.xor(U32.xor(hi, 2147483648), 2147483648), hi, u.xor_xor(hi, 2147483648))

# abs clears the sign bit: twice is once
law abs_abs:
  for x: F.F64
  {F.abs(F.abs(x)) == F.abs(x) : F.F64}

def abs_abs(x):
  match x:
    case F.F64{hi, lo}:
      Equal.cong(U32, F.F64, v => F.F64{v, lo},
        U32.and(U32.and(hi, 2147483647), 2147483647), U32.and(hi, 2147483647),
        u.and_idem(hi, 2147483647))

# IEEE 754's rules at named inputs
# --------------------------------

# x + (-x) is +0 rounding to nearest; -0 + -0 is -0; +0 + -0 is +0
law add.cancel_pz:
  {F.add(one(), mone()) == pz() : F.F64}

def add.cancel_pz():
  {==}

law add.nz_nz:
  {F.add(nz(), nz()) == nz() : F.F64}

def add.nz_nz():
  {==}

law add.pz_nz:
  {F.add(pz(), nz()) == pz() : F.F64}

def add.pz_nz():
  {==}

# a tie rounds to the even neighbour: 1 + 2^-53 is 1, (1 + 2^-52) + 2^-53
# is 1 + 2^-51
law add.tie_down:
  {F.add(one(), hulp()) == one() : F.F64}

def add.tie_down():
  {==}

law add.tie_up:
  {F.add(one.u(), hulp()) == one.uu() : F.F64}

def add.tie_up():
  {==}

law add.exact:
  {F.add(one(), one()) == two() : F.F64}

def add.exact():
  {==}

# overflow is an infinity of the result's sign
law mul.overflow:
  {F.mul(max(), two()) == pinf() : F.F64}

def mul.overflow():
  {==}

law add.overflow:
  {F.add(max(), max()) == pinf() : F.F64}

def add.overflow():
  {==}

# gradual underflow: halving the least normal is exact
law div.subnormal:
  {F.div(minn(), two()) == sub.half() : F.F64}

def div.subnormal():
  {==}

# the least subnormal halved is a tie between 0 and itself: 0 is even
law mul.underflow_tie:
  {F.mul(sub.min(), half()) == pz() : F.F64}

def mul.underflow_tie():
  {==}

# division by zero is an infinity of the signs' product
law div.by_pz:
  {F.div(one(), pz()) == pinf() : F.F64}

def div.by_pz():
  {==}

law div.by_nz:
  {F.div(one(), nz()) == ninf() : F.F64}

def div.by_nz():
  {==}

law div.exact:
  {F.div(one(), four()) == F.mul(half(), half()) : F.F64}

def div.exact():
  {==}

# NaN: inf - inf, 0 / 0, sqrt(-1); a NaN equals nothing, itself included
law nan.inf_sub_inf:
  {F.is_nan(F.sub(pinf(), pinf())) == True{} : Bool}

def nan.inf_sub_inf():
  {==}

law nan.zero_div_zero:
  {F.is_nan(F.div(pz(), pz())) == True{} : Bool}

def nan.zero_div_zero():
  {==}

law nan.sqrt_neg:
  {F.is_nan(F.sqrt(mone())) == True{} : Bool}

def nan.sqrt_neg():
  {==}

law nan.ne_self:
  {F.is_eq(F.nan(), F.nan()) == False{} : Bool}

def nan.ne_self():
  {==}

law nan.unordered:
  {Bool.or(F.is_lt(F.nan(), one()), F.is_ge(F.nan(), one())) == False{} : Bool}

def nan.unordered():
  {==}

# -0 equals +0, and neither is below the other
law zero.eq:
  {F.is_eq(nz(), pz()) == True{} : Bool}

def zero.eq():
  {==}

law zero.not_lt:
  {F.is_lt(nz(), pz()) == False{} : Bool}

def zero.not_lt():
  {==}

law sqrt.exact:
  {F.sqrt(four()) == two() : F.F64}

def sqrt.exact():
  {==}

law sqrt.nz:
  {F.sqrt(nz()) == nz() : F.F64}

def sqrt.nz():
  {==}

law sqrt.inf:
  {F.sqrt(pinf()) == pinf() : F.F64}

def sqrt.inf():
  {==}

import Base

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# F64: IEEE 754 binary64 in plain Bend (Base only, no @unsafe), the meaning
# of bendbis's native F64 and the library G lowers it to (DESIGN.md, "bend
# and bendbis: the adjunction"). Import it as `import PATH/F64.bend as F64`:
# the type is F64.F64 and the operations F64.add, F64.mul, ...
#
# An F64 is its 64 bits, two U32s, the sign and exponent in hi. Every
# operation rounds to nearest, ties to even, as IEEE 754 and every CPU's
# double do: the exact result is computed over big naturals and rounded
# once. A NaN result is always the quiet NaN 0x7FF8000000000000 (a CPU's
# payload and sign differ by vendor; a NaN is equal to nothing, so only
# is_nan observes it).

# The offset of a signed exponent held in a U32: e is e - OFF.
def OFF() -> U32:
  1048576

type F64 is Data:
  F64{hi: U32, lo: U32}

# Big naturals: little-endian 16-bit limbs, one U32 each, no zero limb at
# the top (zero is Nil{}).
# ----------------------------------------------------------------------

def big.trim.go(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{0, t}:
      big.trim.go(t)
    case xs:
      xs

def big.trim(xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, big.trim.go(List.reverse(&2, U32, xs)))

# the 64-bit natural hi * 2^32 + lo
def big.of2(+hi: U32, +lo: U32) -> List<&2, U32>:
  big.trim([(lo .&. 65535 : U32), (lo >> 16n : U32), (hi .&. 65535 : U32), (hi >> 16n : U32)])

def big.one() -> List<&2, U32>:
  [1]

def big.is_zero(xs: List<&2, U32>) -> Bool:
  List.is_empty(&2, U32, xs)

def big.is_odd(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      U32.is_eq((x .&. 1 : U32), 1)

# the i-th limb, 0 past the top
def big.limb(i: Nat, xs: List<&2, U32>) -> U32:
  match i xs:
    case _ Nil{}:
      0
    case 0n Con{x, t}:
      x
    case 1n+p Con{x, t}:
      big.limb(p, t)

# the low 32 bits and the next 32 bits
def big.lo32(+xs: List<&2, U32>) -> U32:
  (big.limb(0n, xs) .|. (big.limb(1n, xs) << 16n : U32) : U32)

def big.hi32(+xs: List<&2, U32>) -> U32:
  (big.limb(2n, xs) .|. (big.limb(3n, xs) << 16n : U32) : U32)

# xs + c, c below 2^16
def big.inc.go(xs: List<&2, U32>, c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [c]
    case Con{+x, t}:
      +v = (x + c : U32)
      (v .&. 65535 : U32) <> big.inc.go(t, (v >> 16n : U32))

def big.add.go(xs: List<&2, U32>, ys: List<&2, U32>, c: U32) -> List<&2, U32>:
  match xs ys:
    case Nil{} ys:
      big.inc.go(ys, c)
    case Con{+x, s} Nil{}:
      big.inc.go(Con{x, s}, c)
    case Con{+x, s} Con{+y, t}:
      +v = ((x + y : U32) + c : U32)
      (v .&. 65535 : U32) <> big.add.go(s, t, (v >> 16n : U32))

def big.add(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  big.trim(big.add.go(xs, ys, 0))

# compare, most significant limb first: c is the verdict of the lower limbs
def big.cmp.limb(d: Cmp, c: Cmp) -> Cmp:
  match d:
    case EQ{}:
      c
    case d:
      d

def big.cmp.go(xs: List<&2, U32>, ys: List<&2, U32>, c: Cmp) -> Cmp:
  match xs ys:
    case Con{+x, s} Con{+y, t}:
      big.cmp.go(s, t, big.cmp.limb(U32.cmp(x, y), c))
    case _ _:
      c

def big.cmp.at(l: Cmp, xs: List<&2, U32>, ys: List<&2, U32>) -> Cmp:
  match l:
    case EQ{}:
      big.cmp.go(xs, ys, EQ{})
    case l:
      l

def big.cmp(+xs: List<&2, U32>, +ys: List<&2, U32>) -> Cmp:
  big.cmp.at(Nat.cmp(List.length(&2, U32, xs), List.length(&2, U32, ys)), xs, ys)

def big.le(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  Cmp.is_le(big.cmp(xs, ys))

# xs - ys, for xs >= ys (b the borrow)
def big.sub.go(xs: List<&2, U32>, ys: List<&2, U32>, b: U32) -> List<&2, U32>:
  match xs ys:
    case Nil{} _:
      Nil{}
    case Con{+x, s} Nil{}:
      +w = ((x + 65536 : U32) - b : U32)
      (w .&. 65535 : U32) <> big.sub.go(s, Nil{}, Bool.pick(U32, U32.is_lt(w, 65536), 1, 0))
    case Con{+x, s} Con{+y, t}:
      +w = ((x + 65536 : U32) - (y + b : U32) : U32)
      (w .&. 65535 : U32) <> big.sub.go(s, t, Bool.pick(U32, U32.is_lt(w, 65536), 1, 0))

def big.sub(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  big.trim(big.sub.go(xs, ys, 0))

# xs * m + c, m and c below 2^16
def big.muladd.go(xs: List<&2, U32>, +m: U32, c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [c]
    case Con{x, t}:
      +v = ((x * m : U32) + c : U32)
      (v .&. 65535 : U32) <> big.muladd.go(t, m, (v >> 16n : U32))

def big.muladd(xs: List<&2, U32>, m: U32, c: U32) -> List<&2, U32>:
  big.trim(big.muladd.go(xs, m, c))

# xs * 2^16
def big.up16(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      0 <> Con{x, t}

def big.mul.go(+xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, t}:
      big.add(big.muladd(xs, y, 0), big.up16(big.mul.go(xs, t)))

def big.mul(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  big.mul.go(xs, ys)

def big.zeros(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      0 <> big.zeros(p, xs)

# xs * 2^n
def big.shl(+n: U32, xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      big.muladd(big.zeros(U32.to_nat((n >> 4n : U32)), Con{h, t}), (1 << U32.to_nat((n .&. 15 : U32)) : U32), 0)

# A shift right: the bits kept, and whether a 1 bit was shifted out
type Sh is Data:
  Sh{m: List<&2, U32>, st: Bool}

def big.drop(k: Nat, xs: List<&2, U32>, st: Bool) -> Sh:
  match k xs:
    case 0n xs:
      Sh{xs, st}
    case 1n+p Nil{}:
      Sh{Nil{}, st}
    case 1n+p Con{+x, t}:
      big.drop(p, t, Bool.or(st, U32.is_ne(x, 0)))

# xs most significant limb first, shifted right by r bits (r < 16) into acc
# (least significant first); c the bits of the limbs above not yet placed
def big.shr.go(+r: Nat, +mask: U32, xs: List<&2, U32>, c: U32, acc: List<&2, U32>) -> Sh:
  match xs:
    case Nil{}:
      Sh{acc, U32.is_ne(c, 0)}
    case Con{+x, t}:
      +v = ((c << 16n : U32) .|. x : U32)
      big.shr.go(r, mask, t, (v .&. mask : U32), (v >> r : U32) <> acc)

def big.shr.fin(st: Bool, s: Sh) -> Sh:
  match s:
    case Sh{m, t}:
      Sh{big.trim(m), Bool.or(st, t)}

def big.shr.bits(+n: U32, s: Sh) -> Sh:
  match s:
    case Sh{m, st}:
      +r = U32.to_nat((n .&. 15 : U32))
      big.shr.fin(st, big.shr.go(r, ((1 << r : U32) - 1 : U32), List.reverse(&2, U32, m), 0, Nil{}))

# xs / 2^n, rounded down, and whether the bits dropped were not all zero
def big.shr(+n: U32, xs: List<&2, U32>) -> Sh:
  big.shr.bits(n, big.drop(U32.to_nat((n >> 4n : U32)), xs, False{}))

def big.sh.m(s: Sh) -> List<&2, U32>:
  match s:
    case Sh{m, st}:
      m

def big.shr.m(n: U32, xs: List<&2, U32>) -> List<&2, U32>:
  big.sh.m(big.shr(n, xs))

def bits.of(k: Nat, +n: U32) -> U32:
  match k:
    case 0n:
      0
    case 1n+p:
      Bool.pick(U32, U32.is_eq(n, 0), 0, (1 + bits.of(p, (n >> 1n : U32)) : U32))

def big.bits.top(xs: List<&2, U32>, n: U32, +top: U32) -> U32:
  match xs:
    case Nil{}:
      ((16 * (n - 1 : U32) : U32) + bits.of(16n, top) : U32)
    case Con{x, t}:
      big.bits.top(t, (n + 1 : U32), x)

# the bit length (0 for zero)
def big.bits(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, t}:
      big.bits.top(Con{x, t}, 0, 0)

# a / b and a % b, for a < b * 2^(k+1): one bit of the quotient a step
type Qr is Data:
  Qr{q: List<&2, U32>, r: List<&2, U32>}

def big.divmod.pick(c: Bool, +k: U32, bk: List<&2, U32>, q: List<&2, U32>, r: List<&2, U32>) -> Qr:
  match c:
    case True{}:
      Qr{big.add(q, big.shl(k, big.one())), big.sub(r, bk)}
    case False{}:
      Qr{q, r}

def big.divmod.step(+b: List<&2, U32>, +k: U32, d: Qr) -> Qr:
  match d:
    case Qr{+q, +r}:
      +bk = big.shl(k, b)
      big.divmod.pick(big.le(bk, r), k, bk, q, r)

def big.divmod.go(+n: Nat, +b: List<&2, U32>, d: Qr) -> Qr:
  match n:
    case 0n:
      big.divmod.step(b, 0, d)
    case 1n+p:
      big.divmod.go(p, b, big.divmod.step(b, U32.from_nat(1n+p), d))

def big.divmod(a: List<&2, U32>, b: List<&2, U32>, k: Nat) -> Qr:
  big.divmod.go(k, b, Qr{Nil{}, a})

# the integer square root of n (r * r <= n < (r + 1) * (r + 1)), for
# n < 2^(2 * (k + 1)): one bit of r a step, from bit k down
def big.isqrt.step(+n: List<&2, U32>, +k: U32, +r: List<&2, U32>) -> List<&2, U32>:
  +c = big.add(r, big.shl(k, big.one()))
  Bool.pick(List<&2, U32>, big.le(big.mul(c, c), n), c, r)

def big.isqrt.go(+k: Nat, +n: List<&2, U32>, r: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      big.isqrt.step(n, 0, r)
    case 1n+p:
      big.isqrt.go(p, n, big.isqrt.step(n, U32.from_nat(1n+p), r))

def big.isqrt(n: List<&2, U32>, k: Nat) -> List<&2, U32>:
  big.isqrt.go(k, n, Nil{})

# Values
# ------

def nan() -> F64:
  F64{2146959360, 0}

# the infinity of sign s (0 or 2^31)
def inf(s: U32) -> F64:
  F64{(s .|. 2146435072 : U32), 0}

def zero(s: U32) -> F64:
  F64{s, 0}

# an F64 by its bits
def lit(hi: U32, lo: U32) -> F64:
  F64{hi, lo}

def bits.hi(x: F64) -> U32:
  match x:
    case F64{hi, lo}:
      hi

def bits.lo(x: F64) -> U32:
  match x:
    case F64{hi, lo}:
      lo

# What an F64 is: s its sign (0 or 2^31); a finite nonzero one is
# m * 2^(e - OFF), 0 < m < 2^53.
type Fv is Data:
  FNaN{}
  FInf{s: U32}
  FZero{s: U32}
  FFin{s: U32, m: List<&2, U32>, e: U32}

def view.special(+s: U32, z: Bool) -> Fv:
  match z:
    case True{}:
      FInf{s}
    case False{}:
      FNaN{}

def view.sub(+s: U32, +mh: U32, +lo: U32, z: Bool) -> Fv:
  match z:
    case True{}:
      FZero{s}
    case False{}:
      FFin{s, big.of2(mh, lo), (OFF() - 1074 : U32)}

def view.at(+s: U32, +ex: U32, +mh: U32, +lo: U32) -> Fv:
  +z = U32.is_eq((mh .|. lo : U32), 0)
  Bool.pick(Fv, U32.is_eq(ex, 2047), view.special(s, z),
    Bool.pick(Fv, U32.is_eq(ex, 0), view.sub(s, mh, lo, z),
      FFin{s, big.of2((mh .|. 1048576 : U32), lo), ((OFF() + ex : U32) - 1075 : U32)}))

def view(x: F64) -> Fv:
  match x:
    case F64{+hi, lo}:
      view.at((hi .&. 2147483648 : U32), ((hi >> 20n : U32) .&. 2047 : U32), (hi .&. 1048575 : U32), lo)

def is_nan.v(x: Fv) -> Bool:
  match x:
    case FNaN{}:
      True{}
    case _:
      False{}

def is_nan(x: F64) -> Bool:
  is_nan.v(view(x))

# Rounding: a format (p bits of precision, the least and the greatest
# exponent of its last bit, offset), and what an exact value rounds to.
# ----------------------------------------------------------------------

type Fmt is Data:
  Fmt{p: U32, qmin: U32, qmax: U32}

def fmt64() -> Fmt:
  Fmt{53, (OFF() - 1074 : U32), (OFF() + 971 : U32)}

def fmt32() -> Fmt:
  Fmt{24, (OFF() - 149 : U32), (OFF() + 104 : U32)}

# Q * 2^(q - OFF), Q below 2^p; or out of range
type Rd is Data:
  RInf{}
  RFin{z: List<&2, U32>, q: U32}

def rd.top(+p: U32, +qmax: U32, +z: List<&2, U32>, +q: U32) -> Rd:
  +ov = U32.is_gt(big.bits(z), p)
  +z2 = Bool.pick(List<&2, U32>, ov, big.shr.m(1, z), z)
  +q2 = Bool.pick(U32, ov, (q + 1 : U32), q)
  Bool.pick(Rd, U32.is_gt(q2, qmax), RInf{}, RFin{z2, q2})

# Q0 rounded up when the round bit is set and the rest or Q0's last bit is
def rd.up(+q0: List<&2, U32>, rb: Bool, st: Bool) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, Bool.and(rb, Bool.or(st, big.is_odd(q0))), big.add(q0, big.one()), q0)

def rd.cut(+p: U32, +qmax: U32, s: Sh, +q: U32) -> Rd:
  match s:
    case Sh{+q1, st}:
      rd.top(p, qmax, rd.up(big.shr.m(1, q1), big.is_odd(q1), st), q)

# exact when q <= e, else cut (the two arms only as asked: a U32
# difference of the wrong sign is a shift by 2^32 - d)
def rd.go(c: Bool, +p: U32, +qmax: U32, m: List<&2, U32>, +e: U32, +q: U32) -> Rd:
  match c:
    case True{}:
      rd.top(p, qmax, big.shl((e - q : U32), m), q)
    case False{}:
      rd.cut(p, qmax, big.shr(((q - e : U32) - 1 : U32), m), q)

def rd.at(f: Fmt, +m: List<&2, U32>, +e: U32) -> Rd:
  match f:
    case Fmt{+p, +qmin, +qmax}:
      +q = U32.max(((e + big.bits(m) : U32) - p : U32), qmin)
      rd.go(U32.is_le(q, e), p, qmax, m, e, q)

# m * 2^(e - OFF) to the nearest value of f (m > 0)
def rd(f: Fmt, m: List<&2, U32>, e: U32) -> Rd:
  rd.at(f, m, e)

def enc64(+s: U32, r: Rd) -> F64:
  match r:
    case RInf{}:
      inf(s)
    case RFin{+z, +q}:
      +ex = Bool.pick(U32, U32.is_eq(big.bits(z), 53), ((q + 1075 : U32) - OFF() : U32), 0)
      F64{((s .|. (ex << 20n : U32) : U32) .|. (big.hi32(z) .&. 1048575 : U32) : U32), big.lo32(z)}

# (-1)^s * m * 2^(e - OFF), rounded; m may be zero
def round64(+s: U32, m: List<&2, U32>, e: U32) -> F64:
  match m:
    case Nil{}:
      zero(s)
    case Con{h, t}:
      enc64(s, rd(fmt64(), Con{h, t}, e))

# m * 2^(e - OFF) as a normal significand: 2^52 <= m' < 2^53
type Nm is Data:
  Nm{m: List<&2, U32>, e: U32}

def norm(+m: List<&2, U32>, +e: U32) -> Nm:
  +k = (53 - big.bits(m) : U32)
  Nm{big.shl(k, m), (e - k : U32)}

# Arithmetic
# ----------

def neg(x: F64) -> F64:
  match x:
    case F64{hi, lo}:
      F64{(hi .^. 2147483648 : U32), lo}

def abs(x: F64) -> F64:
  match x:
    case F64{hi, lo}:
      F64{(hi .&. 2147483647 : U32), lo}

# m * 2^e + n * 2^f with signs s and t, e >= f; past 60 bits apart the
# smaller one only decides the side, so 2^(e - 64) stands for it
def add.cancel.c(c: Cmp, +s: U32, +t: U32, +a: List<&2, U32>, +b: List<&2, U32>, +f: U32) -> F64:
  match c:
    case EQ{}:
      zero(0)
    case GT{}:
      round64(s, big.sub(a, b), f)
    case LT{}:
      round64(t, big.sub(b, a), f)

def add.same(c: Bool, +s: U32, +t: U32, +a: List<&2, U32>, +b: List<&2, U32>, +f: U32) -> F64:
  match c:
    case True{}:
      round64(s, big.add(a, b), f)
    case False{}:
      add.cancel.c(big.cmp(a, b), s, t, a, b, f)

def add.al(+s: U32, m: List<&2, U32>, +e: U32, +t: U32, n: List<&2, U32>, +f: U32) -> F64:
  add.same(U32.is_eq(s, t), s, t, big.shl((e - f : U32), m), n, f)

def add.ord.go(c: Bool, +s: U32, m: List<&2, U32>, +e: U32, +t: U32, n: List<&2, U32>, +f: U32) -> F64:
  match c:
    case True{}:
      add.al(s, m, e, t, big.one(), (e - 64 : U32))
    case False{}:
      add.al(s, m, e, t, n, f)

def add.ord(+s: U32, m: List<&2, U32>, +e: U32, +t: U32, n: List<&2, U32>, +f: U32) -> F64:
  add.ord.go(U32.is_gt((e - f : U32), 60), s, m, e, t, n, f)

def add.fin.go(c: Bool, +s: U32, m: List<&2, U32>, +e: U32, +t: U32, n: List<&2, U32>, +f: U32) -> F64:
  match c:
    case True{}:
      add.ord(s, m, e, t, n, f)
    case False{}:
      add.ord(t, n, f, s, m, e)

def add.fin(+s: U32, m: List<&2, U32>, +e: U32, +t: U32, n: List<&2, U32>, +f: U32) -> F64:
  add.fin.go(U32.is_ge(e, f), s, m, e, t, n, f)

def add.v(x: Fv, y: Fv) -> F64:
  match x y:
    case FNaN{} _:
      nan()
    case _ FNaN{}:
      nan()
    case FInf{+s} FInf{+t}:
      Bool.pick(F64, U32.is_eq(s, t), inf(s), nan())
    case FInf{s} _:
      inf(s)
    case _ FInf{t}:
      inf(t)
    case FZero{s} FZero{t}:
      zero((s .&. t : U32))
    case FZero{s} FFin{t, n, f}:
      round64(t, n, f)
    case FFin{s, m, e} FZero{t}:
      round64(s, m, e)
    case FFin{s, m, e} FFin{t, n, f}:
      add.fin(s, m, e, t, n, f)

def add(a: F64, b: F64) -> F64:
  add.v(view(a), view(b))

def sub(a: F64, b: F64) -> F64:
  add.v(view(a), view(neg(b)))

def mul.v(x: Fv, y: Fv) -> F64:
  match x y:
    case FNaN{} _:
      nan()
    case _ FNaN{}:
      nan()
    case FInf{s} FZero{t}:
      nan()
    case FZero{s} FInf{t}:
      nan()
    case FInf{s} FInf{t}:
      inf((s .^. t : U32))
    case FInf{s} FFin{t, n, f}:
      inf((s .^. t : U32))
    case FFin{s, m, e} FInf{t}:
      inf((s .^. t : U32))
    case FZero{s} FZero{t}:
      zero((s .^. t : U32))
    case FZero{s} FFin{t, n, f}:
      zero((s .^. t : U32))
    case FFin{s, m, e} FZero{t}:
      zero((s .^. t : U32))
    case FFin{s, m, e} FFin{t, n, f}:
      round64((s .^. t : U32), big.mul(m, n), ((e + f : U32) - OFF() : U32))

def mul(a: F64, b: F64) -> F64:
  mul.v(view(a), view(b))

# m / n * 2^(e - f), both normal: the quotient's 56 bits and a sticky bit
def div.qr(+s: U32, +e: U32, +f: U32, d: Qr) -> F64:
  match d:
    case Qr{q, r}:
      round64(s, big.add(big.shl(1, q), Bool.pick(List<&2, U32>, big.is_zero(r), Nil{}, big.one())),
        (((e + OFF() : U32) - f : U32) - 56 : U32))

def div.nm(+s: U32, a: Nm, b: Nm) -> F64:
  match a b:
    case Nm{m, +e} Nm{+n, +f}:
      div.qr(s, e, f, big.divmod(big.shl(55, m), n, 56n))

def div.v(x: Fv, y: Fv) -> F64:
  match x y:
    case FNaN{} _:
      nan()
    case _ FNaN{}:
      nan()
    case FInf{s} FInf{t}:
      nan()
    case FZero{s} FZero{t}:
      nan()
    case FInf{s} FZero{t}:
      inf((s .^. t : U32))
    case FInf{s} FFin{t, n, f}:
      inf((s .^. t : U32))
    case FZero{s} FInf{t}:
      zero((s .^. t : U32))
    case FFin{s, m, e} FInf{t}:
      zero((s .^. t : U32))
    case FFin{s, m, e} FZero{t}:
      inf((s .^. t : U32))
    case FZero{s} FFin{t, n, f}:
      zero((s .^. t : U32))
    case FFin{s, m, e} FFin{t, n, f}:
      div.nm((s .^. t : U32), norm(m, e), norm(n, f))

def div(a: F64, b: F64) -> F64:
  div.v(view(a), view(b))

# sqrt(m * 2^(e - OFF)) for a normal m: m * 2^k with e - k even, its
# integer root (57 bits) and a sticky bit
def sqrt.r(+n: List<&2, U32>, +h: U32, +r: List<&2, U32>) -> F64:
  round64(0, big.add(big.shl(1, r), Bool.pick(List<&2, U32>, Cmp.is_eq(big.cmp(big.mul(r, r), n)), Nil{}, big.one())), h)

def sqrt.k(+n: List<&2, U32>, +h: U32) -> F64:
  sqrt.r(n, h, big.isqrt(n, 57n))

def sqrt.nm(a: Nm) -> F64:
  match a:
    case Nm{m, +e}:
      +k = (60 + (e .&. 1 : U32) : U32)
      sqrt.k(big.shl(k, m), ((((e - k : U32) + OFF() : U32) >> 1n : U32) - 1 : U32))

def sqrt.pos(c: Bool, m: List<&2, U32>, e: U32) -> F64:
  match c:
    case True{}:
      sqrt.nm(norm(m, e))
    case False{}:
      nan()

def sqrt.v(x: Fv) -> F64:
  match x:
    case FNaN{}:
      nan()
    case FZero{s}:
      zero(s)
    case FInf{+s}:
      Bool.pick(F64, U32.is_eq(s, 0), inf(0), nan())
    case FFin{+s, m, e}:
      sqrt.pos(U32.is_eq(s, 0), m, e)

def sqrt(a: F64) -> F64:
  sqrt.v(view(a))

# Comparisons: a NaN is unordered and equal to nothing; -0 equals +0
# ------------------------------------------------------------------

# a key whose unsigned order is the order of the values (zeros as +0)
def key.at(+hi: U32, +lo: U32, z: Bool) -> F64:
  match z:
    case True{}:
      F64{2147483648, 0}
    case False{}:
      Bool.pick(F64, U32.is_eq((hi .&. 2147483648 : U32), 0),
        F64{(hi .|. 2147483648 : U32), lo}, F64{U32.not(hi), U32.not(lo)})

def key(x: F64) -> F64:
  match x:
    case F64{+hi, +lo}:
      key.at(hi, lo, U32.is_eq(((hi .&. 2147483647 : U32) .|. lo : U32), 0))

def key.cmp(a: F64, b: F64) -> Cmp:
  match a b:
    case F64{+ah, +al} F64{+bh, +bl}:
      big.cmp.limb(U32.cmp(ah, bh), U32.cmp(al, bl))

def ord(+a: F64, +b: F64) -> Maybe<&2, Cmp>:
  Bool.pick(Maybe<&2, Cmp>, Bool.or(is_nan(a), is_nan(b)), None{}, Some{key.cmp(key(a), key(b))})

def ord.is(c: Maybe<&2, Cmp>, lt: Bool, eq: Bool, gt: Bool) -> Bool:
  match c:
    case None{}:
      False{}
    case Some{LT{}}:
      lt
    case Some{EQ{}}:
      eq
    case Some{GT{}}:
      gt

def is_eq(a: F64, b: F64) -> Bool:
  ord.is(ord(a, b), False{}, True{}, False{})

def is_ne(a: F64, b: F64) -> Bool:
  Bool.not(is_eq(a, b))

def is_lt(a: F64, b: F64) -> Bool:
  ord.is(ord(a, b), True{}, False{}, False{})

def is_le(a: F64, b: F64) -> Bool:
  ord.is(ord(a, b), True{}, True{}, False{})

def is_gt(a: F64, b: F64) -> Bool:
  ord.is(ord(a, b), False{}, False{}, True{})

def is_ge(a: F64, b: F64) -> Bool:
  ord.is(ord(a, b), False{}, True{}, True{})

# Conversions
# -----------

def from_u32(+u: U32) -> F64:
  round64(0, big.of2(0, u), OFF())

# an F32 by its bits, exactly
def f32.view.at(+s: U32, +ex: U32, +mh: U32) -> Fv:
  +z = U32.is_eq(mh, 0)
  Bool.pick(Fv, U32.is_eq(ex, 255), view.special(s, z),
    Bool.pick(Fv, U32.is_eq(ex, 0),
      Bool.pick(Fv, z, FZero{s}, FFin{s, big.of2(0, mh), (OFF() - 149 : U32)}),
      FFin{s, big.of2(0, (mh .|. 8388608 : U32)), ((OFF() + ex : U32) - 150 : U32)}))

def f32.view(+u: U32) -> Fv:
  f32.view.at((u .&. 2147483648 : U32), ((u >> 23n : U32) .&. 255 : U32), (u .&. 8388607 : U32))

def f32.bits(x: F32) -> U32:
  match x:
    case F32{w}:
      U32{w}

def f32.of_bits(u: U32) -> F32:
  match u:
    case U32{w}:
      F32{w}

def from_f32.v(x: Fv) -> F64:
  match x:
    case FNaN{}:
      nan()
    case FInf{s}:
      inf(s)
    case FZero{s}:
      zero(s)
    case FFin{s, m, e}:
      round64(s, m, e)

def from_f32(x: F32) -> F64:
  from_f32.v(f32.view(f32.bits(x)))

def enc32(+s: U32, r: Rd) -> U32:
  match r:
    case RInf{}:
      (s .|. 2139095040 : U32)
    case RFin{+z, +q}:
      +ex = Bool.pick(U32, U32.is_eq(big.bits(z), 24), ((q + 150 : U32) - OFF() : U32), 0)
      ((s .|. (ex << 23n : U32) : U32) .|. (big.lo32(z) .&. 8388607 : U32) : U32)

def to_f32.v(x: Fv) -> U32:
  match x:
    case FNaN{}:
      2143289344
    case FInf{s}:
      (s .|. 2139095040 : U32)
    case FZero{s}:
      s
    case FFin{+s, m, e}:
      enc32(s, rd(fmt32(), m, e))

# to the nearest F32, ties to even
def to_f32(x: F64) -> F32:
  f32.of_bits(to_f32.v(view(x)))

# Decimals: a literal's value, rounded once
# -----------------------------------------

# digits (character codes '0' to '9') to a big natural
def dec.big(ds: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      dec.big(t, big.muladd(acc, 10, (d - 48 : U32)))

# the count of digits past the leading zeros
def dec.sig(ds: List<&2, U32>) -> U32:
  match ds:
    case Nil{}:
      0
    case Con{48, t}:
      dec.sig(t)
    case Con{d, t}:
      (1 + U32.from_nat(List.length(&2, U32, t)) : U32)

# an exponent's digits, held at 100000 past 10000 (any exponent past 400
# decides the same as 100000)
def dec.exp(ds: List<&2, U32>, +acc: U32) -> U32:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      dec.exp(t, Bool.pick(U32, U32.is_gt(acc, 10000), 100000, ((acc * 10 : U32) + (d - 48 : U32) : U32)))

# acc * 5^k
def big.pow5(k: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      big.pow5(p, big.muladd(acc, 5, 0))

# d * 10^(e10 - OFF) for e10 >= OFF: d * 5^E * 2^E, exact, rounded once
def dec.up(d: List<&2, U32>, +e10: U32) -> F64:
  round64(0, big.mul(d, big.pow5(U32.to_nat((e10 - OFF() : U32)), big.one())), e10)

# a / b * 2^(e - OFF) by its quotient's bits and a sticky bit (as div)
def dec.down.q(+e: U32, d: Qr) -> F64:
  match d:
    case Qr{q, r}:
      round64(0, big.add(big.shl(1, q), Bool.pick(List<&2, U32>, big.is_zero(r), Nil{}, big.one())), e)

def dec.down.at(+a: List<&2, U32>, +b: List<&2, U32>, +e: U32) -> F64:
  dec.down.q(e, big.divmod(a, b, U32.to_nat(((big.bits(a) - big.bits(b) : U32) + 1 : U32))))

# d * 10^-k = d / 5^k * 2^-k for k = OFF - e10: d * 2^s / 5^k has 57 bits
# or more, so its quotient and a sticky bit round as the exact value does
def dec.down.s(d: List<&2, U32>, b: List<&2, U32>, +e10: U32, +s: U32) -> F64:
  dec.down.at(big.shl(s, d), b, ((e10 - s : U32) - 1 : U32))

def dec.down(+d: List<&2, U32>, +e10: U32) -> F64:
  +b = big.pow5(U32.to_nat((OFF() - e10 : U32)), big.one())
  +bd = big.bits(d)
  +bn = (57 + big.bits(b) : U32)
  dec.down.s(d, b, e10, Bool.pick(U32, U32.is_gt(bn, bd), (bn - bd : U32), 0))

def dec.fin(c: Bool, d: List<&2, U32>, +e10: U32) -> F64:
  match c:
    case True{}:
      dec.up(d, e10)
    case False{}:
      dec.down(d, e10)

# past 10^309 infinity, below 10^-324 zero (under half the least
# subnormal, 4.9e-324), else the exact value rounded
def dec.range(hi: Bool, lo: Bool, d: List<&2, U32>, +e10: U32) -> F64:
  match hi lo:
    case True{} _:
      inf(0)
    case False{} True{}:
      zero(0)
    case False{} False{}:
      dec.fin(U32.is_ge(e10, OFF()), d, e10)

# d * 10^(e10 - OFF), d with nd significant digits: in [10^(nd - 1 + E),
# 10^(nd + E))
def dec.go(d: List<&2, U32>, +nd: U32, +e10: U32) -> F64:
  match d:
    case Nil{}:
      zero(0)
    case d:
      +u = (e10 + nd : U32)
      dec.range(U32.is_ge(u, (OFF() + 310 : U32)), U32.is_le(u, (OFF() - 324 : U32)), d, e10)

def of_dec.e(xneg: Bool, +xe: U32, +lf: U32) -> U32:
  match xneg:
    case True{}:
      ((OFF() - xe : U32) - lf : U32)
    case False{}:
      ((OFF() + xe : U32) - lf : U32)

# the decimal I.F e X (e -X when xneg), its parts as written (digit
# character codes): the nearest F64, ties to even; past the greatest
# finite value plus half its ulp, infinity (a literal refuses it)
def of_dec(i: List<&2, U32>, +f: List<&2, U32>, xneg: Bool, x: List<&2, U32>) -> F64:
  +ds = List.append(&2, U32, i, f)
  dec.go(dec.big(ds, Nil{}), dec.sig(ds), of_dec.e(xneg, dec.exp(x, 0), U32.from_nat(List.length(&2, U32, f))))

def is_inf(x: F64) -> Bool:
  match x:
    case F64{+hi, lo}:
      Bool.and(U32.is_eq((hi .&. 2147483647 : U32), 2146435072), U32.is_eq(lo, 0))

# The operators: (a + b : F64.F64) is F64.F64.add(a, b) through the
# alias, so each operator's method is the operation itself
# ----------------------------------------------------------------------

def F64.add(a: F64, b: F64) -> F64:
  add(a, b)

def F64.sub(a: F64, b: F64) -> F64:
  sub(a, b)

def F64.mul(a: F64, b: F64) -> F64:
  mul(a, b)

def F64.div(a: F64, b: F64) -> F64:
  div(a, b)

def F64.is_lt(a: F64, b: F64) -> Bool:
  is_lt(a, b)

def F64.is_le(a: F64, b: F64) -> Bool:
  is_le(a, b)

def F64.is_gt(a: F64, b: F64) -> Bool:
  is_gt(a, b)

def F64.is_ge(a: F64, b: F64) -> Bool:
  is_ge(a, b)

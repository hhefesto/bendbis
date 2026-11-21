import Base

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Num: bend.ts's f32_round (a decimal literal to the nearest F32, ties to
# even) and f32_show (the shortest decimal that reads back to the same
# F32, spelled as JavaScript's String(Number(..)) spells it), exactly, over
# big naturals: little-endian limbs of 16 bits, one U32 each, no zero limb
# at the top. A Nat holds at most 2^48-1 at run time, so none is used for
# the magnitudes; signed exponents are U32s offset by OFF.

def OFF() -> U32:
  1048576

# Big naturals
# ------------

def big.trim.go(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{0, t}:
      big.trim.go(t)
    case xs:
      xs

# drop zero limbs at the top (the list is little-endian)
def big.trim(xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, big.trim.go(List.reverse(&2, U32, xs)))

def big.of(+n: U32) -> List<&2, U32>:
  big.trim([(n .&. 65535 : U32), (n >> 16n : U32)])

# a * m + c, m and c below 2^16
def big.muladd.go(xs: List<&2, U32>, +m: U32, c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      big.trim([c])
    case Con{x, t}:
      +v = ((x * m : U32) + c : U32)
      (v .&. 65535 : U32) <> big.muladd.go(t, m, (v >> 16n : U32))

def big.muladd(xs: List<&2, U32>, m: U32, c: U32) -> List<&2, U32>:
  big.trim(big.muladd.go(xs, m, c))

def big.mul10.n(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      big.mul10.n(p, big.muladd(xs, 10, 0))

def big.mul5.n(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      big.mul5.n(p, big.muladd(xs, 5, 0))

# xs * 2^n
def big.shl.bits(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      big.shl.bits(p, big.muladd(xs, 2, 0))

def big.zeros(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      0 <> big.zeros(p, xs)

def big.shl(+n: U32, xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      big.shl.bits(U32.to_nat((n .&. 15 : U32)), big.zeros(U32.to_nat((n >> 4n : U32)), Con{h, t}))

def big.len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

def bits.of(k: Nat, +n: U32) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Bool.pick(Nat, U32.is_eq(n, 0), 0n, 1n+bits.of(p, (n >> 1n : U32)))

# the bit length of a big natural (0 for zero)
def big.bits.top(xs: List<&2, U32>, n: Nat, top: U32) -> Nat:
  match xs:
    case Nil{}:
      Nat.add(Nat.mul(16n, Nat.sub(n, 1n)), bits.of(16n, top))
    case Con{x, t}:
      big.bits.top(t, 1n+n, x)

def big.bits(xs: List<&2, U32>) -> Nat:
  big.bits.top(xs, 0n, 0)

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
  big.cmp.at(Nat.cmp(big.len(xs), big.len(ys)), xs, ys)

def big.le(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  Cmp.is_le(big.cmp(xs, ys))

# xs - ys, for xs >= ys (b the borrow)
def big.sub.go(xs: List<&2, U32>, ys: List<&2, U32>, b: U32) -> List<&2, U32>:
  match xs ys:
    case Nil{} _:
      Nil{}
    case Con{+x, s} Nil{}:
      +v = (x + 65536 : U32)
      +w = (v - b : U32)
      (w .&. 65535 : U32) <> big.sub.go(s, Nil{}, Bool.pick(U32, U32.is_lt(w, 65536), 1, 0))
    case Con{+x, s} Con{+y, t}:
      +w = ((x + 65536 : U32) - (y + b : U32) : U32)
      (w .&. 65535 : U32) <> big.sub.go(s, t, Bool.pick(U32, U32.is_lt(w, 65536), 1, 0))

def big.sub(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  big.trim(big.sub.go(xs, ys, 0))

def big.is_zero(xs: List<&2, U32>) -> Bool:
  List.is_empty(&2, U32, xs)

def big.is_odd(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      U32.is_eq((x .&. 1 : U32), 1)

# a big natural below 2^32 as a U32
def big.u32(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{a, Nil{}}:
      a
    case Con{a, Con{b, t}}:
      (a .|. (b << 16n : U32) : U32)

# long division of a by b, a < b * 2^k: the quotient and the remainder
type Dv is Data:
  Dv{q: U32, r: List<&2, U32>}

def big.div.step(+bk: List<&2, U32>, +k: Nat, d: Dv) -> Dv:
  match d:
    case Dv{+q, +r}:
      Bool.pick(Dv, big.le(bk, r), Dv{(q .|. (1 << k : U32) : U32), big.sub(r, bk)}, Dv{q, r})

def big.div.go(+k: Nat, +b: List<&2, U32>, d: Dv) -> Dv:
  match k:
    case 0n:
      big.div.step(b, 0n, d)
    case 1n+p:
      big.div.go(p, b, big.div.step(big.shl.bits(1n+p, b), 1n+p, d))

def big.div(a: List<&2, U32>, b: List<&2, U32>, k: Nat) -> Dv:
  big.div.go(k, b, Dv{0, a})

# Decimal to F32 (f32_round)
# --------------------------

# the value of decimal digits (units '0'..'9')
def dec.big(ds: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      dec.big(t, big.muladd(acc, 10, (d - 48 : U32)))

def dec.strip(ds: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Con{48, t}:
      dec.strip(t)
    case ds:
      ds

# the F32 bits nearest n / d, n > 0: e is floor(log2(n / d)), its LSB the
# larger of e - 23 and -149 (offset by OFF)
def f32.near.round(+q: U32, +r: List<&2, U32>, +b: List<&2, U32>) -> U32:
  +c = big.cmp(big.muladd(r, 2, 0), b)
  Bool.pick(U32, Bool.or(Cmp.is_gt(c), Bool.and(Cmp.is_eq(c), U32.is_eq((q .&. 1 : U32), 1))), (q + 1 : U32), q)

def f32.near.bits(+lsb: U32, +q: U32) -> U32:
  # (lsb + 150) << 23 + (q - 2^23) for a normal q (q >= 2^23), q for a
  # subnormal
  Bool.pick(U32, U32.is_lt(q, 8388608), q, ((((lsb + 150 : U32) - OFF() : U32) << 23n : U32) + (q - 8388608 : U32) : U32))

def f32.near.fin(+lsb: U32, dv: Dv, +b: List<&2, U32>) -> U32:
  match dv:
    case Dv{q, r}:
      f32.near.bits(lsb, f32.near.round(q, r, b))

def f32.near.ab(neg: Bool, +lsb: U32, n: List<&2, U32>, d: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match neg:
    case True{}:
      (big.shl((OFF() - lsb : U32), n), d)
    case False{}:
      (n, big.shl((lsb - OFF() : U32), d))

def f32.near.ab.fin(+lsb: U32, ab: List<&2, U32> & List<&2, U32>) -> U32:
  (a, +b) = ab
  f32.near.fin(lsb, big.div(a, b, 24n), b)

def f32.near.at(+lsb: U32, n: List<&2, U32>, d: List<&2, U32>) -> U32:
  f32.near.ab.fin(lsb, f32.near.ab(U32.is_lt(lsb, OFF()), lsb, n, d))

# n * 2^l >= d (l offset by OFF): n >= d * 2^-l when l < 0
def f32.ge.pow.if(neg: Bool, n: List<&2, U32>, d: List<&2, U32>, +l: U32) -> Bool:
  match neg:
    case True{}:
      big.le(big.shl((OFF() - l : U32), d), n)
    case False{}:
      big.le(d, big.shl((l - OFF() : U32), n))

def f32.ge.pow(n: List<&2, U32>, d: List<&2, U32>, +l: U32) -> Bool:
  f32.ge.pow.if(U32.is_lt(l, OFF()), n, d, l)

def f32.near(+n: List<&2, U32>, +d: List<&2, U32>) -> U32:
  +l = ((OFF() + U32.from_nat(big.bits(n)) : U32) - U32.from_nat(big.bits(d)) : U32)
  # e = l if n >= d * 2^l, else l - 1; here as n * 2^(-l) >= d
  +e = Bool.pick(U32, f32.ge.pow(n, d, ((OFF() + OFF() : U32) - l : U32)), l, (l - 1 : U32))
  +lsb = U32.max((e - 23 : U32), (OFF() - 149 : U32))
  f32.near.at(lsb, n, d)

# the exponent's value, saturating at 10^8
def exp.go(ds: List<&2, U32>, acc: U32) -> U32:
  match ds:
    case Nil{}:
      acc
    case Con{+d, t}:
      exp.go(t, U32.min(100000000, ((acc * 10 : U32) + (d - 48 : U32) : U32)))

# f32_round of int digits i, fraction digits f, exponent sign s ('-' or
# not) and digits x: the F32 bits, or 2139095040 (infinity) when it
# overflows
def f32.of_dec.fin.if(up: Bool, n: List<&2, U32>, +e10: U32) -> U32:
  match up:
    case True{}:
      U32.min(2139095040, f32.near(big.mul10.n(U32.to_nat((e10 - OFF() : U32)), n), big.of(1)))
    case False{}:
      U32.min(2139095040, f32.near(n, big.mul10.n(U32.to_nat((OFF() - e10 : U32)), big.of(1))))

def f32.of_dec.fin(n: List<&2, U32>, +e10: U32) -> U32:
  f32.of_dec.fin.if(U32.is_ge(e10, OFF()), n, e10)

def f32.of_dec.range(big: Bool, small: Bool, ds: List<&2, U32>, +e10: U32) -> U32:
  match big small:
    case True{} _:
      2139095040
    case False{} True{}:
      0
    case False{} False{}:
      f32.of_dec.fin(dec.big(ds, Nil{}), e10)

def f32.of_dec.go(zero: Bool, ds: List<&2, U32>, +e10: U32, +nd: U32) -> U32:
  match zero:
    case True{}:
      0
    case False{}:
      f32.of_dec.range(U32.is_ge(((nd - 1 : U32) + e10 : U32), (OFF() + 39 : U32)), U32.is_le((nd + e10 : U32), (OFF() - 46 : U32)), ds, e10)

def f32.of_dec(i: List<&2, U32>, +f: List<&2, U32>, neg: Bool, x: List<&2, U32>) -> U32:
  +ds = dec.strip(List.append(&2, U32, i, f))
  +xe = exp.go(x, 0)
  # e10 = +-x - len(f), offset by OFF (|x| saturates at 10^8)
  +e10 = (Bool.pick(U32, neg, (OFF() - U32.min(xe, 1000000) : U32), (OFF() + U32.min(xe, 1000000) : U32)) - U32.from_nat(List.length(&2, U32, f)) : U32)
  +nd = U32.from_nat(List.length(&2, U32, ds))
  f32.of_dec.go(big.is_zero(dec.big(ds, Nil{})), ds, e10, nd)

# F32 to the shortest decimal (f32_show)
# ---------------------------------------

# the exact value of nonnegative finite bits: m * 2^k, k offset by OFF
type Fx is Data:
  Fx{m: U32, k: U32}

def f32.parts(+b: U32) -> Fx:
  +ex = (b >> 23n : U32)
  +mn = (b .&. 8388607 : U32)
  Bool.pick(Fx, U32.is_eq(ex, 0), Fx{mn, (OFF() - 149 : U32)}, Fx{(mn + 8388608 : U32), ((ex + OFF() : U32) - 150 : U32)})

# xs / 10 and xs % 10 (xs little-endian: the higher limbs divide first)
def big.divmod10.limb(+x: U32, qr: List<&2, U32> & U32) -> List<&2, U32> & U32:
  (q, r) = qr
  +v = ((r << 16n : U32) + x : U32)
  ((v / 10 : U32) <> q, (v % 10 : U32))

def big.divmod10.go(xs: List<&2, U32>) -> List<&2, U32> & U32:
  match xs:
    case Nil{}:
      (Nil{}, 0)
    case Con{x, t}:
      big.divmod10.limb(x, big.divmod10.go(t))

type Dg is Data:
  Dg{xs: List<&2, U32>, acc: List<&2, U32>, done: Bool}

def big.digits.put(qr: List<&2, U32> & U32, acc: List<&2, U32>) -> Dg:
  (q, r) = qr
  +t = big.trim(q)
  Dg{t, (r + 48 : U32) <> acc, big.is_zero(t)}

def big.digits.go(fuel: Nat, d: Dg) -> List<&2, U32>:
  match fuel d:
    case 1n+p Dg{xs, acc, False{}}:
      big.digits.go(p, big.digits.put(big.divmod10.go(xs), acc))
    case _ Dg{xs, acc, done}:
      acc

# the decimal digits (units '0'..'9') of a big natural, most significant
# first
def big.digits(+xs: List<&2, U32>) -> List<&2, U32>:
  big.digits.go(Nat.mul(5n, 1n+big.len(xs)), Dg{xs, Nil{}, big.is_zero(xs)})

def big.digits.or0(+xs: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, big.is_zero(xs), [48], big.digits(xs))

# the exact decimal of m * 2^k: its digits ds and scale s (the value is
# ds * 10^-s)
type Ex is Data:
  Ex{ds: List<&2, U32>, s: U32}

def f32.exact.if(up: Bool, +m: U32, +k: U32) -> Ex:
  match up:
    case True{}:
      Ex{big.digits.or0(big.shl((k - OFF() : U32), big.of(m))), 0}
    case False{}:
      Ex{big.digits.or0(big.mul5.n(U32.to_nat((OFF() - k : U32)), big.of(m))), (OFF() - k : U32)}

def f32.exact(fx: Fx) -> Ex:
  match fx:
    case Fx{+m, +k}:
      f32.exact.if(U32.is_ge(k, OFF()), m, k)

# decimal digits (most significant first) plus one, with the carry out
def dec.inc.digit(+d: U32, +t: List<&2, U32>, c: Bool) -> List<&2, U32> & Bool:
  match c:
    case False{}:
      (d <> t, False{})
    case True{}:
      Bool.pick(List<&2, U32> & Bool, U32.is_eq(d, 57), (48 <> t, True{}), ((d + 1 : U32) <> t, False{}))

def dec.inc.put(+d: U32, r: List<&2, U32> & Bool) -> List<&2, U32> & Bool:
  (t, c) = r
  dec.inc.digit(d, t, c)

def dec.inc.go(ds: List<&2, U32>) -> List<&2, U32> & Bool:
  match ds:
    case Nil{}:
      (Nil{}, True{})
    case Con{d, t}:
      dec.inc.put(d, dec.inc.go(t))

def dec.all_zero(ds: List<&2, U32>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, t}:
      Bool.and(U32.is_eq(d, 48), dec.all_zero(t))

# round up when what is cut is at least half (toExponential: a tie rounds
# to the larger)
def dec.cut.up(rest: List<&2, U32>) -> Bool:
  match rest:
    case Nil{}:
      False{}
    case Con{+d, t}:
      U32.is_ge(d, 53)

# ds rounded to p significant digits: the p digits and whether the
# exponent grows by one (999 rounding to 1000)
def dec.round.carry.if(c: Bool, t: List<&2, U32>, p: Nat) -> List<&2, U32> & Bool:
  match c:
    case True{}:
      (List.take(&2, U32, 49 <> t, p), True{})
    case False{}:
      (t, False{})

def dec.round.carry(r: List<&2, U32> & Bool, +p: Nat) -> List<&2, U32> & Bool:
  (t, c) = r
  dec.round.carry.if(c, t, p)

def dec.pad(+ds: List<&2, U32>, n: Nat) -> List<&2, U32>:
  List.append(&2, U32, ds, List.replicate(U32, Nat.sub(n, List.length(&2, U32, ds)), 48))

def dec.round.go(up: Bool, +t: List<&2, U32>, +p: Nat) -> List<&2, U32> & Bool:
  match up:
    case False{}:
      (dec.pad(t, p), False{})
    case True{}:
      dec.round.carry(dec.inc.go(dec.pad(t, p)), p)

def dec.round(+ds: List<&2, U32>, +p: Nat) -> List<&2, U32> & Bool:
  dec.round.go(dec.cut.up(List.drop(&2, U32, ds, p)), List.take(&2, U32, ds, p), p)

def dec.strip_end(ds: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, dec.strip(List.reverse(&2, U32, ds)))

# the F32 bits nearest the digits ds times 10^e10 (e10 offset by OFF)
def f32.of_ds(+ds: List<&2, U32>, +e10: U32) -> U32:
  +st = dec.strip(ds)
  f32.of_dec.go(big.is_zero(dec.big(st, Nil{})), st, e10, U32.from_nat(List.length(&2, U32, st)))

def zeros(n: Nat) -> List<&2, U32>:
  List.replicate(U32, n, 48)

# JavaScript's Number::toString of the digits ds (k of them, no trailing
# zero) with the point at n (offset by OFF): the value is 0.ds * 10^n
def js.num.exp(+ds: List<&2, U32>, +n: U32) -> List<&2, U32>:
  +e = (n - 1 : U32)
  +head = List.take(&2, U32, ds, 1n)
  +tail = List.drop(&2, U32, ds, 1n)
  +frac = Bool.pick(List<&2, U32>, List.is_empty(&2, U32, tail), Nil{}, 46 <> tail)
  +sign = Bool.pick(U32, U32.is_ge(e, OFF()), 43, 45)
  +mag = Bool.pick(U32, U32.is_ge(e, OFF()), (e - OFF() : U32), (OFF() - e : U32))
  List.append(&2, U32, head, List.append(&2, U32, frac, 101 <> sign <> big.digits.or0(big.of(mag))))

def js.num.go(c: Nat, +ds: List<&2, U32>, +n: U32, +k: U32) -> List<&2, U32>:
  match c:
    case 0n:
      List.append(&2, U32, ds, zeros(U32.to_nat((n - (OFF() + k : U32) : U32))))
    case 1n:
      List.append(&2, U32, List.take(&2, U32, ds, U32.to_nat((n - OFF() : U32))), 46 <> List.drop(&2, U32, ds, U32.to_nat((n - OFF() : U32))))
    case 2n:
      48 <> 46 <> List.append(&2, U32, zeros(U32.to_nat((OFF() - n : U32))), ds)
    case _:
      js.num.exp(ds, n)

def js.num(+ds: List<&2, U32>, +n: U32) -> List<&2, U32>:
  +k = U32.from_nat(List.length(&2, U32, ds))
  +c = Bool.pick(Nat, Bool.and(U32.is_le((OFF() + k : U32), n), U32.is_le(n, (OFF() + 21 : U32))), 0n,
    Bool.pick(Nat, Bool.and(U32.is_lt(OFF(), n), U32.is_le(n, (OFF() + 21 : U32))), 1n,
      Bool.pick(Nat, Bool.and(U32.is_lt((OFF() - 6 : U32), n), U32.is_le(n, OFF())), 2n, 3n)))
  js.num.go(c, ds, n, k)

# s.replace(/^-?\d+(?=e|$)/, "$&.0"): an integer, or a mantissa with no
# point, takes ".0"
def dot0.go(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [46, 48]
    case Con{101, t}:
      46 <> 48 <> 101 <> t
    case Con{46, t}:
      46 <> t
    case Con{d, t}:
      d <> dot0.go(t)

# the candidate for p digits: Some(the text) when it reads back to bits
def f32.show.cand(r: List<&2, U32> & Bool, +e: U32, +bits: U32, +p: Nat) -> Maybe<&2, List<&2, U32>>:
  (+rs, grow) = r
  +e2 = Bool.pick(U32, grow, (e + 1 : U32), e)
  Bool.pick(Maybe<&2, List<&2, U32>>, U32.is_eq(f32.of_ds(rs, (e2 - (U32.from_nat(p) - 1 : U32) : U32)), bits),
    Some{dot0.go(js.num(dec.strip_end(rs), (e2 + 1 : U32)))}, None{})

def f32.show.try(+ex: Ex, +bits: U32, +p: Nat) -> Maybe<&2, List<&2, U32>>:
  match ex:
    case Ex{+ds, +s}:
      +e = (((OFF() + U32.from_nat(List.length(&2, U32, ds)) : U32) - 1 : U32) - s : U32)
      f32.show.cand(dec.round(ds, p), e, bits, p)

def nan.text() -> List<&2, U32>:
  [110, 97, 110]

def f32.show.go(fuel: Nat, +ex: Ex, +bits: U32, +p: Nat) -> List<&2, U32>:
  match fuel:
    case 0n:
      nan.text()
    case 1n+f:
      Maybe.default(&2, List<&2, U32>, f32.show.try(ex, bits, p), f32.show.go(f, ex, bits, 1n+p))

# f32_show of nonnegative finite bits, as units
def f32.show.pos(+bits: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_eq(bits, 0), [48, 46, 48], f32.show.go(9n, f32.exact(f32.parts(bits)), bits, 1n))

# f32_show of any bits: nan, inf and -inf as such, -0 as -0.0
def f32.show.cls(+mag: U32) -> Nat:
  Bool.pick(Nat, U32.is_gt(mag, 2139095040), 0n, Bool.pick(Nat, U32.is_eq(mag, 2139095040), 1n, 2n))

def f32.show.go2(c: Nat, neg: Bool, +mag: U32) -> List<&2, U32>:
  match c neg:
    case 0n _:
      nan.text()
    case 1n True{}:
      [45, 105, 110, 102]
    case 1n False{}:
      [105, 110, 102]
    case _ True{}:
      45 <> f32.show.pos(mag)
    case _ False{}:
      f32.show.pos(mag)

# f32_show of any bits: nan, inf and -inf as such, -0 as -0.0
def f32.show(+bits: U32) -> List<&2, U32>:
  +mag = (bits .&. 2147483647 : U32)
  f32.show.go2(f32.show.cls(mag), U32.is_ge(bits, 2147483648), mag)

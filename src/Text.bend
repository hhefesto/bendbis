import Base

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Text: the source as JavaScript sees it. Upstream reads a file with
# fs.readFileSync(f, "utf8") into a JS string, a sequence of UTF-16 code
# units, and every offset it keeps (a span's beg and end, a column) counts
# those units. bendbis holds a file the same way: its bytes, decoded as
# the WHATWG UTF-8 decoder does (each maximal invalid subpart is one
# U+FFFD), then spelled in UTF-16 code units, one U32 each. Output goes
# the other way: a surrogate pair is its scalar, a lone surrogate U+FFFD
# (what Buffer.from(text) writes).

type Dec is Data:
  Dec{need: U32, cp: U32, lo: U32, hi: U32, acc: List<&2, U32>}

def u8.cls(+b: U32) -> Nat:
  Bool.pick(Nat, U32.is_lt(b, 128), 0n,
    Bool.pick(Nat, U32.is_lt(b, 194), 4n,
      Bool.pick(Nat, U32.is_lt(b, 224), 1n,
        Bool.pick(Nat, U32.is_lt(b, 240), 2n,
          Bool.pick(Nat, U32.is_lt(b, 245), 3n, 4n)))))

# a lead byte, no sequence pending
def u8.lead(+b: U32, acc: List<&2, U32>, c: Nat) -> Dec:
  match c:
    case 0n:
      Dec{0, 0, 128, 191, b <> acc}
    case 1n:
      Dec{1, (b .&. 31 : U32), 128, 191, acc}
    case 2n:
      Dec{2, (b .&. 15 : U32), Bool.pick(U32, U32.is_eq(b, 224), 160, 128), Bool.pick(U32, U32.is_eq(b, 237), 159, 191), acc}
    case 3n:
      Dec{3, (b .&. 7 : U32), Bool.pick(U32, U32.is_eq(b, 240), 144, 128), Bool.pick(U32, U32.is_eq(b, 244), 143, 191), acc}
    case _:
      Dec{0, 0, 128, 191, 65533 <> acc}

def u8.cont.fin(+cp: U32, acc: List<&2, U32>, need: Nat) -> Dec:
  match need:
    case 0n:
      Dec{0, 0, 128, 191, cp <> acc}
    case 1n+p:
      Dec{U32.from_nat(1n+p), cp, 128, 191, acc}

def u8.cont(+b: U32, need: U32, cp: U32, acc: List<&2, U32>, ok: Bool) -> Dec:
  match ok:
    case True{}:
      u8.cont.fin(((cp << 6n) .|. (b .&. 63) : U32), acc, Nat.sub(U32.to_nat(need), 1n))
    case False{}:
      u8.lead(b, 65533 <> acc, u8.cls(b))

def u8.step.go(+b: U32, need: U32, cp: U32, +lo: U32, +hi: U32, acc: List<&2, U32>, z: Bool) -> Dec:
  match z:
    case True{}:
      u8.lead(b, acc, u8.cls(b))
    case False{}:
      u8.cont(b, need, cp, acc, Bool.and(U32.is_le(lo, b), U32.is_le(b, hi)))

def u8.step(+b: U32, s: Dec) -> Dec:
  match s:
    case Dec{+need, cp, +lo, +hi, acc}:
      u8.step.go(b, need, cp, lo, hi, acc, U32.is_eq(need, 0))

def u8.end.if(acc: List<&2, U32>, z: Bool) -> List<&2, U32>:
  match z:
    case True{}:
      acc
    case False{}:
      65533 <> acc

def u8.end(s: Dec) -> List<&2, U32>:
  match s:
    case Dec{need, cp, lo, hi, acc}:
      u8.end.if(acc, U32.is_eq(need, 0))

def u8.go(xs: List<&2, U32>, s: Dec) -> List<&2, U32>:
  match xs:
    case Nil{}:
      u8.end(s)
    case Con{+b, t}:
      u8.go(t, u8.step(b, s))

# a code point's UTF-16 units put in front of acc
def u16.put.if(+c: U32, acc: List<&2, U32>, big: Bool) -> List<&2, U32>:
  match big:
    case False{}:
      c <> acc
    case True{}:
      +d = (c - 65536 : U32)
      (55296 + (d >> 10n : U32) : U32) <> (56320 + (d .&. 1023 : U32) : U32) <> acc

def u16.put(+c: U32, acc: List<&2, U32>) -> List<&2, U32>:
  u16.put.if(c, acc, U32.is_ge(c, 65536))

def u16.rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{+c, t}:
      u16.rev(t, u16.put(c, acc))

# bytes to UTF-16 units, as readFileSync(f, "utf8") reads them
def of_bytes(xs: List<&2, U32>) -> List<&2, U32>:
  u16.rev(u8.go(xs, Dec{0, 0, 128, 191, Nil{}}), Nil{})

# code points to UTF-16 units
def of_cps(xs: List<&2, U32>) -> List<&2, U32>:
  u16.rev(List.reverse(&2, U32, xs), Nil{})

def hi.sur(+c: U32) -> Bool:
  Bool.and(U32.is_le(55296, c), U32.is_le(c, 56319))

def lo.sur(+c: U32) -> Bool:
  Bool.and(U32.is_le(56320, c), U32.is_le(c, 57343))

def sur(+c: U32) -> Bool:
  Bool.and(U32.is_le(55296, c), U32.is_le(c, 57343))

# UTF-16 units to code points, as codePointAt walks them; a lone surrogate
# stays itself (lone is the code a lone one becomes: itself, or U+FFFD)
def cps.pair(+h: U32, t: List<&2, U32>, +lone: U32, acc: List<&2, U32>, ok: Bool) -> List<&2, U32> & List<&2, U32>:
  match t ok:
    case Con{+l, r} True{}:
      (r, (((h - 55296 : U32) << 10n : U32) + ((l - 56320 : U32) + 65536 : U32) : U32) <> acc)
    case u _:
      (u, Bool.pick(U32, sur(h), lone, h) <> acc)

def cps.next(t: List<&2, U32>) -> Bool:
  match t:
    case Nil{}:
      False{}
    case Con{+c, r}:
      lo.sur(c)

# the next code point of xs (at a high surrogate with its low one, the pair)
def step(+lone: U32, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match xs:
    case Nil{}:
      (Nil{}, acc)
    case Con{+h, +t}:
      cps.pair(h, t, lone, acc, Bool.and(hi.sur(h), cps.next(t)))

def cps.go(+lone: U32, fuel: Nat, st: List<&2, U32> & List<&2, U32>) -> List<&2, U32>:
  match fuel st:
    case 0n, (xs, acc):
      List.reverse(&2, U32, acc)
    case 1n+p, (Nil{}, acc):
      List.reverse(&2, U32, acc)
    case 1n+p, (Con{h, t}, acc):
      cps.go(lone, p, step(lone, Con{h, t}, acc))

def cps.with(+lone: U32, +xs: List<&2, U32>) -> List<&2, U32>:
  cps.go(lone, List.length(&2, U32, xs), (xs, Nil{}))

# UTF-16 units to code points, a lone surrogate as U+FFFD (Buffer.from)
def cps(+xs: List<&2, U32>) -> List<&2, U32>:
  cps.with(65533, xs)

def str.go(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{c, t}:
      SCon{Chr{c}, str.go(t)}

# code points to a String
def str.cps(xs: List<&2, U32>) -> String:
  str.go(xs)

# UTF-16 units to a String (a lone surrogate as U+FFFD)
def str(+xs: List<&2, U32>) -> String:
  str.go(cps(xs))

def ofstr.go(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      c <> ofstr.go(t)

# a String's code points
def cps.of(s: String) -> List<&2, U32>:
  ofstr.go(s)

# a String's UTF-16 units
def units(s: String) -> List<&2, U32>:
  of_cps(ofstr.go(s))

# Characters, as bend.ts classes them (on one UTF-16 unit)
# ----------

def is_head(+c: U32) -> Bool:
  Bool.or(Bool.or(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)), Bool.and(U32.is_le(97, c), U32.is_le(c, 122))), U32.is_eq(c, 95))

def is_digit(+c: U32) -> Bool:
  Bool.and(U32.is_le(48, c), U32.is_le(c, 57))

def is_name(+c: U32) -> Bool:
  Bool.or(Bool.or(is_head(c), is_digit(c)), U32.is_eq(c, 46))

# \w
def is_word(+c: U32) -> Bool:
  Bool.or(is_head(c), is_digit(c))

# space, newline, carriage return, tab: what parse_skip skips
def is_blank(+c: U32) -> Bool:
  Bool.or(Bool.or(U32.is_eq(c, 32), U32.is_eq(c, 10)), Bool.or(U32.is_eq(c, 13), U32.is_eq(c, 9)))

# JavaScript's \s (and String.prototype.trim's set): WhiteSpace and
# LineTerminator
def is_space(+c: U32) -> Bool:
  Bool.or(Bool.or(Bool.and(U32.is_le(9, c), U32.is_le(c, 13)), U32.is_eq(c, 32)),
    Bool.or(Bool.or(U32.is_eq(c, 160), U32.is_eq(c, 5760)),
      Bool.or(Bool.or(Bool.and(U32.is_le(8192, c), U32.is_le(c, 8202)), Bool.or(U32.is_eq(c, 8232), U32.is_eq(c, 8233))),
        Bool.or(Bool.or(U32.is_eq(c, 8239), U32.is_eq(c, 8287)), Bool.or(U32.is_eq(c, 12288), U32.is_eq(c, 65279))))))

# Lists of units
# --------------

def eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, s} Con{b, t}:
      Bool.and(U32.is_eq(a, b), eq(s, t))
    case _ _:
      False{}

# does xs start with p
def prefix(xs: List<&2, U32>, p: List<&2, U32>) -> Bool:
  match xs p:
    case _ Nil{}:
      True{}
    case Con{b, t} Con{a, s}:
      Bool.and(U32.is_eq(a, b), prefix(t, s))
    case Nil{} Con{a, s}:
      False{}

def append(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

def drop(xs: List<&2, U32>, n: Nat) -> List<&2, U32>:
  List.drop(&2, U32, xs, n)

def take(xs: List<&2, U32>, n: Nat) -> List<&2, U32>:
  List.take(&2, U32, xs, n)

def len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

def at.go(n: Nat, xs: List<&2, U32>) -> U32:
  match n xs:
    case 0n Con{c, t}:
      c
    case 1n+p Con{c, t}:
      at.go(p, t)
    case _ Nil{}:
      4294967295

# the unit at offset n, 4294967295 past the end
def at(xs: List<&2, U32>, n: U32) -> U32:
  at.go(U32.to_nat(n), xs)

# xs from offset a up to offset b
def slice(+xs: List<&2, U32>, +a: U32, b: U32) -> List<&2, U32>:
  take(drop(xs, U32.to_nat(a)), Nat.sub(U32.to_nat(b), U32.to_nat(a)))

def lit(s: String) -> List<&2, U32>:
  units(s)

# decimal digits of a U32
def u32(n: U32) -> String:
  U32.show(n)

# Encoding
# --------

# a code point's UTF-8 bytes put in front of acc (reversed)
def utf8.put(+c: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_lt(c, 128), c <> acc,
    Bool.pick(List<&2, U32>, U32.is_lt(c, 2048), (128 + (c .&. 63 : U32) : U32) <> (192 + (c >> 6n : U32) : U32) <> acc,
      Bool.pick(List<&2, U32>, U32.is_lt(c, 65536), (128 + (c .&. 63 : U32) : U32) <> (128 + ((c >> 6n : U32) .&. 63 : U32) : U32) <> (224 + (c >> 12n : U32) : U32) <> acc,
        (128 + (c .&. 63 : U32) : U32) <> (128 + ((c >> 6n : U32) .&. 63 : U32) : U32) <> (128 + ((c >> 12n : U32) .&. 63 : U32) : U32) <> (240 + (c >> 18n : U32) : U32) <> acc)))

def utf8.go(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      List.reverse(&2, U32, acc)
    case Con{+c, t}:
      utf8.go(t, utf8.put(c, acc))

# a String's UTF-8 bytes (as Buffer.from writes it)
def utf8(s: String) -> List<&2, U32>:
  utf8.go(cps.of(s), Nil{})

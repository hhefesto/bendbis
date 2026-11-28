import Base

# gen: the U32 natives' differential test (gate/u32n.sh). It prints files,
# each after a line "=== NAME": laws.bend, a law for each native op at edge
# and pseudo-random literals, its right side computed here by the compiled
# program (comp.ts's natives), and mut.OP.bend, one wrong law per op.
# Upstream checks laws.bend through Base's own defs, bit by bit over Word,
# so ALL PROOFS CHECK there says Base's def and the native agree at each
# input; bendbis checks it through its natives (Wnf.bend, "U32 natives"),
# so the same output there says the natives fired and agree too; and the
# mutants fail in both with the same report.

# xorshift32
def rng(+x: U32) -> U32:
  +a = U32.xor(x, U32.shln(x, 13n))
  +b = U32.xor(a, U32.shrn(a, 17n))
  U32.xor(b, U32.shln(b, 5n))

def edge(+k: U32) -> U32:
  match k:
    case 0:
      0
    case 1:
      1
    case 2:
      2
    case 3:
      3
    case 4:
      31
    case 5:
      32
    case 6:
      33
    case 7:
      255
    case 8:
      256
    case 9:
      65535
    case 10:
      65536
    case 11:
      2147483647
    case 12:
      2147483648
    case 13:
      2147483649
    case 14:
      4294967294
    case _:
      4294967295

# a literal from r: an edge value, a small one, or r itself
def val.at(+k: U32, +r: U32) -> U32:
  match k:
    case 0:
      edge(U32.and(U32.shrn(r, 2n), 15))
    case 1:
      U32.shrn(r, 24n)
    case _:
      r

def val(+r: U32) -> U32:
  val.at(U32.and(r, 3), r)

def b.show(z: Bool) -> String:
  match z:
    case True{}:
      "True{}"
    case False{}:
      "False{}"

def c.show(c: Cmp) -> String:
  match c:
    case LT{}:
      "LT{}"
    case EQ{}:
      "EQ{}"
    case GT{}:
      "GT{}"

def u.show(+v: U32) -> String:
  U32.show(v)

def n.show(+v: U32) -> String:
  U32.show(v) ++ "n"

# a law named t.N: {lhs == rhs : T}
def lw(+n: String, lhs: String, rhs: String, ty: String) -> String:
  "law t." ++ n ++ ":\n  {" ++ lhs ++ " == " ++ rhs ++ " : " ++ ty ++ "}\n\ndef t." ++ n ++ "():\n  {==}\n\n"

def call2(op: String, +a: U32, +b: U32) -> String:
  "U32." ++ op ++ "(" ++ U32.show(a) ++ ", " ++ U32.show(b) ++ ")"

def call1(op: String, +a: U32) -> String:
  "U32." ++ op ++ "(" ++ U32.show(a) ++ ")"

def calln(op: String, +a: U32, +k: U32) -> String:
  "U32." ++ op ++ "(" ++ U32.show(a) ++ ", " ++ n.show(k) ++ ")"

# the laws at inputs a, b (U32s), k (a shift, 0 to 39), m (a small U32 for
# to_nat and from_nat); i names them
def laws.at(+i: String, +a: U32, +b: U32, +k: U32, +m: U32) -> String:
  String.concat([
    lw("add." ++ i, call2("add", a, b), u.show(U32.add(a, b)), "U32"),
    lw("sub." ++ i, call2("sub", a, b), u.show(U32.sub(a, b)), "U32"),
    lw("mul." ++ i, call2("mul", a, b), u.show(U32.mul(a, b)), "U32"),
    lw("div." ++ i, call2("div", a, b), u.show(U32.div(a, b)), "U32"),
    lw("mod." ++ i, call2("mod", a, b), u.show(U32.mod(a, b)), "U32"),
    lw("and." ++ i, call2("and", a, b), u.show(U32.and(a, b)), "U32"),
    lw("or." ++ i, call2("or", a, b), u.show(U32.or(a, b)), "U32"),
    lw("xor." ++ i, call2("xor", a, b), u.show(U32.xor(a, b)), "U32"),
    lw("min." ++ i, call2("min", a, b), u.show(U32.min(a, b)), "U32"),
    lw("max." ++ i, call2("max", a, b), u.show(U32.max(a, b)), "U32"),
    lw("cmp." ++ i, call2("cmp", a, b), c.show(U32.cmp(a, b)), "Cmp"),
    lw("is_eq." ++ i, call2("is_eq", a, b), b.show(U32.is_eq(a, b)), "Bool"),
    lw("is_ne." ++ i, call2("is_ne", a, b), b.show(U32.is_ne(a, b)), "Bool"),
    lw("is_lt." ++ i, call2("is_lt", a, b), b.show(U32.is_lt(a, b)), "Bool"),
    lw("is_le." ++ i, call2("is_le", a, b), b.show(U32.is_le(a, b)), "Bool"),
    lw("is_gt." ++ i, call2("is_gt", a, b), b.show(U32.is_gt(a, b)), "Bool"),
    lw("is_ge." ++ i, call2("is_ge", a, b), b.show(U32.is_ge(a, b)), "Bool"),
    lw("eq_self." ++ i, call2("is_eq", a, a), b.show(U32.is_eq(a, a)), "Bool"),
    lw("not." ++ i, call1("not", a), u.show(U32.not(a)), "U32"),
    lw("inc." ++ i, call1("inc", a), u.show(U32.inc(a)), "U32"),
    lw("is_zero." ++ i, call1("is_zero", a), b.show(U32.is_zero(a)), "Bool"),
    lw("is_even." ++ i, call1("is_even", a), b.show(U32.is_even(a)), "Bool"),
    lw("shl." ++ i, call1("shl", a), u.show(U32.shl(a)), "U32"),
    lw("shr." ++ i, call1("shr", a), u.show(U32.shr(a)), "U32"),
    lw("shln." ++ i, calln("shln", a, k), u.show(U32.shln(a, U32.to_nat(k))), "U32"),
    lw("shrn." ++ i, calln("shrn", a, k), u.show(U32.shrn(a, U32.to_nat(k))), "U32"),
    lw("to_nat." ++ i, call1("to_nat", m), n.show(m), "Nat"),
    lw("from_nat." ++ i, "U32.from_nat(" ++ n.show(m) ++ ")", u.show(m), "U32"),
    lw("nest." ++ i, "U32.add(U32.mul(" ++ U32.show(a) ++ ", " ++ U32.show(b) ++ "), U32.shrn(U32.xor(" ++ U32.show(b) ++ ", " ++ U32.show(a) ++ "), " ++ n.show(k) ++ "))",
      u.show(U32.add(U32.mul(a, b), U32.shrn(U32.xor(b, a), U32.to_nat(k)))), "U32")])

# n rounds from seed r; round i's b is 0 every 8th round (div and mod)
def laws.go(n: Nat, +i: U32, +r: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      +r1 = rng(r)
      +r2 = rng(r1)
      +r3 = rng(r2)
      laws.at("r" ++ U32.show(i), val(r1), Bool.pick(U32, U32.is_eq(U32.and(i, 7), 0), 0, val(r2)), U32.mod(r3, 40), U32.and(r3, 255)) ++ laws.go(p, U32.add(i, 1), r3)

# one wrong law, op's value at (a, b) off by one (or the other Bool)
def mut(op: String, +lhs: String, +rhs: String, ty: String) -> String:
  "=== mut." ++ op ++ ".bend\nimport Base\n\n" ++ lw("m", lhs, rhs, ty)

def muts() -> String:
  String.concat([
    mut("add", call2("add", 7, 9), "15", "U32"),
    mut("sub", call2("sub", 1, 2), "4294967294", "U32"),
    mut("mul", call2("mul", 65536, 65536), "1", "U32"),
    mut("div", call2("div", 7, 0), "7", "U32"),
    mut("mod", call2("mod", 7, 0), "0", "U32"),
    mut("cmp", call2("cmp", 3, 3), "LT{}", "Cmp"),
    mut("is_lt", call2("is_lt", 2147483648, 1), "True{}", "Bool"),
    mut("not", call1("not", 0), "0", "U32"),
    mut("to_nat", call1("to_nat", 5), "4n", "Nat"),
    mut("from_nat", "U32.from_nat(5n)", "4", "U32"),
    mut("shln", calln("shln", 1, 32), "1", "U32"),
    mut("shrn", calln("shrn", 4294967295, 31), "0", "U32")])

# one wrong law over a variable x (or a Nat n): the report prints its
# stuck sides, so bendbis's stuck whnfs print as upstream's
def stk(nm: String, +v: String, eq: String) -> String:
  "=== stuck." ++ nm ++ ".bend\nimport Base\n\nlaw s:\n  for " ++ v ++ "\n  {" ++ eq ++ "}\n\ndef s(" ++ String.take(v, 1n) ++ "):\n  {==}\n"

def stucks() -> String:
  String.concat([
    stk("add_r", "x: U32", "U32.add(x, 1) == U32.add(1, x) : U32"),
    stk("add_l", "x: U32", "U32.add(1, x) == 2 : U32"),
    stk("nest", "x: U32", "U32.mul(U32.add(x, 1), U32.sub(9, 2)) == 0 : U32"),
    stk("nest_r", "x: U32", "U32.add(3, U32.add(4, U32.xor(5, x))) == 0 : U32"),
    stk("div", "x: U32", "U32.div(7, x) == U32.mod(x, 7) : U32"),
    stk("shln", "x: U32", "U32.shln(x, 3n) == U32.shrn(x, 2n) : U32"),
    stk("is_eq", "x: U32", "U32.is_eq(U32.add(x, 2), 3) == True{} : Bool"),
    stk("cmp", "x: U32", "U32.cmp(5, x) == LT{} : Cmp"),
    stk("min", "x: U32", "U32.min(U32.max(x, 2), 9) == 2 : U32"),
    stk("from", "n: Nat", "U32.from_nat(n) == U32.inc(U32.from_nat(n)) : U32"),
    stk("to_nat", "x: U32", "U32.to_nat(U32.add(x, 2)) == 0n : Nat"),
    stk("not", "x: U32", "U32.not(U32.shl(x)) == U32.shr(U32.not(x)) : U32")])

def main() -> IO(Unit):
  IO.print("=== laws.bend\nimport Base\n\n" ++ laws.go(48n, 0, 2463534242) ++ muts() ++ stucks())

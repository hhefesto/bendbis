import Base
import ./Core.bend as C
import ./High.bend as H

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Wnf: the checker's book, and bend.ts's evaluation: term_wnf (the machine,
# its frames and its stuck-call reconstruction, lhs), term_snf lowered
# (what expr_show prints), term_compare, lit_step, term_apply, lhs_ext.
#
# bend.ts's machine shares every argument, let value and demanded field in
# a cell it overwrites with the cell's whnf; bendbis has no mutable cell,
# so an argument is passed as it is and evaluated where it is read. The
# whnf, the normal forms and every verdict are the same; what is lost is
# the sharing (milestone 3). term_compare's identity tests (a === b, a
# cell's class) only shortcut answers the structural walk gives.

# The book
# --------

# a constructor: its name, field count, type (parameters and fields) and
# family
type Cr is Data:
  Cr{k: String, n: U32, T: H.H, f: String}

# book.tlds[k]: nothing, a datatype (parameter count, leading quantity
# count, type, constructors, Base's), or a def (arity, template count, type,
# body when checked, Base's, @unsafe, foreign, a law, and the names its
# elaborated body refers to once checked)
type Td is Data:
  TdNo{}
  TdAdt{n: U32, g: U32, T: H.H, c: List<&2, Cr>, b: Bool}
  TdDef{n: U32, x: U32, T: H.H, v: Maybe<&2, H.H>, b: Bool, u: Bool, ffi: Bool, l: Bool, rs: Maybe<&2, Map<&2, Bool>>}

def td.get(m: Map<&2, Td>, +k: String) -> Td:
  C.mp.get(Td, TdNo{}, m, k)

# the evaluator's view: the defs it unfolds (none for term_compare's rigid
# pass), and the book a check-mat goal reads its fields' types in
type W is Data:
  W{bk: Map<&2, Td>, real: Map<&2, Td>}

def w.rigid(+real: Map<&2, Td>) -> W:
  W{Map.new(&2, Td), real}

def w.real(w: W) -> Map<&2, Td>:
  match w:
    case W{bk, real}:
      real

# Applying
# --------

def FUEL() -> Nat:
  4294967295n

def hr.h(r: H.HR) -> H.H:
  match r:
    case H.HRH{h}:
      h
    case _:
      H.HHol{"bendbis: an evaluation failed", C.NoSp{}}

# term_apply(f, x, s)
def ap(f: H.H, x: H.H, s: C.Sp) -> H.H:
  hr.h(H.hm.go(FUEL(), Nil{}, H.JTApply{f, x, s}))

# a closure (no check-mat goal: the machine opens only lambdas and lets)
def ap0(cl: H.Cl, x: H.H) -> H.H:
  hr.h(H.hm.go(FUEL(), Nil{}, H.JApply{cl, x}))

def apL(cl: H.Cl, xs: List<&2, H.H>) -> H.H:
  hr.h(H.hm.go(FUEL(), Nil{}, H.JApplyL{cl, xs}))

# lhs_ext(lhs, k, n): lhs applied to k's n fields, as lambdas
def lhs_ext.go(z: Bool, t: H.H, k: String, n: U32) -> H.H:
  match z:
    case True{}:
      ap(t, H.HCtr{k, Nil{}, C.NoSp{}}, C.NoSp{})
    case False{}:
      H.HLam{"_", 0, H.ClExt{t, k, n, Nil{}}, C.NoSp{}, C.QL{}}

def lhs_ext(t: H.H, k: String, +n: U32) -> H.H:
  lhs_ext.go(U32.is_eq(n, 0), t, k, n)

# Literals
# --------

def word.go(+k: Nat, +n: U32, +s: C.Sp, out: H.H) -> H.H:
  match k:
    case 0n:
      out
    case 1n+i:
      word.go(i, n, s, H.HCtr{"WCon", [H.HCtr{Bool.pick(String, U32.is_eq(((n >> i : U32) .&. 1 : U32), 1), "True", "False"), Nil{}, s}, out], s})

def word(n: U32, +s: C.Sp) -> H.H:
  word.go(32n, n, s, H.HCtr{"WNil", Nil{}, s})

# lit_step: a literal's first constructor layer (any other term as is)
def lit_step(t: H.H) -> H.H:
  match t:
    case H.HNat{+v, +s}:
      Bool.pick(H.H, U32.is_eq(v, 0), H.HCtr{"Zero", Nil{}, s}, H.HCtr{"Succ", [H.HNat{(v - 1 : U32), s}], s})
    case H.HU32{v, +s}:
      H.HCtr{"U32", [word(v, s)], s}
    case H.HF32{v, +s}:
      H.HCtr{"F32", [word(v, s)], s}
    case H.HStr{Nil{}, s}:
      H.HCtr{"SNil", Nil{}, s}
    case H.HStr{Con{c, r}, +s}:
      H.HCtr{"SCon", [H.HCtr{"Chr", [H.HU32{c, s}], s}, H.HStr{r, s}], s}
    case t:
      t

def is.lit(t: H.H) -> Bool:
  match t:
    case H.HNat{v, s}:
      True{}
    case H.HU32{v, s}:
      True{}
    case H.HF32{v, s}:
      True{}
    case H.HStr{v, s}:
      True{}
    case _:
      False{}

def is.ctr(t: H.H) -> Bool:
  match t:
    case H.HCtr{k, x, s}:
      True{}
    case _:
      False{}

def is.lam(t: H.H) -> Bool:
  match t:
    case H.HLam{k, i, cl, s, q}:
      True{}
    case _:
      False{}

def is.qua(t: H.H) -> Bool:
  match t:
    case H.HQua{q, s}:
      True{}
    case _:
      False{}

# The machine
# -----------

# the stuck call being rebuilt: the def's ref, applied to the arguments
# its lambdas took, its matched columns rebuilt from their fields
type Lt is Data:
  LtRef{rf: H.H}
  LtApp{t: Lt, x: H.H, s: C.Sp}
  LtExt{t: Lt, k: String, n: U32}

type Lh is Data:
  LhNo{}
  LhYes{t: Lt, n: U32}

def lt.mat(t: Lt) -> H.H:
  match t:
    case LtRef{rf}:
      rf
    case LtApp{t, x, s}:
      ap(lt.mat(t), x, s)
    case LtExt{t, k, n}:
      lhs_ext(lt.mat(t), k, n)

# the Ann a cell's value restores when filled (bend.ts's VAR frame's a)
type Va is Data:
  VaNo{}
  VaYes{T: H.H, s: C.Sp}

def va.of(h: H.H) -> Va:
  match h:
    case H.HAnn{x, A, s}:
      VaYes{A, s}
    case _:
      VaNo{}

type Fr is Data:
  FApp{x: H.H, s: C.Sp}
  FMat{t: H.H, e: H.H, lhs: Lh, s: C.Sp}
  FMna{b: H.H, s: C.Sp}
  FMnb{a: H.H, s: C.Sp}
  FVar{n: U32, a: Va}
  FRwt{t: H.H, lhs: Lh}

# Share cells
# -----------

# bend.ts's machine shares every argument, let value and demanded field in
# a cell: a Var whose value it overwrites with the value's whnf, so work
# shared is done once; its comparison links two cells it found equal, so a
# shared graph is compared once. bendbis's cell is an HVal whose index is
# 2^31 plus its number in a store (Cm), and whose own v is the raw term:
# anywhere the store is not (term_lower, h.force, a run without cells) it
# reads as that raw term, as bend.ts's term_force reads a cell. A store is
# made by one term_compare and dropped when it answers, and no other call
# makes cells, so no cell reaches the checker's terms.

# a filled cell: its whnf, and its class's link (its own number at a root)
type Ce is Data:
  CeNo{}
  CeV{v: H.H, c: U32}

# the store's entries, as bend.ts's mutable array of cells: a flat Array
# of cap = 2^d entries, made at the first write (a store that fills no
# cell allocates none) and doubled when a write is past its end. An Array
# is affine (Type), so every store is threaded, never copied: a read
# answers the entries back with the entry. Past depth 23 (the most a boxed
# entry may have) a write is dropped: that cell reads as unfilled, so the
# machine computes its whnf again, as it would with cells off.
type Ca is Type:
  CaNo{}
  CaA{d: Nat, cap: U32, a: Array<Ce>}

# a store: whether the machine makes cells, the next number, the entries
type Cm is Type:
  Cm{on: Bool, n: U32, t: Ca}

def CELL() -> U32:
  2147483648

# a store that makes no cells (term_wnf as the checker calls it)
def cm.off() -> Cm:
  Cm{False{}, 0, CaNo{}}

def cm.new() -> Cm:
  Cm{True{}, 0, CaNo{}}

def ca.got(+d: Nat, +cap: U32, r: Array<Ce> & Ce) -> Ca & Ce:
  (a, e) = r
  (CaA{d, cap, a}, e)

def ca.get.in(z: Bool, +d: Nat, +cap: U32, a: Array<Ce>, +k: U32) -> Ca & Ce:
  match z:
    case True{}:
      ca.got(d, cap, Array.get(Ce, a, k))
    case False{}:
      (CaA{d, cap, a}, CeNo{})

# entry k (CeNo past the end), and the entries
def ca.get(t: Ca, +k: U32) -> Ca & Ce:
  match t:
    case CaNo{}:
      (CaNo{}, CeNo{})
    case CaA{+d, +cap, a}:
      ca.get.in(U32.is_lt(k, cap), d, cap, a, k)

# a doubling's copy: the old entries moved, one by one, to the new array
type Cg is Type:
  Cg{src: Array<Ce>, dst: Array<Ce>}

def ca.mv.at(r: Array<Ce> & Ce, dst: Array<Ce>, +i: U32) -> Cg:
  (s, x) = r
  Cg{s, Array.set(Ce, dst, i, x)}

def ca.mv(f: Nat, g: Cg, +i: U32) -> Array<Ce>:
  match f g:
    case 0n Cg{s, d}:
      d
    case 1n+h Cg{s, d}:
      ca.mv(h, ca.mv.at(Array.swap(Ce, s, i, CeNo{}), d, i), (i + 1 : U32))

# doubled until k is inside (z), at most fuel times
def ca.fit(fuel: Nat, z: Bool, +d: Nat, +cap: U32, a: Array<Ce>, +k: U32) -> Ca:
  match fuel z:
    case _ True{}:
      CaA{d, cap, a}
    case 0n False{}:
      CaA{d, cap, a}
    case 1n+f False{}:
      +c2 = (cap + cap : U32)
      ca.fit(f, U32.is_lt(k, c2), 1n+d, c2, ca.mv(U32.to_nat(cap), Cg{a, Array.new(Ce, 1n+d, CeNo{})}, 0), k)

def ca.set.in(z: Bool, +d: Nat, +cap: U32, a: Array<Ce>, +k: U32, x: Ce) -> Ca:
  match z:
    case True{}:
      CaA{d, cap, Array.set(Ce, a, k, x)}
    case False{}:
      CaA{d, cap, a}

def ca.set.a(t: Ca, +k: U32, x: Ce) -> Ca:
  match t:
    case CaNo{}:
      CaNo{}
    case CaA{+d, +cap, a}:
      ca.set.in(U32.is_lt(k, cap), d, cap, a, k, x)

def ca.set(t: Ca, +k: U32, x: Ce) -> Ca:
  match t:
    case CaNo{}:
      ca.set.a(ca.fit(19n, U32.is_lt(k, 16), 4n, 16, Array.new(Ce, 4n, CeNo{}), k), k, x)
    case CaA{+d, +cap, a}:
      ca.set.a(ca.fit(Nat.sub(23n, d), U32.is_lt(k, cap), d, cap, a, k), k, x)

def is.cell(+i: U32) -> Bool:
  U32.is_ge(i, CELL())

def h.is.cell(h: H.H) -> Bool:
  match h:
    case H.HVal{k, +i, s, v}:
      is.cell(i)
    case _:
      False{}

# a term and the store after making it
type Cx is Type:
  Cx{h: H.H, cm: Cm}

type Cxs is Type:
  Cxs{hs: List<&2, H.H>, cm: Cm}

def cx.h(r: Cx) -> H.H:
  match r:
    case Cx{h, cm}:
      h

def cx.cm(r: Cx) -> Cm:
  match r:
    case Cx{h, cm}:
      cm

# x in cell n, unless x is a cell already or z (cells off)
def cell.of(+z: Bool, +n: U32, +x: H.H, +k: String) -> H.H:
  match z:
    case True{}:
      x
    case False{}:
      H.HVal{k, (CELL() + n : U32), H.h.s(x), x}

def cell.next(+z: Bool, +n: U32) -> U32:
  Bool.pick(U32, z, n, (n + 1 : U32))

# term_cell(x, k): x in a new cell, unless x is one (or the store makes none)
def cell(cm: Cm, +x: H.H, +k: String) -> Cx:
  match cm:
    case Cm{+on, +n, t}:
      +z = Bool.or(Bool.not(on), h.is.cell(x))
      Cx{cell.of(z, n, x, k), Cm{on, cell.next(z, n), t}}

# each of xs in a cell (a let's values named by its binders, in ks)
def cells.go(xs: List<&2, H.H>, +on: Bool, +n: U32, t: Ca, +ks: List<&2, String>, acc: List<&2, H.H>) -> Cxs:
  match xs:
    case Nil{}:
      Cxs{List.reverse(&2, H.H, acc), Cm{on, n, t}}
    case Con{+x, r}:
      +z = Bool.or(Bool.not(on), h.is.cell(x))
      +k = Maybe.default(&2, String, List.head(&2, String, ks), "_")
      cells.go(r, on, cell.next(z, n), t, List.tail(&2, String, ks), cell.of(z, n, x, k) <> acc)

def cells(cm: Cm, xs: List<&2, H.H>) -> Cxs:
  match cm:
    case Cm{on, n, t}:
      cells.go(xs, on, n, t, Nil{}, Nil{})

def hb.vals(bs: List<&2, H.HB>) -> List<&2, H.H>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{H.HB{k, i, q, v}, t}:
      v <> hb.vals(t)

def hb.ks(bs: List<&2, H.HB>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{H.HB{k, i, q, v}, t}:
      k <> hb.ks(t)

def cells.let(cm: Cm, +bs: List<&2, H.HB>) -> Cxs:
  match cm:
    case Cm{on, n, t}:
      cells.go(hb.vals(bs), on, n, t, hb.ks(bs), Nil{})

# a cell's root: the end of its class's links (a cell linked to itself, or
# unfilled), and the entries
type Rs is Type:
  RsDone{t: Ca, k: U32}
  RsNext{t: Ca, e: Ce, k: U32}

def rs.next(r: Ca & Ce, +k: U32) -> Rs:
  (t, e) = r
  RsNext{t, e, k}

def rs.step(z: Bool, t: Ca, +c: U32) -> Rs:
  match z:
    case True{}:
      RsDone{t, c}
    case False{}:
      rs.next(ca.get(t, c), c)

def cm.root.go(fuel: Nat, s: Rs) -> Ca & U32:
  match fuel s:
    case _ RsDone{t, k}:
      (t, k)
    case 0n RsNext{t, e, k}:
      (t, k)
    case 1n+f RsNext{t, CeV{v, +c}, +k}:
      cm.root.go(f, rs.step(U32.is_eq(c, k), t, c))
    case 1n+f RsNext{t, CeNo{}, k}:
      (t, k)

def cm.root(t: Ca, +k: U32) -> Ca & U32:
  cm.root.go(4294967295n, rs.next(ca.get(t, k), k))

# a cell's whnf as its own (the store's, once filled); the frame the
# machine pushes to fill it, if not yet
type Rd is Type:
  Rd{v: H.H, fs: List<&2, Fr>, cm: Cm}

def cell.read.e(e: Ce, cm: Cm, +j: U32, v: H.H) -> Rd:
  match e:
    case CeV{fv, c}:
      Rd{fv, Nil{}, cm}
    case CeNo{}:
      +u = v
      Rd{u, [FVar{j, va.of(u)}], cm}

def cell.read.r(r: Ca & Ce, +on: Bool, +n: U32, +j: U32, v: H.H) -> Rd:
  (t, e) = r
  cell.read.e(e, Cm{on, n, t}, j, v)

def cell.read.at(z: Bool, cm: Cm, +i: U32, v: H.H) -> Rd:
  match z cm:
    case False{} cm:
      Rd{v, Nil{}, cm}
    case True{} Cm{+on, +n, t}:
      +j = (i - CELL() : U32)
      cell.read.r(ca.get(t, j), on, n, j, v)

# reading HVal{_, i, _, v}: a let's value (v), or cell i of the store
def cell.read(cm: Cm, +i: U32, v: H.H) -> Rd:
  match cm:
    case Cm{+on, n, t}:
      cell.read.at(Bool.and(on, is.cell(i)), Cm{on, n, t}, i, v)

# the VAR frame's fill: the whnf's parts in cells (tree nodes inside a leaf
# stay plain), then cell j holds it (with the Ann its raw value had)
def pt.ctr(r: Cxs, k: String, s: C.Sp) -> Cx:
  match r:
    case Cxs{ys, c2}:
      Cx{H.HCtr{k, ys, s}, c2}

def pt.adt(r: Cxs, k: String, rs: List<&2, String>, s: C.Sp) -> Cx:
  match r:
    case Cxs{ys, c2}:
      Cx{H.HAdt{k, ys, rs, s}, c2}

def pt.all(r: Cx, q: C.Q, k: String, i: U32, cl: H.Cl, s: C.Sp) -> Cx:
  match r:
    case Cx{B, c2}:
      Cx{H.HAll{q, k, i, B, cl, s}, c2}

def pt.typ(r: Cx, s: C.Sp) -> Cx:
  match r:
    case Cx{g, c2}:
      Cx{H.HTyp{g, s}, c2}

def pt.mat(r: Cxs, k: String, s: C.Sp) -> Cx:
  match r:
    case Cxs{Con{h, Con{m, Nil{}}}, c2}:
      Cx{H.HMat{k, h, m, s}, c2}
    case Cxs{ys, c2}:
      Cx{H.HHol{"bendbis: unreachable (two cells)", s}, c2}

def pt.min(r: Cxs, s: C.Sp) -> Cx:
  match r:
    case Cxs{Con{a, Con{b, Nil{}}}, c2}:
      Cx{H.HMin{a, b, s}, c2}
    case Cxs{ys, c2}:
      Cx{H.HHol{"bendbis: unreachable (two cells)", s}, c2}

def pt.eql(r: Cxs, s: C.Sp) -> Cx:
  match r:
    case Cxs{Con{a, Con{b, Con{T, Nil{}}}}, c2}:
      Cx{H.HEql{a, b, T, s}, c2}
    case Cxs{ys, c2}:
      Cx{H.HHol{"bendbis: unreachable (three cells)", s}, c2}

def cell.parts(cm: Cm, tm: H.H) -> Cx:
  match tm:
    case H.HCtr{k, xs, s}:
      pt.ctr(cells(cm, xs), k, s)
    case H.HAdt{k, xs, r, s}:
      pt.adt(cells(cm, xs), k, r, s)
    case H.HAll{q, k, i, A, cl, s}:
      pt.all(cell(cm, A, "_"), q, k, i, cl, s)
    case H.HMat{k, h, m, s}:
      pt.mat(cells(cm, [h, m]), k, s)
    case H.HEql{a, b, T, s}:
      pt.eql(cells(cm, [a, b, T]), s)
    case H.HMin{a, b, s}:
      pt.min(cells(cm, [a, b]), s)
    case H.HTyp{g, s}:
      pt.typ(cell(cm, g, "_"), s)
    case tm:
      Cx{tm, cm}

def cell.put(cm: Cm, +j: U32, v: H.H) -> Cm:
  match cm:
    case Cm{on, n, t}:
      Cm{on, n, ca.set(t, j, CeV{v, j})}

def fill.ann(r: Cx, +j: U32, +t2: H.H, s: C.Sp) -> Cx:
  match r:
    case Cx{T2, c3}:
      Cx{t2, cell.put(c3, j, H.HAnn{t2, T2, s})}

def fill.at(r: Cx, +j: U32, a: Va) -> Cx:
  match r:
    case Cx{+t2, c2}:
      match a:
        case VaNo{}:
          Cx{t2, cell.put(c2, j, t2)}
        case VaYes{T, s}:
          fill.ann(cell(c2, T, "_"), j, t2, s)

def cell.fill(cm: Cm, +j: U32, a: Va, tm: H.H) -> Cx:
  fill.at(cell.parts(cm, tm), j, a)

# the APP frames on top, up to n
def run.count(n: Nat, frs: List<&2, Fr>, run: Nat) -> Nat:
  match n frs:
    case 0n _:
      run
    case 1n+m Con{FApp{x, s}, t}:
      run.count(m, t, 1n+run)
    case _ _:
      run

def lh.step.at(z: Bool, t: Lt, x: H.H, s: C.Sp, +n: U32) -> Lh:
  match z:
    case True{}:
      LhNo{}
    case False{}:
      LhYes{LtApp{t, x, s}, (n - 1 : U32)}

def lh.step(lhs: Lh, x: H.H, s: C.Sp) -> Lh:
  match lhs:
    case LhNo{}:
      LhNo{}
    case LhYes{t, +n}:
      lh.step.at(U32.is_eq(n, 0), t, x, s, n)

def lh.ext(fl: Lh, +k: String, +n: U32) -> Lh:
  match fl:
    case LhNo{}:
      LhNo{}
    case LhYes{t, m}:
      LhYes{LtExt{t, k, n}, ((m - 1 : U32) + n : U32)}

def fields.frames(xs: List<&2, H.H>, frs: List<&2, Fr>) -> List<&2, Fr>:
  match xs:
    case Nil{}:
      frs
    case Con{x, t}:
      FApp{x, C.NoSp{}} <> fields.frames(t, frs)

# a match's arm for constructor k: the arm, Efq (none), or a default term
type Arm is Data:
  ArmHit{h: H.H}
  ArmNone{}
  ArmDef{t: H.H}

def arm.pick(z: Bool, h: H.H, rest: Unit -> Arm) -> Arm:
  match z:
    case True{}:
      ArmHit{h}
    case False{}:
      rest(Unit{})

def arm.find(t: H.H, +k: String) -> Arm:
  match t:
    case H.HAnn{x, A, s}:
      arm.find(x, k)
    case H.HMat{+j, h, m, s}:
      arm.pick(String.eq(j, k), h, u => arm.find(m, k))
    case H.HEfq{s}:
      ArmNone{}
    case t:
      ArmDef{t}

def lh.t(fl: Lh, t: H.H) -> H.H:
  match fl:
    case LhNo{}:
      t
    case LhYes{l, n}:
      lt.mat(l)

# lhs.n > 0, n read as a JavaScript number: a match past a def's last
# parameter takes it below zero (two's complement here)
def pos(+n: U32) -> Bool:
  Bool.and(Bool.not(U32.is_eq(n, 0)), U32.is_lt(n, 2147483648))

def efq.lhs.at(z: Bool, t: Lt) -> Maybe<&2, H.H>:
  match z:
    case True{}:
      Some{lt.mat(t)}
    case False{}:
      None{}

def efq.lhs(lhs: Lh, frs: List<&2, Fr>) -> Maybe<&2, H.H>:
  match lhs frs:
    case LhYes{t, +n} Con{FApp{x, s}, r}:
      efq.lhs.at(pos(n), t)
    case _ _:
      None{}

def min.back(+tm: H.H, +a: H.H, +s: C.Sp) -> H.H:
  match tm:
    case H.HQua{C.QM{}, u}:
      a
    case H.HQua{C.QN{}, u}:
      tm
    case H.HQua{C.QL{}, u}:
      Bool.pick(H.H, is.qua(a), tm, H.HMin{a, tm, s})
    case _:
      H.HMin{a, tm, s}

type Mv is Data:
  MvMany{}
  MvNone{}
  MvOther{}

def mna.kind(tm: H.H) -> Mv:
  match tm:
    case H.HQua{C.QM{}, s}:
      MvMany{}
    case H.HQua{C.QN{}, s}:
      MvNone{}
    case _:
      MvOther{}

def is.rfl(t: H.H) -> Bool:
  match t:
    case H.HRfl{s}:
      True{}
    case _:
      False{}

# what the machine does next: reduce the focus (main), unwind a frame
# (back), or decide on something it computed
type Md is Type:
  MdMain{}
  MdBack{}
  MdRef{td: Td}
  MdRun{ok: Bool, v: H.H, n: U32}
  MdMna{mv: Mv, b: H.H, s: C.Sp}
  MdMat{t: H.H, e: H.H, fl: Lh, s: C.Sp}
  MdArm{arm: Arm, t: H.H, e: H.H, fl: Lh, s: C.Sp}
  MdRd{rd: Rd}
  MdLet{r: Cxs, cl: H.Cl}
  MdApp{r: Cx, s: C.Sp}
  MdFill{r: Cx}
  MdHit{r: Cxs}
  MdRwt{t: H.H, fl: Lh}
  MdNx{o: Nx, v: H.H, n: U32, s: C.Sp}
  MdN1{o: Nx, v: H.H, n: U32, s: C.Sp, r: Cx}
  MdN2{o: Nx, v: H.H, n: U32, s: C.Sp, x: U32, r: Cx}
  MdNs{ns: Ns, o: Nx, v: H.H, n: U32, s: C.Sp}

# U32 natives
# -----------
# Base's U32 operations on literals, in one step. bend.ts runs them as
# Base defines them, bit by bit through Word's constructors (U32.add is
# Word.add's ripple carry over 32 WCon cells), and so does bendbis when a
# native does not apply. The natives are the Base defs whose body matches
# its arguments first, in order (`match a b: case U32{x} U32{y}`, `match
# a`, `match n`, and U32.div's and U32.mod's `U32{aw} = a`): U32.add, sub,
# mul, div, mod, and, or, xor, min, max, cmp (two U32s), not, inc, to_nat,
# shl, shr (one), from_nat (a Nat). The rest of Base's U32 ops are made of
# these (U32.is_eq is Cmp.is_eq(U32.cmp(a, b)), U32.shln is n U32.shls) and
# reach them by Base's own unfolding.
#
# A def applied to all its arguments reads them as Base's def does: the
# first to its whnf, and the second only when the first is a literal.
# Each read ends one of four ways. A literal of the def's own type: on to
# the next, or the value, the one Base's def computes (comp.ts's natives
# compute it, gate/u32n.sh checks it against Base's def bit by bit). A
# whnf Base's match is stuck on (no constructor and no literal): the call
# is stuck, and its whnf is the call itself with the arguments read so far
# in their whnf, which is what Base's def answers there (its first match
# stuck rebuilds the call, bend.ts's lhs); the argument is not read again,
# since a stuck call read again runs again, and a native that read it and
# then gave it to Base's def would double the work at every level of a
# chain of them. Anything else (a constructor, or a literal of another
# type): Base's def runs, given that whnf, which it reads again in one
# step. So every verdict is Base's, and every whnf is too up to the
# arguments' own whnfs (Base's def, stuck on b after matching a, rebuilds
# a as `U32{w}` from its literal; here a stays the literal); the work is
# what changes. A literal needs Base (Load), whose names are no file's own,
# so a def named U32.op on literals is Base's.
type Nx is Data:
  NxNo{}
  NxAdd{}
  NxSub{}
  NxMul{}
  NxDiv{}
  NxMod{}
  NxAnd{}
  NxOr{}
  NxXor{}
  NxMin{}
  NxMax{}
  NxCmp{}
  NxNot{}
  NxInc{}
  NxNat{}
  NxShl{}
  NxShr{}
  NxFrom{}

# a native's shape: one U32 (U1), two U32s read a then b (U2),
# U32.from_nat's Nat (N1)
type Nk is Data:
  NkNo{}
  NkU1{}
  NkU2{}
  NkN1{}

# a whnf read: a U32 literal, a Nat literal, another constructor or
# literal (Base's match reads it), or stuck (Base's match is stuck on it)
type Nl is Data:
  NlU{v: U32}
  NlN{v: U32}
  NlK{}
  NlS{}

# what a native does after a read: answer h, read its second argument
# after x, run Base's def, or answer the call stuck
type Ns is Data:
  NsNo{}
  NsDone{h: H.H}
  NsMore{x: U32}
  NsStuck{}

# a native's name past "U32."
type Ne is Data:
  Ne{k: String, o: Nx}

def nx.tbl() -> List<&2, Ne>:
  [Ne{"add", NxAdd{}}, Ne{"sub", NxSub{}}, Ne{"mul", NxMul{}}, Ne{"div", NxDiv{}},
   Ne{"mod", NxMod{}}, Ne{"and", NxAnd{}}, Ne{"or", NxOr{}}, Ne{"xor", NxXor{}},
   Ne{"min", NxMin{}}, Ne{"max", NxMax{}}, Ne{"cmp", NxCmp{}}, Ne{"not", NxNot{}},
   Ne{"inc", NxInc{}}, Ne{"to_nat", NxNat{}}, Ne{"shl", NxShl{}},
   Ne{"shr", NxShr{}}, Ne{"from_nat", NxFrom{}}]

def nx.if(z: Bool, o: Nx) -> Nx:
  match z:
    case True{}:
      o
    case False{}:
      NxNo{}

def nx.hit(e: Ne, +r: String) -> Nx:
  match e:
    case Ne{k, o}:
      nx.if(String.eq(k, r), o)

def nx.find(t: List<&2, Ne>, got: Nx, +r: String) -> Nx:
  match t got:
    case Con{e, u} NxNo{}:
      nx.find(u, nx.hit(e, r), r)
    case _ got:
      got

# the native a def's name names: U32.<op> in nx.tbl, else NxNo
def nx.of(k: String) -> Nx:
  match k:
    case SCon{Chr{85}, SCon{Chr{51}, SCon{Chr{50}, SCon{Chr{46}, r}}}}:
      nx.find(nx.tbl(), NxNo{}, r)
    case _:
      NxNo{}

def nx.kind(o: Nx) -> Nk:
  match o:
    case NxNo{}:
      NkNo{}
    case NxNot{}:
      NkU1{}
    case NxInc{}:
      NkU1{}
    case NxNat{}:
      NkU1{}
    case NxShl{}:
      NkU1{}
    case NxShr{}:
      NkU1{}
    case NxFrom{}:
      NkN1{}
    case _:
      NkU2{}

# its arity
def nk.ar(k: Nk) -> U32:
  match k:
    case NkU2{}:
      2
    case NkNo{}:
      0
    case _:
      1

def nl.of(h: H.H) -> Nl:
  match h:
    case H.HU32{v, s}:
      NlU{v}
    case H.HNat{v, s}:
      NlN{v}
    case H.HCtr{k, x, s}:
      NlK{}
    case H.HF32{v, s}:
      NlK{}
    case H.HStr{v, s}:
      NlK{}
    case _:
      NlS{}

def nx.c(c: Cmp, +s: C.Sp) -> H.H:
  match c:
    case LT{}:
      H.HCtr{"LT", Nil{}, s}
    case EQ{}:
      H.HCtr{"EQ", Nil{}, s}
    case GT{}:
      H.HCtr{"GT", Nil{}, s}

# a one-argument native's value at a
def nx.u1(o: Nx, +a: U32, +s: C.Sp) -> H.H:
  match o:
    case NxNot{}:
      H.HU32{U32.not(a), s}
    case NxInc{}:
      H.HU32{U32.inc(a), s}
    case NxNat{}:
      H.HNat{a, s}
    case NxShl{}:
      H.HU32{U32.shl(a), s}
    case NxShr{}:
      H.HU32{U32.shr(a), s}
    case _:
      H.HHol{"bendbis: a U32 native's arity", s}

# a two-argument native's value at (a, b)
def nx.u2(o: Nx, +a: U32, +b: U32, +s: C.Sp) -> H.H:
  match o:
    case NxAdd{}:
      H.HU32{U32.add(a, b), s}
    case NxSub{}:
      H.HU32{U32.sub(a, b), s}
    case NxMul{}:
      H.HU32{U32.mul(a, b), s}
    case NxDiv{}:
      H.HU32{U32.div(a, b), s}
    case NxMod{}:
      H.HU32{U32.mod(a, b), s}
    case NxAnd{}:
      H.HU32{U32.and(a, b), s}
    case NxOr{}:
      H.HU32{U32.or(a, b), s}
    case NxXor{}:
      H.HU32{U32.xor(a, b), s}
    case NxMin{}:
      H.HU32{U32.min(a, b), s}
    case NxMax{}:
      H.HU32{U32.max(a, b), s}
    case NxCmp{}:
      nx.c(U32.cmp(a, b), s)
    case _:
      H.HHol{"bendbis: a U32 native's arity", s}

# after the first read
def nx.one.at(k: Nk, o: Nx, l: Nl, +s: C.Sp) -> Ns:
  match k l:
    case NkU1{} NlU{+a}:
      NsDone{nx.u1(o, a, s)}
    case NkU2{} NlU{a}:
      NsMore{a}
    case NkN1{} NlN{n}:
      NsDone{H.HU32{n, s}}
    case _ NlS{}:
      NsStuck{}
    case _ _:
      NsNo{}

def nx.one(+o: Nx, l: Nl, +s: C.Sp) -> Ns:
  nx.one.at(nx.kind(o), o, l, s)

# after the second read (a, the first, a U32 literal)
def nx.two(o: Nx, +a: U32, l: Nl, +s: C.Sp) -> Ns:
  match l:
    case NlU{b}:
      NsDone{nx.u2(o, a, b, s)}
    case NlS{}:
      NsStuck{}
    case _:
      NsNo{}

# the i-th argument frame's term (0 the first)
def nx.arg(i: Nat, frs: List<&2, Fr>) -> H.H:
  match i frs:
    case 0n Con{FApp{x, s}, t}:
      x
    case 1n+j Con{f, t}:
      nx.arg(j, t)
    case _ _:
      H.HHol{"bendbis: a U32 native's argument", C.NoSp{}}

def nx.keep.at(z: Bool, x: H.H, h: H.H) -> H.H:
  match z:
    case True{}:
      x
    case False{}:
      h

# the i-th argument frame with its term x read: its whnf h in its place (a
# cell x stays, h its fill), so nothing after reads x again
def nx.keep(x: H.H, h: H.H) -> H.H:
  match x:
    case H.HVal{k, +i, s, v}:
      nx.keep.at(is.cell(i), H.HVal{k, i, s, v}, h)
    case _:
      h

def nx.set(i: Nat, h: H.H, frs: List<&2, Fr>) -> List<&2, Fr>:
  match i frs:
    case 0n Con{FApp{x, u}, t}:
      FApp{nx.keep(x, h), u} <> t
    case 1n+j Con{f, t}:
      f <> nx.set(j, h, t)
    case _ frs:
      frs

# the frames past the first i
def frs.drop(i: Nat, frs: List<&2, Fr>) -> List<&2, Fr>:
  match i frs:
    case 1n+j Con{f, t}:
      frs.drop(j, t)
    case _ frs:
      frs

def nx.md.at(z: Bool, o: Nx, v: H.H, +n: U32, s: C.Sp) -> Md:
  match z:
    case True{}:
      MdNx{o, v, n, s}
    case False{}:
      MdRun{True{}, v, n}

# a def unfolding: a native when o is one and the def takes its arity
def nx.md(ok: Bool, +o: Nx, v: H.H, +n: U32, s: C.Sp) -> Md:
  match ok:
    case True{}:
      nx.md.at(Bool.and(Bool.not(U32.is_eq(nk.ar(nx.kind(o)), 0)), U32.is_eq(nk.ar(nx.kind(o)), n)), o, v, n, s)
    case False{}:
      MdRun{False{}, v, n}

def w.bk(w: W) -> Map<&2, Td>:
  match w:
    case W{bk, real}:
      bk

# the machine, as bend.ts's term_wnf: a cell met unfilled is read with a
# FVar frame under it, which fills the cell once its value is a whnf; a
# rewrite's evidence runs above a FRwt frame (bend.ts runs it as its own
# term_wnf: the frame keeps the frames below out of its reach)
def wnf.go(+fuel: Nat, +w: W, cm: Cm, md: Md, tm: H.H, +frs: List<&2, Fr>, lhs: Lh) -> Cx:
  match fuel md:
    case 0n _:
      Cx{H.HHol{"bendbis: term_wnf ran out of fuel", C.NoSp{}}, cm}
    case 1n+p MdMain{}:
      match tm:
        case H.HVal{k, +i, s, v}:
          wnf.go(p, w, cm.off(), MdRd{cell.read(cm, i, v)}, H.HQnt{s}, frs, lhs)
        case H.HAnn{x, A, s}:
          wnf.go(p, w, cm, MdMain{}, x, frs, lhs)
        case H.HMin{a, b, s}:
          wnf.go(p, w, cm, MdMain{}, a, FMna{b, s} <> frs, lhs)
        case H.HLet{bs, cl, s}:
          wnf.go(p, w, cm.off(), MdLet{cells.let(cm, bs), cl}, H.HQnt{s}, frs, lhs)
        case H.HApp{f, x, s}:
          wnf.go(p, w, cm.off(), MdApp{cell(cm, x, "_"), s}, f, frs, lhs)
        case H.HLam{k, i, cl, s, q}:
          match frs:
            case Con{FApp{+x, u}, r}:
              wnf.go(p, w, cm, MdMain{}, ap0(cl, x), r, lh.step(lhs, x, u))
            case frs:
              wnf.go(p, w, cm, MdBack{}, H.HLam{k, i, cl, s, q}, frs, LhNo{})
        case H.HMat{k, h, m, s}:
          match frs:
            case Con{FApp{+x, u}, r}:
              wnf.go(p, w, cm, MdMain{}, x, FMat{H.HMat{k, h, m, s}, x, lhs, u} <> r, LhNo{})
            case frs:
              wnf.go(p, w, cm, MdBack{}, H.HMat{k, h, m, s}, frs, LhNo{})
        case H.HEfq{s}:
          wnf.go(p, w, cm, MdBack{}, Maybe.default(&2, H.H, efq.lhs(lhs, frs), H.HEfq{s}), frs, LhNo{})
        case H.HRwt{+e, m, f, s}:
          wnf.go(p, w, cm, MdMain{}, e, FRwt{H.HRwt{e, m, f, s}, lhs} <> frs, LhNo{})
        case H.HRef{+k, s, b}:
          wnf.go(p, w, cm, MdRef{td.get(w.bk(w), k)}, H.HRef{k, s, b}, frs, lhs)
        case tm:
          wnf.go(p, w, cm, MdBack{}, tm, frs, LhNo{})
    case 1n+p MdRd{rd}:
      match rd:
        case Rd{v2, fs, cm2}:
          wnf.go(p, w, cm2, MdMain{}, v2, List.append(&2, Fr, fs, frs), LhNo{})
    case 1n+p MdLet{r, cl}:
      match r:
        case Cxs{vs, cm2}:
          wnf.go(p, w, cm2, MdMain{}, apL(cl, vs), frs, lhs)
    case 1n+p MdApp{r, s}:
      match r:
        case Cx{y, cm2}:
          wnf.go(p, w, cm2, MdMain{}, tm, FApp{y, s} <> frs, LhNo{})
    case 1n+p MdFill{r}:
      match r:
        case Cx{t2, cm2}:
          wnf.go(p, w, cm2, MdMain{}, t2, frs, LhNo{})
    case 1n+p MdHit{r}:
      match r:
        case Cxs{ys, cm2}:
          wnf.go(p, w, cm2, MdMain{}, tm, fields.frames(ys, frs), lhs)
    case 1n+p MdRef{td}:
      match td tm:
        case TdAdt{+n, g, T, c, ab} H.HRef{+k, +s, b}:
          wnf.go(p, w, cm, MdBack{}, Bool.pick(H.H, U32.is_eq(n, 0), H.HAdt{k, Nil{}, Nil{}, s}, H.HRef{k, s, b}), frs, LhNo{})
        case TdDef{+n, x, T, Some{v}, db, u, ffi, l, rs} H.HRef{+k, +s, b}:
          +m = U32.to_nat(n)
          wnf.go(p, w, cm, nx.md(Nat.is_eq(run.count(m, frs, 0n), m), nx.of(k), v, n, s), H.HRef{k, s, b}, frs, lhs)
        case TdDef{+n, x, T, Some{v}, db, u, ffi, l, rs} tm:
          +m = U32.to_nat(n)
          wnf.go(p, w, cm, MdRun{Nat.is_eq(run.count(m, frs, 0n), m), v, n}, tm, frs, lhs)
        case _ tm:
          wnf.go(p, w, cm, MdBack{}, tm, frs, LhNo{})
    case 1n+p MdNx{+o, v, n, s}:
      wnf.go(p, w, cm.off(), MdN1{o, v, n, s, wnf.go(p, w, cm, MdMain{}, nx.arg(0n, frs), Nil{}, LhNo{})}, tm, frs, lhs)
    case 1n+p MdN1{+o, v, n, +s, r}:
      match r:
        case Cx{+h, cm2}:
          wnf.go(p, w, cm2, MdNs{nx.one(o, nl.of(h), s), o, v, n, s}, tm, nx.set(0n, h, frs), lhs)
    case 1n+p MdN2{+o, v, n, +s, +x, r}:
      match r:
        case Cx{+h, cm2}:
          wnf.go(p, w, cm2, MdNs{nx.two(o, x, nl.of(h), s), o, v, n, s}, tm, nx.set(1n, h, frs), lhs)
    case 1n+p MdNs{ns, +o, v, +n, +s}:
      match ns:
        case NsDone{h}:
          wnf.go(p, w, cm, MdBack{}, h, frs.drop(U32.to_nat(n), frs), LhNo{})
        case NsMore{+x}:
          wnf.go(p, w, cm.off(), MdN2{o, v, n, s, x, wnf.go(p, w, cm, MdMain{}, nx.arg(1n, frs), Nil{}, LhNo{})}, tm, frs, lhs)
        case NsNo{}:
          wnf.go(p, w, cm, MdRun{True{}, v, n}, tm, frs, lhs)
        case NsStuck{}:
          wnf.go(p, w, cm, MdBack{}, tm, frs, LhNo{})
    case 1n+p MdRun{ok, v, n}:
      match ok:
        case True{}:
          wnf.go(p, w, cm, MdMain{}, v, frs, LhYes{LtRef{tm}, n})
        case False{}:
          wnf.go(p, w, cm, MdBack{}, tm, frs, LhNo{})
    case 1n+p MdBack{}:
      match frs:
        case Nil{}:
          Cx{tm, cm}
        case Con{FApp{x, s}, r}:
          wnf.go(p, w, cm, MdBack{}, ap(tm, x, s), r, LhNo{})
        case Con{FMna{b, s}, r}:
          +t = tm
          wnf.go(p, w, cm, MdMna{mna.kind(t), b, s}, t, r, LhNo{})
        case Con{FMnb{a, s}, r}:
          wnf.go(p, w, cm, MdBack{}, min.back(tm, a, s), r, LhNo{})
        case Con{FMat{t, e, fl, s}, r}:
          wnf.go(p, w, cm, MdMat{t, e, fl, s}, lit_step(tm), r, LhNo{})
        case Con{FVar{n, a}, r}:
          wnf.go(p, w, cm.off(), MdFill{cell.fill(cm, n, a, tm)}, H.HQnt{C.NoSp{}}, r, LhNo{})
        case Con{FRwt{t, fl}, r}:
          wnf.go(p, w, cm, MdRwt{t, fl}, tm, r, LhNo{})
    case 1n+p MdRwt{t, fl}:
      match t tm:
        case H.HRwt{e, m, f, s} H.HRfl{u}:
          wnf.go(p, w, cm, MdMain{}, f, frs, fl)
        case t _:
          wnf.go(p, w, cm, MdBack{}, t, frs, LhNo{})
    case 1n+p MdMna{mv, b, s}:
      match mv:
        case MvMany{}:
          wnf.go(p, w, cm, MdMain{}, b, frs, LhNo{})
        case MvNone{}:
          wnf.go(p, w, cm, MdBack{}, tm, frs, LhNo{})
        case MvOther{}:
          wnf.go(p, w, cm, MdMain{}, b, FMnb{tm, s} <> frs, LhNo{})
    case 1n+p MdMat{+t, e, fl, s}:
      match tm:
        case H.HCtr{+k, xs, cs}:
          wnf.go(p, w, cm, MdArm{arm.find(t, k), t, e, fl, s}, H.HCtr{k, xs, cs}, frs, LhNo{})
        case tm:
          wnf.go(p, w, cm, MdBack{}, ap(lh.t(fl, t), e, s), frs, LhNo{})
    case 1n+p MdArm{arm, t, e, fl, s}:
      match arm tm:
        case ArmHit{h} H.HCtr{+k, +xs, cs}:
          wnf.go(p, w, cm.off(), MdHit{cells(cm, xs)}, h, frs, lh.ext(fl, k, U32.from_nat(List.length(&2, H.H, xs))))
        case ArmDef{d} tm:
          wnf.go(p, w, cm, MdMain{}, d, FApp{tm, C.NoSp{}} <> frs, fl)
        case _ tm:
          wnf.go(p, w, cm, MdBack{}, ap(lh.t(fl, t), e, s), frs, LhNo{})

# term_wnf: weak head normal form (no cells: the checker's own calls)
def wnf(+w: W, tm: H.H) -> H.H:
  cx.h(wnf.go(FUEL(), w, cm.off(), MdMain{}, tm, Nil{}, LhNo{}))

# term_wnf inside a comparison: its store's cells shared
def wnf.c(+w: W, cm: Cm, tm: H.H) -> Cx:
  wnf.go(FUEL(), w, cm, MdMain{}, tm, Nil{}, LhNo{})

# Opening any binder (a check-mat goal reads its fields' types in the book)
# -------------------------------------------------------------------------

type Aj is Data:
  AjCl{cl: H.Cl, x: H.H}
  AjGoal{z: Bool, cur: H.H, n: U32, xs: List<&2, H.H>, tq: C.Q, tb: H.Cl, k: String, s: C.Sp}
  AjAll{c: H.H, n: U32, xs: List<&2, H.H>, tq: C.Q, tb: H.Cl, k: String, s: C.Sp}

# a case's field quantity, its scrutinee's tq: - stays -, a plain field
# takes the scrutinee's, a + one its double
def c.dem(cq: C.Q, +tq: C.Q) -> C.Q:
  match cq:
    case C.QN{}:
      C.QN{}
    case C.QL{}:
      tq
    case C.QM{}:
      C.q.add(tq, tq)

def ap.go(+fuel: Nat, +real: Map<&2, Td>, j: Aj) -> H.H:
  match fuel j:
    case 0n _:
      H.HHol{"bendbis: a binder ran out of fuel", C.NoSp{}}
    case 1n+p AjCl{cl, x}:
      match cl:
        case H.ClMat{tq, tb, cb, +n, xs, k, s}:
          +y = x
          ap.go(p, real, AjGoal{U32.is_eq(n, 0), ap.go(p, real, AjCl{cb, y}), n, y <> xs, tq, tb, k, s})
        case cl:
          ap0(cl, x)
    case 1n+p AjGoal{z, cur, n, xs, tq, tb, k, s}:
      match z:
        case True{}:
          ap.go(p, real, AjCl{tb, H.HCtr{k, List.reverse(&2, H.H, xs), s}})
        case False{}:
          ap.go(p, real, AjAll{wnf(W{real, real}, cur), n, xs, tq, tb, k, s})
    case 1n+p AjAll{c, n, xs, +tq, tb, k, +s}:
      match c:
        case H.HAll{cq, ck, ci, cA, ccl, cs}:
          H.HAll{c.dem(cq, tq), ck, ci, cA, H.ClMat{tq, tb, ccl, (n - 1 : U32), xs, k, s}, s}
        case _:
          H.HHol{"bendbis: unreachable (a telescope binds its parameters and fields)", s}

# B(x), for any closure
def apc(+real: Map<&2, Td>, cl: H.Cl, x: H.H) -> H.H:
  ap.go(FUEL(), real, AjCl{cl, x})

# term_lower(term_snf(t), d): what expr_show prints
# -------------------------------------------------

# term_snf shares as term_compare does: one store of cells for the whole
# normal form, so a value demanded twice (a + parameter, a let read in two
# places) is reduced once, as bend.ts's cells reduce it. Without it a
# normal form of shared arithmetic (an F64 law's failing side, F64.bend's
# + parameters) is reduced once per path to each use: exponential. The
# store is dropped when the normal form is done (snfl), so no cell reaches
# the checker's terms. A node with children is a frame (Sk) that its next
# child's normal form, with the store as that child left it, returns to.

type Sv is Type:
  SvT{t: C.Tm, cm: Cm}
  SvL{ts: List<&2, C.Tm>, cm: Cm}

type Sk is Data:
  KTyp{s: C.Sp}
  KMin1{b: H.H, s: C.Sp, d: U32}
  KMin2{x: C.Tm, s: C.Sp}
  KAll1{q: C.Q, k: String, cl: H.Cl, s: C.Sp, d: U32}
  KAll2{q: C.Q, k: String, d: U32, x: C.Tm, s: C.Sp}
  KLam{k: String, d: U32, s: C.Sp}
  KAppR{k: String, u: C.Sp, b: Bool, s: C.Sp}
  KApp1{x: H.H, s: C.Sp, d: U32}
  KApp2{y: C.Tm, s: C.Sp}
  KAdt{k: String, r: List<&2, String>, s: C.Sp}
  KCtr{k: String, s: C.Sp}
  KMat1{k: String, m: H.H, s: C.Sp, d: U32}
  KMat2{k: String, x: C.Tm, s: C.Sp}
  KEql1{b: H.H, A: H.H, s: C.Sp, d: U32}
  KEql2{x: C.Tm, A: H.H, s: C.Sp, d: U32}
  KEql3{x: C.Tm, y: C.Tm, s: C.Sp}
  KRwt1{m: H.H, f: H.H, s: C.Sp, d: U32}
  KRwt2{x: C.Tm, f: H.H, s: C.Sp, d: U32}
  KRwt3{x: C.Tm, y: C.Tm, s: C.Sp}
  KL1{t: List<&2, H.H>, d: U32}
  KL2{x: C.Tm}

type Sj is Type:
  SjT{h: H.H, d: U32}
  SjX{x: Cx, d: U32}
  SjW{t: H.H, d: U32}
  SjL{hs: List<&2, H.H>, d: U32}
  SjK{k: Sk, r: Sv}

def sv.t(v: Sv) -> C.Tm:
  match v:
    case SvT{t, cm}:
      t
    case _:
      C.THol{"bendbis", C.NoSp{}}

def snf.go(+fuel: Nat, +w: W, cm: Cm, j: Sj) -> Sv:
  match fuel j:
    case 0n _:
      SvT{C.THol{"bendbis: term_snf ran out of fuel", C.NoSp{}}, cm.off()}
    case 1n+p SjT{h, d}:
      snf.go(p, w, cm.off(), SjX{wnf.c(w, cm, h), d})
    case 1n+p SjX{x, d}:
      match x:
        case Cx{t, c2}:
          snf.go(p, w, c2, SjW{t, d})
    case 1n+p SjL{hs, +d}:
      match hs:
        case Nil{}:
          SvL{Nil{}, cm}
        case Con{h, t}:
          snf.go(p, w, cm.off(), SjK{KL1{t, d}, snf.go(p, w, cm, SjT{h, d})})
    case 1n+p SjK{k, r}:
      match k r:
        case KL1{t, d} SvT{x, c2}:
          snf.go(p, w, cm.off(), SjK{KL2{x}, snf.go(p, w, c2, SjL{t, d})})
        case KL2{x} SvL{ts, c2}:
          SvL{x <> ts, c2}
        case KTyp{s} SvT{x, c2}:
          SvT{C.TTyp{x, s}, c2}
        case KMin1{b, s, d} SvT{x, c2}:
          snf.go(p, w, cm.off(), SjK{KMin2{x, s}, snf.go(p, w, c2, SjT{b, d})})
        case KMin2{x, s} SvT{y, c2}:
          SvT{C.TMin{x, y, s}, c2}
        case KAll1{q, +k, cl, s, +d} SvT{x, c2}:
          snf.go(p, w, cm.off(), SjK{KAll2{q, k, d, x, s}, snf.go(p, w, c2, SjT{apc(w.real(w), cl, H.HVar{k, d, C.NoSp{}}), (d + 1 : U32)})})
        case KAll2{q, k, d, x, s} SvT{y, c2}:
          SvT{C.TAll{q, k, d, x, y, s}, c2}
        case KLam{k, d, s} SvT{y, c2}:
          SvT{C.TLam{k, d, y, s, C.QL{}}, c2}
        case KAppR{k, u, b, s} SvT{x, c2}:
          SvT{C.TApp{C.TRef{k, u, b}, x, s}, c2}
        case KApp1{x, s, d} SvT{y, c2}:
          snf.go(p, w, cm.off(), SjK{KApp2{y, s}, snf.go(p, w, c2, SjT{x, d})})
        case KApp2{y, s} SvT{x, c2}:
          SvT{C.TApp{y, x, s}, c2}
        case KAdt{k, rs, s} SvL{ts, c2}:
          SvT{C.TAdt{k, ts, rs, s}, c2}
        case KCtr{k, s} SvL{ts, c2}:
          SvT{C.TCtr{k, ts, s}, c2}
        case KMat1{k, m, s, d} SvT{x, c2}:
          snf.go(p, w, cm.off(), SjK{KMat2{k, x, s}, snf.go(p, w, c2, SjT{m, d})})
        case KMat2{k, x, s} SvT{y, c2}:
          SvT{C.TMat{k, x, y, s}, c2}
        case KEql1{b, A, s, +d} SvT{x, c2}:
          snf.go(p, w, cm.off(), SjK{KEql2{x, A, s, d}, snf.go(p, w, c2, SjT{b, d})})
        case KEql2{x, A, s, d} SvT{y, c2}:
          snf.go(p, w, cm.off(), SjK{KEql3{x, y, s}, snf.go(p, w, c2, SjT{A, d})})
        case KEql3{x, y, s} SvT{z, c2}:
          SvT{C.TEql{x, y, z, s}, c2}
        case KRwt1{m, f, s, +d} SvT{x, c2}:
          snf.go(p, w, cm.off(), SjK{KRwt2{x, f, s, d}, snf.go(p, w, c2, SjT{m, d})})
        case KRwt2{x, f, s, d} SvT{y, c2}:
          snf.go(p, w, cm.off(), SjK{KRwt3{x, y, s}, snf.go(p, w, c2, SjT{f, d})})
        case KRwt3{x, y, s} SvT{z, c2}:
          SvT{C.TRwt{x, y, z, s}, c2}
        case _ SvT{x, c2}:
          SvT{C.THol{"bendbis: unreachable (an snf frame and its child)", C.NoSp{}}, c2}
        case _ SvL{ts, c2}:
          SvT{C.THol{"bendbis: unreachable (an snf frame and its child)", C.NoSp{}}, c2}
    case 1n+p SjW{t, +d}:
      match t:
        case H.HTyp{g, s}:
          snf.go(p, w, cm.off(), SjK{KTyp{s}, snf.go(p, w, cm, SjT{g, d})})
        case H.HMin{a, b, s}:
          snf.go(p, w, cm.off(), SjK{KMin1{b, s, d}, snf.go(p, w, cm, SjT{a, d})})
        case H.HAll{q, k, i, A, cl, s}:
          snf.go(p, w, cm.off(), SjK{KAll1{q, k, cl, s, d}, snf.go(p, w, cm, SjT{A, d})})
        case H.HLam{+k, i, cl, s, q}:
          snf.go(p, w, cm.off(), SjK{KLam{k, d, s}, snf.go(p, w, cm, SjT{apc(w.real(w), cl, H.HVar{k, d, C.NoSp{}}), (d + 1 : U32)})})
        case H.HApp{f, x, s}:
          match f:
            case H.HRef{k, u, b}:
              snf.go(p, w, cm.off(), SjK{KAppR{k, u, b, s}, snf.go(p, w, cm, SjT{x, d})})
            case f:
              snf.go(p, w, cm.off(), SjK{KApp1{x, s, d}, snf.go(p, w, cm, SjT{f, d})})
        case H.HAdt{k, xs, r, s}:
          snf.go(p, w, cm.off(), SjK{KAdt{k, r, s}, snf.go(p, w, cm, SjL{xs, d})})
        case H.HCtr{k, xs, s}:
          snf.go(p, w, cm.off(), SjK{KCtr{k, s}, snf.go(p, w, cm, SjL{xs, d})})
        case H.HMat{k, h, m, s}:
          snf.go(p, w, cm.off(), SjK{KMat1{k, m, s, d}, snf.go(p, w, cm, SjT{h, d})})
        case H.HEql{a, b, A, s}:
          snf.go(p, w, cm.off(), SjK{KEql1{b, A, s, d}, snf.go(p, w, cm, SjT{a, d})})
        case H.HRwt{e, m, f, s}:
          snf.go(p, w, cm.off(), SjK{KRwt1{m, f, s, d}, snf.go(p, w, cm, SjT{e, d})})
        case H.HVar{k, i, s}:
          SvT{C.TVar{k, i, s}, cm}
        case H.HRef{k, s, b}:
          SvT{C.TRef{k, s, b}, cm}
        case H.HQnt{s}:
          SvT{C.TQnt{s}, cm}
        case H.HQua{q, s}:
          SvT{C.TQua{q, s}, cm}
        case H.HNat{v, s}:
          SvT{C.TNat{v, s}, cm}
        case H.HU32{v, s}:
          SvT{C.TU32{v, s}, cm}
        case H.HF32{v, s}:
          SvT{C.TF32{v, s}, cm}
        case H.HStr{v, s}:
          SvT{C.TStr{v, s}, cm}
        case H.HEfq{s}:
          SvT{C.TEfq{s}, cm}
        case H.HRfl{s}:
          SvT{C.TRfl{s}, cm}
        case H.HHol{k, s}:
          SvT{C.THol{k, s}, cm}
        case _:
          SvT{C.THol{"bendbis: snf met an unreduced node", C.NoSp{}}, cm}

def snfl(+w: W, h: H.H, d: U32) -> C.Tm:
  sv.t(snf.go(FUEL(), w, cm.new(), SjT{h, d}))

# term_compare
# ------------

# a comparison to make: two terms (eq: mode EQ, else LE) at depth d, or two
# closures opened on Var(k, d) at d + 1
type Cp is Data:
  CpT{eq: Bool, a: H.H, b: H.H, d: U32}
  CpB{eq: Bool, a: H.Cl, b: H.Cl, k: String, d: U32}
  CpW{eq: Bool, a: H.H, b: H.H, d: U32}
  CpLink{a: U32, b: U32}

# what one comparison asks next: nothing (true or false), all of ps, or
# either list (bend.ts's ||)
type Cs is Data:
  CsTrue{}
  CsFalse{}
  CsAll{ps: List<&2, Cp>}
  CsOr{a: List<&2, Cp>, b: List<&2, Cp>}

def cs.if(z: Bool, c: Cs) -> Cs:
  match z:
    case True{}:
      c
    case False{}:
      CsFalse{}

def cs.bool(z: Bool) -> Cs:
  match z:
    case True{}:
      CsTrue{}
    case False{}:
      CsFalse{}

def q.eq(a: C.Q, b: C.Q) -> Bool:
  match a b:
    case C.QN{} C.QN{}:
      True{}
    case C.QL{} C.QL{}:
      True{}
    case C.QM{} C.QM{}:
      True{}
    case _ _:
      False{}

# (the walks stop at the first answer: Bool.or/and would read the rest)
def strs.has.go(xs: List<&2, String>, hit: Bool, +k: String) -> Bool:
  match xs hit:
    case _ True{}:
      True{}
    case Nil{} False{}:
      False{}
    case Con{x, t} False{}:
      strs.has.go(t, String.eq(x, k), k)

def strs.has(xs: List<&2, String>, +k: String) -> Bool:
  strs.has.go(xs, False{}, k)

def strs.sub.go(xs: List<&2, String>, ok: Bool, +ys: List<&2, String>) -> Bool:
  match xs ok:
    case _ False{}:
      False{}
    case Nil{} True{}:
      True{}
    case Con{x, t} True{}:
      strs.sub.go(t, strs.has(ys, x), ys)

def strs.sub(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  strs.sub.go(xs, True{}, ys)

def u32s.eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{+a, s} Con{+b, t}:
      Bool.and(U32.is_eq(a, b), u32s.eq(s, t))
    case _ _:
      False{}

# EQ pairs of two lists of the same length
def cp.pairs(xs: List<&2, H.H>, ys: List<&2, H.H>, +d: U32) -> List<&2, Cp>:
  match xs ys:
    case Con{x, s} Con{y, t}:
      CpT{True{}, x, y, d} <> cp.pairs(s, t, d)
    case _ _:
      Nil{}

def hs.len(xs: List<&2, H.H>) -> U32:
  U32.from_nat(List.length(&2, H.H, xs))

# cs.if(z, CsAll{cp.pairs(xs, ys, d)}), the pairs built only when z
def cs.pairs.if(z: Bool, xs: List<&2, H.H>, ys: List<&2, H.H>, +d: U32) -> Cs:
  match z:
    case True{}:
      CsAll{cp.pairs(xs, ys, d)}
    case False{}:
      CsFalse{}

# f applied to n fresh variables from depth d on
def apps(n: Nat, f: H.H, +d: U32) -> H.H:
  match n:
    case 0n:
      f
    case 1n+m:
      apps(m, H.HApp{f, H.HVar{"_", d, C.NoSp{}}, C.NoSp{}}, (d + 1 : U32))

def td.n(t: Td) -> U32:
  match t:
    case TdAdt{n, g, T, c, b}:
      n
    case TdDef{n, x, T, v, b, u, ffi, l, rs}:
      n
    case TdNo{}:
      0

def is.many(t: H.H) -> Bool:
  match t:
    case H.HQua{C.QM{}, s}:
      True{}
    case _:
      False{}

def is.qua.notmany(t: H.H) -> Bool:
  match t:
    case H.HQua{C.QM{}, s}:
      False{}
    case H.HQua{q, s}:
      True{}
    case _:
      False{}

# the LE comparison of two kinds, their quantities' whnfs g and h
def typ.le.min(g: H.H, h: H.H, +a: H.H, +b: H.H, +d: U32) -> Cs:
  match g h:
    case H.HMin{ga, gb, s} h:
      CsAll{[CpT{False{}, H.HTyp{ga, C.NoSp{}}, b, d}, CpT{False{}, H.HTyp{gb, C.NoSp{}}, b, d}]}
    case g H.HMin{ha, hb, s}:
      CsOr{[CpT{False{}, a, H.HTyp{ha, C.NoSp{}}, d}], [CpT{False{}, a, H.HTyp{hb, C.NoSp{}}, d}]}
    case g h:
      CsAll{[CpT{False{}, g, h, d}]}

def typ.le.go(z: Bool, g: H.H, h: H.H, a: H.H, b: H.H, d: U32) -> Cs:
  match z:
    case True{}:
      CsTrue{}
    case False{}:
      typ.le.min(g, h, a, b, d)

def typ.le(+g: H.H, +h: H.H, a: H.H, b: H.H, d: U32) -> Cs:
  typ.le.go(Bool.or(is.many(g), is.qua.notmany(h)), g, h, a, b, d)

def cmp.ref.n(+eq: Bool, a: H.H, b: H.H, +d: U32, +n: U32) -> Cs:
  cs.if(U32.is_gt(n, 0), CsAll{[CpT{eq, apps(U32.to_nat(n), a, d), apps(U32.to_nat(n), b, d), (d + n : U32)}]})

def cmp.typ(eq: Bool, +w: W, +g: H.H, +h: H.H, s1: C.Sp, s2: C.Sp, +d: U32) -> Cs:
  match eq:
    case True{}:
      CsAll{[CpT{True{}, g, h, d}]}
    case False{}:
      typ.le(wnf(w, g), wnf(w, h), H.HTyp{g, s1}, H.HTyp{h, s2}, d)

# a stuck call compares its head by name
def cmp.app(f1: H.H, f2: H.H, x1: H.H, x2: H.H, +d: U32) -> Cs:
  match f1 f2:
    case H.HRef{k1, u1, b1} H.HRef{k2, u2, b2}:
      cs.if(String.eq(k1, k2), CsAll{[CpT{True{}, x1, x2, d}]})
    case f1 f2:
      CsAll{[CpT{True{}, f1, f2, d}, CpT{True{}, x1, x2, d}]}

# two refs: one name, or a def each, compared on n fresh arguments
def cmp.ref(z: Bool, +eq: Bool, +w: W, a: H.H, b: H.H, +d: U32) -> Cs:
  match z a b:
    case True{} a b:
      CsTrue{}
    case False{} H.HRef{+k1, s1, b1} H.HRef{+k2, s2, b2}:
      cmp.ref.n(eq, H.HRef{k1, s1, b1}, H.HRef{k2, s2, b2}, d, U32.max(td.n(td.get(w.bk(w), k1)), td.n(td.get(w.bk(w), k2))))
    case _ a b:
      CsFalse{}

# compare_go's cases, after the whnfs (and the lambdas and literals)
def cmp.cases(+eq: Bool, +w: W, a: H.H, b: H.H, +d: U32) -> Cs:
  match a b:
    case H.HVar{k1, +i, s1} H.HVar{k2, +j, s2}:
      cs.bool(U32.is_eq(i, j))
    case H.HRef{+k1, s1, b1} H.HRef{+k2, s2, b2}:
      cmp.ref(String.eq(k1, k2), eq, w, H.HRef{k1, s1, b1}, H.HRef{k2, s2, b2}, d)
    case H.HTyp{g, s1} H.HTyp{h, s2}:
      cmp.typ(eq, w, g, h, s1, s2, d)
    case H.HQnt{s1} H.HQnt{s2}:
      CsTrue{}
    case H.HEfq{s1} H.HEfq{s2}:
      CsTrue{}
    case H.HRfl{s1} H.HRfl{s2}:
      CsTrue{}
    case H.HQua{q1, s1} H.HQua{q2, s2}:
      cs.bool(q.eq(q1, q2))
    case H.HMin{a1, b1, s1} H.HMin{a2, b2, s2}:
      CsAll{[CpT{True{}, a1, a2, d}, CpT{True{}, b1, b2, d}]}
    case H.HAll{q1, k1, i1, A1, c1, s1} H.HAll{q2, k2, i2, A2, c2, s2}:
      cs.if(q.eq(q1, q2), CsAll{[CpT{eq, A2, A1, d}, CpB{eq, c1, c2, k1, d}]})
    case H.HApp{f1, x1, s1} H.HApp{f2, x2, s2}:
      cmp.app(f1, f2, x1, x2, d)
    case H.HAdt{+k1, +xs1, +r1, s1} H.HAdt{+k2, +xs2, +r2, s2}:
      +ln = Bool.and(String.eq(k1, k2), U32.is_eq(hs.len(xs1), hs.len(xs2)))
      +rn = Bool.not(Bool.and(eq, Bool.not(Nat.is_eq(List.length(&2, String, r1), List.length(&2, String, r2)))))
      cs.pairs.if(Bool.and(Bool.and(ln, rn), strs.sub(r2, r1)), xs1, xs2, d)
    case H.HCtr{+k1, +xs1, s1} H.HCtr{+k2, +xs2, s2}:
      cs.pairs.if(Bool.and(String.eq(k1, k2), U32.is_eq(hs.len(xs1), hs.len(xs2))), xs1, xs2, d)
    case H.HNat{+v1, s1} H.HNat{+v2, s2}:
      cs.bool(U32.is_eq(v1, v2))
    case H.HU32{+v1, s1} H.HU32{+v2, s2}:
      cs.bool(U32.is_eq(v1, v2))
    case H.HF32{+v1, s1} H.HF32{+v2, s2}:
      cs.bool(U32.is_eq(v1, v2))
    case H.HStr{v1, s1} H.HStr{v2, s2}:
      cs.bool(u32s.eq(v1, v2))
    case H.HMat{+k1, h1, m1, s1} H.HMat{+k2, h2, m2, s2}:
      cs.if(String.eq(k1, k2), CsAll{[CpT{True{}, h1, h2, d}, CpT{True{}, m1, m2, d}]})
    case H.HEql{a1, b1, A1, s1} H.HEql{a2, b2, A2, s2}:
      CsAll{[CpT{True{}, a1, a2, d}, CpT{True{}, b1, b2, d}, CpT{True{}, A1, A2, d}]}
    case H.HHol{+k1, s1} H.HHol{+k2, s2}:
      cs.bool(String.eq(k1, k2))
    case H.HRwt{e1, p1, f1, s1} H.HRwt{e2, p2, f2, s2}:
      CsAll{[CpT{True{}, e1, e2, d}, CpT{True{}, p1, p2, d}, CpT{True{}, f1, f2, d}]}
    case _ _:
      CsFalse{}

# lit_step(t) when z (a literal met by a constructor), else t
def lit.if(z: Bool, t: H.H) -> H.H:
  match z:
    case True{}:
      lit_step(t)
    case False{}:
      t

def cmp.lam(z: Bool, +eq: Bool, +w: W, +a: H.H, +b: H.H, +d: U32) -> Cs:
  match z:
    case True{}:
      +x : H.H = H.HVar{"_", d, C.NoSp{}}
      CsAll{[CpT{eq, ap(a, x, C.NoSp{}), ap(b, x, C.NoSp{}), (d + 1 : U32)}]}
    case False{}:
      +a2 = lit.if(Bool.and(is.lit(a), is.ctr(b)), a)
      +b2 = lit.if(Bool.and(is.lit(b), is.ctr(a2)), b)
      cmp.cases(eq, w, a2, b2, d)

def cmp.whnf(+eq: Bool, +w: W, +a: H.H, +b: H.H, +d: U32) -> Cs:
  cmp.lam(Bool.or(is.lam(a), is.lam(b)), eq, w, a, b, d)

# two refs of one name are one object once unfolded (bend.ts's a === b
# after the whnfs): equal, as the walk finds them whenever it ends
def same.ref(a: H.H, b: H.H) -> Bool:
  match a b:
    case H.HRef{k1, s1, b1} H.HRef{k2, s2, b2}:
      String.eq(k1, k2)
    case _ _:
      False{}

# a comparison's next ask, and the store after it
type Cq is Type:
  Cq{cs: Cs, cm: Cm}

def cell.n(h: H.H) -> U32:
  match h:
    case H.HVal{k, i, s, v}:
      (i - CELL() : U32)
    case _:
      0

def cs.is.true(c: Cs) -> Bool:
  match c:
    case CsTrue{}:
      True{}
    case _:
      False{}

# compare_go after the whnfs: two cells compared EQ are linked into one
# class once their values compare equal (the CpLink after their pair)
def cmp.link(z: Bool, +eq: Bool, +w: W, cm: Cm, l: H.H, r: H.H, +a: H.H, +b: H.H, +d: U32) -> Cq:
  match z:
    case True{}:
      Cq{CsAll{[CpW{eq, a, b, d}, CpLink{cell.n(l), cell.n(r)}]}, cm}
    case False{}:
      Cq{cmp.whnf(eq, w, a, b, d), cm}

def cmp.cells.b(rb: Cx, +eq: Bool, +w: W, +l: H.H, +r: H.H, +a: H.H, +d: U32) -> Cq:
  match rb:
    case Cx{b, c3}:
      cmp.link(Bool.and(eq, Bool.and(h.is.cell(l), h.is.cell(r))), eq, w, c3, l, r, a, b, d)

def cmp.cells.a(ra: Cx, +eq: Bool, +w: W, +l: H.H, +r: H.H, +d: U32) -> Cq:
  match ra:
    case Cx{a, c2}:
      cmp.cells.b(wnf.c(w, c2, r), eq, w, l, r, a, d)

# both whnfs, each filling its cell (unless z: equal already)
def cmp.cells(z: Bool, +eq: Bool, +w: W, cm: Cm, +l: H.H, +r: H.H, +d: U32) -> Cq:
  match z:
    case True{}:
      Cq{CsTrue{}, cm}
    case False{}:
      cmp.cells.a(wnf.c(w, cm, l), eq, w, l, r, d)

# compare_go's start: one cell, or two of one class (found equal before);
# the roots are looked up only for two cells
def cells.same.c(rb: Ca & U32, +a: U32) -> Ca & Bool:
  (t, +b) = rb
  (t, U32.is_eq(a, b))

def cells.same.b(ra: Ca & U32, +r: H.H) -> Ca & Bool:
  (t, +a) = ra
  cells.same.c(cm.root(t, cell.n(r)), a)

def cells.same.at(z: Bool, t: Ca, +l: H.H, +r: H.H) -> Ca & Bool:
  match z:
    case True{}:
      cells.same.b(cm.root(t, cell.n(l)), r)
    case False{}:
      (t, False{})

def cells.same.d(r: Ca & Bool, +on: Bool, +n: U32) -> Cq:
  (t, z) = r
  Cq{cs.bool(z), Cm{on, n, t}}

def cells.same(cm: Cm, +l: H.H, +r: H.H) -> Cq:
  match cm:
    case Cm{+on, +n, t}:
      cells.same.d(cells.same.at(Bool.and(h.is.cell(l), h.is.cell(r)), t, l, r), on, n)

def cmp.pre.at(sm: Cq, +eq: Bool, +w: W, +l: H.H, +r: H.H, +d: U32) -> Cq:
  match sm:
    case Cq{c, c2}:
      cmp.cells(Bool.or(same.ref(l, r), cs.is.true(c)), eq, w, c2, l, r, d)

def cmp.pre(+eq: Bool, +w: W, cm: Cm, +l: H.H, +r: H.H, +d: U32) -> Cq:
  cmp.pre.at(cells.same(cm, l, r), eq, w, l, r, d)

# bend.ts's r.c = l: the second class under the first
def cm.link.e(e: Ce, t: Ca, +rb: U32, +ra: U32) -> Ca:
  match e:
    case CeV{v, c}:
      ca.set(t, rb, CeV{v, ra})
    case CeNo{}:
      t

def cm.link.d(r: Ca & Ce, +on: Bool, +n: U32, +rb: U32, +ra: U32) -> Cm:
  (t, e) = r
  Cm{on, n, cm.link.e(e, t, rb, ra)}

def cm.link.at(z: Bool, cm: Cm, +ra: U32, +rb: U32) -> Cm:
  match z cm:
    case True{} cm:
      cm
    case False{} Cm{+on, +n, t}:
      cm.link.d(ca.get(t, rb), on, n, rb, ra)

def cm.link.c(rb: Ca & U32, +ra: U32, +on: Bool, +n: U32) -> Cm:
  (t, +b) = rb
  cm.link.at(U32.is_eq(ra, b), Cm{on, n, t}, ra, b)

def cm.link.b(ra: Ca & U32, +b: U32, +on: Bool, +n: U32) -> Cm:
  (t, +a) = ra
  cm.link.c(cm.root(t, b), a, on, n)

def cm.link(cm: Cm, +a: U32, +b: U32) -> Cm:
  match cm:
    case Cm{+on, +n, t}:
      cm.link.b(cm.root(t, a), b, on, n)

def cmp.step(+w: W, cm: Cm, c: Cp) -> Cq:
  match c:
    case CpT{eq, l, r, d}:
      cmp.pre(eq, w, cm, l, r, d)
    case CpW{eq, a, b, d}:
      Cq{cmp.whnf(eq, w, a, b, d), cm}
    case CpLink{a, b}:
      Cq{CsTrue{}, cm.link(cm, a, b)}
    case CpB{eq, a, b, +k, +d}:
      +x : H.H = H.HVar{k, d, C.NoSp{}}
      Cq{CsAll{[CpT{eq, apc(w.real(w), a, x), apc(w.real(w), b, x), (d + 1 : U32)}]}, cm}

# an answer, and the store after it
type Cb is Type:
  Cb{z: Bool, cm: Cm}

def cb.z(r: Cb) -> Bool:
  match r:
    case Cb{z, cm}:
      z

def cmp.or2(r: Cb, rest: Cm -> Cb) -> Cb:
  match r:
    case Cb{z, cm}:
      match z:
        case True{}:
          rest(cm)
        case False{}:
          Cb{False{}, cm}

def cmp.or(r: Cb, alt: Cm -> Cb, rest: Cm -> Cb) -> Cb:
  match r:
    case Cb{z, cm}:
      match z:
        case True{}:
          rest(cm)
        case False{}:
          cmp.or2(alt(cm), rest)

type Cst is Type:
  CstNext{}
  CstGot{r: Cq}

def cmp.go(+fuel: Nat, +w: W, cm: Cm, st: Cst, ps: List<&2, Cp>) -> Cb:
  match fuel st:
    case 0n _:
      Cb{False{}, cm}
    case 1n+p CstNext{}:
      match ps:
        case Nil{}:
          Cb{True{}, cm}
        case Con{c, rest}:
          cmp.go(p, w, cm.off(), CstGot{cmp.step(w, cm, c)}, rest)
    case 1n+p CstGot{r}:
      match r:
        case Cq{CsTrue{}, c2}:
          cmp.go(p, w, c2, CstNext{}, ps)
        case Cq{CsFalse{}, c2}:
          Cb{False{}, c2}
        case Cq{CsAll{qs}, c2}:
          cmp.go(p, w, c2, CstNext{}, List.append(&2, Cp, qs, ps))
        case Cq{CsOr{a, b}, c2}:
          +rest = ps
          cmp.or(cmp.go(p, w, c2, CstNext{}, a), y2 => cmp.go(p, w, y2, CstNext{}, b), y3 => cmp.go(p, w, y3, CstNext{}, rest))

def cmp.first(r: Cb, +eq: Bool, +w: W, +a: H.H, +b: H.H, +d: U32) -> Bool:
  match r:
    case Cb{z, cm}:
      match z:
        case True{}:
          True{}
        case False{}:
          cb.z(cmp.go(FUEL(), w, cm, CstNext{}, [CpT{eq, a, b, d}]))

# term_compare(mode, book, a, b, d) in store cm (the one a and b's cells
# are in): first with every def rigid, then as usual (eq: mode EQ, else
# LE). The second pass goes on in the first's store, as bend.ts's cells
# keep what the rigid pass filled (a whnf there, read on from here)
def compare.cm(+eq: Bool, +w: W, cm: Cm, +a: H.H, +b: H.H, +d: U32) -> Bool:
  cmp.first(cmp.go(FUEL(), w.rigid(w.real(w)), cm, CstNext{}, [CpT{eq, a, b, d}]), eq, w, a, b, d)

# term_compare on terms with no cells: a store of its own
def compare(+eq: Bool, +w: W, +a: H.H, +b: H.H, +d: U32) -> Bool:
  compare.cm(eq, w, cm.new(), a, b, d)

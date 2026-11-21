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
  Pair.snd(Map<&2, Td>, Td, Map.get(Td, TdNo{}, m, k))

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

type Fr is Data:
  FApp{x: H.H, s: C.Sp}
  FMat{t: H.H, e: H.H, lhs: Lh, s: C.Sp}
  FMna{b: H.H, s: C.Sp}
  FMnb{a: H.H, s: C.Sp}

# the APP frames on top, up to n
def run.count(n: Nat, frs: List<&2, Fr>, run: Nat) -> Nat:
  match n frs:
    case 0n _:
      run
    case 1n+m Con{FApp{x, s}, t}:
      run.count(m, t, 1n+run)
    case _ _:
      run

def hb.vals(bs: List<&2, H.HB>) -> List<&2, H.H>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{H.HB{k, i, q, v}, t}:
      v <> hb.vals(t)

def lh.step(lhs: Lh, x: H.H, s: C.Sp) -> Lh:
  match lhs:
    case LhNo{}:
      LhNo{}
    case LhYes{t, +n}:
      Bool.pick(Lh, U32.is_eq(n, 0), LhNo{}, LhYes{LtApp{t, x, s}, (n - 1 : U32)})

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
type Md is Data:
  MdMain{}
  MdBack{}
  MdRef{td: Td}
  MdRun{ok: Bool, v: H.H, n: U32}
  MdRwt{ev: H.H}
  MdMna{mv: Mv, b: H.H, s: C.Sp}
  MdMat{t: H.H, e: H.H, fl: Lh, s: C.Sp}
  MdArm{arm: Arm, t: H.H, e: H.H, fl: Lh, s: C.Sp}

def w.bk(w: W) -> Map<&2, Td>:
  match w:
    case W{bk, real}:
      bk

def wnf.go(+fuel: Nat, +w: W, md: Md, tm: H.H, +frs: List<&2, Fr>, lhs: Lh) -> H.H:
  match fuel md:
    case 0n _:
      H.HHol{"bendbis: term_wnf ran out of fuel", C.NoSp{}}
    case 1n+p MdMain{}:
      match tm:
        case H.HVal{k, i, s, v}:
          wnf.go(p, w, MdMain{}, v, frs, LhNo{})
        case H.HAnn{x, A, s}:
          wnf.go(p, w, MdMain{}, x, frs, lhs)
        case H.HMin{a, b, s}:
          wnf.go(p, w, MdMain{}, a, FMna{b, s} <> frs, lhs)
        case H.HLet{bs, cl, s}:
          wnf.go(p, w, MdMain{}, apL(cl, hb.vals(bs)), frs, lhs)
        case H.HApp{f, x, s}:
          wnf.go(p, w, MdMain{}, f, FApp{x, s} <> frs, LhNo{})
        case H.HLam{k, i, cl, s, q}:
          match frs:
            case Con{FApp{+x, u}, r}:
              wnf.go(p, w, MdMain{}, ap0(cl, x), r, lh.step(lhs, x, u))
            case frs:
              wnf.go(p, w, MdBack{}, H.HLam{k, i, cl, s, q}, frs, LhNo{})
        case H.HMat{k, h, m, s}:
          match frs:
            case Con{FApp{+x, u}, r}:
              wnf.go(p, w, MdMain{}, x, FMat{H.HMat{k, h, m, s}, x, lhs, u} <> r, LhNo{})
            case frs:
              wnf.go(p, w, MdBack{}, H.HMat{k, h, m, s}, frs, LhNo{})
        case H.HEfq{s}:
          wnf.go(p, w, MdBack{}, Maybe.default(&2, H.H, efq.lhs(lhs, frs), H.HEfq{s}), frs, LhNo{})
        case H.HRwt{+e, m, f, s}:
          wnf.go(p, w, MdRwt{wnf.go(p, w, MdMain{}, e, Nil{}, LhNo{})}, H.HRwt{e, m, f, s}, frs, lhs)
        case H.HRef{+k, s, b}:
          wnf.go(p, w, MdRef{td.get(w.bk(w), k)}, H.HRef{k, s, b}, frs, lhs)
        case tm:
          wnf.go(p, w, MdBack{}, tm, frs, LhNo{})
    case 1n+p MdRwt{ev}:
      match ev tm:
        case H.HRfl{u} H.HRwt{e, m, f, s}:
          wnf.go(p, w, MdMain{}, f, frs, lhs)
        case _ tm:
          wnf.go(p, w, MdBack{}, tm, frs, LhNo{})
    case 1n+p MdRef{td}:
      match td tm:
        case TdAdt{+n, g, T, c, ab} H.HRef{+k, +s, b}:
          wnf.go(p, w, MdBack{}, Bool.pick(H.H, U32.is_eq(n, 0), H.HAdt{k, Nil{}, Nil{}, s}, H.HRef{k, s, b}), frs, LhNo{})
        case TdDef{+n, x, T, Some{v}, db, u, ffi, l, rs} tm:
          +m = U32.to_nat(n)
          wnf.go(p, w, MdRun{Nat.is_eq(run.count(m, frs, 0n), m), v, n}, tm, frs, lhs)
        case _ tm:
          wnf.go(p, w, MdBack{}, tm, frs, LhNo{})
    case 1n+p MdRun{ok, v, n}:
      match ok:
        case True{}:
          wnf.go(p, w, MdMain{}, v, frs, LhYes{LtRef{tm}, n})
        case False{}:
          wnf.go(p, w, MdBack{}, tm, frs, LhNo{})
    case 1n+p MdBack{}:
      match frs:
        case Nil{}:
          tm
        case Con{FApp{x, s}, r}:
          wnf.go(p, w, MdBack{}, ap(tm, x, s), r, LhNo{})
        case Con{FMna{b, s}, r}:
          +t = tm
          wnf.go(p, w, MdMna{mna.kind(t), b, s}, t, r, LhNo{})
        case Con{FMnb{a, s}, r}:
          wnf.go(p, w, MdBack{}, min.back(tm, a, s), r, LhNo{})
        case Con{FMat{t, e, fl, s}, r}:
          wnf.go(p, w, MdMat{t, e, fl, s}, lit_step(tm), r, LhNo{})
    case 1n+p MdMna{mv, b, s}:
      match mv:
        case MvMany{}:
          wnf.go(p, w, MdMain{}, b, frs, LhNo{})
        case MvNone{}:
          wnf.go(p, w, MdBack{}, tm, frs, LhNo{})
        case MvOther{}:
          wnf.go(p, w, MdMain{}, b, FMnb{tm, s} <> frs, LhNo{})
    case 1n+p MdMat{+t, e, fl, s}:
      match tm:
        case H.HCtr{+k, xs, cs}:
          wnf.go(p, w, MdArm{arm.find(t, k), t, e, fl, s}, H.HCtr{k, xs, cs}, frs, LhNo{})
        case tm:
          wnf.go(p, w, MdBack{}, ap(lh.t(fl, t), e, s), frs, LhNo{})
    case 1n+p MdArm{arm, t, e, fl, s}:
      match arm tm:
        case ArmHit{h} H.HCtr{+k, +xs, cs}:
          wnf.go(p, w, MdMain{}, h, fields.frames(xs, frs), lh.ext(fl, k, U32.from_nat(List.length(&2, H.H, xs))))
        case ArmDef{d} tm:
          wnf.go(p, w, MdMain{}, d, FApp{tm, C.NoSp{}} <> frs, fl)
        case _ tm:
          wnf.go(p, w, MdBack{}, ap(lh.t(fl, t), e, s), frs, LhNo{})

# term_wnf: weak head normal form
def wnf(+w: W, tm: H.H) -> H.H:
  wnf.go(FUEL(), w, MdMain{}, tm, Nil{}, LhNo{})

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

type Sj is Data:
  SjT{h: H.H, d: U32}
  SjW{t: H.H, d: U32}
  SjL{hs: List<&2, H.H>, d: U32}

type Sv is Data:
  SvT{t: C.Tm}
  SvL{ts: List<&2, C.Tm>}

def sv.t(v: Sv) -> C.Tm:
  match v:
    case SvT{t}:
      t
    case _:
      C.THol{"bendbis", C.NoSp{}}

def sv.ts(v: Sv) -> List<&2, C.Tm>:
  match v:
    case SvL{ts}:
      ts
    case _:
      Nil{}

def snf.go(+fuel: Nat, +w: W, j: Sj) -> Sv:
  match fuel j:
    case 0n _:
      SvT{C.THol{"bendbis: term_snf ran out of fuel", C.NoSp{}}}
    case 1n+p SjL{hs, +d}:
      match hs:
        case Nil{}:
          SvL{Nil{}}
        case Con{h, t}:
          +x = sv.t(snf.go(p, w, SjT{h, d}))
          SvL{x <> sv.ts(snf.go(p, w, SjL{t, d}))}
    case 1n+p SjT{h, +d}:
      snf.go(p, w, SjW{wnf(w, h), d})
    case 1n+p SjW{t, +d}:
      match t:
        case H.HTyp{g, s}:
          SvT{C.TTyp{sv.t(snf.go(p, w, SjT{g, d})), s}}
        case H.HMin{a, b, s}:
          +x = sv.t(snf.go(p, w, SjT{a, d}))
          SvT{C.TMin{x, sv.t(snf.go(p, w, SjT{b, d})), s}}
        case H.HAll{q, +k, i, A, cl, s}:
          +x = sv.t(snf.go(p, w, SjT{A, d}))
          SvT{C.TAll{q, k, d, x, sv.t(snf.go(p, w, SjT{apc(w.real(w), cl, H.HVar{k, d, C.NoSp{}}), (d + 1 : U32)})), s}}
        case H.HLam{+k, i, cl, s, q}:
          SvT{C.TLam{k, d, sv.t(snf.go(p, w, SjT{apc(w.real(w), cl, H.HVar{k, d, C.NoSp{}}), (d + 1 : U32)})), s, C.QL{}}}
        case H.HApp{f, x, s}:
          match f:
            case H.HRef{k, u, b}:
              SvT{C.TApp{C.TRef{k, u, b}, sv.t(snf.go(p, w, SjT{x, d})), s}}
            case f:
              +y = sv.t(snf.go(p, w, SjT{f, d}))
              SvT{C.TApp{y, sv.t(snf.go(p, w, SjT{x, d})), s}}
        case H.HAdt{k, xs, r, s}:
          SvT{C.TAdt{k, sv.ts(snf.go(p, w, SjL{xs, d})), r, s}}
        case H.HCtr{k, xs, s}:
          SvT{C.TCtr{k, sv.ts(snf.go(p, w, SjL{xs, d})), s}}
        case H.HMat{k, h, m, s}:
          +x = sv.t(snf.go(p, w, SjT{h, d}))
          SvT{C.TMat{k, x, sv.t(snf.go(p, w, SjT{m, d})), s}}
        case H.HEql{a, b, A, s}:
          +x = sv.t(snf.go(p, w, SjT{a, d}))
          +y = sv.t(snf.go(p, w, SjT{b, d}))
          SvT{C.TEql{x, y, sv.t(snf.go(p, w, SjT{A, d})), s}}
        case H.HRwt{e, m, f, s}:
          +x = sv.t(snf.go(p, w, SjT{e, d}))
          +y = sv.t(snf.go(p, w, SjT{m, d}))
          SvT{C.TRwt{x, y, sv.t(snf.go(p, w, SjT{f, d})), s}}
        case H.HVar{k, i, s}:
          SvT{C.TVar{k, i, s}}
        case H.HRef{k, s, b}:
          SvT{C.TRef{k, s, b}}
        case H.HQnt{s}:
          SvT{C.TQnt{s}}
        case H.HQua{q, s}:
          SvT{C.TQua{q, s}}
        case H.HNat{v, s}:
          SvT{C.TNat{v, s}}
        case H.HU32{v, s}:
          SvT{C.TU32{v, s}}
        case H.HF32{v, s}:
          SvT{C.TF32{v, s}}
        case H.HStr{v, s}:
          SvT{C.TStr{v, s}}
        case H.HEfq{s}:
          SvT{C.TEfq{s}}
        case H.HRfl{s}:
          SvT{C.TRfl{s}}
        case H.HHol{k, s}:
          SvT{C.THol{k, s}}
        case _:
          SvT{C.THol{"bendbis: snf met an unreduced node", C.NoSp{}}}

def snfl(+w: W, h: H.H, d: U32) -> C.Tm:
  sv.t(snf.go(FUEL(), w, SjT{h, d}))

# term_compare
# ------------

# a comparison to make: two terms (eq: mode EQ, else LE) at depth d, or two
# closures opened on Var(k, d) at d + 1
type Cp is Data:
  CpT{eq: Bool, a: H.H, b: H.H, d: U32}
  CpB{eq: Bool, a: H.Cl, b: H.Cl, k: String, d: U32}

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

def strs.has(xs: List<&2, String>, +k: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      Bool.or(String.eq(x, k), strs.has(t, k))

def strs.sub(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(strs.has(ys, x), strs.sub(t, ys))

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
      cs.if(Bool.and(Bool.and(ln, rn), strs.sub(r2, r1)), CsAll{cp.pairs(xs1, xs2, d)})
    case H.HCtr{+k1, +xs1, s1} H.HCtr{+k2, +xs2, s2}:
      cs.if(Bool.and(String.eq(k1, k2), U32.is_eq(hs.len(xs1), hs.len(xs2))), CsAll{cp.pairs(xs1, xs2, d)})
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

def cmp.lam(z: Bool, +eq: Bool, +w: W, +a: H.H, +b: H.H, +d: U32) -> Cs:
  match z:
    case True{}:
      +x : H.H = H.HVar{"_", d, C.NoSp{}}
      CsAll{[CpT{eq, ap(a, x, C.NoSp{}), ap(b, x, C.NoSp{}), (d + 1 : U32)}]}
    case False{}:
      +a2 = Bool.pick(H.H, Bool.and(is.lit(a), is.ctr(b)), lit_step(a), a)
      +b2 = Bool.pick(H.H, Bool.and(is.lit(b), is.ctr(a2)), lit_step(b), b)
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

def cmp.pre(z: Bool, +eq: Bool, +w: W, l: H.H, r: H.H, +d: U32) -> Cs:
  match z:
    case True{}:
      CsTrue{}
    case False{}:
      cmp.whnf(eq, w, wnf(w, l), wnf(w, r), d)

def cmp.step(+w: W, c: Cp) -> Cs:
  match c:
    case CpT{eq, +l, +r, d}:
      cmp.pre(same.ref(l, r), eq, w, l, r, d)
    case CpB{eq, a, b, +k, +d}:
      +x : H.H = H.HVar{k, d, C.NoSp{}}
      CsAll{[CpT{eq, apc(w.real(w), a, x), apc(w.real(w), b, x), (d + 1 : U32)}]}

def cmp.or2(z: Bool, rest: Unit -> Bool) -> Bool:
  match z:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}

def cmp.or(z: Bool, alt: Unit -> Bool, rest: Unit -> Bool) -> Bool:
  match z:
    case True{}:
      rest(Unit{})
    case False{}:
      cmp.or2(alt(Unit{}), rest)

type Cst is Data:
  CstNext{}
  CstGot{cs: Cs}

def cmp.go(+fuel: Nat, +w: W, st: Cst, ps: List<&2, Cp>) -> Bool:
  match fuel st:
    case 0n _:
      False{}
    case 1n+p CstNext{}:
      match ps:
        case Nil{}:
          True{}
        case Con{c, rest}:
          cmp.go(p, w, CstGot{cmp.step(w, c)}, rest)
    case 1n+p CstGot{cs}:
      match cs:
        case CsTrue{}:
          cmp.go(p, w, CstNext{}, ps)
        case CsFalse{}:
          False{}
        case CsAll{qs}:
          cmp.go(p, w, CstNext{}, List.append(&2, Cp, qs, ps))
        case CsOr{a, b}:
          +rest = ps
          cmp.or(cmp.go(p, w, CstNext{}, a), u => cmp.go(p, w, CstNext{}, b), v => cmp.go(p, w, CstNext{}, rest))

def cmp.first(z: Bool, +eq: Bool, +w: W, +a: H.H, +b: H.H, +d: U32) -> Bool:
  match z:
    case True{}:
      True{}
    case False{}:
      cmp.go(FUEL(), w, CstNext{}, [CpT{eq, a, b, d}])

# term_compare(mode, book, a, b, d): first with every def rigid, then as
# usual (eq: mode EQ, else LE)
def compare(+eq: Bool, +w: W, +a: H.H, +b: H.H, +d: U32) -> Bool:
  cmp.first(cmp.go(FUEL(), w.rigid(w.real(w)), CstNext{}, [CpT{eq, a, b, d}]), eq, w, a, b, d)

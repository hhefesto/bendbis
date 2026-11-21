import Base
import ./Text.bend as T
import ./Core.bend as C

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# High: bend.ts's term_higher and term_lower. An HTerm's binder holds a
# closure: bend.ts's JS function is here an environment and the LTerm body
# it reads, so a Lam, an All's codomain and a Let's body wait as they do
# there, and are read where term_lower (or a beta step) opens them. The
# order of the work, and so which unannotated operator is reported first,
# is bend.ts's: term_higher reads every part outside a binder at once,
# term_lower opens the binders left to right.

type H is Data:
  HVar{k: String, i: U32, s: C.Sp}
  HRef{k: String, s: C.Sp, b: Bool}
  HLet{bs: List<&2, HB>, ev: Em, f: C.Tm, s: C.Sp}
  HTyp{g: H, s: C.Sp}
  HQnt{s: C.Sp}
  HQua{q: C.Q, s: C.Sp}
  HMin{a: H, b: H, s: C.Sp}
  HAll{q: C.Q, k: String, i: U32, A: H, ev: Em, B: C.Tm, s: C.Sp}
  HLam{k: String, i: U32, ev: Em, f: C.Tm, s: C.Sp, q: C.Q}
  HApp{f: H, x: H, s: C.Sp}
  HAdt{k: String, x: List<&2, H>, r: List<&2, String>, s: C.Sp}
  HCtr{k: String, x: List<&2, H>, s: C.Sp}
  HNat{v: U32, s: C.Sp}
  HU32{v: U32, s: C.Sp}
  HF32{v: U32, s: C.Sp}
  HStr{v: List<&2, U32>, s: C.Sp}
  HMat{k: String, h: H, m: H, s: C.Sp}
  HEfq{s: C.Sp}
  HEql{a: H, b: H, T: H, s: C.Sp}
  HRfl{s: C.Sp}
  HRwt{e: H, p: H, f: H, s: C.Sp}
  HHol{k: String, s: C.Sp}
  HAnn{x: H, T: H, s: C.Sp}

type HB is Data:
  HB{k: String, i: U32, q: C.Q, v: H}

# an environment entry: nothing, an HTerm, or a Sub's pattern, read in its
# own environment at the occurrence's span
type Ev is Data:
  EvNo{}
  EvH{h: H}
  EvP{p: C.Pat, ev: Em}

# an environment: binder index to entry, a trie as bend.ts's PMap (key 0
# here, an odd key k left as (k-1)/2, an even one right as (k-2)/2). bend.ts
# keeps a list and walks it; a flattened match's Subs make that list as
# long as its patterns are deep, and every node a Sub's pattern expands
# into walks it again (CorpusV2.bend's c2.args: 31 string patterns), so
# the walk is a trie lookup here: the key's binary digits, not the binders
type Em is Data:
  EmTip{}
  EmBin{v: Ev, l: Em, r: Em}

# what one step of the machine answers
type HR is Data:
  HRH{h: H}
  HRHs{hs: List<&2, H>}
  HRT{t: C.Tm}
  HRTs{ts: List<&2, C.Tm>}
  HRE{e: C.Er}

# Spans
# -----

def h.s(h: H) -> C.Sp:
  match h:
    case HVar{k, i, s}:
      s
    case HRef{k, s, b}:
      s
    case HLet{bs, ev, f, s}:
      s
    case HTyp{g, s}:
      s
    case HQnt{s}:
      s
    case HQua{q, s}:
      s
    case HMin{a, b, s}:
      s
    case HAll{q, k, i, A, ev, B, s}:
      s
    case HLam{k, i, ev, f, s, q}:
      s
    case HApp{f, x, s}:
      s
    case HAdt{k, x, r, s}:
      s
    case HCtr{k, x, s}:
      s
    case HNat{v, s}:
      s
    case HU32{v, s}:
      s
    case HF32{v, s}:
      s
    case HStr{v, s}:
      s
    case HMat{k, h, m, s}:
      s
    case HEfq{s}:
      s
    case HEql{a, b, T, s}:
      s
    case HRfl{s}:
      s
    case HRwt{e, p, f, s}:
      s
    case HHol{k, s}:
      s
    case HAnn{x, T, s}:
      s

def h.with_sp(h: H, s: C.Sp) -> H:
  match h:
    case HVar{k, i, u}:
      HVar{k, i, s}
    case HRef{k, u, b}:
      HRef{k, s, b}
    case HLet{bs, ev, f, u}:
      HLet{bs, ev, f, s}
    case HTyp{g, u}:
      HTyp{g, s}
    case HQnt{u}:
      HQnt{s}
    case HQua{q, u}:
      HQua{q, s}
    case HMin{a, b, u}:
      HMin{a, b, s}
    case HAll{q, k, i, A, ev, B, u}:
      HAll{q, k, i, A, ev, B, s}
    case HLam{k, i, ev, f, u, q}:
      HLam{k, i, ev, f, s, q}
    case HApp{f, x, u}:
      HApp{f, x, s}
    case HAdt{k, x, r, u}:
      HAdt{k, x, r, s}
    case HCtr{k, x, u}:
      HCtr{k, x, s}
    case HNat{v, u}:
      HNat{v, s}
    case HU32{v, u}:
      HU32{v, s}
    case HF32{v, u}:
      HF32{v, s}
    case HStr{v, u}:
      HStr{v, s}
    case HMat{k, h, m, u}:
      HMat{k, h, m, s}
    case HEfq{u}:
      HEfq{s}
    case HEql{a, b, T, u}:
      HEql{a, b, T, s}
    case HRfl{u}:
      HRfl{s}
    case HRwt{e, p, f, u}:
      HRwt{e, p, f, s}
    case HHol{k, u}:
      HHol{k, s}
    case HAnn{x, T, u}:
      HAnn{x, T, s}

def h.is_cell(h: H) -> Bool:
  match h:
    case HVar{k, i, s}:
      U32.is_eq(i, C.MINUS())
    case _:
      False{}

# a value found for a variable takes the occurrence's span when it has
# none of its own (and is no share cell)
def h.adopt(+h: H, +s: C.Sp) -> H:
  Bool.pick(H, Bool.or(Bool.or(C.sp.has(h.s(h)), Bool.not(C.sp.has(s))), h.is_cell(h)), h, h.with_sp(h, s))

# Environments
# ------------

# where key k goes at a node: 0n here, 1n left, 2n right
def em.side(+k: U32) -> Nat:
  Bool.pick(Nat, U32.is_eq(k, 0), 0n, Bool.pick(Nat, U32.is_eq((k .&. 1 : U32), 1), 1n, 2n))

# the key below, for side 1n or 2n
def em.down(+k: U32, side: Nat) -> U32:
  match side:
    case 1n:
      (k >> 1n : U32)
    case _:
      ((k >> 1n : U32) - 1 : U32)

# a U32 key has at most 32 binary digits, so 33 steps always reach it
def em.fuel() -> Nat:
  33n

def em.get.go(fuel: Nat, m: Em, side: Nat, +k: U32) -> Ev:
  match fuel m:
    case 0n _:
      EvNo{}
    case _ EmTip{}:
      EvNo{}
    case 1n+f EmBin{v, l, r}:
      match side:
        case 0n:
          v
        case 1n:
          +j = em.down(k, 1n)
          em.get.go(f, l, em.side(j), j)
        case _:
          +j = em.down(k, 2n)
          em.get.go(f, r, em.side(j), j)

def em.get(m: Em, +k: U32) -> Ev:
  em.get.go(em.fuel(), m, em.side(k), k)

def em.set.go(fuel: Nat, m: Em, side: Nat, +k: U32, x: Ev) -> Em:
  match fuel m:
    case 0n m:
      m
    case 1n+f EmTip{}:
      match side:
        case 0n:
          EmBin{x, EmTip{}, EmTip{}}
        case 1n:
          +j = em.down(k, 1n)
          EmBin{EvNo{}, em.set.go(f, EmTip{}, em.side(j), j, x), EmTip{}}
        case _:
          +j = em.down(k, 2n)
          EmBin{EvNo{}, EmTip{}, em.set.go(f, EmTip{}, em.side(j), j, x)}
    case 1n+f EmBin{v, l, r}:
      match side:
        case 0n:
          EmBin{x, l, r}
        case 1n:
          +j = em.down(k, 1n)
          EmBin{v, em.set.go(f, l, em.side(j), j, x), r}
        case _:
          +j = em.down(k, 2n)
          EmBin{v, l, em.set.go(f, r, em.side(j), j, x)}

# m with index k bound to x (list_set: the nearer binding wins)
def em.set(m: Em, +k: U32, x: Ev) -> Em:
  em.set.go(em.fuel(), m, em.side(k), k, x)

type Fd is Data:
  FdNo{}
  FdH{h: H}
  FdP{p: C.Pat, ev: Em}

def ev.fd(e: Ev) -> Fd:
  match e:
    case EvNo{}:
      FdNo{}
    case EvH{h}:
      FdH{h}
    case EvP{p, m}:
      FdP{p, m}

def ev.find(ev: Em, +i: U32) -> Fd:
  ev.fd(em.get(ev, i))

# patt_term(q, s): a pattern as the term it binds
def patt.terms(xs: List<&2, C.Pat>, +s: C.Sp) -> List<&2, C.Tm>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{C.PVar{k, i, qq, u}, t}:
      C.TVar{k, i, C.sp.or(s, u)} <> patt.terms(t, s)
    case Con{C.PCtr{k, ys, u}, t}:
      C.TCtr{k, patt.terms(ys, s), C.sp.or(s, u)} <> patt.terms(t, s)

def tm.first(xs: List<&2, C.Tm>) -> C.Tm:
  match xs:
    case Con{x, t}:
      x
    case Nil{}:
      C.TEfq{C.NoSp{}}

def patt.term(q: C.Pat, s: C.Sp) -> C.Tm:
  tm.first(patt.terms([q], s))

# Operators
# ---------

# a Ref spelled ".op": an operator no ": T" named the type of
def is_op(k: String) -> Bool:
  match k:
    case SCon{Chr{46}, t}:
      Bool.not(C.str.has_dot(t))
    case _:
      False{}

def op.text(txt: List<&2, U32>, k: String, s: C.Sp) -> String:
  match s:
    case C.NoSp{}:
      k
    case C.Sp{f, +b, e}:
      T.str(T.slice(txt, b, e))

def op.err(+txt: List<&2, U32>, k: String, +s: C.Sp) -> C.Er:
  C.Er{"a type for this operator (write (a " ++ op.text(txt, k, s) ++ " b : Nat))", None{}, s, txt,
    Some{"Note: we broke this after launch, sorry. Until 2.0.16 a bare operator meant Nat.\nThat was a bug: operators demand annotation. Wrap the expression and it'll work again."}}

# The machine
# -----------

# a node term_higher rebuilds once its parts are read
type Sh is Data:
  ShTyp{s: C.Sp}
  ShMin{s: C.Sp}
  ShAll{q: C.Q, k: String, i: U32, ev: Em, B: C.Tm, s: C.Sp}
  ShApp{s: C.Sp}
  ShAdt{k: String, r: List<&2, String>, s: C.Sp}
  ShCtr{k: String, s: C.Sp}
  ShMat{k: String, s: C.Sp}
  ShEql{s: C.Sp}
  ShRwt{s: C.Sp}
  ShAnn{s: C.Sp}
  ShLet{ms: List<&2, Bm>, ev: Em, f: C.Tm, s: C.Sp}

# a Let binding's name, index and quantity
type Bm is Data:
  Bm{k: String, i: U32, q: C.Q}

# a node term_lower rebuilds once its parts are lowered
type Lsh is Data:
  LTyp{s: C.Sp}
  LMin{s: C.Sp}
  LAll{q: C.Q, k: String, d: U32, s: C.Sp}
  LLam{k: String, d: U32, s: C.Sp, q: C.Q}
  LApp{s: C.Sp}
  LAdt{k: String, r: List<&2, String>, s: C.Sp}
  LCtr{k: String, s: C.Sp}
  LMat{k: String, s: C.Sp}
  LEql{s: C.Sp}
  LRwt{s: C.Sp}
  LAnn{s: C.Sp}
  LLet{ms: List<&2, Bm>, d: U32, s: C.Sp}

# a part to lower: an HTerm, or a binder's body read in its environment
type Lt is Data:
  LtH{h: H, d: U32}
  LtB{t: C.Tm, ev: Em, d: U32}

type HJ is Data:
  JH{t: C.Tm, ev: Em}
  JHs{ts: List<&2, C.Tm>, ev: Em, acc: List<&2, H>}
  JHs2{r: HR, ts: List<&2, C.Tm>, ev: Em, acc: List<&2, H>}
  JHk{r: HR, sh: Sh}
  JBeta{f: H, x: H, s: C.Sp}
  JVar{cell: Bool, fd: Fd, k: String, s: C.Sp}
  JRef{op: Bool, k: String, s: C.Sp, b: Bool}
  JL{h: H, d: U32}
  JLs{ts: List<&2, Lt>, acc: List<&2, C.Tm>}
  JLs2{r: HR, ts: List<&2, Lt>, acc: List<&2, C.Tm>}
  JLB{r: HR, d: U32}
  JLk{sh: Lsh, r: HR}

def bnd.metas(bs: List<&2, C.Bnd>) -> List<&2, Bm>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{C.Bnd{k, i, q, v}, t}:
      Bm{k, i, q} <> bnd.metas(t)

def bnd.vals(bs: List<&2, C.Bnd>) -> List<&2, C.Tm>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{C.Bnd{k, i, q, v}, t}:
      v <> bnd.vals(t)

def hb.zip(ms: List<&2, Bm>, hs: List<&2, H>) -> List<&2, HB>:
  match ms hs:
    case Con{Bm{k, i, q}, m} Con{h, t}:
      HB{k, i, q, h} <> hb.zip(m, t)
    case _ _:
      Nil{}

def hb.metas(bs: List<&2, HB>) -> List<&2, Bm>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{HB{k, i, q, v}, t}:
      Bm{k, i, q} <> hb.metas(t)

def hb.tasks(bs: List<&2, HB>, +d: U32) -> List<&2, Lt>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{HB{k, i, q, v}, t}:
      LtH{v, d} <> hb.tasks(t, d)

# the Let body's environment: binding j at its index is Var(k_j, d + j)
def let.env(ms: List<&2, Bm>, +d: U32, ev: Em) -> Em:
  match ms:
    case Nil{}:
      ev
    case Con{Bm{k, i, q}, t}:
      let.env(t, (d + 1 : U32), em.set(ev, i, EvH{HVar{k, d, C.NoSp{}}}))

def bnds.zip(ms: List<&2, Bm>, +d: U32, ts: List<&2, C.Tm>) -> List<&2, C.Bnd>:
  match ms ts:
    case Con{Bm{k, i, q}, m} Con{t, r}:
      C.Bnd{k, d, q, t} <> bnds.zip(m, (d + 1 : U32), r)
    case _ _:
      Nil{}

# rebuild a higher node from its parts (the App's beta step is the machine's)
def h.build(sh: Sh, hs: List<&2, H>) -> H:
  match sh hs:
    case ShTyp{s} Con{g, t}:
      HTyp{g, s}
    case ShMin{s} Con{a, Con{b, t}}:
      HMin{a, b, s}
    case ShAll{q, k, i, ev, B, s} Con{A, t}:
      HAll{q, k, i, A, ev, B, s}
    case ShAdt{k, r, s} xs:
      HAdt{k, xs, r, s}
    case ShCtr{k, s} xs:
      HCtr{k, xs, s}
    case ShMat{k, s} Con{h, Con{m, t}}:
      HMat{k, h, m, s}
    case ShEql{s} Con{a, Con{b, Con{A, t}}}:
      HEql{a, b, A, s}
    case ShRwt{s} Con{e, Con{p, Con{f, t}}}:
      HRwt{e, p, f, s}
    case ShAnn{s} Con{x, Con{A, t}}:
      HAnn{x, A, s}
    case ShLet{ms, ev, f, s} vs:
      HLet{hb.zip(ms, vs), ev, f, s}
    case _ _:
      HEfq{C.NoSp{}}

# the last of a Let's lowered parts is its body
def let.body(ts: List<&2, C.Tm>, n: U32) -> C.Tm:
  match ts:
    case Nil{}:
      C.TEfq{C.NoSp{}}
    case Con{t, Nil{}}:
      t
    case Con{t, r}:
      let.body(r, n)

def t.build(sh: Lsh, +ts: List<&2, C.Tm>) -> C.Tm:
  match sh ts:
    case LTyp{s} Con{g, t}:
      C.TTyp{g, s}
    case LMin{s} Con{a, Con{b, t}}:
      C.TMin{a, b, s}
    case LAll{q, k, d, s} Con{A, Con{B, t}}:
      C.TAll{q, k, d, A, B, s}
    case LLam{k, d, s, q} Con{f, t}:
      C.TLam{k, d, f, s, q}
    case LApp{s} Con{f, Con{x, t}}:
      C.TApp{f, x, s}
    case LAdt{k, r, s} xs:
      C.TAdt{k, xs, r, s}
    case LCtr{k, s} xs:
      C.TCtr{k, xs, s}
    case LMat{k, s} Con{h, Con{m, t}}:
      C.TMat{k, h, m, s}
    case LEql{s} Con{a, Con{b, Con{A, t}}}:
      C.TEql{a, b, A, s}
    case LRwt{s} Con{e, Con{p, Con{f, t}}}:
      C.TRwt{e, p, f, s}
    case LAnn{s} Con{x, Con{A, t}}:
      C.TAnn{x, A, s}
    case LLet{+ms, +d, s} ts:
      +n = U32.from_nat(List.length(&2, Bm, ms))
      C.TLet{bnds.zip(ms, d, ts), let.body(ts, n), s}
    case _ _:
      C.TEfq{C.NoSp{}}

def lt.hs(hs: List<&2, H>, +d: U32) -> List<&2, Lt>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      LtH{h, d} <> lt.hs(t, d)

def hm.go(+fuel: Nat, +txt: List<&2, U32>, j: HJ) -> HR:
  match fuel j:
    case 0n _:
      HRE{C.ErRaw{"bendbis: term_higher ran out of fuel"}}
    case 1n+p JHs{ts, +ev, acc}:
      match ts:
        case Nil{}:
          HRHs{List.reverse(&2, H, acc)}
        case Con{t, r}:
          hm.go(p, txt, JHs2{hm.go(p, txt, JH{t, ev}), r, ev, acc})
    case 1n+p JHs2{r, ts, ev, acc}:
      match r:
        case HRH{h}:
          hm.go(p, txt, JHs{ts, ev, h <> acc})
        case HRE{e}:
          HRE{e}
        case _:
          HRE{C.ErRaw{"bendbis: JHs2"}}
    case 1n+p JHk{r, sh}:
      match r:
        case HRHs{hs}:
          match hs sh:
            case Con{f, Con{x, Nil{}}} ShApp{s}:
              hm.go(p, txt, JBeta{f, x, s})
            case hs sh:
              HRH{h.build(sh, hs)}
        case HRE{e}:
          HRE{e}
        case _:
          HRE{C.ErRaw{"bendbis: JHk"}}
    case 1n+p JBeta{f, x, s}:
      match f:
        case HLam{k, i, ev, b, u, q}:
          hm.go(p, txt, JH{b, em.set(ev, i, EvH{x})})
        case f:
          HRH{HApp{f, x, s}}
    case 1n+p JVar{cell, fd, +k, +s}:
      match cell:
        case True{}:
          HRH{HVar{k, C.MINUS(), s}}
        case False{}:
          match fd:
            case FdNo{}:
              HRH{HRef{k, s, False{}}}
            case FdH{h}:
              HRH{h.adopt(h, s)}
            case FdP{q, e}:
              hm.go(p, txt, JH{patt.term(q, s), e})
    case 1n+p JRef{op, +k, +s, b}:
      match op:
        case True{}:
          HRE{op.err(txt, k, s)}
        case False{}:
          HRH{HRef{k, s, b}}
    case 1n+p JH{t, +ev}:
      match t:
        case C.TVar{k, +i, s}:
          hm.go(p, txt, JVar{U32.is_eq(i, C.MINUS()), ev.find(ev, i), k, s})
        case C.TVr{k, i, +s, r}:
          HRH{HRef{r, s, False{}}}
        case C.TRef{+k, s, b}:
          hm.go(p, txt, JRef{is_op(k), k, s, b})
        case C.TSub{i, v, f, s}:
          hm.go(p, txt, JH{f, em.set(ev, i, EvP{v, ev})})
        case C.TLet{+bs, f, s}:
          hm.go(p, txt, JHk{hm.go(p, txt, JHs{bnd.vals(bs), ev, Nil{}}), ShLet{bnd.metas(bs), ev, f, s}})
        case C.TTyp{g, s}:
          hm.go(p, txt, JHk{hm.go(p, txt, JHs{[g], ev, Nil{}}), ShTyp{s}})
        case C.TQnt{s}:
          HRH{HQnt{s}}
        case C.TQua{q, s}:
          HRH{HQua{q, s}}
        case C.TMin{a, b, s}:
          hm.go(p, txt, JHk{hm.go(p, txt, JHs{[a, b], ev, Nil{}}), ShMin{s}})
        case C.TAll{q, k, i, A, B, s}:
          hm.go(p, txt, JHk{hm.go(p, txt, JHs{[A], ev, Nil{}}), ShAll{q, k, i, ev, B, s}})
        case C.TLam{k, i, f, s, q}:
          HRH{HLam{k, i, ev, f, s, q}}
        case C.TApp{f, x, s}:
          hm.go(p, txt, JHk{hm.go(p, txt, JHs{[f, x], ev, Nil{}}), ShApp{s}})
        case C.TAdt{k, xs, r, s}:
          hm.go(p, txt, JHk{hm.go(p, txt, JHs{xs, ev, Nil{}}), ShAdt{k, r, s}})
        case C.TCtr{k, xs, s}:
          hm.go(p, txt, JHk{hm.go(p, txt, JHs{xs, ev, Nil{}}), ShCtr{k, s}})
        case C.TNat{v, s}:
          HRH{HNat{v, s}}
        case C.TU32{v, s}:
          HRH{HU32{v, s}}
        case C.TF32{v, s}:
          HRH{HF32{v, s}}
        case C.TStr{v, s}:
          HRH{HStr{v, s}}
        case C.TMat{k, h, m, s}:
          hm.go(p, txt, JHk{hm.go(p, txt, JHs{[h, m], ev, Nil{}}), ShMat{k, s}})
        case C.TEfq{s}:
          HRH{HEfq{s}}
        case C.TEql{a, b, A, s}:
          hm.go(p, txt, JHk{hm.go(p, txt, JHs{[a, b, A], ev, Nil{}}), ShEql{s}})
        case C.TRfl{s}:
          HRH{HRfl{s}}
        case C.TRwt{e, m, f, s}:
          hm.go(p, txt, JHk{hm.go(p, txt, JHs{[e, m, f], ev, Nil{}}), ShRwt{s}})
        case C.THol{k, s}:
          HRH{HHol{k, s}}
        case C.TAnn{x, A, s}:
          hm.go(p, txt, JHk{hm.go(p, txt, JHs{[x, A], ev, Nil{}}), ShAnn{s}})
    case 1n+p JLs{ts, acc}:
      match ts:
        case Nil{}:
          HRTs{List.reverse(&2, C.Tm, acc)}
        case Con{LtH{h, d}, r}:
          hm.go(p, txt, JLs2{hm.go(p, txt, JL{h, d}), r, acc})
        case Con{LtB{t, ev, d}, r}:
          hm.go(p, txt, JLs2{hm.go(p, txt, JLB{hm.go(p, txt, JH{t, ev}), d}), r, acc})
    case 1n+p JLs2{r, ts, acc}:
      match r:
        case HRT{t}:
          hm.go(p, txt, JLs{ts, t <> acc})
        case HRE{e}:
          HRE{e}
        case _:
          HRE{C.ErRaw{"bendbis: JLs2"}}
    case 1n+p JLB{r, d}:
      match r:
        case HRH{h}:
          hm.go(p, txt, JL{h, d})
        case HRE{e}:
          HRE{e}
        case _:
          HRE{C.ErRaw{"bendbis: JLB"}}
    case 1n+p JLk{sh, r}:
      match r:
        case HRTs{ts}:
          HRT{t.build(sh, ts)}
        case HRE{e}:
          HRE{e}
        case _:
          HRE{C.ErRaw{"bendbis: JLk"}}
    case 1n+p JL{h, +d}:
      match h:
        case HVar{k, i, s}:
          HRT{C.TVar{k, i, s}}
        case HRef{k, s, b}:
          HRT{C.TRef{k, s, b}}
        case HLet{+bs, ev, f, s}:
          +ms = hb.metas(bs)
          hm.go(p, txt, JLk{LLet{ms, d, s}, hm.go(p, txt, JLs{List.append(&2, Lt, hb.tasks(bs, d), [LtB{f, let.env(ms, d, ev), (d + U32.from_nat(List.length(&2, Bm, ms)) : U32)}]), Nil{}})})
        case HTyp{g, s}:
          hm.go(p, txt, JLk{LTyp{s}, hm.go(p, txt, JLs{[LtH{g, d}], Nil{}})})
        case HQnt{s}:
          HRT{C.TQnt{s}}
        case HQua{q, s}:
          HRT{C.TQua{q, s}}
        case HMin{a, b, s}:
          hm.go(p, txt, JLk{LMin{s}, hm.go(p, txt, JLs{[LtH{a, d}, LtH{b, d}], Nil{}})})
        case HAll{q, +k, i, A, ev, B, s}:
          hm.go(p, txt, JLk{LAll{q, k, d, s}, hm.go(p, txt, JLs{[LtH{A, d}, LtB{B, em.set(ev, i, EvH{HVar{k, d, C.NoSp{}}}), (d + 1 : U32)}], Nil{}})})
        case HLam{+k, i, ev, f, s, q}:
          hm.go(p, txt, JLk{LLam{k, d, s, q}, hm.go(p, txt, JLs{[LtB{f, em.set(ev, i, EvH{HVar{k, d, C.NoSp{}}}), (d + 1 : U32)}], Nil{}})})
        case HApp{f, x, s}:
          hm.go(p, txt, JLk{LApp{s}, hm.go(p, txt, JLs{[LtH{f, d}, LtH{x, d}], Nil{}})})
        case HAdt{k, xs, r, s}:
          hm.go(p, txt, JLk{LAdt{k, r, s}, hm.go(p, txt, JLs{lt.hs(xs, d), Nil{}})})
        case HCtr{k, xs, s}:
          hm.go(p, txt, JLk{LCtr{k, s}, hm.go(p, txt, JLs{lt.hs(xs, d), Nil{}})})
        case HNat{v, s}:
          HRT{C.TNat{v, s}}
        case HU32{v, s}:
          HRT{C.TU32{v, s}}
        case HF32{v, s}:
          HRT{C.TF32{v, s}}
        case HStr{v, s}:
          HRT{C.TStr{v, s}}
        case HMat{k, a, m, s}:
          hm.go(p, txt, JLk{LMat{k, s}, hm.go(p, txt, JLs{[LtH{a, d}, LtH{m, d}], Nil{}})})
        case HEfq{s}:
          HRT{C.TEfq{s}}
        case HEql{a, b, A, s}:
          hm.go(p, txt, JLk{LEql{s}, hm.go(p, txt, JLs{[LtH{a, d}, LtH{b, d}, LtH{A, d}], Nil{}})})
        case HRfl{s}:
          HRT{C.TRfl{s}}
        case HRwt{e, m, f, s}:
          hm.go(p, txt, JLk{LRwt{s}, hm.go(p, txt, JLs{[LtH{e, d}, LtH{m, d}, LtH{f, d}], Nil{}})})
        case HHol{k, s}:
          HRT{C.THol{k, s}}
        case HAnn{x, A, s}:
          hm.go(p, txt, JLk{LAnn{s}, hm.go(p, txt, JLs{[LtH{x, d}, LtH{A, d}], Nil{}})})

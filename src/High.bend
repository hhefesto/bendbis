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
  HVal{k: String, i: U32, s: C.Sp, v: H}
  HRef{k: String, s: C.Sp, b: Bool}
  HLet{bs: List<&2, HB>, cl: Cl, s: C.Sp}
  HTyp{g: H, s: C.Sp}
  HQnt{s: C.Sp}
  HQua{q: C.Q, s: C.Sp}
  HMin{a: H, b: H, s: C.Sp}
  HAll{q: C.Q, k: String, i: U32, A: H, cl: Cl, s: C.Sp}
  HLam{k: String, i: U32, cl: Cl, s: C.Sp, q: C.Q}
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

# a binder's closure (bend.ts's JS functions, as data): term_higher's, a body
# read in its environment with index i (a Let's, one index a binding)
# bound to the argument; lhs_ext's, the stuck call t waiting for n more of
# the fields of k (xs, the ones so far, newest first); check-rwt's motive
# type; a constant; check-mat's goal for a case's fields (Check.bend)
type Cl is Data:
  ClH{ev: Em, i: U32, b: C.Tm}
  ClL{ev: Em, ms: List<&2, Bm>, b: C.Tm}
  ClExt{t: H, k: String, n: U32, xs: List<&2, H>}
  ClRwt{a: H, T: H, s: C.Sp}
  ClK{t: H}
  ClMat{tq: C.Q, tb: Cl, cb: Cl, n: U32, xs: List<&2, H>, k: String, s: C.Sp}

# a Let binding's name, index and quantity
type Bm is Data:
  Bm{k: String, i: U32, q: C.Q}

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
    case HVal{k, i, s, v}:
      s
    case HRef{k, s, b}:
      s
    case HLet{bs, cl, s}:
      s
    case HTyp{g, s}:
      s
    case HQnt{s}:
      s
    case HQua{q, s}:
      s
    case HMin{a, b, s}:
      s
    case HAll{q, k, i, A, cl, s}:
      s
    case HLam{k, i, cl, s, q}:
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
    case HVal{k, i, u, v}:
      HVal{k, i, s, v}
    case HRef{k, u, b}:
      HRef{k, s, b}
    case HLet{bs, cl, u}:
      HLet{bs, cl, s}
    case HTyp{g, u}:
      HTyp{g, s}
    case HQnt{u}:
      HQnt{s}
    case HQua{q, u}:
      HQua{q, s}
    case HMin{a, b, u}:
      HMin{a, b, s}
    case HAll{q, k, i, A, cl, u}:
      HAll{q, k, i, A, cl, s}
    case HLam{k, i, cl, u, q}:
      HLam{k, i, cl, s, q}
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

# term_force and term_strip: through a Var's value, and through annotations
def h.force(h: H) -> H:
  match h:
    case HVal{k, i, s, v}:
      h.force(v)
    case h:
      h

def h.strip.go(h: H) -> H:
  match h:
    case HVal{k, i, s, v}:
      h.strip.go(v)
    case HAnn{x, A, s}:
      h.strip.go(x)
    case h:
      h

def h.strip(h: H) -> H:
  h.strip.go(h)

def h.is_cell(h: H) -> Bool:
  match h:
    case HVar{k, i, s}:
      U32.is_eq(i, C.MINUS())
    case HVal{k, +i, s, v}:
      U32.is_ge(i, 2147483648)
    case _:
      False{}

# a value found for a variable takes the occurrence's span when it has
# none of its own (and is no share cell)
def h.adopt.at(z: Bool, h: H, s: C.Sp) -> H:
  match z:
    case True{}:
      h
    case False{}:
      h.with_sp(h, s)

def h.adopt(+h: H, +s: C.Sp) -> H:
  h.adopt.at(Bool.or(Bool.or(C.sp.has(h.s(h)), Bool.not(C.sp.has(s))), h.is_cell(h)), h, s)

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

# a part to lower: an HTerm, or a closure applied (to fresh variables)
type Lt is Data:
  LtH{h: H, d: U32}
  LtC{cl: Cl, x: H, d: U32}
  LtCL{cl: Cl, xs: List<&2, H>, d: U32}

type HJ is Data:
  JH{t: C.Tm, ev: Em}
  JHs{ts: List<&2, C.Tm>, ev: Em, acc: List<&2, H>}
  JHs2{r: HR, ts: List<&2, C.Tm>, ev: Em, acc: List<&2, H>}
  JHk{r: HR, sh: Sh}
  JBeta{f: H, x: H, s: C.Sp}
  JApply{cl: Cl, x: H}
  JApplyL{cl: Cl, xs: List<&2, H>}
  JTApply{f: H, x: H, s: C.Sp}
  JTA2{g: H, x: H, s: C.Sp}
  JExt{one: Bool, t: H, k: String, n: U32, xs: List<&2, H>}
  JVar{cell: Bool, fd: Fd, k: String, s: C.Sp}
  JRef{op: Bool, k: String, s: C.Sp, b: Bool}
  JL{h: H, d: U32}
  JLs{ts: List<&2, Lt>, acc: List<&2, C.Tm>}
  JLs2{r: HR, ts: List<&2, Lt>, acc: List<&2, C.Tm>}
  JLB{r: HR, d: U32}
  JLk{sh: Lsh, r: HR}
  JH1{r: HR, sh: Sh}
  JH2{a: HR, b: HR, sh: Sh}
  JH3{a: HR, b: HR, c: HR, sh: Sh}
  JL1{r: HR, sh: Lsh}
  JL2{a: HR, b: HR, sh: Lsh}
  JL3{a: HR, b: HR, c: HR, sh: Lsh}

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

# the Let body's variables, Var(k_j, d + j)
def let.vars(ms: List<&2, Bm>, +d: U32) -> List<&2, H>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Bm{k, i, q}, t}:
      HVar{k, d, C.NoSp{}} <> let.vars(t, (d + 1 : U32))

# the Let closure's environment: each binding's index to its value
def let.bind(ms: List<&2, Bm>, xs: List<&2, H>, ev: Em) -> Em:
  match ms xs:
    case Con{Bm{k, +i, q}, m} Con{x, t}:
      let.bind(m, t, em.set(ev, i, EvH{x}))
    case _ _:
      ev

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
    case ShAll{q, k, +i, ev, B, s} Con{A, t}:
      HAll{q, k, i, A, ClH{ev, i, B}, s}
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
    case ShLet{+ms, ev, f, s} vs:
      HLet{hb.zip(ms, vs), ClL{ev, ms, f}, s}
    case _ _:
      HEfq{C.NoSp{}}

# h.build for a node of one, two or three parts, read straight into the
# node (no list of parts: JH1..JH3 hold the parts' results; the first
# error, left to right, is the answer, as JHs's)
def h.b1(sh: Sh, a: H) -> H:
  match sh:
    case ShTyp{s}:
      HTyp{a, s}
    case ShAll{q, k, +i, ev, B, s}:
      HAll{q, k, i, a, ClH{ev, i, B}, s}
    case _:
      HEfq{C.NoSp{}}

def h.b2(sh: Sh, a: H, b: H) -> H:
  match sh:
    case ShMin{s}:
      HMin{a, b, s}
    case ShMat{k, s}:
      HMat{k, a, b, s}
    case ShAnn{s}:
      HAnn{a, b, s}
    case _:
      HEfq{C.NoSp{}}

def h.b3(sh: Sh, a: H, b: H, c: H) -> H:
  match sh:
    case ShEql{s}:
      HEql{a, b, c, s}
    case ShRwt{s}:
      HRwt{a, b, c, s}
    case _:
      HEfq{C.NoSp{}}

# t.build's, the same way (JL1..JL3)
def t.b1(sh: Lsh, a: C.Tm) -> C.Tm:
  match sh:
    case LTyp{s}:
      C.TTyp{a, s}
    case LLam{k, d, s, q}:
      C.TLam{k, d, a, s, q}
    case _:
      C.TEfq{C.NoSp{}}

def t.b2(sh: Lsh, a: C.Tm, b: C.Tm) -> C.Tm:
  match sh:
    case LMin{s}:
      C.TMin{a, b, s}
    case LAll{q, k, d, s}:
      C.TAll{q, k, d, a, b, s}
    case LApp{s}:
      C.TApp{a, b, s}
    case LMat{k, s}:
      C.TMat{k, a, b, s}
    case LAnn{s}:
      C.TAnn{a, b, s}
    case _:
      C.TEfq{C.NoSp{}}

def t.b3(sh: Lsh, a: C.Tm, b: C.Tm, c: C.Tm) -> C.Tm:
  match sh:
    case LEql{s}:
      C.TEql{a, b, c, s}
    case LRwt{s}:
      C.TRwt{a, b, c, s}
    case _:
      C.TEfq{C.NoSp{}}

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
        case HLam{k, i, cl, u, q}:
          hm.go(p, txt, JApply{cl, x})
        case f:
          HRH{HApp{f, x, s}}
    # a closure applied (term_apply's f.f(x)), and term_apply
    case 1n+p JApply{cl, x}:
      match cl:
        case ClH{ev, +i, b}:
          hm.go(p, txt, JH{b, em.set(ev, i, EvH{x})})
        case ClL{ev, ms, b}:
          hm.go(p, txt, JApplyL{ClL{ev, ms, b}, [x]})
        case ClExt{t, k, +n, xs}:
          hm.go(p, txt, JExt{U32.is_eq(n, 1), t, k, n, x <> xs})
        case ClRwt{a, A, s}:
          HRH{HAll{C.QL{}, "e", 0, HEql{a, x, A, C.NoSp{}}, ClK{HTyp{HQua{C.QL{}, C.NoSp{}}, C.NoSp{}}}, s}}
        case ClK{t}:
          HRH{t}
        case ClMat{tq, tb, cb, n, xs, k, s}:
          HRE{C.ErRaw{"bendbis: a check-mat goal opened without the book"}}
    case 1n+p JApplyL{cl, xs}:
      match cl:
        case ClL{ev, ms, b}:
          hm.go(p, txt, JH{b, let.bind(ms, xs, ev)})
        case _:
          HRE{C.ErRaw{"bendbis: a let closure expected"}}
    case 1n+p JExt{one, t, k, n, xs}:
      match one:
        case True{}:
          hm.go(p, txt, JTApply{t, HCtr{k, List.reverse(&2, H, xs), C.NoSp{}}, C.NoSp{}})
        case False{}:
          HRH{HLam{"_", 0, ClExt{t, k, (n - 1 : U32), xs}, C.NoSp{}, C.QL{}}}
    case 1n+p JTApply{f, x, s}:
      hm.go(p, txt, JTA2{h.strip(f), x, s})
    case 1n+p JTA2{g, x, s}:
      match g:
        case HLam{k, i, cl, u, q}:
          hm.go(p, txt, JApply{cl, x})
        case g:
          HRH{HApp{g, x, s}}
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
          hm.go(p, txt, JH1{hm.go(p, txt, JH{g, ev}), ShTyp{s}})
        case C.TQnt{s}:
          HRH{HQnt{s}}
        case C.TQua{q, s}:
          HRH{HQua{q, s}}
        case C.TMin{a, b, s}:
          hm.go(p, txt, JH2{hm.go(p, txt, JH{a, ev}), hm.go(p, txt, JH{b, ev}), ShMin{s}})
        case C.TAll{q, k, i, A, B, s}:
          hm.go(p, txt, JH1{hm.go(p, txt, JH{A, ev}), ShAll{q, k, i, ev, B, s}})
        case C.TLam{k, +i, f, s, q}:
          HRH{HLam{k, i, ClH{ev, i, f}, s, q}}
        case C.TApp{f, x, s}:
          hm.go(p, txt, JH2{hm.go(p, txt, JH{f, ev}), hm.go(p, txt, JH{x, ev}), ShApp{s}})
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
          hm.go(p, txt, JH2{hm.go(p, txt, JH{h, ev}), hm.go(p, txt, JH{m, ev}), ShMat{k, s}})
        case C.TEfq{s}:
          HRH{HEfq{s}}
        case C.TEql{a, b, A, s}:
          hm.go(p, txt, JH3{hm.go(p, txt, JH{a, ev}), hm.go(p, txt, JH{b, ev}), hm.go(p, txt, JH{A, ev}), ShEql{s}})
        case C.TRfl{s}:
          HRH{HRfl{s}}
        case C.TRwt{e, m, f, s}:
          hm.go(p, txt, JH3{hm.go(p, txt, JH{e, ev}), hm.go(p, txt, JH{m, ev}), hm.go(p, txt, JH{f, ev}), ShRwt{s}})
        case C.THol{k, s}:
          HRH{HHol{k, s}}
        case C.TAnn{x, A, s}:
          hm.go(p, txt, JH2{hm.go(p, txt, JH{x, ev}), hm.go(p, txt, JH{A, ev}), ShAnn{s}})
    case 1n+p JLs{ts, acc}:
      match ts:
        case Nil{}:
          HRTs{List.reverse(&2, C.Tm, acc)}
        case Con{LtH{h, d}, r}:
          hm.go(p, txt, JLs2{hm.go(p, txt, JL{h, d}), r, acc})
        case Con{LtC{cl, x, d}, r}:
          hm.go(p, txt, JLs2{hm.go(p, txt, JLB{hm.go(p, txt, JApply{cl, x}), d}), r, acc})
        case Con{LtCL{cl, xs, d}, r}:
          hm.go(p, txt, JLs2{hm.go(p, txt, JLB{hm.go(p, txt, JApplyL{cl, xs}), d}), r, acc})
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
    case 1n+p JH1{r, sh}:
      match r:
        case HRH{a}:
          HRH{h.b1(sh, a)}
        case HRE{e}:
          HRE{e}
        case _:
          HRE{C.ErRaw{"bendbis: JH1"}}
    case 1n+p JH2{ra, rb, sh}:
      match ra rb sh:
        case HRH{f} HRH{x} ShApp{s}:
          hm.go(p, txt, JBeta{f, x, s})
        case HRH{a} HRH{b} sh:
          HRH{h.b2(sh, a, b)}
        case HRE{e} _ _:
          HRE{e}
        case _ HRE{e} _:
          HRE{e}
        case _ _ _:
          HRE{C.ErRaw{"bendbis: JH2"}}
    case 1n+p JH3{ra, rb, rc, sh}:
      match ra rb rc:
        case HRH{a} HRH{b} HRH{c}:
          HRH{h.b3(sh, a, b, c)}
        case HRE{e} _ _:
          HRE{e}
        case _ HRE{e} _:
          HRE{e}
        case _ _ HRE{e}:
          HRE{e}
        case _ _ _:
          HRE{C.ErRaw{"bendbis: JH3"}}
    case 1n+p JL1{r, sh}:
      match r:
        case HRT{a}:
          HRT{t.b1(sh, a)}
        case HRE{e}:
          HRE{e}
        case _:
          HRE{C.ErRaw{"bendbis: JL1"}}
    case 1n+p JL2{ra, rb, sh}:
      match ra rb:
        case HRT{a} HRT{b}:
          HRT{t.b2(sh, a, b)}
        case HRE{e} _:
          HRE{e}
        case _ HRE{e}:
          HRE{e}
        case _ _:
          HRE{C.ErRaw{"bendbis: JL2"}}
    case 1n+p JL3{ra, rb, rc, sh}:
      match ra rb rc:
        case HRT{a} HRT{b} HRT{c}:
          HRT{t.b3(sh, a, b, c)}
        case HRE{e} _ _:
          HRE{e}
        case _ HRE{e} _:
          HRE{e}
        case _ _ HRE{e}:
          HRE{e}
        case _ _ _:
          HRE{C.ErRaw{"bendbis: JL3"}}
    case 1n+p JL{h, +d}:
      match h:
        case HVar{k, i, s}:
          HRT{C.TVar{k, i, s}}
        case HVal{k, i, s, v}:
          hm.go(p, txt, JL{v, d})
        case HRef{k, s, b}:
          HRT{C.TRef{k, s, b}}
        case HLet{+bs, cl, s}:
          +ms = hb.metas(bs)
          hm.go(p, txt, JLk{LLet{ms, d, s}, hm.go(p, txt, JLs{List.append(&2, Lt, hb.tasks(bs, d), [LtCL{cl, let.vars(ms, d), (d + U32.from_nat(List.length(&2, Bm, ms)) : U32)}]), Nil{}})})
        case HTyp{g, s}:
          hm.go(p, txt, JL1{hm.go(p, txt, JL{g, d}), LTyp{s}})
        case HQnt{s}:
          HRT{C.TQnt{s}}
        case HQua{q, s}:
          HRT{C.TQua{q, s}}
        case HMin{a, b, s}:
          hm.go(p, txt, JL2{hm.go(p, txt, JL{a, d}), hm.go(p, txt, JL{b, d}), LMin{s}})
        case HAll{q, +k, i, A, cl, s}:
          hm.go(p, txt, JL2{hm.go(p, txt, JL{A, d}), hm.go(p, txt, JLB{hm.go(p, txt, JApply{cl, HVar{k, d, C.NoSp{}}}), (d + 1 : U32)}), LAll{q, k, d, s}})
        case HLam{+k, i, cl, s, q}:
          hm.go(p, txt, JL1{hm.go(p, txt, JLB{hm.go(p, txt, JApply{cl, HVar{k, d, C.NoSp{}}}), (d + 1 : U32)}), LLam{k, d, s, q}})
        case HApp{f, x, s}:
          hm.go(p, txt, JL2{hm.go(p, txt, JL{f, d}), hm.go(p, txt, JL{x, d}), LApp{s}})
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
          hm.go(p, txt, JL2{hm.go(p, txt, JL{a, d}), hm.go(p, txt, JL{m, d}), LMat{k, s}})
        case HEfq{s}:
          HRT{C.TEfq{s}}
        case HEql{a, b, A, s}:
          hm.go(p, txt, JL3{hm.go(p, txt, JL{a, d}), hm.go(p, txt, JL{b, d}), hm.go(p, txt, JL{A, d}), LEql{s}})
        case HRfl{s}:
          HRT{C.TRfl{s}}
        case HRwt{e, m, f, s}:
          hm.go(p, txt, JL3{hm.go(p, txt, JL{e, d}), hm.go(p, txt, JL{m, d}), hm.go(p, txt, JL{f, d}), LRwt{s}})
        case HHol{k, s}:
          HRT{C.THol{k, s}}
        case HAnn{x, A, s}:
          hm.go(p, txt, JL2{hm.go(p, txt, JL{x, d}), hm.go(p, txt, JL{A, d}), LAnn{s}})

# The normal form in one walk
# ---------------------------

# nf(t) = term_lower(term_higher(t)) for a def body with no bare operator
# (body.ops below decides, P.norm.by in PHelp.bend picks). An operator's is
# the one error term_higher throws, so on such a body the machine above
# answers HRT, and each node's normal form can be read in one walk, outside
# in, instead of a higher node, and a closure a binder, that term_lower then
# opens: a Var at its environment entry (a binder's Var(k, d), or a Sub's
# pattern, read in the environment the Sub saw), a Lam's or an All's body
# under Var(k, d) at depth d + 1, a Let's body under its bindings' vars at
# d + n, a Sub's body under its pattern. The environment is the machine's,
# its entries made by the same em.set calls, so an App whose head may turn
# into a Lam (the beta step, the one place term_higher puts a term for a
# variable) is the machine's whole (nf.slow), at the same environment and
# depth. The order of the work differs, which only an error could show.
type NJ is Data:
  NjT{t: C.Tm, ev: Em, d: U32}
  NjTs{ts: List<&2, C.Tm>, ev: Em, d: U32}
  NjFd{fd: Fd, k: String, s: C.Sp, d: U32}
  NjA{f: C.Tm, x: C.Tm, s: C.Sp, ev: Em, d: U32}
  NjR{r: HR}

# the machine on t, in ev at depth d (no operator below: the text an
# operator's error quotes is not read)
def nf.slow(t: C.Tm, ev: Em, d: U32) -> HR:
  hm.go(4294967295n, Nil{}, JLB{hm.go(4294967295n, Nil{}, JH{t, ev}), d})

# whether term_higher may make t a Lam: a Lam, under Subs, or an App's head
# (a beta step's answer). A Var is not: nf's entries are binders' Vars and
# patterns, whose terms are Vars and Ctrs
def may.lam(t: C.Tm) -> Bool:
  match t:
    case C.TLam{k, i, f, s, q}:
      True{}
    case C.TSub{i, v, f, s}:
      may.lam(f)
    case C.TApp{f, x, s}:
      may.lam(f)
    case _:
      False{}

# a Var's step: a share cell's Var as it is, else its entry
def nf.vj(cell: Bool, k: String, +i: U32, s: C.Sp, +ev: Em, d: U32) -> NJ:
  match cell:
    case True{}:
      NjR{HRT{C.TVar{k, i, s}}}
    case False{}:
      NjFd{ev.find(ev, i), k, s, d}

# an App's step: the machine's when its head may become a Lam
def nf.aj(z: Bool, f: C.Tm, x: C.Tm, s: C.Sp, ev: Em, d: U32) -> NJ:
  match z:
    case True{}:
      NjR{nf.slow(C.TApp{f, x, s}, ev, d)}
    case False{}:
      NjA{f, x, s, ev, d}

# a Ref: an operator here is a bug of body.ops (loud, never a wrong term)
def nf.ref(z: Bool, k: String, s: C.Sp, b: Bool) -> HR:
  match z:
    case True{}:
      HRE{C.ErRaw{"bendbis: nf met an operator (body.ops missed it)"}}
    case False{}:
      HRT{C.TRef{k, s, b}}

# an entry's HTerm (its span adopted) lowered at d: a binder's Var at once
def nf.h(h: H, +d: U32) -> HR:
  match h:
    case HVar{k, i, s}:
      HRT{C.TVar{k, i, s}}
    case h:
      hm.go(4294967295n, Nil{}, JL{h, d})

# a node rebuilt from its parts' answers (the first error, left to right,
# is the answer, as term_lower's JL1..JL3 and JLs)
def nf.k1(r: HR, sh: Lsh) -> HR:
  match r:
    case HRT{a}:
      HRT{t.b1(sh, a)}
    case HRE{e}:
      HRE{e}
    case _:
      HRE{C.ErRaw{"bendbis: nf.k1"}}

def nf.k2(ra: HR, rb: HR, sh: Lsh) -> HR:
  match ra rb:
    case HRT{a} HRT{b}:
      HRT{t.b2(sh, a, b)}
    case HRE{e} _:
      HRE{e}
    case _ HRE{e}:
      HRE{e}
    case _ _:
      HRE{C.ErRaw{"bendbis: nf.k2"}}

def nf.k3(ra: HR, rb: HR, rc: HR, sh: Lsh) -> HR:
  match ra rb rc:
    case HRT{a} HRT{b} HRT{c}:
      HRT{t.b3(sh, a, b, c)}
    case HRE{e} _ _:
      HRE{e}
    case _ HRE{e} _:
      HRE{e}
    case _ _ HRE{e}:
      HRE{e}
    case _ _ _:
      HRE{C.ErRaw{"bendbis: nf.k3"}}

def nf.ks(r: HR, sh: Lsh) -> HR:
  match r:
    case HRTs{ts}:
      HRT{t.build(sh, ts)}
    case HRE{e}:
      HRE{e}
    case _:
      HRE{C.ErRaw{"bendbis: nf.ks"}}

def nf.cons(ra: HR, rb: HR) -> HR:
  match ra rb:
    case HRT{a} HRTs{xs}:
      HRTs{a <> xs}
    case HRE{e} _:
      HRE{e}
    case _ HRE{e}:
      HRE{e}
    case _ _:
      HRE{C.ErRaw{"bendbis: nf.cons"}}

# a Let: its values at d, its body under its bindings' Vars at d + n (as
# t.build's LLet: bnds.zip numbers them d, d + 1, ..)
def nf.let(rv: HR, rb: HR, ms: List<&2, Bm>, +d: U32, s: C.Sp) -> HR:
  match rv rb:
    case HRTs{vs} HRT{b}:
      HRT{C.TLet{bnds.zip(ms, d, vs), b, s}}
    case HRE{e} _:
      HRE{e}
    case _ HRE{e}:
      HRE{e}
    case _ _:
      HRE{C.ErRaw{"bendbis: nf.let"}}

def nf.go(+fuel: Nat, j: NJ) -> HR:
  match fuel j:
    case 0n _:
      HRE{C.ErRaw{"bendbis: term_higher ran out of fuel"}}
    case 1n+p NjR{r}:
      r
    case 1n+p NjTs{ts, +ev, +d}:
      match ts:
        case Nil{}:
          HRTs{Nil{}}
        case Con{t, r}:
          nf.cons(nf.go(p, NjT{t, ev, d}), nf.go(p, NjTs{r, ev, d}))
    case 1n+p NjFd{fd, k, +s, +d}:
      match fd:
        case FdNo{}:
          HRT{C.TRef{k, s, False{}}}
        case FdH{h}:
          nf.h(h.adopt(h, s), d)
        case FdP{q, e}:
          nf.go(p, NjT{patt.term(q, s), e, d})
    case 1n+p NjA{f, x, s, +ev, +d}:
      nf.k2(nf.go(p, NjT{f, ev, d}), nf.go(p, NjT{x, ev, d}), LApp{s})
    case 1n+p NjT{t, +ev, +d}:
      match t:
        case C.TVar{k, +i, s}:
          nf.go(p, nf.vj(U32.is_eq(i, C.MINUS()), k, i, s, ev, d))
        case C.TVr{k, i, s, r}:
          HRT{C.TRef{r, s, False{}}}
        case C.TRef{+k, s, b}:
          nf.ref(is_op(k), k, s, b)
        case C.TSub{+i, v, f, s}:
          nf.go(p, NjT{f, em.set(ev, i, EvP{v, ev}), d})
        case C.TLet{+bs, f, s}:
          +ms = bnd.metas(bs)
          +n = U32.from_nat(List.length(&2, Bm, ms))
          nf.let(nf.go(p, NjTs{bnd.vals(bs), ev, d}), nf.go(p, NjT{f, let.bind(ms, let.vars(ms, d), ev), (d + n : U32)}), ms, d, s)
        case C.TTyp{g, s}:
          nf.k1(nf.go(p, NjT{g, ev, d}), LTyp{s})
        case C.TQnt{s}:
          HRT{C.TQnt{s}}
        case C.TQua{q, s}:
          HRT{C.TQua{q, s}}
        case C.TMin{a, b, s}:
          nf.k2(nf.go(p, NjT{a, ev, d}), nf.go(p, NjT{b, ev, d}), LMin{s})
        case C.TAll{q, +k, +i, A, B, s}:
          nf.k2(nf.go(p, NjT{A, ev, d}), nf.go(p, NjT{B, em.set(ev, i, EvH{HVar{k, d, C.NoSp{}}}), (d + 1 : U32)}), LAll{q, k, d, s})
        case C.TLam{+k, +i, f, s, q}:
          nf.k1(nf.go(p, NjT{f, em.set(ev, i, EvH{HVar{k, d, C.NoSp{}}}), (d + 1 : U32)}), LLam{k, d, s, q})
        case C.TApp{+f, x, s}:
          nf.go(p, nf.aj(may.lam(f), f, x, s, ev, d))
        case C.TAdt{k, xs, r, s}:
          nf.ks(nf.go(p, NjTs{xs, ev, d}), LAdt{k, r, s})
        case C.TCtr{k, xs, s}:
          nf.ks(nf.go(p, NjTs{xs, ev, d}), LCtr{k, s})
        case C.TNat{v, s}:
          HRT{C.TNat{v, s}}
        case C.TU32{v, s}:
          HRT{C.TU32{v, s}}
        case C.TF32{v, s}:
          HRT{C.TF32{v, s}}
        case C.TStr{v, s}:
          HRT{C.TStr{v, s}}
        case C.TMat{k, h, m, s}:
          nf.k2(nf.go(p, NjT{h, ev, d}), nf.go(p, NjT{m, ev, d}), LMat{k, s})
        case C.TEfq{s}:
          HRT{C.TEfq{s}}
        case C.TEql{a, b, A, s}:
          nf.k3(nf.go(p, NjT{a, ev, d}), nf.go(p, NjT{b, ev, d}), nf.go(p, NjT{A, ev, d}), LEql{s})
        case C.TRfl{s}:
          HRT{C.TRfl{s}}
        case C.TRwt{e, m, f, s}:
          nf.k3(nf.go(p, NjT{e, ev, d}), nf.go(p, NjT{m, ev, d}), nf.go(p, NjT{f, ev, d}), LRwt{s})
        case C.THol{k, s}:
          HRT{C.THol{k, s}}
        case C.TAnn{x, A, s}:
          nf.k2(nf.go(p, NjT{x, ev, d}), nf.go(p, NjT{A, ev, d}), LAnn{s})

def nf(t: C.Tm) -> HR:
  nf.go(4294967295n, NjT{t, EmTip{}, 0})

# whether a def body names a bare operator (a Ref is_op holds of) anywhere
# (then P.norm.by takes the machine, whose error, the first operator in its
# order, is the answer): a work list, on fuel; out of fuel, yes
type OpW is Data:
  OwT{t: C.Tm}
  OwB{b: C.Body}

def ow.ts(ts: List<&2, C.Tm>, r: List<&2, OpW>) -> List<&2, OpW>:
  match ts:
    case Nil{}:
      r
    case Con{t, u}:
      OwT{t} <> ow.ts(u, r)

def ow.rows(rs: List<&2, C.Row>, r: List<&2, OpW>) -> List<&2, OpW>:
  match rs:
    case Nil{}:
      r
    case Con{C.Row{ps, f}, u}:
      OwB{f} <> ow.rows(u, r)

def ow.bnds(bs: List<&2, C.Bnd>, r: List<&2, OpW>) -> List<&2, OpW>:
  match bs:
    case Nil{}:
      r
    case Con{C.Bnd{k, i, q, v}, u}:
      OwT{v} <> ow.bnds(u, r)

def ops.go(fuel: Nat, ws: List<&2, OpW>) -> Bool:
  match fuel ws:
    case 0n _:
      True{}
    case _ Nil{}:
      False{}
    case 1n+f Con{OwB{b}, r}:
      match b:
        case C.BMat{es, rs, s}:
          ops.go(f, ow.ts(es, ow.rows(rs, r)))
        case C.BLoc{ks, q, vs, g}:
          ops.go(f, ow.ts(vs, OwB{g} <> r))
        case C.BTm{t}:
          ops.go(f, OwT{t} <> r)
    case 1n+f Con{OwT{t}, r}:
      match t:
        case C.TRef{k, s, b}:
          Bool.or(is_op(k), ops.go(f, r))
        case C.TSub{i, v, g, s}:
          ops.go(f, OwT{g} <> r)
        case C.TLet{bs, g, s}:
          ops.go(f, ow.bnds(bs, OwT{g} <> r))
        case C.TTyp{g, s}:
          ops.go(f, OwT{g} <> r)
        case C.TMin{a, b, s}:
          ops.go(f, OwT{a} <> OwT{b} <> r)
        case C.TAll{q, k, i, A, B, s}:
          ops.go(f, OwT{A} <> OwT{B} <> r)
        case C.TLam{k, i, g, s, q}:
          ops.go(f, OwT{g} <> r)
        case C.TApp{a, b, s}:
          ops.go(f, OwT{a} <> OwT{b} <> r)
        case C.TAdt{k, xs, rr, s}:
          ops.go(f, ow.ts(xs, r))
        case C.TCtr{k, xs, s}:
          ops.go(f, ow.ts(xs, r))
        case C.TMat{k, h, m, s}:
          ops.go(f, OwT{h} <> OwT{m} <> r)
        case C.TEql{a, b, A, s}:
          ops.go(f, OwT{a} <> OwT{b} <> OwT{A} <> r)
        case C.TRwt{e, m, g, s}:
          ops.go(f, OwT{e} <> OwT{m} <> OwT{g} <> r)
        case C.TAnn{x, A, s}:
          ops.go(f, OwT{x} <> OwT{A} <> r)
        case _:
          ops.go(f, r)

def body.ops(b: C.Body) -> Bool:
  ops.go(4294967295n, [OwB{b}])

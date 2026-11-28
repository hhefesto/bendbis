import Base
import ./Core.bend as C
import ./Flat.bend as F
import ./High.bend as H

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# LAWS: what bendbis's own functions satisfy, proven in Bend, each passing
# `bend src/LAWS.bend --verdict` (BendTT rechecks every proof). Below: the
# quantity algebra, spans, application spines (term_apply and
# term_unapply), and match flattening's pattern and row helpers. The first
# set is the quantity algebra the checker's usage rides on (Core's q.add,
# q.join, q.dem: bend.ts's quant_add, quant_join, quant_dem), the facts
# check-lam, check-let and uses_close lean on: - is the unit of both, +
# absorbs, both commute, join is idempotent, and dem keeps - and passes
# any other demand on.

# q.add (quant_add)
# -----------------

law q.add.none_l:
  for q: C.Q
  {C.q.add(C.QN{}, q) == q : C.Q}

def q.add.none_l(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.add.none_r:
  for q: C.Q
  {C.q.add(q, C.QN{}) == q : C.Q}

def q.add.none_r(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.add.comm:
  for a: C.Q
  for b: C.Q
  {C.q.add(a, b) == C.q.add(b, a) : C.Q}

def q.add.comm(a, b):
  match a b:
    case C.QN{} C.QN{}:
      {==}
    case C.QN{} C.QL{}:
      {==}
    case C.QN{} C.QM{}:
      {==}
    case C.QL{} C.QN{}:
      {==}
    case C.QL{} C.QL{}:
      {==}
    case C.QL{} C.QM{}:
      {==}
    case C.QM{} C.QN{}:
      {==}
    case C.QM{} C.QL{}:
      {==}
    case C.QM{} C.QM{}:
      {==}

# two live uses are many: what uses_close reports as "consumed more than once"
law q.add.lone_lone:
  {C.q.add(C.QL{}, C.QL{}) == C.QM{} : C.Q}

def q.add.lone_lone():
  {==}

# q.join (quant_join)
# -------------------

law q.join.none_l:
  for q: C.Q
  {C.q.join(C.QN{}, q) == q : C.Q}

def q.join.none_l(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.join.many_l:
  for q: C.Q
  {C.q.join(C.QM{}, q) == C.QM{} : C.Q}

def q.join.many_l(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.join.idem:
  for q: C.Q
  {C.q.join(q, q) == q : C.Q}

def q.join.idem(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.join.comm:
  for a: C.Q
  for b: C.Q
  {C.q.join(a, b) == C.q.join(b, a) : C.Q}

def q.join.comm(a, b):
  match a b:
    case C.QN{} C.QN{}:
      {==}
    case C.QN{} C.QL{}:
      {==}
    case C.QN{} C.QM{}:
      {==}
    case C.QL{} C.QN{}:
      {==}
    case C.QL{} C.QL{}:
      {==}
    case C.QL{} C.QM{}:
      {==}
    case C.QM{} C.QN{}:
      {==}
    case C.QM{} C.QL{}:
      {==}
    case C.QM{} C.QM{}:
      {==}

# q.dem (quant_dem)
# -----------------

law q.dem.none:
  for qt: C.Q
  {C.q.dem(C.QN{}, qt) == C.QN{} : C.Q}

def q.dem.none(qt):
  {==}

law q.dem.lone:
  for qt: C.Q
  {C.q.dem(C.QL{}, qt) == qt : C.Q}

def q.dem.lone(qt):
  {==}

law q.dem.many:
  for qt: C.Q
  {C.q.dem(C.QM{}, qt) == qt : C.Q}

def q.dem.many(qt):
  {==}

# q.show (quant_show): the three spellings
law q.show.all:
  {[C.q.show(C.QN{}), C.q.show(C.QL{}), C.q.show(C.QM{})] == ["-", "", "+"] : List<&2, String>}

def q.show.all():
  {==}

# More of the algebra: both operations associate, + absorbs on either
# side, and the predicates read it
# ------------------------------------------------------------------

law q.add.assoc:
  for a: C.Q
  for b: C.Q
  for c: C.Q
  {C.q.add(C.q.add(a, b), c) == C.q.add(a, C.q.add(b, c)) : C.Q}

def q.add.assoc(a, b, c):
  match a b c:
    case C.QN{} C.QN{} C.QN{}:
      {==}
    case C.QN{} C.QN{} C.QL{}:
      {==}
    case C.QN{} C.QN{} C.QM{}:
      {==}
    case C.QN{} C.QL{} C.QN{}:
      {==}
    case C.QN{} C.QL{} C.QL{}:
      {==}
    case C.QN{} C.QL{} C.QM{}:
      {==}
    case C.QN{} C.QM{} C.QN{}:
      {==}
    case C.QN{} C.QM{} C.QL{}:
      {==}
    case C.QN{} C.QM{} C.QM{}:
      {==}
    case C.QL{} C.QN{} C.QN{}:
      {==}
    case C.QL{} C.QN{} C.QL{}:
      {==}
    case C.QL{} C.QN{} C.QM{}:
      {==}
    case C.QL{} C.QL{} C.QN{}:
      {==}
    case C.QL{} C.QL{} C.QL{}:
      {==}
    case C.QL{} C.QL{} C.QM{}:
      {==}
    case C.QL{} C.QM{} C.QN{}:
      {==}
    case C.QL{} C.QM{} C.QL{}:
      {==}
    case C.QL{} C.QM{} C.QM{}:
      {==}
    case C.QM{} C.QN{} C.QN{}:
      {==}
    case C.QM{} C.QN{} C.QL{}:
      {==}
    case C.QM{} C.QN{} C.QM{}:
      {==}
    case C.QM{} C.QL{} C.QN{}:
      {==}
    case C.QM{} C.QL{} C.QL{}:
      {==}
    case C.QM{} C.QL{} C.QM{}:
      {==}
    case C.QM{} C.QM{} C.QN{}:
      {==}
    case C.QM{} C.QM{} C.QL{}:
      {==}
    case C.QM{} C.QM{} C.QM{}:
      {==}

law q.join.assoc:
  for a: C.Q
  for b: C.Q
  for c: C.Q
  {C.q.join(C.q.join(a, b), c) == C.q.join(a, C.q.join(b, c)) : C.Q}

def q.join.assoc(a, b, c):
  match a b c:
    case C.QN{} C.QN{} C.QN{}:
      {==}
    case C.QN{} C.QN{} C.QL{}:
      {==}
    case C.QN{} C.QN{} C.QM{}:
      {==}
    case C.QN{} C.QL{} C.QN{}:
      {==}
    case C.QN{} C.QL{} C.QL{}:
      {==}
    case C.QN{} C.QL{} C.QM{}:
      {==}
    case C.QN{} C.QM{} C.QN{}:
      {==}
    case C.QN{} C.QM{} C.QL{}:
      {==}
    case C.QN{} C.QM{} C.QM{}:
      {==}
    case C.QL{} C.QN{} C.QN{}:
      {==}
    case C.QL{} C.QN{} C.QL{}:
      {==}
    case C.QL{} C.QN{} C.QM{}:
      {==}
    case C.QL{} C.QL{} C.QN{}:
      {==}
    case C.QL{} C.QL{} C.QL{}:
      {==}
    case C.QL{} C.QL{} C.QM{}:
      {==}
    case C.QL{} C.QM{} C.QN{}:
      {==}
    case C.QL{} C.QM{} C.QL{}:
      {==}
    case C.QL{} C.QM{} C.QM{}:
      {==}
    case C.QM{} C.QN{} C.QN{}:
      {==}
    case C.QM{} C.QN{} C.QL{}:
      {==}
    case C.QM{} C.QN{} C.QM{}:
      {==}
    case C.QM{} C.QL{} C.QN{}:
      {==}
    case C.QM{} C.QL{} C.QL{}:
      {==}
    case C.QM{} C.QL{} C.QM{}:
      {==}
    case C.QM{} C.QM{} C.QN{}:
      {==}
    case C.QM{} C.QM{} C.QL{}:
      {==}
    case C.QM{} C.QM{} C.QM{}:
      {==}

law q.add.many_l:
  for q: C.Q
  {C.q.add(C.QM{}, q) == C.QM{} : C.Q}

def q.add.many_l(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.add.many_r:
  for q: C.Q
  {C.q.add(q, C.QM{}) == C.QM{} : C.Q}

def q.add.many_r(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.join.none_r:
  for q: C.Q
  {C.q.join(q, C.QN{}) == q : C.Q}

def q.join.none_r(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.join.many_r:
  for q: C.Q
  {C.q.join(q, C.QM{}) == C.QM{} : C.Q}

def q.join.many_r(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

# join is below add: in the order - < (live) < +, q.join(a, b) never
# exceeds q.add(a, b), so joining the two branches of a match never asks
# more than using both
law q.join.below_add:
  for a: C.Q
  for b: C.Q
  {C.q.join(C.q.add(a, b), C.q.join(a, b)) == C.q.add(a, b) : C.Q}

def q.join.below_add(a, b):
  match a b:
    case C.QN{} C.QN{}:
      {==}
    case C.QN{} C.QL{}:
      {==}
    case C.QN{} C.QM{}:
      {==}
    case C.QL{} C.QN{}:
      {==}
    case C.QL{} C.QL{}:
      {==}
    case C.QL{} C.QM{}:
      {==}
    case C.QM{} C.QN{}:
      {==}
    case C.QM{} C.QL{}:
      {==}
    case C.QM{} C.QM{}:
      {==}

# a demand of - is no demand, whatever the binder's quantity
law q.dem.none_r:
  for q: C.Q
  {C.q.dem(q, C.QN{}) == C.QN{} : C.Q}

def q.dem.none_r(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

# demanding twice is demanding once
law q.dem.idem:
  for q: C.Q
  for t: C.Q
  {C.q.dem(C.q.dem(q, t), t) == C.q.dem(q, t) : C.Q}

def q.dem.idem(q, t):
  match q t:
    case C.QN{} C.QN{}:
      {==}
    case C.QN{} C.QL{}:
      {==}
    case C.QN{} C.QM{}:
      {==}
    case C.QL{} C.QN{}:
      {==}
    case C.QL{} C.QL{}:
      {==}
    case C.QL{} C.QM{}:
      {==}
    case C.QM{} C.QN{}:
      {==}
    case C.QM{} C.QL{}:
      {==}
    case C.QM{} C.QM{}:
      {==}

# a sum is unused exactly when both parts are
law q.is_none.add:
  for a: C.Q
  for b: C.Q
  {C.q.is_none(C.q.add(a, b)) == Bool.and(C.q.is_none(a), C.q.is_none(b)) : Bool}

def q.is_none.add(a, b):
  match a b:
    case C.QN{} C.QN{}:
      {==}
    case C.QN{} C.QL{}:
      {==}
    case C.QN{} C.QM{}:
      {==}
    case C.QL{} C.QN{}:
      {==}
    case C.QL{} C.QL{}:
      {==}
    case C.QL{} C.QM{}:
      {==}
    case C.QM{} C.QN{}:
      {==}
    case C.QM{} C.QL{}:
      {==}
    case C.QM{} C.QM{}:
      {==}

# each quantity is exactly one of -, live and +
law q.is.one:
  for q: C.Q
  {Bool.or(C.q.is_none(q), Bool.or(C.q.is_lone(q), C.q.is_many(q))) == True{} : Bool}

def q.is.one(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

# Spans (sp.or: the first span that is one)
# -----------------------------------------

law sp.or.none_l:
  for t: C.Sp
  {C.sp.or(C.NoSp{}, t) == t : C.Sp}

def sp.or.none_l(t):
  {==}

law sp.or.none_r:
  for s: C.Sp
  {C.sp.or(s, C.NoSp{}) == s : C.Sp}

def sp.or.none_r(s):
  match s:
    case C.NoSp{}:
      {==}
    case C.Sp{f, b, e}:
      {==}

law sp.or.assoc:
  for a: C.Sp
  for b: C.Sp
  for c: C.Sp
  {C.sp.or(C.sp.or(a, b), c) == C.sp.or(a, C.sp.or(b, c)) : C.Sp}

def sp.or.assoc(a, b, c):
  match a:
    case C.NoSp{}:
      {==}
    case C.Sp{f, x, e}:
      {==}

law sp.has.or:
  for s: C.Sp
  for t: C.Sp
  {C.sp.has(C.sp.or(s, t)) == Bool.or(C.sp.has(s), C.sp.has(t)) : Bool}

def sp.has.or(s, t):
  match s:
    case C.NoSp{}:
      {==}
    case C.Sp{f, b, e}:
      {==}

# Application spines (term_apply, term_unapply)
# ---------------------------------------------

# applying f to arguments keeps f's head
law tm.head.app:
  for xs: List<&2, C.Tm>
  for f: C.Tm
  for +s: C.Sp
  {C.tm.head(C.tm.app.go(xs, f, s)) == C.tm.head(f) : C.Tm}

def tm.head.app(xs, f, s):
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      tm.head.app(r, C.TApp{f, x, s}, s)

# splitting an applied term gives back its head and its arguments, those
# the spine had (acc) after the ones applied
law tm.unapp.app:
  for xs: List<&2, C.Tm>
  for f: C.Tm
  for +s: C.Sp
  for acc: List<&2, C.Tm>
  {C.tm.unapp.go(C.tm.app.go(xs, f, s), acc) == C.tm.unapp.go(f, List.append(&2, C.Tm, xs, acc)) : C.Tm & List<&2, C.Tm>}

def tm.unapp.app(xs, f, s, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      tm.unapp.app(r, C.TApp{f, x, s}, s, acc)

# term_unapply's head is tm.head's
law tm.unapp.head:
  for t: C.Tm
  for acc: List<&2, C.Tm>
  {Pair.fst(C.Tm, List<&2, C.Tm>, C.tm.unapp.go(t, acc)) == C.tm.head(t) : C.Tm}

def tm.unapp.head(t, acc):
  match t:
    case C.TApp{f, x, s}:
      tm.unapp.head(f, x <> acc)
    case C.TVar{k, i, s}:
      {==}
    case C.TVr{k, i, s, r}:
      {==}
    case C.TRef{k, s, b}:
      {==}
    case C.TSub{i, v, f, s}:
      {==}
    case C.TLet{bs, f, s}:
      {==}
    case C.TTyp{g, s}:
      {==}
    case C.TQnt{s}:
      {==}
    case C.TQua{q, s}:
      {==}
    case C.TMin{a, b, s}:
      {==}
    case C.TAll{q, k, i, A, B, s}:
      {==}
    case C.TLam{k, i, f, s, q}:
      {==}
    case C.TAdt{k, x, r, s}:
      {==}
    case C.TCtr{k, x, s}:
      {==}
    case C.TNat{v, s}:
      {==}
    case C.TU32{v, s}:
      {==}
    case C.TF32{v, s}:
      {==}
    case C.TStr{v, s}:
      {==}
    case C.TMat{k, h, m, s}:
      {==}
    case C.TEfq{s}:
      {==}
    case C.TEql{a, b, T, s}:
      {==}
    case C.TRfl{s}:
      {==}
    case C.TRwt{e, p, f, s}:
      {==}
    case C.THol{k, s}:
      {==}
    case C.TAnn{x, T, s}:
      {==}

# Match flattening (Flat)
# -----------------------

# setting a pattern's quantity to its own changes nothing
law pv.with_q.own:
  for +p: C.Pat
  {F.pv.with_q(p, F.pv.q(p)) == p : C.Pat}

def pv.with_q.own(p):
  match p:
    case C.PVar{k, i, q, s}:
      {==}
    case C.PCtr{k, xs, s}:
      {==}

# and a variable's quantity is the one set
law pv.q.with_q:
  for k: String
  for i: U32
  for o: C.Q
  for s: C.Sp
  for q: C.Q
  {F.pv.q(F.pv.with_q(C.PVar{k, i, o, s}, q)) == q : C.Q}

def pv.q.with_q(k, i, o, s, q):
  {==}

# dropping each row's first column keeps every row
law rows.tails.length:
  for rs: List<&2, C.Row>
  {List.length(&2, C.Row, F.rows.tails(rs)) == List.length(&2, C.Row, rs) : Nat}

def rows.tails.length(rs):
  match rs:
    case Nil{}:
      {==}
    case Con{C.Row{Con{p, ps}, f}, t}:
      %rows.tails.length(t) : {1n+List.length(&2, C.Row, F.rows.tails(t)) == 1n+_ : Nat}
      {==}
    case Con{C.Row{Nil{}, f}, t}:
      %rows.tails.length(t) : {1n+List.length(&2, C.Row, F.rows.tails(t)) == 1n+_ : Nat}
      {==}

# a pattern list read back as terms has one term a pattern
law patt.terms.length:
  for xs: List<&2, C.Pat>
  for +s: C.Sp
  {List.length(&2, C.Tm, F.patt.terms(xs, s)) == List.length(&2, C.Pat, xs) : Nat}

def patt.terms.length(xs, s):
  match xs:
    case Nil{}:
      {==}
    case Con{C.PVar{k, i, q, u}, t}:
      %patt.terms.length(t, s) : {1n+List.length(&2, C.Tm, F.patt.terms(t, s)) == 1n+_ : Nat}
      {==}
    case Con{C.PCtr{k, ys, u}, t}:
      %patt.terms.length(t, s) : {1n+List.length(&2, C.Tm, F.patt.terms(t, s)) == 1n+_ : Nat}
      {==}

# Dead Subs (Flat's sub.live): a Sub stays only over a term its index occurs
# in; a literal has none, so a Sub over one is the literal, and out of fuel
# the answer is yes (the Sub stays)
law tm.has.u32:
  for +i: U32
  for +n: U32
  for +s: C.Sp
  {C.tm.has(C.TU32{n, s}, i) == False{} : Bool}

def tm.has.u32(i, n, s):
  {==}

law sub.live.u32:
  for +i: U32
  for v: C.Pat
  for +n: U32
  for +s: C.Sp
  {F.sub.live(i, v, C.TU32{n, s}) == C.TU32{n, s} : C.Tm}

def sub.live.u32(i, v, n, s):
  {==}

law tms.has.out:
  for hit: Bool
  for ps: List<&2, C.Pat>
  for ts: List<&2, C.Tm>
  for +i: U32
  {C.tms.has(0n, hit, ps, ts, i) == True{} : Bool}

def tms.has.out(hit, ps, ts, i):
  match hit ps ts:
    case True{} Nil{} Nil{}:
      {==}
    case True{} Nil{} Con{t, r}:
      {==}
    case True{} Con{p, r} Nil{}:
      {==}
    case True{} Con{p, r} Con{t, u}:
      {==}
    case False{} Nil{} Nil{}:
      {==}
    case False{} Nil{} Con{t, r}:
      {==}
    case False{} Con{p, r} Nil{}:
      {==}
    case False{} Con{p, r} Con{t, u}:
      {==}

# The normal form in one walk (High.bend's nf): on a body with no bare
# operator, term_lower(term_higher(t)) read in one walk. Instances, one a
# kind of step: each side is computed (the machine is H.nf.slow at the
# empty environment and depth 0, P.norm's call), and they meet. The gates
# compare the two on every file's every def (DESIGN.md, "The gates")
law nf.u32:
  for +n: U32
  for +s: C.Sp
  {H.nf(C.TU32{n, s}) == H.nf.slow(C.TU32{n, s}, H.EmTip{}, 0) : H.HR}

def nf.u32(n, s):
  {==}

# a free name is a Ref at its span
law nf.free:
  for k: String
  for +s: C.Sp
  {H.nf(C.TVar{k, 5, s}) == H.nf.slow(C.TVar{k, 5, s}, H.EmTip{}, 0) : H.HR}

def nf.free(k, s):
  {==}

# a Lam's Var is Var(k, 0) under it, with the occurrence's span
law nf.lam:
  for +k: String
  for j: String
  for +f: U32
  for +b: U32
  for +e: U32
  for +s: C.Sp
  for q: C.Q
  {H.nf(C.TLam{k, 3, C.TVar{j, 3, C.Sp{f, b, e}}, s, q}) == H.nf.slow(C.TLam{k, 3, C.TVar{j, 3, C.Sp{f, b, e}}, s, q}, H.EmTip{}, 0) : H.HR}

def nf.lam(k, j, f, b, e, s, q):
  {==}

# a Sub's Var is its pattern, read where the Sub stands
law nf.sub:
  for x: String
  for h: String
  for +f: U32
  for +b: U32
  for +e: U32
  {H.nf(C.TSub{2, C.PCtr{"Con", [C.PVar{h, 7, C.QL{}, C.NoSp{}}], C.NoSp{}}, C.TVar{x, 2, C.Sp{f, b, e}}, C.NoSp{}}) == H.nf.slow(C.TSub{2, C.PCtr{"Con", [C.PVar{h, 7, C.QL{}, C.NoSp{}}], C.NoSp{}}, C.TVar{x, 2, C.Sp{f, b, e}}, C.NoSp{}}, H.EmTip{}, 0) : H.HR}

def nf.sub(x, h, f, b, e):
  {==}

# a Let's body sees its binding's Var at d
law nf.let:
  for +x: String
  for y: String
  for +n: U32
  for +f: U32
  for +b: U32
  for +e: U32
  {H.nf(C.TLet{[C.Bnd{x, 4, C.QL{}, C.TU32{n, C.NoSp{}}}], C.TVar{y, 4, C.Sp{f, b, e}}, C.NoSp{}}) == H.nf.slow(C.TLet{[C.Bnd{x, 4, C.QL{}, C.TU32{n, C.NoSp{}}}], C.TVar{y, 4, C.Sp{f, b, e}}, C.NoSp{}}, H.EmTip{}, 0) : H.HR}

def nf.let(x, y, n, f, b, e):
  {==}

# a Lam applied: the machine's beta step, as nf hands it over
law nf.beta:
  for +x: String
  for +n: U32
  for +f: U32
  for +b: U32
  for +e: U32
  for q: C.Q
  {H.nf(C.TApp{C.TLam{x, 1, C.TVar{x, 1, C.Sp{f, b, e}}, C.NoSp{}, q}, C.TU32{n, C.NoSp{}}, C.NoSp{}}) == H.nf.slow(C.TApp{C.TLam{x, 1, C.TVar{x, 1, C.Sp{f, b, e}}, C.NoSp{}, q}, C.TU32{n, C.NoSp{}}, C.NoSp{}}, H.EmTip{}, 0) : H.HR}

def nf.beta(x, n, f, b, e, q):
  {==}

import Base

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# BendTT in Bend: upstream's kernel (bend2/bendtt.lean, at 0e2f38f7) as
# Bend data and defs, and its lemmas as Bend laws, in bendtt.lean's order.
# Started: Part 1's terms and renaming (Quan, Term, Ren, Term.ren,
# Term.spine, Term.unspine), and the lemmas up_ren and ren_ren (the first
# two), with unspine_spine (taken early: it needs no substitution). Term's
# constructors are prefixed K (Base has a constructor App).
#
# One change of form, not of content: bendtt.lean's Ren is a function
# (Nat -> Nat), and Term.ren reads it at every variable. A Bend function
# can't be duplicated (a + binder needs Data, and Data holds no lambda),
# and a rewrite uses its proof live, so a hypothesis "r and s agree at
# every i" can't be shared by a term's two halves either. Here a renaming
# is Data: the renamings bendtt.lean builds (the identity, Nat.succ,
# Ren.up, Ren.pick and composition), read by ren.at. A lemma over every
# renaming (bendtt.lean's `r`, `s`) is a law over every such datum; one
# stated with funext (up_ren) is stated at every index.

# Quan, Term
# ----------

type Quan is Data:
  Q0{}
  Q1{}
  Q2{}

type Term is Data:
  KVar{i: Nat}
  KRef{k: String}
  KAnn{x: Term, T: Term}
  KLet{q: Quan, v: Term, f: Term}
  KTyp{q: Term}
  KMin{a: Term, b: Term}
  KAll{q: Quan, A: Term, B: Term}
  KLam{q: Quan, f: Term}
  KApp{q: Quan, f: Term, x: Term}
  KSig{q: Quan, A: Term, B: Term}
  KTup{q: Quan, a: Term, b: Term}
  KPrj{h: Term}
  KEnu{ks: List<&2, String>}
  KLab{k: String}
  KMat{k: String, h: Term, m: Term}
  KEfq{}
  KEql{a: Term, b: Term, T: Term}
  KRfl{}
  KRwt{e: Term, P: Term, f: Term}

# Ren
# ---

type Ren is Data:
  RId{}
  RSuc{}
  RUp{r: Ren}
  RPick{v: Nat}
  RComp{r: Ren, s: Ren}

# Ren.pick v i: v to 0, under a new binder
def ren.pick.at(z: Bool, i: Nat) -> Nat:
  match z:
    case True{}:
      0n
    case False{}:
      1n+i

# a renaming read at index i
def ren.at(r: Ren, +i: Nat) -> Nat:
  match r:
    case RId{}:
      i
    case RSuc{}:
      1n+i
    case RUp{s}:
      match i:
        case 0n:
          0n
        case 1n+j:
          1n+ren.at(s, j)
    case RPick{+v}:
      ren.pick.at(Nat.is_eq(i, v), i)
    case RComp{a, b}:
      ren.at(a, ren.at(b, i))

# Ren.up applied n times
def ren.ups(n: Nat, r: Ren) -> Ren:
  match n:
    case 0n:
      r
    case 1n+m:
      RUp{ren.ups(m, r)}

# Term
# ----

def term.ren(t: Term, +r: Ren) -> Term:
  match t:
    case KVar{i}:
      KVar{ren.at(r, i)}
    case KRef{k}:
      KRef{k}
    case KAnn{x, T}:
      KAnn{term.ren(x, r), term.ren(T, r)}
    case KLet{q, v, f}:
      KLet{q, term.ren(v, r), term.ren(f, RUp{r})}
    case KTyp{q}:
      KTyp{term.ren(q, r)}
    case KMin{a, b}:
      KMin{term.ren(a, r), term.ren(b, r)}
    case KAll{q, A, B}:
      KAll{q, term.ren(A, r), term.ren(B, RUp{r})}
    case KLam{q, f}:
      KLam{q, term.ren(f, RUp{r})}
    case KApp{q, f, x}:
      KApp{q, term.ren(f, r), term.ren(x, r)}
    case KSig{q, A, B}:
      KSig{q, term.ren(A, r), term.ren(B, RUp{r})}
    case KTup{q, a, b}:
      KTup{q, term.ren(a, r), term.ren(b, r)}
    case KPrj{h}:
      KPrj{term.ren(h, r)}
    case KEnu{ks}:
      KEnu{ks}
    case KLab{k}:
      KLab{k}
    case KMat{k, h, m}:
      KMat{k, term.ren(h, r), term.ren(m, r)}
    case KEfq{}:
      KEfq{}
    case KEql{a, b, T}:
      KEql{term.ren(a, r), term.ren(b, r), term.ren(T, r)}
    case KRfl{}:
      KRfl{}
    case KRwt{e, P, f}:
      KRwt{term.ren(e, r), term.ren(P, RUp{RUp{r}}), term.ren(f, r)}

# an argument: its quantity and its term (bendtt.lean's Arg)
type Arg is Data:
  KArg{q: Quan, x: Term}

def term.spine(xs: List<&2, Arg>, t: Term) -> Term:
  match xs:
    case Nil{}:
      t
    case Con{KArg{q, x}, r}:
      term.spine(r, KApp{q, t, x})

def term.unspine(t: Term, xs: List<&2, Arg>) -> Term & List<&2, Arg>:
  match t:
    case KApp{q, f, x}:
      term.unspine(f, KArg{q, x} <> xs)
    case t:
      (t, xs)

# Lemmas (bendtt.lean's order)
# ----------------------------

# up_ren: Ren.up r ∘ Ren.up s = Ren.up (r ∘ s), at every index
law up_ren:
  for +r: Ren
  for +s: Ren
  for i: Nat
  {ren.at(RComp{RUp{r}, RUp{s}}, i) == ren.at(RUp{RComp{r, s}}, i) : Nat}

def up_ren(r, s, i):
  match i:
    case 0n:
      {==}
    case 1n+j:
      {==}

# up_ren under n binders: Ren.up^n r ∘ Ren.up^n s = Ren.up^n (r ∘ s)
law ups_ren:
  for n: Nat
  for +i: Nat
  for +r: Ren
  for +s: Ren
  {ren.at(ren.ups(n, r), ren.at(ren.ups(n, s), i)) == ren.at(ren.ups(n, RComp{r, s}), i) : Nat}

def ups_ren(n, i, r, s):
  match n:
    case 0n:
      {==}
    case 1n+m:
      match i:
        case 0n:
          {==}
        case 1n+j:
          %ups_ren(m, j, r, s) : {1n+ren.at(ren.ups(m, r), ren.at(ren.ups(m, s), j)) == 1n+_ : Nat}
          {==}

# ren_ren under n binders, by induction on the term (n grows under each
# binder): Term.ren (up^n r) (Term.ren (up^n s) t) = Term.ren (up^n (r ∘ s)) t
law ren_ren_ups:
  for t: Term
  for +n: Nat
  for +r: Ren
  for +s: Ren
  {term.ren(term.ren(t, ren.ups(n, s)), ren.ups(n, r)) == term.ren(t, ren.ups(n, RComp{r, s})) : Term}

def ren_ren_ups(t, n, r, s):
  match t:
    case KVar{i}:
      %ups_ren(n, i, r, s) : {KVar{ren.at(ren.ups(n, r), ren.at(ren.ups(n, s), i))} == KVar{_} : Term}
      {==}
    case KRef{k}:
      {==}
    case KAnn{x, T}:
      %ren_ren_ups(x, n, r, s) : {KAnn{term.ren(term.ren(x, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(T, ren.ups(n, s)), ren.ups(n, r))} == KAnn{_, term.ren(T, ren.ups(n, RComp{r, s}))} : Term}
      %ren_ren_ups(T, n, r, s) : {KAnn{term.ren(term.ren(x, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(T, ren.ups(n, s)), ren.ups(n, r))} == KAnn{term.ren(term.ren(x, ren.ups(n, s)), ren.ups(n, r)), _} : Term}
      {==}
    case KLet{q, v, f}:
      %ren_ren_ups(v, n, r, s) : {KLet{q, term.ren(term.ren(v, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(f, RUp{ren.ups(n, s)}), RUp{ren.ups(n, r)})} == KLet{q, _, term.ren(f, RUp{ren.ups(n, RComp{r, s})})} : Term}
      %ren_ren_ups(f, 1n+n, r, s) : {KLet{q, term.ren(term.ren(v, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(f, RUp{ren.ups(n, s)}), RUp{ren.ups(n, r)})} == KLet{q, term.ren(term.ren(v, ren.ups(n, s)), ren.ups(n, r)), _} : Term}
      {==}
    case KTyp{q}:
      %ren_ren_ups(q, n, r, s) : {KTyp{term.ren(term.ren(q, ren.ups(n, s)), ren.ups(n, r))} == KTyp{_} : Term}
      {==}
    case KMin{a, b}:
      %ren_ren_ups(a, n, r, s) : {KMin{term.ren(term.ren(a, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(b, ren.ups(n, s)), ren.ups(n, r))} == KMin{_, term.ren(b, ren.ups(n, RComp{r, s}))} : Term}
      %ren_ren_ups(b, n, r, s) : {KMin{term.ren(term.ren(a, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(b, ren.ups(n, s)), ren.ups(n, r))} == KMin{term.ren(term.ren(a, ren.ups(n, s)), ren.ups(n, r)), _} : Term}
      {==}
    case KAll{q, A, B}:
      %ren_ren_ups(A, n, r, s) : {KAll{q, term.ren(term.ren(A, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(B, RUp{ren.ups(n, s)}), RUp{ren.ups(n, r)})} == KAll{q, _, term.ren(B, RUp{ren.ups(n, RComp{r, s})})} : Term}
      %ren_ren_ups(B, 1n+n, r, s) : {KAll{q, term.ren(term.ren(A, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(B, RUp{ren.ups(n, s)}), RUp{ren.ups(n, r)})} == KAll{q, term.ren(term.ren(A, ren.ups(n, s)), ren.ups(n, r)), _} : Term}
      {==}
    case KLam{q, f}:
      %ren_ren_ups(f, 1n+n, r, s) : {KLam{q, term.ren(term.ren(f, RUp{ren.ups(n, s)}), RUp{ren.ups(n, r)})} == KLam{q, _} : Term}
      {==}
    case KApp{q, f, x}:
      %ren_ren_ups(f, n, r, s) : {KApp{q, term.ren(term.ren(f, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(x, ren.ups(n, s)), ren.ups(n, r))} == KApp{q, _, term.ren(x, ren.ups(n, RComp{r, s}))} : Term}
      %ren_ren_ups(x, n, r, s) : {KApp{q, term.ren(term.ren(f, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(x, ren.ups(n, s)), ren.ups(n, r))} == KApp{q, term.ren(term.ren(f, ren.ups(n, s)), ren.ups(n, r)), _} : Term}
      {==}
    case KSig{q, A, B}:
      %ren_ren_ups(A, n, r, s) : {KSig{q, term.ren(term.ren(A, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(B, RUp{ren.ups(n, s)}), RUp{ren.ups(n, r)})} == KSig{q, _, term.ren(B, RUp{ren.ups(n, RComp{r, s})})} : Term}
      %ren_ren_ups(B, 1n+n, r, s) : {KSig{q, term.ren(term.ren(A, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(B, RUp{ren.ups(n, s)}), RUp{ren.ups(n, r)})} == KSig{q, term.ren(term.ren(A, ren.ups(n, s)), ren.ups(n, r)), _} : Term}
      {==}
    case KTup{q, a, b}:
      %ren_ren_ups(a, n, r, s) : {KTup{q, term.ren(term.ren(a, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(b, ren.ups(n, s)), ren.ups(n, r))} == KTup{q, _, term.ren(b, ren.ups(n, RComp{r, s}))} : Term}
      %ren_ren_ups(b, n, r, s) : {KTup{q, term.ren(term.ren(a, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(b, ren.ups(n, s)), ren.ups(n, r))} == KTup{q, term.ren(term.ren(a, ren.ups(n, s)), ren.ups(n, r)), _} : Term}
      {==}
    case KPrj{h}:
      %ren_ren_ups(h, n, r, s) : {KPrj{term.ren(term.ren(h, ren.ups(n, s)), ren.ups(n, r))} == KPrj{_} : Term}
      {==}
    case KEnu{ks}:
      {==}
    case KLab{k}:
      {==}
    case KMat{k, h, m}:
      %ren_ren_ups(h, n, r, s) : {KMat{k, term.ren(term.ren(h, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(m, ren.ups(n, s)), ren.ups(n, r))} == KMat{k, _, term.ren(m, ren.ups(n, RComp{r, s}))} : Term}
      %ren_ren_ups(m, n, r, s) : {KMat{k, term.ren(term.ren(h, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(m, ren.ups(n, s)), ren.ups(n, r))} == KMat{k, term.ren(term.ren(h, ren.ups(n, s)), ren.ups(n, r)), _} : Term}
      {==}
    case KEfq{}:
      {==}
    case KEql{a, b, T}:
      %ren_ren_ups(a, n, r, s) : {KEql{term.ren(term.ren(a, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(b, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(T, ren.ups(n, s)), ren.ups(n, r))} == KEql{_, term.ren(b, ren.ups(n, RComp{r, s})), term.ren(T, ren.ups(n, RComp{r, s}))} : Term}
      %ren_ren_ups(b, n, r, s) : {KEql{term.ren(term.ren(a, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(b, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(T, ren.ups(n, s)), ren.ups(n, r))} == KEql{term.ren(term.ren(a, ren.ups(n, s)), ren.ups(n, r)), _, term.ren(T, ren.ups(n, RComp{r, s}))} : Term}
      %ren_ren_ups(T, n, r, s) : {KEql{term.ren(term.ren(a, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(b, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(T, ren.ups(n, s)), ren.ups(n, r))} == KEql{term.ren(term.ren(a, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(b, ren.ups(n, s)), ren.ups(n, r)), _} : Term}
      {==}
    case KRfl{}:
      {==}
    case KRwt{e, P, f}:
      %ren_ren_ups(e, n, r, s) : {KRwt{term.ren(term.ren(e, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(P, RUp{RUp{ren.ups(n, s)}}), RUp{RUp{ren.ups(n, r)}}), term.ren(term.ren(f, ren.ups(n, s)), ren.ups(n, r))} == KRwt{_, term.ren(P, RUp{RUp{ren.ups(n, RComp{r, s})}}), term.ren(f, ren.ups(n, RComp{r, s}))} : Term}
      %ren_ren_ups(P, 2n+n, r, s) : {KRwt{term.ren(term.ren(e, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(P, RUp{RUp{ren.ups(n, s)}}), RUp{RUp{ren.ups(n, r)}}), term.ren(term.ren(f, ren.ups(n, s)), ren.ups(n, r))} == KRwt{term.ren(term.ren(e, ren.ups(n, s)), ren.ups(n, r)), _, term.ren(f, ren.ups(n, RComp{r, s}))} : Term}
      %ren_ren_ups(f, n, r, s) : {KRwt{term.ren(term.ren(e, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(P, RUp{RUp{ren.ups(n, s)}}), RUp{RUp{ren.ups(n, r)}}), term.ren(term.ren(f, ren.ups(n, s)), ren.ups(n, r))} == KRwt{term.ren(term.ren(e, ren.ups(n, s)), ren.ups(n, r)), term.ren(term.ren(P, RUp{RUp{ren.ups(n, s)}}), RUp{RUp{ren.ups(n, r)}}), _} : Term}
      {==}

# ren_ren: Term.ren r (Term.ren s t) = Term.ren (r ∘ s) t
law ren_ren:
  for t: Term
  for +r: Ren
  for +s: Ren
  {term.ren(term.ren(t, s), r) == term.ren(t, RComp{r, s}) : Term}

def ren_ren(t, r, s):
  ren_ren_ups(t, 0n, r, s)

# unspine_spine, with the arguments a spine already had (acc)
law unspine_spine_acc:
  for xs: List<&2, Arg>
  for t: Term
  for acc: List<&2, Arg>
  {term.unspine(term.spine(xs, t), acc) == term.unspine(t, List.append(&2, Arg, xs, acc)) : Term & List<&2, Arg>}

def unspine_spine_acc(xs, t, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{KArg{q, x}, r}:
      unspine_spine_acc(r, KApp{q, t, x}, acc)

law args.append_nil:
  for xs: List<&2, Arg>
  {List.append(&2, Arg, xs, Nil{}) == xs : List<&2, Arg>}

def args.append_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %args.append_nil(t) : {h <> List.append(&2, Arg, t, Nil{}) == h <> _ : List<&2, Arg>}
      {==}

# unspine_spine: unspine (spine t xs) [] = unspine t xs
law unspine_spine:
  for +xs: List<&2, Arg>
  for t: Term
  {term.unspine(term.spine(xs, t), Nil{}) == term.unspine(t, xs) : Term & List<&2, Arg>}

def unspine_spine(xs, t):
  %args.append_nil(xs) : {term.unspine(term.spine(xs, t), Nil{}) == term.unspine(t, _) : Term & List<&2, Arg>}
  unspine_spine_acc(xs, t, Nil{})

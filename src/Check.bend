import Base
import ./Core.bend as C
import ./Text.bend as T
import ./High.bend as H
import ./Show.bend as S
import ./Wnf.bend as W

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Check: bend.ts's checker: term_infer, term_check, tele_check,
# term_check_kind, uses_close, term_descend, book_adt, ctx_dead, def_check
# and def_inst, as one recursive def, ck.go, on the fuel's predecessor (a
# rule's premises are its jobs, KJ), each a do-block in the checker's monad
# K: a run on the checker's state (the book as it grows: its defs, the
# template instances minted so far; the names the def being checked refers
# to; a counter) to a value or the Err bend.ts would throw.
#
# A checked term returns, in bend.ts, as an elaborated LTerm (each node
# Ann-wrapped with its type); bendbis keeps of it what is read later: the
# usage, its head (check-any's note), and the names it refers to, which
# book_promises floods (the state's rs, a node's own name and the
# first-order part of its type, as term_refs walks it). A premise whose
# term bend.ts drops (infer-ann's type, a binder's kind check at a lambda
# or a let, def_inst's ~ arguments) is checked quietly: its names do not
# count. term_check_kind's err.exp === kind is a tag here: the kind's id
# rides with the expected type (g) down every rule that passes it on.

# Contexts and usages: bend.ts's PMaps (key 0 here, an odd key k left as
# (k-1)/2, an even one right as (k-2)/2)
# ----------------------------------------------------------------------

type An is Data:
  An{q: C.Q, k: String, T: H.H}

type Cx is Data:
  CxTip{}
  CxBin{v: Maybe<&2, An>, l: Cx, r: Cx}

def cx.get.go(fuel: Nat, m: Cx, side: Nat, +k: U32) -> Maybe<&2, An>:
  match fuel m:
    case 0n _:
      None{}
    case _ CxTip{}:
      None{}
    case 1n+f CxBin{v, l, r}:
      match side:
        case 0n:
          v
        case 1n:
          +j = H.em.down(k, 1n)
          cx.get.go(f, l, H.em.side(j), j)
        case _:
          +j = H.em.down(k, 2n)
          cx.get.go(f, r, H.em.side(j), j)

def cx.get(m: Cx, +k: U32) -> Maybe<&2, An>:
  cx.get.go(H.em.fuel(), m, H.em.side(k), k)

def cx.set.go(fuel: Nat, m: Cx, side: Nat, +k: U32, x: An) -> Cx:
  match fuel m:
    case 0n m:
      m
    case 1n+f CxTip{}:
      match side:
        case 0n:
          CxBin{Some{x}, CxTip{}, CxTip{}}
        case 1n:
          +j = H.em.down(k, 1n)
          CxBin{None{}, cx.set.go(f, CxTip{}, H.em.side(j), j, x), CxTip{}}
        case _:
          +j = H.em.down(k, 2n)
          CxBin{None{}, CxTip{}, cx.set.go(f, CxTip{}, H.em.side(j), j, x)}
    case 1n+f CxBin{v, l, r}:
      match side:
        case 0n:
          CxBin{Some{x}, l, r}
        case 1n:
          +j = H.em.down(k, 1n)
          CxBin{v, cx.set.go(f, l, H.em.side(j), j, x), r}
        case _:
          +j = H.em.down(k, 2n)
          CxBin{v, l, cx.set.go(f, r, H.em.side(j), j, x)}

# ctx_bind
def cx.set(m: Cx, +k: U32, x: An) -> Cx:
  cx.set.go(H.em.fuel(), m, H.em.side(k), k, x)

# an entry and its index
type Ci is Data:
  Ci{i: U32, a: An}

def cx.items.v(v: Maybe<&2, An>, +i: U32, rest: List<&2, Ci>) -> List<&2, Ci>:
  match v:
    case None{}:
      rest
    case Some{a}:
      Ci{i, a} <> rest

# pmap_to_array: here, then the left keys, then the right ones
def cx.items(m: Cx, +acc: U32, +scl: U32) -> List<&2, Ci>:
  match m:
    case CxTip{}:
      Nil{}
    case CxBin{v, l, r}:
      +s2 = (scl * 2 : U32)
      cx.items.v(v, acc, List.append(&2, Ci, cx.items(l, (acc + scl : U32), s2), cx.items(r, (acc + s2 : U32), s2)))

def ci.ins.at(z: Bool, x: Ci, y: Ci, t: List<&2, Ci>, rest: Unit -> List<&2, Ci>) -> List<&2, Ci>:
  match z:
    case True{}:
      x <> y <> t
    case False{}:
      y <> rest(Unit{})

def ci.ins(x: Ci, xs: List<&2, Ci>) -> List<&2, Ci>:
  match x xs:
    case x Nil{}:
      [x]
    case Ci{+i, +a} Con{Ci{+j, b}, +t}:
      ci.ins.at(U32.is_lt(i, j), Ci{i, a}, Ci{j, b}, t, u => ci.ins(Ci{i, a}, t))

def ci.sort(xs: List<&2, Ci>) -> List<&2, Ci>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      ci.ins(x, ci.sort(t))

# the entries by index
def cx.sorted(m: Cx) -> List<&2, Ci>:
  ci.sort(cx.items(m, 0, 1))

def ci.max(xs: List<&2, Ci>, +n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case Con{Ci{+i, a}, t}:
      ci.max(t, U32.max(n, (i + 1 : U32)))

def ci.name(xs: List<&2, Ci>, +i: U32) -> String:
  match xs:
    case Nil{}:
      "_"
    case Con{Ci{+j, An{q, k, A}}, t}:
      Bool.pick(String, U32.is_eq(i, j), k, ci.name(t, i))

def scope.go(n: Nat, +xs: List<&2, Ci>, +i: U32) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      ci.name(xs, i) <> scope.go(m, xs, (i + 1 : U32))

# ctx_scope: each index's name, "_" for an index with none
def cx.scope(m: Cx) -> List<&2, String>:
  +xs = cx.items(m, 0, 1)
  scope.go(U32.to_nat(ci.max(xs, 0)), xs, 0)

def cx.pre.go(fuel: Nat, ms: List<&2, Cx>) -> List<&2, An>:
  match fuel ms:
    case 0n _:
      Nil{}
    case _ Nil{}:
      Nil{}
    case 1n+f Con{CxTip{}, t}:
      cx.pre.go(f, t)
    case 1n+f Con{CxBin{None{}, l, r}, t}:
      cx.pre.go(f, l <> r <> t)
    case 1n+f Con{CxBin{Some{a}, l, r}, t}:
      a <> cx.pre.go(f, l <> r <> t)

# pmap_any's order: here, then the left, then the right
def cx.pre(m: Cx) -> List<&2, An>:
  cx.pre.go(4294967295n, [m])

type Us is Data:
  UsTip{}
  UsBin{v: Maybe<&2, C.Q>, l: Us, r: Us}

def us.get.go(fuel: Nat, m: Us, side: Nat, +k: U32) -> Maybe<&2, C.Q>:
  match fuel m:
    case 0n _:
      None{}
    case _ UsTip{}:
      None{}
    case 1n+f UsBin{v, l, r}:
      match side:
        case 0n:
          v
        case 1n:
          +j = H.em.down(k, 1n)
          us.get.go(f, l, H.em.side(j), j)
        case _:
          +j = H.em.down(k, 2n)
          us.get.go(f, r, H.em.side(j), j)

def us.get(m: Us, +k: U32) -> Maybe<&2, C.Q>:
  us.get.go(H.em.fuel(), m, H.em.side(k), k)

def us.set.go(fuel: Nat, m: Us, side: Nat, +k: U32, x: C.Q) -> Us:
  match fuel m:
    case 0n m:
      m
    case 1n+f UsTip{}:
      match side:
        case 0n:
          UsBin{Some{x}, UsTip{}, UsTip{}}
        case 1n:
          +j = H.em.down(k, 1n)
          UsBin{None{}, us.set.go(f, UsTip{}, H.em.side(j), j, x), UsTip{}}
        case _:
          +j = H.em.down(k, 2n)
          UsBin{None{}, UsTip{}, us.set.go(f, UsTip{}, H.em.side(j), j, x)}
    case 1n+f UsBin{v, l, r}:
      match side:
        case 0n:
          UsBin{Some{x}, l, r}
        case 1n:
          +j = H.em.down(k, 1n)
          UsBin{v, us.set.go(f, l, H.em.side(j), j, x), r}
        case _:
          +j = H.em.down(k, 2n)
          UsBin{v, l, us.set.go(f, r, H.em.side(j), j, x)}

def us.set(m: Us, +k: U32, x: C.Q) -> Us:
  us.set.go(H.em.fuel(), m, H.em.side(k), k, x)

def q.merge(a: Maybe<&2, C.Q>, b: Maybe<&2, C.Q>, add: Bool) -> Maybe<&2, C.Q>:
  match a b:
    case None{} b:
      b
    case a None{}:
      a
    case Some{+x} Some{+y}:
      Some{Bool.pick(C.Q, add, C.q.add(x, y), C.q.join(x, y))}

# pmap_union, by quant_add (add) or quant_join
def us.union(a: Us, b: Us, +add: Bool) -> Us:
  match a b:
    case UsTip{} b:
      b
    case a UsTip{}:
      a
    case UsBin{v1, l1, r1} UsBin{v2, l2, r2}:
      UsBin{q.merge(v1, v2, add), us.union(l1, l2, add), us.union(r1, r2, add)}

def us.add(a: Us, b: Us) -> Us:
  us.union(a, b, True{})

def us.join(a: Us, b: Us) -> Us:
  us.union(a, b, False{})

def us.one(+k: U32, q: C.Q) -> Us:
  us.set(UsTip{}, k, q)

# The checker's values and state
# ------------------------------

# the elaborated term's head, as check-any's note reads it
# (term_strip(term_unapply(term_strip(tm))[0])): a Ref, an App of one
type Es is Data:
  EsNo{}
  EsRef{k: String}
  EsApp{k: String}

def es.app(e: Es) -> Es:
  match e:
    case EsRef{k}:
      EsApp{k}
    case _:
      EsNo{}

def es.name(e: Es) -> Maybe<&2, String>:
  match e:
    case EsRef{k}:
      Some{k}
    case EsApp{k}:
      Some{k}
    case EsNo{}:
      None{}

# what a job answers: an Infer (its type, usage, pending ~ arguments, head),
# a Check, a telescope's usage and rest, a term, an instance's name, a
# datatype's view (book_adt), a truth, or nothing
type KV is Data:
  VI{ty: H.H, us: Us, x: U32, es: Es}
  VU{us: Us, es: Es}
  VT{us: Us, ret: H.H}
  VH{h: H.H}
  VK{k: String}
  VA{n: U32, T: H.H, c: List<&2, W.Cr>}
  VB{b: Bool}
  VN{}

def kv.ty(v: KV) -> H.H:
  match v:
    case VI{ty, us, x, es}:
      ty
    case _:
      H.HHol{"bendbis: kv.ty", C.NoSp{}}

def kv.us(v: KV) -> Us:
  match v:
    case VI{ty, us, x, es}:
      us
    case VU{us, es}:
      us
    case VT{us, ret}:
      us
    case _:
      UsTip{}

def kv.x(v: KV) -> U32:
  match v:
    case VI{ty, us, x, es}:
      x
    case _:
      0

def kv.es(v: KV) -> Es:
  match v:
    case VI{ty, us, x, es}:
      es
    case VU{us, es}:
      es
    case _:
      EsNo{}

def kv.ret(v: KV) -> H.H:
  match v:
    case VT{us, ret}:
      ret
    case VH{h}:
      h
    case _:
      H.HHol{"bendbis: kv.ret", C.NoSp{}}

def kv.n(v: KV) -> U32:
  match v:
    case VA{n, T, c}:
      n
    case _:
      0

def kv.T(v: KV) -> H.H:
  match v:
    case VA{n, T, c}:
      T
    case _:
      H.HHol{"bendbis: kv.T", C.NoSp{}}

def kv.c(v: KV) -> List<&2, W.Cr>:
  match v:
    case VA{n, T, c}:
      c
    case _:
      Nil{}

def kv.b(v: KV) -> Bool:
  match v:
    case VB{b}:
      b
    case _:
      False{}

def kv.k(v: KV) -> String:
  match v:
    case VK{k}:
      k
    case _:
      ""

# the def's own equation (bend.ts's LHS): its call rebuilt as the tree
# walks, the parameters left, its name, its parameter quantities, @unsafe,
# and the instance depth
type Lhs is Data:
  Lhs{t: H.H, n: U32, dn: String, qs: List<&2, C.Q>, u: Bool, z: U32}

def lhs.t(l: Lhs) -> H.H:
  match l:
    case Lhs{t, n, dn, qs, u, z}:
      t

def lhs.n(l: Lhs) -> U32:
  match l:
    case Lhs{t, n, dn, qs, u, z}:
      n

def lhs.dn(l: Lhs) -> String:
  match l:
    case Lhs{t, n, dn, qs, u, z}:
      dn

def lhs.qs(l: Lhs) -> List<&2, C.Q>:
  match l:
    case Lhs{t, n, dn, qs, u, z}:
      qs

def lhs.u(l: Lhs) -> Bool:
  match l:
    case Lhs{t, n, dn, qs, u, z}:
      u

def lhs.z(l: Lhs) -> U32:
  match l:
    case Lhs{t, n, dn, qs, u, z}:
      z

# lhs_kind: an @unsafe def's + binder needs no Data
def lhs.kind(l: Lhs, q: C.Q) -> C.Q:
  match q:
    case C.QM{}:
      Bool.pick(C.Q, lhs.u(l), C.QL{}, C.QM{})
    case q:
      q

def lhs.step.go(z: Bool, l: Lhs, x: H.H) -> Lhs:
  match z l:
    case True{} Lhs{t, +n, dn, qs, u, zz}:
      Lhs{W.ap(t, x, C.NoSp{}), (n - 1 : U32), dn, qs, u, zz}
    case False{} l:
      l

# check-lam: the lhs takes x while a parameter remains
def lhs.step(+l: Lhs, x: H.H) -> Lhs:
  lhs.step.go(U32.is_gt(lhs.n(l), 0), l, x)

def lhs.ext.go(z: Bool, l: Lhs, +k: String, +n: U32) -> Lhs:
  match z l:
    case True{} Lhs{t, +m, dn, qs, u, zz}:
      Lhs{W.lhs_ext(t, k, n), ((m - 1 : U32) + n : U32), dn, qs, u, zz}
    case False{} l:
      l

# check-mat: a case's lhs rebuilds the column from its n fields
def lhs.ext(+l: Lhs, k: String, n: U32) -> Lhs:
  lhs.ext.go(U32.is_gt(lhs.n(l), 0), l, k, n)

# what an error shows: a text, or a term
type Ex is Data:
  ExS{s: String}
  ExH{h: H.H}

# bend.ts's Err: the book it was thrown in, its context, expected and
# observed, span, def and note; g the expected kind's tag (0: none)
type Ek is Data:
  Ek{bk: Map<&2, W.Td>, ctx: Cx, exp: Ex, obs: Maybe<&2, Ex>, spn: C.Sp, dn: Maybe<&2, String>, nte: Maybe<&2, String>, g: U32}

# a file a span can point into: its id, text and names
type Fi is Data:
  Fi{fid: U32, txt: List<&2, U32>, fl: S.Fl}

def fi.fl(fs: List<&2, Fi>, +f: U32) -> S.Fl:
  match fs:
    case Nil{}:
      S.NoFl{}
    case Con{Fi{+g, txt, fl}, t}:
      Bool.pick(S.Fl, U32.is_eq(f, g), fl, fi.fl(t, f))

def fi.txt(fs: List<&2, Fi>, +f: U32) -> List<&2, U32>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fi{+g, txt, fl}, t}:
      Bool.pick(List<&2, U32>, U32.is_eq(f, g), txt, fi.txt(t, f))

def sp.fl(fs: List<&2, Fi>, s: C.Sp) -> S.Fl:
  match s:
    case C.NoSp{}:
      S.NoFl{}
    case C.Sp{f, b, e}:
      fi.fl(fs, f)

# the checker's state: the book's defs and datatypes (tlds), constructors,
# each template's instances (term_key to name), the names the def being
# checked refers to, the kind tag counter, the files, and the TODO count
type Ks is Data:
  Ks{tl: Map<&2, W.Td>, ct: Map<&2, W.Cr>, tp: Map<&2, Map<&2, String>>, rs: Map<&2, Bool>, g: U32, fs: List<&2, Fi>, hols: U32}

type KR<-A: Type> is Type:
  KOk{v: A, st: Ks}
  KErr{e: Ek}

def K(-A: Type) -> Type:
  Ks -> KR<A>

def K.pure(-A: Type, x: A) -> K(A):
  st => KOk{x, st}

def K.bind.go(-A: Type, -B: Type, r: KR<A>, f: A -> K(B)) -> KR<B>:
  match r:
    case KOk{a, st}:
      f(a, st)
    case KErr{e}:
      KErr{e}

def K.bind(-A: Type, -B: Type, m: K(A), f: A -> K(B)) -> K(B):
  st => K.bind.go(A, B, m(st), f)

def K.throw(-A: Type, e: Ek) -> K(A):
  st => KErr{e}

def K.if(-A: Type, z: Bool, a: K(A), b: K(A)) -> K(A):
  match z:
    case True{}:
      a
    case False{}:
      b

def ks.tl(st: Ks) -> Map<&2, W.Td>:
  match st:
    case Ks{tl, ct, tp, rs, g, fs, hols}:
      tl

def ks.fs(st: Ks) -> List<&2, Fi>:
  match st:
    case Ks{tl, ct, tp, rs, g, fs, hols}:
      fs

# Err(book, ctx, exp, obs, spn, def, nte), g the expected kind's tag
def K.err(-A: Type, ctx: Cx, exp: Ex, obs: Maybe<&2, Ex>, spn: C.Sp, dn: Maybe<&2, String>, nte: Maybe<&2, String>, g: U32) -> K(A):
  st => KErr{Ek{ks.tl(st), ctx, exp, obs, spn, dn, nte, g}}

def K.raw(-A: Type, m: String) -> K(A):
  K.err(A, CxTip{}, ExS{m}, None{}, C.NoSp{}, None{}, None{}, 0)

# try { m } catch (e) { h(e) }: an error is final in bend.ts's checker
# but where a rule rewrites it and throws it again
def K.catch.go(r: KR<KV>, h: Ek -> K(KV), st: Ks) -> KR<KV>:
  match r:
    case KOk{v, s2}:
      KOk{v, s2}
    case KErr{e}:
      h(e, st)

def K.catch(m: K(KV), h: Ek -> K(KV)) -> K(KV):
  +st => K.catch.go(m(st), h, st)

# a step that does nothing (a do block opening with a let needs one first)
def K.nop() -> K(Unit):
  st => KOk{Unit{}, st}

def K.st() -> K(Ks):
  +st => KOk{st, st}

def K.tl.go(st: Ks) -> KR<Map<&2, W.Td>>:
  match st:
    case Ks{+tl, ct, tp, rs, g, fs, hols}:
      KOk{tl, Ks{tl, ct, tp, rs, g, fs, hols}}

def K.tl() -> K(Map<&2, W.Td>):
  st => K.tl.go(st)

def K.w() -> K(W.W):
  K.bind(Map<&2, W.Td>, W.W, K.tl(), +tl => K.pure(W.W, W.W{tl, tl}))

def K.ct.go(st: Ks) -> KR<Map<&2, W.Cr>>:
  match st:
    case Ks{tl, +ct, tp, rs, g, fs, hols}:
      KOk{ct, Ks{tl, ct, tp, rs, g, fs, hols}}

def K.ct() -> K(Map<&2, W.Cr>):
  st => K.ct.go(st)

def K.fl.go(s: C.Sp, st: Ks) -> KR<S.Fl>:
  match st:
    case Ks{tl, ct, tp, rs, g, +fs, hols}:
      KOk{sp.fl(fs, s), Ks{tl, ct, tp, rs, g, fs, hols}}

# the file a span points into, for name_show
def K.fl(s: C.Sp) -> K(S.Fl):
  st => K.fl.go(s, st)

def K.set_tl.go(m: Map<&2, W.Td>, st: Ks) -> KR<Unit>:
  match st:
    case Ks{tl, ct, tp, rs, g, fs, hols}:
      KOk{Unit{}, Ks{m, ct, tp, rs, g, fs, hols}}

def K.set_tl(m: Map<&2, W.Td>) -> K(Unit):
  st => K.set_tl.go(m, st)

def K.set_td.go(k: String, t: W.Td, st: Ks) -> KR<Unit>:
  match st:
    case Ks{tl, ct, tp, rs, g, fs, hols}:
      KOk{Unit{}, Ks{Map.set(&2, W.Td, tl, k, t), ct, tp, rs, g, fs, hols}}

# book.tlds[k] = t
def K.set_td(k: String, t: W.Td) -> K(Unit):
  st => K.set_td.go(k, t, st)

def K.tp.go(+k: String, st: Ks) -> KR<Map<&2, String>>:
  match st:
    case Ks{tl, ct, +tp, rs, g, fs, hols}:
      KOk{Pair.snd(Map<&2, Map<&2, String>>, Map<&2, String>, Map.get(Map<&2, String>, Map.new(&2, String), tp, k)), Ks{tl, ct, tp, rs, g, fs, hols}}

# book.tmps[k] (empty when k has none yet)
def K.tp(k: String) -> K(Map<&2, String>):
  st => K.tp.go(k, st)

def K.set_tp.go(k: String, m: Map<&2, String>, st: Ks) -> KR<Unit>:
  match st:
    case Ks{tl, ct, tp, rs, g, fs, hols}:
      KOk{Unit{}, Ks{tl, ct, Map.set(&2, Map<&2, String>, tp, k, m), rs, g, fs, hols}}

def K.set_tp(k: String, m: Map<&2, String>) -> K(Unit):
  st => K.set_tp.go(k, m, st)

def K.gid.go(st: Ks) -> KR<U32>:
  match st:
    case Ks{tl, ct, tp, rs, +g, fs, hols}:
      KOk{(g + 1 : U32), Ks{tl, ct, tp, rs, (g + 1 : U32), fs, hols}}

# a fresh kind tag
def K.gid() -> K(U32):
  st => K.gid.go(st)

def K.rs_swap.go(m: Map<&2, Bool>, st: Ks) -> KR<Map<&2, Bool>>:
  match st:
    case Ks{tl, ct, tp, rs, g, fs, hols}:
      KOk{rs, Ks{tl, ct, tp, m, g, fs, hols}}

# the names so far, m in their place
def K.rs_swap(m: Map<&2, Bool>) -> K(Map<&2, Bool>):
  st => K.rs_swap.go(m, st)

def K.quiet.go(rs0: Map<&2, Bool>, r: KR<KV>) -> KR<KV>:
  match r:
    case KOk{v, Ks{tl, ct, tp, rs, g, fs, hols}}:
      KOk{v, Ks{tl, ct, tp, rs0, g, fs, hols}}
    case KErr{e}:
      KErr{e}

def K.quiet.at(m: K(KV), st: Ks) -> KR<KV>:
  match st:
    case Ks{tl, ct, tp, +rs, g, fs, hols}:
      K.quiet.go(rs, m(Ks{tl, ct, tp, rs, g, fs, hols}))

# m, its names dropped: a premise whose elaborated term bend.ts drops
def K.quiet(m: K(KV)) -> K(KV):
  st => K.quiet.at(m, st)

def K.hols.go(st: Ks) -> KR<Unit>:
  match st:
    case Ks{tl, ct, tp, rs, g, fs, hols}:
      KOk{Unit{}, Ks{tl, ct, tp, rs, g, fs, (hols + 1 : U32)}}

# book.hols += 1
def K.hol() -> K(Unit):
  st => K.hols.go(st)

# Names (term_refs)
# -----------------

def hb.vals(bs: List<&2, H.HB>) -> List<&2, H.H>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{H.HB{k, i, q, v}, t}:
      v <> hb.vals(t)

def rs.put(m: Map<&2, Bool>, k: String) -> Map<&2, Bool>:
  Map.set(&2, Bool, m, k, True{})

# the names in the first-order part of the terms hs (a binder's closure is
# a JS function there, which term_refs does not enter)
def rs.go(fuel: Nat, hs: List<&2, H.H>, m: Map<&2, Bool>) -> Map<&2, Bool>:
  match fuel hs:
    case 0n _:
      m
    case _ Nil{}:
      m
    case 1n+f Con{h, r}:
      match h:
        case H.HRef{k, s, b}:
          rs.go(f, r, rs.put(m, k))
        case H.HAdt{k, xs, rr, s}:
          rs.go(f, List.append(&2, H.H, xs, r), rs.put(m, k))
        case H.HVal{k, i, s, v}:
          rs.go(f, v <> r, m)
        case H.HLet{bs, cl, s}:
          rs.go(f, List.append(&2, H.H, hb.vals(bs), r), m)
        case H.HTyp{g, s}:
          rs.go(f, g <> r, m)
        case H.HMin{a, b, s}:
          rs.go(f, a <> b <> r, m)
        case H.HAll{q, k, i, A, cl, s}:
          rs.go(f, A <> r, m)
        case H.HApp{a, x, s}:
          rs.go(f, a <> x <> r, m)
        case H.HCtr{k, xs, s}:
          rs.go(f, List.append(&2, H.H, xs, r), m)
        case H.HMat{k, a, b, s}:
          rs.go(f, a <> b <> r, m)
        case H.HEql{a, b, A, s}:
          rs.go(f, a <> b <> A <> r, m)
        case H.HRwt{e, a, b, s}:
          rs.go(f, e <> a <> b <> r, m)
        case H.HAnn{x, A, s}:
          rs.go(f, x <> A <> r, m)
        case _:
          rs.go(f, r, m)

def rs.of(h: H.H, m: Map<&2, Bool>) -> Map<&2, Bool>:
  rs.go(4294967295n, [h], m)

def K.ref.go(h: H.H, st: Ks) -> KR<Unit>:
  match st:
    case Ks{tl, ct, tp, rs, g, fs, hols}:
      KOk{Unit{}, Ks{tl, ct, tp, rs.of(h, rs), g, fs, hols}}

# an elaborated node's type, in its share cell
def K.ref(h: H.H) -> K(Unit):
  st => K.ref.go(h, st)

def K.refk.go(k: String, st: Ks) -> KR<Unit>:
  match st:
    case Ks{tl, ct, tp, rs, g, fs, hols}:
      KOk{Unit{}, Ks{tl, ct, tp, rs.put(rs, k), g, fs, hols}}

# an elaborated Ref or ADT node's name
def K.refk(k: String) -> K(Unit):
  st => K.refk.go(k, st)

# The book's entries
# ------------------

def td.is_def(t: W.Td) -> Bool:
  match t:
    case W.TdDef{n, x, T, v, b, u, ffi, l, rs}:
      True{}
    case _:
      False{}

def td.is_adt(t: W.Td) -> Bool:
  match t:
    case W.TdAdt{n, g, T, c, b}:
      True{}
    case _:
      False{}

def td.x(t: W.Td) -> U32:
  match t:
    case W.TdDef{n, x, T, v, b, u, ffi, l, rs}:
      x
    case _:
      0

def td.T(t: W.Td) -> H.H:
  match t:
    case W.TdDef{n, x, T, v, b, u, ffi, l, rs}:
      T
    case W.TdAdt{n, g, T, c, b}:
      T
    case W.TdNo{}:
      H.HHol{"bendbis: td.T", C.NoSp{}}

def td.v(t: W.Td) -> H.H:
  match t:
    case W.TdDef{n, x, T, Some{v}, b, u, ffi, l, rs}:
      v
    case _:
      H.HHol{"bendbis: td.v", C.NoSp{}}

def td.has_v(t: W.Td) -> Bool:
  match t:
    case W.TdDef{n, x, T, Some{v}, b, u, ffi, l, rs}:
      True{}
    case _:
      False{}

def td.b(t: W.Td) -> Bool:
  match t:
    case W.TdDef{n, x, T, v, b, u, ffi, l, rs}:
      b
    case W.TdAdt{n, g, T, c, b}:
      b
    case W.TdNo{}:
      False{}

def td.u(t: W.Td) -> Bool:
  match t:
    case W.TdDef{n, x, T, v, b, u, ffi, l, rs}:
      u
    case _:
      False{}

def td.ffi(t: W.Td) -> Bool:
  match t:
    case W.TdDef{n, x, T, v, b, u, ffi, l, rs}:
      ffi
    case _:
      False{}

# a def with no body yet, not foreign
def td.bodiless(t: W.Td) -> Bool:
  match t:
    case W.TdDef{n, x, T, None{}, b, u, ffi, l, rs}:
      Bool.not(ffi)
    case _:
      False{}

def td.is_no(t: W.Td) -> Bool:
  match t:
    case W.TdNo{}:
      True{}
    case _:
      False{}

def td.has(m: Map<&2, W.Td>, +k: String) -> Bool:
  Bool.not(td.is_no(W.td.get(m, k)))

def cr.k(c: W.Cr) -> String:
  match c:
    case W.Cr{k, n, T, f}:
      k

def cr.n(c: W.Cr) -> U32:
  match c:
    case W.Cr{k, n, T, f}:
      n

def cr.T(c: W.Cr) -> H.H:
  match c:
    case W.Cr{k, n, T, f}:
      T

def cr.f(c: W.Cr) -> String:
  match c:
    case W.Cr{k, n, T, f}:
      f

def cr.has(cs: List<&2, W.Cr>, +k: String) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{W.Cr{j, n, T, f}, t}:
      Bool.or(String.eq(j, k), cr.has(t, k))

def cr.get(cs: List<&2, W.Cr>, +k: String) -> W.Cr:
  match cs:
    case Nil{}:
      W.Cr{"", 0, H.HEfq{C.NoSp{}}, ""}
    case Con{W.Cr{+j, n, T, f}, t}:
      Bool.pick(W.Cr, String.eq(j, k), W.Cr{j, n, T, f}, cr.get(t, k))

# the constructors not in r
def cr.keep(z: Bool, c: W.Cr, rest: List<&2, W.Cr>) -> List<&2, W.Cr>:
  match z:
    case True{}:
      rest
    case False{}:
      c <> rest

def cr.drop(cs: List<&2, W.Cr>, +r: List<&2, String>) -> List<&2, W.Cr>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{W.Cr{+j, n, T, f}, t}:
      cr.keep(W.strs.has(r, j), W.Cr{j, n, T, f}, cr.drop(t, r))

def cr.names(cs: List<&2, W.Cr>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{W.Cr{j, n, T, f}, Nil{}}:
      S.name.key(j)
    case Con{W.Cr{j, n, T, f}, t}:
      S.name.key(j) ++ ", " ++ cr.names(t)

def ct.has(m: Map<&2, W.Cr>, +k: String) -> Bool:
  Pair.snd(Map<&2, W.Cr>, Bool, Map.has(&2, W.Cr, m, k))

def ct.get(m: Map<&2, W.Cr>, +k: String) -> W.Cr:
  Pair.snd(Map<&2, W.Cr>, W.Cr, Map.get(W.Cr, W.Cr{"", 0, H.HEfq{C.NoSp{}}, ""}, m, k))

# Terms read off a computed value
# -------------------------------

def h.is_all(t: H.H) -> Bool:
  match t:
    case H.HAll{q, k, i, A, cl, s}:
      True{}
    case _:
      False{}

def h.all.q(t: H.H) -> C.Q:
  match t:
    case H.HAll{q, k, i, A, cl, s}:
      q
    case _:
      C.QL{}

def h.all.k(t: H.H) -> String:
  match t:
    case H.HAll{q, k, i, A, cl, s}:
      k
    case _:
      "_"

def h.all.i(t: H.H) -> U32:
  match t:
    case H.HAll{q, k, i, A, cl, s}:
      i
    case _:
      0

def h.all.A(t: H.H) -> H.H:
  match t:
    case H.HAll{q, k, i, A, cl, s}:
      A
    case _:
      H.HEfq{C.NoSp{}}

def h.all.cl(t: H.H) -> H.Cl:
  match t:
    case H.HAll{q, k, i, A, cl, s}:
      cl
    case _:
      H.ClK{H.HEfq{C.NoSp{}}}

def h.is_adt(t: H.H) -> Bool:
  match t:
    case H.HAdt{k, x, r, s}:
      True{}
    case _:
      False{}

def h.adt.k(t: H.H) -> String:
  match t:
    case H.HAdt{k, x, r, s}:
      k
    case _:
      ""

def h.adt.x(t: H.H) -> List<&2, H.H>:
  match t:
    case H.HAdt{k, x, r, s}:
      x
    case _:
      Nil{}

def h.adt.r(t: H.H) -> List<&2, String>:
  match t:
    case H.HAdt{k, x, r, s}:
      r
    case _:
      Nil{}

def h.is_eql(t: H.H) -> Bool:
  match t:
    case H.HEql{a, b, T, s}:
      True{}
    case _:
      False{}

def h.eql.a(t: H.H) -> H.H:
  match t:
    case H.HEql{a, b, T, s}:
      a
    case _:
      H.HEfq{C.NoSp{}}

def h.eql.b(t: H.H) -> H.H:
  match t:
    case H.HEql{a, b, T, s}:
      b
    case _:
      H.HEfq{C.NoSp{}}

def h.eql.T(t: H.H) -> H.H:
  match t:
    case H.HEql{a, b, T, s}:
      T
    case _:
      H.HEfq{C.NoSp{}}

def h.is_mat(t: H.H) -> Bool:
  match t:
    case H.HMat{k, h, m, s}:
      True{}
    case _:
      False{}

def h.is_ctr(t: H.H) -> Bool:
  match t:
    case H.HCtr{k, x, s}:
      True{}
    case _:
      False{}

def h.ctr.k(t: H.H) -> String:
  match t:
    case H.HCtr{k, x, s}:
      k
    case _:
      ""

def h.is_sigma(t: H.H) -> Bool:
  match t:
    case H.HAdt{k, x, r, s}:
      String.eq(k, "Sigma")
    case _:
      False{}

def hs.len(xs: List<&2, H.H>) -> U32:
  U32.from_nat(List.length(&2, H.H, xs))

def hs.drop(xs: List<&2, H.H>, n: U32) -> List<&2, H.H>:
  List.drop(&2, H.H, xs, U32.to_nat(n))

def hs.take(xs: List<&2, H.H>, n: U32) -> List<&2, H.H>:
  List.take(&2, H.H, xs, U32.to_nat(n))

# xs.reduce((f, a) => term_apply(f, a), f)
def hs.apply.go(xs: List<&2, H.H>, f: H.H) -> H.H:
  match xs:
    case Nil{}:
      f
    case Con{x, t}:
      hs.apply.go(t, W.ap(f, x, C.NoSp{}))

def hs.apply(f: H.H, xs: List<&2, H.H>) -> H.H:
  hs.apply.go(xs, f)

# term_unapply(t)[1]
def h.args.go(t: H.H, acc: List<&2, H.H>) -> List<&2, H.H>:
  match t:
    case H.HApp{f, x, s}:
      h.args.go(f, x <> acc)
    case _:
      acc

def h.args(t: H.H) -> List<&2, H.H>:
  h.args.go(t, Nil{})

# term_lower(t, d)
def low.of(r: H.HR) -> C.Tm:
  match r:
    case H.HRT{t}:
      t
    case _:
      C.THol{"bendbis: term_lower failed", C.NoSp{}}

def low(h: H.H, d: U32) -> C.Tm:
  low.of(H.hm.go(W.FUEL(), Nil{}, H.JL{h, d}))

# term_descend
# ------------

type Cm is Data:
  CmEQ{}
  CmLT{}
  CmGT{}

def cm.is_eq(c: Cm) -> Bool:
  match c:
    case CmEQ{}:
      True{}
    case _:
      False{}

def cm.is_gt(c: Cm) -> Bool:
  match c:
    case CmGT{}:
      True{}
    case _:
      False{}

def cm.is_lt(c: Cm) -> Bool:
  match c:
    case CmLT{}:
      True{}
    case _:
      False{}

# a descent to make: term_descend(q, a, p), its Ctr case's field loop (the
# fields of a and p, the order so far, the index), or its second loop
# (does a descend, not GT, into a field of p other than bad's)
type Dj is Data:
  DjOne{q: C.Q, a: H.H, p: H.H}
  DjCol{s: H.H, pc: H.H}
  DjCol2{pc: H.H, x: H.H}
  DjCtr{z: Bool, a: H.H, p: H.H}
  DjFlds{as: List<&2, H.H>, ps: List<&2, H.H>, ord: Cm, j: U32, a: H.H, pall: List<&2, H.H>}
  DjFld{fld: Cm, as: List<&2, H.H>, ps: List<&2, H.H>, ord: Cm, j: U32, a: H.H, pall: List<&2, H.H>}
  DjAny{a: H.H, ps: List<&2, H.H>, j: U32, bad: U32}
  DjAnyS{skip: Bool, a: H.H, y: H.H, ps: List<&2, H.H>, j: U32, bad: U32}
  DjAny2{r: Cm, a: H.H, ps: List<&2, H.H>, j: U32, bad: U32}

def ctr.same(a: H.H, p: H.H) -> Bool:
  match a p:
    case H.HCtr{+k1, +x1, s1} H.HCtr{+k2, +x2, s2}:
      Bool.and(String.eq(k1, k2), U32.is_eq(hs.len(x1), hs.len(x2)))
    case _ _:
      False{}

def h.ctr.x(t: H.H) -> List<&2, H.H>:
  match t:
    case H.HCtr{k, x, s}:
      x
    case _:
      Nil{}

def desc.go(+fuel: Nat, j: Dj) -> Cm:
  match fuel j:
    case 0n _:
      CmGT{}
    case 1n+f DjOne{q, a, p}:
      match q:
        case C.QN{}:
          CmEQ{}
        case _:
          desc.go(f, DjCol{H.h.strip(a), H.h.strip(p)})
    case 1n+f DjCol{+s, +pc}:
      desc.go(f, DjCol2{pc, Bool.pick(H.H, Bool.and(W.is.lit(s), W.is.ctr(pc)), W.lit_step(s), s)})
    case 1n+f DjCol2{pc, +x}:
          match pc:
            case H.HVar{k, +i, u}:
              match x:
                case H.HVar{k2, +i2, u2}:
                  Bool.pick(Cm, U32.is_eq(i, i2), CmEQ{}, CmGT{})
                case H.HVal{k2, +i2, u2, v2}:
                  Bool.pick(Cm, U32.is_eq(i, i2), CmEQ{}, CmGT{})
                case _:
                  CmGT{}
            case H.HVal{k, +i, u, v}:
              match x:
                case H.HVar{k2, +i2, u2}:
                  Bool.pick(Cm, U32.is_eq(i, i2), CmEQ{}, CmGT{})
                case H.HVal{k2, +i2, u2, v2}:
                  Bool.pick(Cm, U32.is_eq(i, i2), CmEQ{}, CmGT{})
                case _:
                  CmGT{}
            case H.HCtr{+k, +xs, +u}:
              desc.go(f, DjCtr{ctr.same(x, H.HCtr{k, xs, u}), x, H.HCtr{k, xs, u}})
            case _:
              CmGT{}
    case 1n+f DjCtr{z, +a, +p}:
      match z:
        case True{}:
          desc.go(f, DjFlds{h.ctr.x(a), h.ctr.x(p), CmEQ{}, 0, a, h.ctr.x(p)})
        case False{}:
          desc.go(f, DjAny{a, h.ctr.x(p), 0, C.NONE()})
    case 1n+f DjFlds{as, ps, ord, +j, +a, +pall}:
      match as ps:
        case Con{x, xt} Con{y, yt}:
          desc.go(f, DjFld{desc.go(f, DjOne{C.QL{}, x, y}), xt, yt, ord, j, a, pall})
        case _ _:
          ord
    case 1n+f DjFld{+fld, as, ps, ord, +j, a, pall}:
      match fld:
        case CmGT{}:
          desc.go(f, DjAny{a, pall, 0, j})
        case CmEQ{}:
          desc.go(f, DjFlds{as, ps, ord, (j + 1 : U32), a, pall})
        case _:
          desc.go(f, DjFlds{as, ps, fld, (j + 1 : U32), a, pall})
    case 1n+f DjAny{+a, ps, +j, +bad}:
      match ps:
        case Nil{}:
          CmGT{}
        case Con{y, yt}:
          desc.go(f, DjAnyS{U32.is_eq(j, bad), a, y, yt, j, bad})
    case 1n+f DjAnyS{skip, +a, y, yt, +j, +bad}:
      match skip:
        case True{}:
          desc.go(f, DjAny{a, yt, (j + 1 : U32), bad})
        case False{}:
          desc.go(f, DjAny2{desc.go(f, DjOne{C.QL{}, a, y}), a, yt, j, bad})
    case 1n+f DjAny2{r, a, ps, +j, bad}:
      match r:
        case CmGT{}:
          desc.go(f, DjAny{a, ps, (j + 1 : U32), bad})
        case _:
          CmLT{}

def desc(q: C.Q, a: H.H, p: H.H) -> Cm:
  desc.go(4294967295n, DjOne{q, a, p})

def q.first(qs: List<&2, C.Q>) -> C.Q:
  match qs:
    case Con{q, t}:
      q
    case Nil{}:
      C.QL{}

def desc.cols.go(xs: List<&2, H.H>, cols: List<&2, H.H>, ord: Cm, +qs: List<&2, C.Q>) -> Cm:
  match xs cols ord:
    case Con{x, xt} Con{c, ct} CmEQ{}:
      desc.cols.go(xt, ct, desc(q.first(qs), x, c), List.tail(&2, C.Q, qs))
    case _ _ ord:
      ord

# infer-ref's descent: the arguments against the lhs columns, left to
# right, while EQ
def desc.cols(qs: List<&2, C.Q>, xs: List<&2, H.H>, cols: List<&2, H.H>) -> Cm:
  desc.cols.go(xs, cols, CmEQ{}, qs)

# term_key
# --------

type Tj is Data:
  TjT{t: C.Tm}
  TjL{ts: List<&2, C.Tm>}

def js.hex.go(+n: U32, +k: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      +d = ((n >> Nat.mul(m, 4n) : U32) .&. 15 : U32)
      Bool.pick(String, U32.is_lt(d, 10), U32.show(d), String.from_list([Chr{(d + 87 : U32)}])) ++ js.hex.go(n, m)

def js.u(+n: U32) -> String:
  "\\u" ++ js.hex.go(n, 4n)

# JSON.stringify's escapes for a string's units (a lone surrogate as \u)
def js.next.lo(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{+c, t}:
      Bool.and(U32.is_ge(c, 56320), U32.is_lt(c, 57344))
    case Nil{}:
      False{}

def js.esc(xs: List<&2, U32>, prev: Bool) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+c, +t}:
      +hi = Bool.and(U32.is_ge(c, 55296), U32.is_lt(c, 56320))
      +lo = Bool.and(U32.is_ge(c, 56320), U32.is_lt(c, 57344))
      +nlo = js.next.lo(t)
      Bool.pick(String, U32.is_eq(c, 34), "\\\"",
      Bool.pick(String, U32.is_eq(c, 92), "\\\\",
      Bool.pick(String, U32.is_eq(c, 8), "\\b",
      Bool.pick(String, U32.is_eq(c, 12), "\\f",
      Bool.pick(String, U32.is_eq(c, 10), "\\n",
      Bool.pick(String, U32.is_eq(c, 13), "\\r",
      Bool.pick(String, U32.is_eq(c, 9), "\\t",
      Bool.pick(String, U32.is_lt(c, 32), js.u(c),
      Bool.pick(String, Bool.and(hi, Bool.not(nlo)), js.u(c),
      Bool.pick(String, Bool.and(lo, Bool.not(prev)), js.u(c), T.str([c])))))))))))
      ++ js.esc(t, Bool.and(hi, nlo))

def js.str(s: String) -> String:
  "\"" ++ js.esc(T.units(s), False{}) ++ "\""

def js.q(q: C.Q) -> String:
  match q:
    case C.QN{}:
      "{\"$\":\"None\"}"
    case C.QL{}:
      "{\"$\":\"Lone\"}"
    case C.QM{}:
      "{\"$\":\"Many\"}"

def js.int(+i: U32) -> String:
  S.int.show(i)

def js.strs(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, Nil{}}:
      js.str(x)
    case Con{x, t}:
      js.str(x) ++ "," ++ js.strs(t)

def js.bnd.k(bs: List<&2, C.Bnd>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{C.Bnd{k, i, q, v}, t}:
      k <> js.bnd.k(t)

def js.bnd.i(bs: List<&2, C.Bnd>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{C.Bnd{k, +i, q, v}, Nil{}}:
      js.int(i)
    case Con{C.Bnd{k, +i, q, v}, t}:
      js.int(i) ++ "," ++ js.bnd.i(t)

def js.bnd.q(bs: List<&2, C.Bnd>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{C.Bnd{k, i, q, v}, Nil{}}:
      js.q(q)
    case Con{C.Bnd{k, i, q, v}, t}:
      js.q(q) ++ "," ++ js.bnd.q(t)

def js.lit(+k: String, v: String) -> String:
  "{\"$\":\"Lit\",\"k\":\"" ++ k ++ "\",\"v\":" ++ v ++ "}"

def js.go(+fuel: Nat, j: Tj) -> String:
  match fuel j:
    case 0n _:
      "..."
    case 1n+f TjL{ts}:
      match ts:
        case Nil{}:
          ""
        case Con{t, Nil{}}:
          js.go(f, TjT{t})
        case Con{t, r}:
          js.go(f, TjT{t}) ++ "," ++ js.go(f, TjL{r})
    case 1n+f TjT{t}:
      match t:
        case C.TVar{k, +i, s}:
          "{\"$\":\"Var\",\"k\":" ++ js.str(k) ++ ",\"i\":" ++ js.int(i) ++ "}"
        case C.TVr{k, +i, s, r}:
          "{\"$\":\"Var\",\"k\":" ++ js.str(k) ++ ",\"i\":" ++ js.int(i) ++ "}"
        case C.TRef{k, s, b}:
          "{\"$\":\"Ref\",\"k\":" ++ js.str(k) ++ Bool.pick(String, b, ",\"b\":true", "") ++ "}"
        case C.TSub{i, v, b, s}:
          js.go(f, TjT{b})
        case C.TLet{+bs, b, s}:
          "{\"$\":\"Let\",\"k\":[" ++ js.strs(js.bnd.k(bs)) ++ "],\"i\":[" ++ js.bnd.i(bs) ++ "],\"q\":[" ++ js.bnd.q(bs) ++ "],\"v\":[" ++ js.go(f, TjL{C.bnd.vals(bs)}) ++ "],\"f\":" ++ js.go(f, TjT{b}) ++ "}"
        case C.TTyp{g, s}:
          "{\"$\":\"Typ\",\"g\":" ++ js.go(f, TjT{g}) ++ "}"
        case C.TQnt{s}:
          "{\"$\":\"Qnt\"}"
        case C.TQua{q, s}:
          "{\"$\":\"Qua\",\"q\":" ++ js.q(q) ++ "}"
        case C.TMin{a, b, s}:
          "{\"$\":\"Min\",\"a\":" ++ js.go(f, TjT{a}) ++ ",\"b\":" ++ js.go(f, TjT{b}) ++ "}"
        case C.TAll{q, k, +i, A, B, s}:
          "{\"$\":\"All\",\"q\":" ++ js.q(q) ++ ",\"k\":" ++ js.str(k) ++ ",\"i\":" ++ js.int(i) ++ ",\"A\":" ++ js.go(f, TjT{A}) ++ ",\"B\":" ++ js.go(f, TjT{B}) ++ "}"
        case C.TLam{k, +i, b, s, q}:
          "{\"$\":\"Lam\",\"k\":" ++ js.str(k) ++ ",\"i\":" ++ js.int(i) ++ ",\"f\":" ++ js.go(f, TjT{b}) ++ ",\"q\":" ++ js.q(q) ++ "}"
        case C.TApp{a, x, s}:
          "{\"$\":\"App\",\"f\":" ++ js.go(f, TjT{a}) ++ ",\"x\":" ++ js.go(f, TjT{x}) ++ "}"
        case C.TAdt{k, xs, r, s}:
          "{\"$\":\"ADT\",\"k\":" ++ js.str(k) ++ ",\"x\":[" ++ js.go(f, TjL{xs}) ++ "],\"r\":[" ++ js.strs(r) ++ "]}"
        case C.TCtr{k, xs, s}:
          "{\"$\":\"Ctr\",\"k\":" ++ js.str(k) ++ ",\"x\":[" ++ js.go(f, TjL{xs}) ++ "]}"
        case C.TNat{+v, s}:
          js.lit("Nat", U32.show(v))
        case C.TU32{+v, s}:
          js.lit("U32", U32.show(v))
        case C.TF32{+v, s}:
          js.lit("F32", U32.show(v))
        case C.TStr{v, s}:
          js.lit("String", "\"" ++ js.esc(v, False{}) ++ "\"")
        case C.TMat{k, h, m, s}:
          "{\"$\":\"Mat\",\"k\":" ++ js.str(k) ++ ",\"h\":" ++ js.go(f, TjT{h}) ++ ",\"m\":" ++ js.go(f, TjT{m}) ++ "}"
        case C.TEfq{s}:
          "{\"$\":\"Efq\"}"
        case C.TEql{a, b, A, s}:
          "{\"$\":\"Eql\",\"a\":" ++ js.go(f, TjT{a}) ++ ",\"b\":" ++ js.go(f, TjT{b}) ++ ",\"T\":" ++ js.go(f, TjT{A}) ++ "}"
        case C.TRfl{s}:
          "{\"$\":\"Rfl\"}"
        case C.TRwt{e, a, b, s}:
          "{\"$\":\"Rwt\",\"e\":" ++ js.go(f, TjT{e}) ++ ",\"p\":" ++ js.go(f, TjT{a}) ++ ",\"f\":" ++ js.go(f, TjT{b}) ++ "}"
        case C.THol{k, s}:
          "{\"$\":\"Hol\",\"k\":" ++ js.str(k) ++ "}"
        case C.TAnn{x, A, s}:
          "{\"$\":\"Ann\",\"x\":" ++ js.go(f, TjT{x}) ++ ",\"T\":" ++ js.go(f, TjT{A}) ++ "}"

def tkey.go(xs: List<&2, H.H>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, Nil{}}:
      js.go(4294967295n, TjT{low(x, 0)})
    case Con{x, t}:
      js.go(4294967295n, TjT{low(x, 0)}) ++ "\n" ++ tkey.go(t)

# xs.map((a) => term_key(term_lower(a))).join("\n")
def tkey(xs: List<&2, H.H>) -> String:
  tkey.go(xs)

# Rules read as helpers (no premise to check)
# -------------------------------------------

# a do block's note at an unknown k.pure or k.bind
def do.note.at(+fl: S.Fl, +k: String, +n: Nat) -> Maybe<&2, String>:
  +e = S.name.show(fl, String.take(k, n))
  Some{"Note: a do block on " ++ e ++ " calls " ++ e ++ ".bind and " ++ e ++ ".pure"}

def do.note.if(z: Bool, +fl: S.Fl, +k: String, +n: Nat) -> Maybe<&2, String>:
  match z:
    case True{}:
      do.note.at(fl, k, Nat.sub(n, 5n))
    case False{}:
      None{}

def do.note(+fl: S.Fl, +k: String) -> Maybe<&2, String>:
  +n = String.length(k)
  do.note.if(Bool.and(Nat.is_gt(n, 5n), Bool.or(String.ends_with(k, ".pure"), String.ends_with(k, ".bind"))), fl, k, n)

# infer-var, its binder found (or not)
def ivar(a: Maybe<&2, An>, +tm: H.H, +i: U32, qt: C.Q, ctx: Cx, +dn: String) -> K(KV):
  match a:
    case None{}:
      K.err(KV, ctx, ExS{"a bound variable"}, Some{ExH{tm}}, H.h.s(tm), Some{dn}, None{}, 0)
    case Some{An{q, k, +A}}:
      do K<KV>:
        K.ref(A)
        return VI{A, us.one(i, qt), 0, EsNo{}}

# infer-ref's end: a family head errs, else the ref (k, or its instance o)
def iret(+o: String, +x: U32, +td: W.Td, +k: String, +s: C.Sp, +b: Bool, ctx: Cx, +dn: String) -> K(KV):
  K.if(KV, Bool.and(td.is_adt(td), U32.is_gt(W.td.n(td), 0)),
    K.err(KV, ctx, ExS{"a family instance (write " ++ S.name.key(k) ++ "<..>)"}, Some{ExH{H.HRef{k, s, b}}}, s, Some{dn}, None{}, 0),
    st => (do K<KV>:
      +bk : Map<&2, W.Td> <- K.tl()
      +A : H.H = td.T(W.td.get(bk, o))
      K.refk(o)
      K.ref(A)
      return VI{A, UsTip{}, x, EsRef{o}})(st))

# infer-ref's descent, at a self-call (o is the def being checked)
def iref3(+o: String, +x: U32, +xs: List<&2, H.H>, +td: W.Td, +k: String, +s: C.Sp, +b: Bool, +ctx: Cx, +lhs: Lhs) -> K(KV):
  K.if(KV, Bool.and(String.eq(o, lhs.dn(lhs)), Bool.not(lhs.u(lhs))),
    st => K.if(KV, cm.is_lt(desc.cols(lhs.qs(lhs), xs, h.args(lhs.t(lhs)))),
      st2 => iret(o, x, td, k, s, b, ctx, lhs.dn(lhs), st2),
      st2 => (do K<KV>:
        +fl : S.Fl <- K.fl(s)
        +bnd : List<&2, String> = cx.scope(ctx)
        +n : U32 = U32.from_nat(List.length(&2, String, bnd))
        +rb : List<&2, String> = List.reverse(&2, String, bnd)
        +exp : String = "a call smaller than " ++ S.term.show(fl, low(lhs.t(lhs), n), 0, rb) ++ " (arguments are read left to right: each passed unchanged until one shrinks)"
        K.err(KV, ctx, ExS{exp}, Some{ExS{S.term.show(fl, low(hs.apply(H.HRef{o, s, False{}}, xs), n), 0, rb)}}, s, Some{lhs.dn(lhs)}, None{}, 0))(st2), st),
    st => iret(o, x, td, k, s, b, ctx, lhs.dn(lhs), st))

# infer-err: a term with no rule to infer it
def ierr(+tm: H.H, +ct: Map<&2, W.Cr>, ctx: Cx, dn: String) -> K(KV):
  +t = W.lit_step(tm)
  +ex : String = Bool.pick(String, Bool.and(h.is_ctr(t), Bool.not(ct.has(ct, h.ctr.k(t)))), "a declared constructor", "an annotated term (cannot infer)")
  K.err(KV, ctx, ExS{ex}, Some{ExH{tm}}, H.h.s(tm), Some{dn}, None{}, 0)

# book_adt
def kadt(td: W.Td, +k: String, r: List<&2, String>, +s: C.Sp, +ctx: Cx, +dn: Maybe<&2, String>) -> K(KV):
  match td:
    case W.TdAdt{n, g, T, c, b}:
      K.pure(KV, VA{n, T, cr.drop(c, r)})
    case W.TdNo{}:
      do K<KV>:
        +fl : S.Fl <- K.fl(s)
        K.err(KV, ctx, ExS{"a declared datatype (unknown: " ++ S.name.show(fl, k) ++ ")"}, None{}, s, dn, None{}, 0)
    case W.TdDef{+n, x, T, v, b, u, ffi, l, rs}:
      do K<KV>:
        +fl : S.Fl <- K.fl(s)
        +ks : String = S.name.show(fl, k)
        K.err(KV, ctx, ExS{"a declared datatype"}, None{}, s, dn, Some{"Note: " ++ ks ++ " is a def" ++ Bool.pick(String, U32.is_eq(n, 0), " with no arguments: write it as " ++ ks, ": write its arguments as ()")}, 0)

# tele_head
def khead(+tel: H.H, +ctx: Cx, +dn: Maybe<&2, String>, +s: C.Sp) -> K(H.H):
  do K<H.H>:
    +w : W.W <- K.w()
    +t : H.H = W.wnf(w, tel)
    K.if(H.H, h.is_all(t), K.pure(H.H, t), K.err(H.H, ctx, ExS{"unreachable (a telescope binds its parameters and fields)"}, None{}, s, dn, None{}, 0))

# tele_fill
def kfill(xs: List<&2, H.H>, +tel: H.H, +ctx: Cx, +dn: Maybe<&2, String>, +s: C.Sp) -> K(H.H):
  match xs:
    case Nil{}:
      K.pure(H.H, tel)
    case Con{+x, t}:
      do K<H.H>:
        +a : H.H <- khead(tel, ctx, dn, s)
        +w : W.W <- K.w()
        kfill(t, W.apc(W.w.real(w), h.all.cl(a), x), ctx, dn, s)

def uses.close.at(+o: Maybe<&2, C.Q>, +us: Us, +ctx: Cx, +i: U32, +k: String, +q: C.Q, +s: C.Sp, +dn: String) -> K(Us):
  +u : C.Q = Maybe.default(&2, C.Q, o, C.QN{})
  +none : Bool = Bool.not(Maybe.is_some(&2, C.Q, o))
  K.if(Us, W.q.eq(C.q.join(u, q), q),
    K.pure(Us, Bool.pick(Us, none, us, us.set(us, i, C.QN{}))),
    K.err(Us, ctx, ExS{C.q.show(q) ++ k}, Some{ExS{Bool.pick(String, C.q.is_many(u), k ++ " (consumed more than once)", C.q.show(u) ++ k)}}, s, Some{dn}, None{}, 0))

# uses_close
def uses.close(+ctx: Cx, +us: Us, +i: U32, +k: String, +q: C.Q, +s: C.Sp, +dn: String) -> K(Us):
  uses.close.at(us.get(us, i), us, ctx, i, k, q, s, dn)

# check-let's closes, binder by binder
def uses.closes(bs: List<&2, H.HB>, +ctx: Cx, us: Us, +d: U32, +s: C.Sp, +dn: String) -> K(Us):
  match bs:
    case Nil{}:
      K.pure(Us, us)
    case Con{H.HB{k, i, q, v}, t}:
      do K<Us>:
        u2 : Us <- uses.close(ctx, us, d, k, q, s, dn)
        uses.closes(t, ctx, u2, (d + 1 : U32), s, dn)

# term_check_kind's catch: a miss at the kind itself reports at s
def ek.g(e: Ek) -> U32:
  match e:
    case Ek{bk, ctx, exp, obs, spn, dn, nte, g}:
      g

def kind.fix.go(z: Bool, e: Ek, q: C.Q, k: String, s: C.Sp) -> K(KV):
  match z e:
    case True{} Ek{bk, ctx, exp, obs, spn, dn, nte, g}:
      K.throw(KV, Ek{bk, ctx, exp, obs, C.sp.or(s, spn), dn, Bool.pick(Maybe<&2, String>, C.q.is_many(q), Some{"Note: +" ++ k ++ " can be used many times, so its type must be Data."}, None{}), g})
    case False{} e:
      K.throw(KV, e)

def kind.fix(+e: Ek, +gid: U32, q: C.Q, k: String, s: C.Sp) -> K(KV):
  kind.fix.go(U32.is_eq(ek.g(e), gid), e, q, k, s)

def obs.var(o: Maybe<&2, Ex>, +d: U32) -> Maybe<&2, String>:
  match o:
    case Some{ExH{H.HVar{k, +i, s}}}:
      Bool.pick(Maybe<&2, String>, U32.is_lt(i, d), Some{k}, None{})
    case Some{ExH{H.HVal{k, +i, s, v}}}:
      Bool.pick(Maybe<&2, String>, U32.is_lt(i, d), Some{k}, None{})
    case _:
      None{}

def inst.var.at(m: Maybe<&2, String>, e: Ek, k: String, +s: C.Sp, b: Bool, ctx: Cx, dn: String) -> K(KV):
  match m e:
    case Some{v} Ek{bk, c, exp, obs, spn, d, nte, g}:
      K.throw(KV, Ek{bk, ctx, ExS{"a template applied to closed ~ arguments (" ++ v ++ " is a variable here, not comptime: pass it at run time)"}, Some{ExH{H.HRef{k, s, b}}}, s, Some{dn}, None{}, 0})
    case None{} e:
      K.throw(KV, e)

# def_inst's catch: a miss that observes a variable of the caller's
def inst.var(e: Ek, k: String, s: C.Sp, b: Bool, ctx: Cx, +d: U32, dn: String) -> K(KV):
  match e:
    case Ek{bk, c, exp, +obs, spn, dd, nte, g}:
      inst.var.at(obs.var(obs, d), Ek{bk, c, exp, obs, spn, dd, nte, g}, k, s, b, ctx, dn)

# the first dt of [k, k's name after its last ':'] that is a datatype
def colon.last(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{Chr{58}, t}:
      colon.last(t, "")
    case SCon{c, t}:
      colon.last(t, SCon{c, acc})

def dt.find(+bk: Map<&2, W.Td>, +k: String) -> Maybe<&2, String>:
  +k2 = colon.last(k, "")
  Bool.pick(Maybe<&2, String>, td.is_adt(W.td.get(bk, k)), Some{k}, Bool.pick(Maybe<&2, String>, td.is_adt(W.td.get(bk, k2)), Some{k2}, None{}))

def dt.note(fam: Maybe<&2, String>, dt: Maybe<&2, String>) -> Maybe<&2, String>:
  match fam dt:
    case None{} Some{x}:
      Some{"Note: " ++ x ++ " is a datatype: write its arguments as <>"}
    case _ _:
      None{}

def fam.of(+ct: Map<&2, W.Cr>, +k: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, ct.has(ct, k), Some{cr.f(ct.get(ct, k))}, None{})

def fam.obs(fam: Maybe<&2, String>, s: C.Sp) -> Ex:
  match fam:
    case None{}:
      ExS{"non-inferrable term"}
    case Some{f}:
      ExH{H.HRef{f, s, False{}}}

# check-any's second note: Data where a pair's type is Sigma
def note.sigma.go(z: Bool, +w: W.W, +tm: H.H) -> Maybe<&2, String>:
  match z:
    case True{}:
      Bool.pick(Maybe<&2, String>, h.is_sigma(W.wnf(w, tm)), Some{"Note: A & B is Type. A pair that is Data is +Sigma<A, _ => B>."}, None{})
    case False{}:
      None{}

def note.sigma(+w: W.W, +ty: H.H, +tm: H.H) -> Maybe<&2, String>:
  note.sigma.go(String.eq(S.term.show(S.NoFl{}, W.snfl(w, ty, 0), 0, Nil{}), "Data"), w, tm)

def note.call.go(z: Bool, +w: W.W, +ty: H.H, +tm: H.H) -> Maybe<&2, String>:
  match z:
    case True{}:
      Some{"Note: this call is missing arguments."}
    case False{}:
      note.sigma(w, ty, tm)

def note.call(z: Bool, +w: W.W, +xty: H.H, +ty: H.H, +tm: H.H) -> Maybe<&2, String>:
  match z:
    case True{}:
      note.call.go(Bool.and(h.is_all(W.wnf(w, xty)), Bool.not(h.is_all(W.wnf(w, ty)))), w, ty, tm)
    case False{}:
      note.sigma(w, ty, tm)

def td.callable(t: W.Td) -> Bool:
  match t:
    case W.TdDef{n, x, T, v, b, u, ffi, l, rs}:
      Bool.not(ffi)
    case _:
      False{}

# check-any's note
def any.note.go(m: Maybe<&2, String>, +w: W.W, +bk: Map<&2, W.Td>, +xty: H.H, +ty: H.H, +tm: H.H) -> Maybe<&2, String>:
  match m:
    case Some{k}:
      note.call(td.callable(W.td.get(bk, k)), w, xty, ty, tm)
    case None{}:
      note.sigma(w, ty, tm)

def any.note(+w: W.W, +bk: Map<&2, W.Td>, es: Es, +xty: H.H, +ty: H.H, +tm: H.H) -> Maybe<&2, String>:
  any.note.go(es.name(es), w, bk, xty, ty, tm)

# let's values as the body reads them: Var(k, d + j) with its value
def let.xs(bs: List<&2, H.HB>, +d: U32) -> List<&2, H.H>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{H.HB{k, i, q, v}, t}:
      H.HVal{k, d, C.NoSp{}, v} <> let.xs(t, (d + 1 : U32))

def hbs.len(bs: List<&2, H.HB>) -> U32:
  U32.from_nat(List.length(&2, H.HB, bs))

# the parameter quantities of a def's type (tele_unbind's doms), from its whnf
def tele.qs.go(fuel: Nat, +w: W.W, t: H.H, +i: U32) -> List<&2, C.Q>:
  match fuel t:
    case 0n _:
      Nil{}
    case 1n+f H.HAll{q, +k, j, A, cl, s}:
      q <> tele.qs.go(f, w, W.wnf(w, W.apc(W.w.real(w), cl, H.HVar{k, i, C.NoSp{}})), (i + 1 : U32))
    case _ _:
      Nil{}

def tele.qs(+w: W.W, t: H.H) -> List<&2, C.Q>:
  tele.qs.go(4294967295n, w, W.wnf(w, t), 0)

def HTYPE(+s: C.Sp) -> H.H:
  H.HTyp{H.HQua{C.QL{}, C.NoSp{}}, s}

# The jobs
# --------

type KJ is Data:
  JInf{lhs: Lhs, tm: H.H, qt: C.Q, ctx: Cx, d: U32, sp: List<&2, H.H>}
  JIRef{td: W.Td, k: String, s: C.Sp, b: Bool, qt: C.Q, ctx: Cx, d: U32, sp: List<&2, H.H>, lhs: Lhs}
  JChk{lhs: Lhs, tm: H.H, qt: C.Q, ty: H.H, g: U32, ctx: Cx, d: U32}
  JLit{lk: String, tm: H.H, lhs: Lhs, qt: C.Q, ty: H.H, g: U32, ctx: Cx, d: U32}
  JMat{tm: H.H, s: C.Sp, lhs: Lhs, qt: C.Q, ty: H.H, g: U32, ctx: Cx, d: U32}
  JMat2{tm: H.H, s: C.Sp, tw: H.H, aw: H.H, rem: List<&2, W.Cr>, lhs: Lhs, qt: C.Q, ty: H.H, ctx: Cx, d: U32}
  JAny{tm: H.H, lhs: Lhs, qt: C.Q, ty: H.H, g: U32, ctx: Cx, d: U32}
  JLet{bs: List<&2, H.HB>, j: U32, us: Us, fctx: Cx, all: List<&2, H.HB>, cl: H.Cl, s: C.Sp, lhs: Lhs, qt: C.Q, ty: H.H, g: U32, ctx: Cx, d: U32}
  JTele{lhs: Lhs, tel: H.H, xs: List<&2, H.H>, qt: C.Q, ctx: Cx, d: U32, s: C.Sp, us: Us}
  JKind{lhs: Lhs, T: H.H, q: C.Q, k: String, ctx: Cx, d: U32, s: C.Sp}
  JDead{as: List<&2, An>, ctx: Cx}
  JInst{lhs: Lhs, k: String, s: C.Sp, b: Bool, td: W.Td, sp: List<&2, H.H>, ctx: Cx, d: U32}
  JDef{k: String, td: W.Td, z: U32}
  JDefT{j: U32, t: H.H, v: H.H, T: H.H, k: String, n: U32, qs: List<&2, C.Q>, u: Bool, z: U32}

def ck.go(+fuel: Nat, j: KJ) -> K(KV):
  match fuel j:
    case 0n _:
      K.raw(KV, "bendbis: the checker ran out of fuel")

    # term_infer
    case 1n+p JInf{+lhs, tm, +qt, +ctx, +d, +sp}:
      match tm:
        # infer-var
        case H.HVar{+k, +i, +s}:
          ivar(cx.get(ctx, i), H.HVar{k, i, s}, i, qt, ctx, lhs.dn(lhs))
        case H.HVal{+k, +i, +s, +v}:
          ivar(cx.get(ctx, i), H.HVal{k, i, s, v}, i, qt, ctx, lhs.dn(lhs))
        # infer-ref
        case H.HRef{+k, +s, +b}:
          do K<KV>:
            +bk : Map<&2, W.Td> <- K.tl()
            ck.go(p, JIRef{W.td.get(bk, k), k, s, b, qt, ctx, d, sp, lhs})
        # infer-typ
        case H.HTyp{g, +s}:
          do K<KV>:
            r : KV <- ck.go(p, JChk{lhs, g, C.QN{}, H.HQnt{s}, 0, ctx, d})
            return VI{HTYPE(s), UsTip{}, 0, EsNo{}}
        # infer-qnt
        case H.HQnt{+s}:
          K.pure(KV, VI{HTYPE(s), UsTip{}, 0, EsNo{}})
        case H.HQua{q, +s}:
          K.pure(KV, VI{H.HQnt{s}, UsTip{}, 0, EsNo{}})
        # infer-min
        case H.HMin{a, b, +s}:
          do K<KV>:
            +ac : KV <- ck.go(p, JChk{lhs, a, qt, H.HQnt{s}, 0, ctx, d})
            +bc : KV <- ck.go(p, JChk{lhs, b, qt, H.HQnt{s}, 0, ctx, d})
            return VI{H.HQnt{s}, us.add(kv.us(ac), kv.us(bc)), 0, EsNo{}}
        # infer-all
        case H.HAll{+q, +k, i, +A, +cl, +s}:
          do K<KV>:
            +bctx : Cx = cx.set(ctx, d, An{q, k, A})
            ac : KV <- ck.go(p, JKind{lhs, A, q, k, ctx, d, C.sp.or(H.h.s(A), s)})
            +w : W.W <- K.w()
            bc : KV <- ck.go(p, JChk{lhs, W.apc(W.w.real(w), cl, H.HVar{k, d, C.NoSp{}}), C.QN{}, HTYPE(s), 0, bctx, (d + 1 : U32)})
            return VI{HTYPE(s), UsTip{}, 0, EsNo{}}
        # infer-app
        case H.HApp{f, +x, +s}:
          do K<KV>:
            +fi : KV <- ck.go(p, JInf{lhs, f, qt, ctx, d, x <> sp})
            K.if(KV, U32.is_gt(kv.x(fi), 0),
              K.pure(KV, VI{kv.ty(fi), kv.us(fi), (kv.x(fi) - 1 : U32), kv.es(fi)}),
              st => (do K<KV>:
                +w : W.W <- K.w()
                +fw : H.H = W.wnf(w, kv.ty(fi))
                K.if(KV, h.is_all(fw),
                  st2 => (do K<KV>:
                    +xc : KV <- ck.go(p, JChk{lhs, x, C.q.dem(h.all.q(fw), qt), h.all.A(fw), 0, ctx, d})
                    +w2 : W.W <- K.w()
                    +B : H.H = W.apc(W.w.real(w2), h.all.cl(fw), x)
                    K.ref(B)
                    return VI{B, us.add(kv.us(fi), kv.us(xc)), 0, es.app(kv.es(fi))})(st2),
                  K.err(KV, ctx, ExS{"a function type"}, Some{ExH{kv.ty(fi)}}, s, Some{lhs.dn(lhs)}, None{}, 0)))(st))
        # infer-adt
        case H.HAdt{+k, +xs, +r, +s}:
          do K<KV>:
            +bk : Map<&2, W.Td> <- K.tl()
            +a : KV <- kadt(W.td.get(bk, k), k, r, s, ctx, Some{lhs.dn(lhs)})
            +n : U32 = kv.n(a)
            K.if(KV, U32.is_eq(hs.len(xs), n),
              st => (do K<KV>:
                +tc : KV <- ck.go(p, JTele{lhs, kv.T(a), xs, qt, ctx, d, s, UsTip{}})
                K.refk(k)
                K.ref(kv.ret(tc))
                return VI{kv.ret(tc), kv.us(tc), 0, EsNo{}})(st),
              K.err(KV, ctx, ExS{S.name.key(k) ++ " with " ++ U32.show(n) ++ Bool.pick(String, U32.is_eq(n, 1), " parameter", " parameters")}, Some{ExH{H.HAdt{k, xs, r, s}}}, s, Some{lhs.dn(lhs)}, None{}, 0))
        # infer-eql
        case H.HEql{a, b, +A, +s}:
          do K<KV>:
            tc : KV <- ck.go(p, JChk{lhs, A, C.QN{}, HTYPE(s), 0, ctx, d})
            ac : KV <- ck.go(p, JChk{lhs, a, C.QN{}, A, 0, ctx, d})
            bc : KV <- ck.go(p, JChk{lhs, b, C.QN{}, A, 0, ctx, d})
            return VI{H.HTyp{H.HQua{C.QM{}, C.NoSp{}}, s}, UsTip{}, 0, EsNo{}}
        # infer-ann
        case H.HAnn{x, +A, +s}:
          do K<KV>:
            tc : KV <- K.quiet(ck.go(p, JChk{lhs, A, C.QN{}, HTYPE(s), 0, ctx, d}))
            +xc : KV <- ck.go(p, JChk{lhs, x, qt, A, 0, ctx, d})
            return VI{A, kv.us(xc), 0, kv.es(xc)}
        # infer-err
        case t:
          do K<KV>:
            +ct : Map<&2, W.Cr> <- K.ct()
            ierr(t, ct, ctx, lhs.dn(lhs))

    # infer-ref, k's entry read
    case 1n+p JIRef{+td, +k, +s, +b, +qt, +ctx, +d, +sp, +lhs}:
      match td:
        case W.TdNo{}:
          do K<KV>:
            +fl : S.Fl <- K.fl(s)
            K.err(KV, ctx, ExS{"a defined name"}, Some{ExH{H.HRef{k, s, b}}}, s, Some{lhs.dn(lhs)}, do.note(fl, k), 0)
        case _:
          K.if(KV, C.q.is_none(qt),
            st => iret(k, 0, td, k, s, b, ctx, lhs.dn(lhs), st),
            st => (do K<KV>:
              +bk : Map<&2, W.Td> <- K.tl()
              +gen : Bool = Bool.and(U32.is_gt(td.x(td), 0), U32.is_eq(td.x(W.td.get(bk, lhs.dn(lhs))), 0))
              +bad : Bool = Bool.and(Bool.and(td.bodiless(td), Bool.or(Bool.and(Bool.not(td.b(td)), Bool.not(lhs.u(lhs))), gen)), Bool.not(String.eq(k, lhs.dn(lhs))))
              K.if(KV, bad,
                K.err(KV, ctx, ExS{"a def whose body is implemented before the def is used (defs are checked in file order, and an unfilled law has none)"}, Some{ExH{H.HRef{k, s, b}}}, s, Some{lhs.dn(lhs)}, None{}, 0),
                K.if(KV, gen,
                  st2 => (do K<KV>:
                    +o : KV <- ck.go(p, JInst{lhs, k, s, b, td, sp, ctx, d})
                    iref3(kv.k(o), td.x(td), hs.drop(sp, td.x(td)), td, k, s, b, ctx, lhs))(st2),
                  st2 => iref3(k, 0, sp, td, k, s, b, ctx, lhs, st2))))(st))

    # term_check
    case 1n+p JChk{+lhs, tm, +qt, +ty, +g, +ctx, +d}:
      match tm:
        # check-lam
        case H.HLam{+k, i, +cl, +s, lq}:
          do K<KV>:
            +w : W.W <- K.w()
            +tw : H.H = W.wnf(w, ty)
            K.if(KV, h.is_all(tw),
              st => (do K<KV>:
                K.nop()
                +x : H.H = H.HVar{k, d, C.NoSp{}}
                +bump : Bool = Bool.and(C.q.is_many(lq), C.q.is_lone(h.all.q(tw)))
                +q : C.Q = Bool.pick(C.Q, bump, C.QM{}, h.all.q(tw))
                r0 : KV <- K.if(KV, bump, st2 => K.quiet(ck.go(p, JKind{lhs, h.all.A(tw), q, k, ctx, d, s}), st2), K.pure(KV, VN{}))
                +fc : KV <- ck.go(p, JChk{lhs.step(lhs, x), W.apc(W.w.real(w), cl, x), qt, W.apc(W.w.real(w), h.all.cl(tw), x), 0, cx.set(ctx, d, An{q, k, h.all.A(tw)}), (d + 1 : U32)})
                u2 : Us <- uses.close(ctx, kv.us(fc), d, k, q, s, lhs.dn(lhs))
                K.ref(ty)
                return VU{u2, EsNo{}})(st),
              K.err(KV, ctx, ExH{ty}, Some{ExS{"non-inferrable term"}}, s, Some{lhs.dn(lhs)}, None{}, g))
        # check-let
        case H.HLet{+bs, +cl, +s}:
          ck.go(p, JLet{bs, 0, UsTip{}, ctx, bs, cl, s, lhs, qt, ty, g, ctx, d})
        # check-ctr
        case H.HCtr{+k, +xs, +s}:
          do K<KV>:
            +w : W.W <- K.w()
            +tw : H.H = W.wnf(w, ty)
            +bk : Map<&2, W.Td> <- K.tl()
            +ct : Map<&2, W.Cr> <- K.ct()
            K.if(KV, h.is_adt(tw),
              st => (do K<KV>:
                +a : KV <- kadt(W.td.get(bk, h.adt.k(tw)), h.adt.k(tw), h.adt.r(tw), H.h.s(tw), ctx, Some{lhs.dn(lhs)})
                +cs : List<&2, W.Cr> = kv.c(a)
                +c : W.Cr = cr.get(cs, k)
                K.if(KV, cr.has(cs, k),
                  K.if(KV, U32.is_eq(hs.len(xs), cr.n(c)),
                    st2 => (do K<KV>:
                      +tel : H.H <- kfill(h.adt.x(tw), cr.T(c), ctx, Some{lhs.dn(lhs)}, s)
                      +tc : KV <- ck.go(p, JTele{lhs, tel, xs, qt, ctx, d, s, UsTip{}})
                      K.ref(ty)
                      return VU{kv.us(tc), EsNo{}})(st2),
                    K.err(KV, ctx, ExS{S.name.key(k) ++ " with " ++ U32.show(cr.n(c)) ++ Bool.pick(String, U32.is_eq(cr.n(c), 1), " field", " fields")}, Some{ExH{H.HCtr{k, xs, s}}}, s, Some{lhs.dn(lhs)}, None{}, 0)),
                  K.if(KV, ct.has(ct, k),
                    K.err(KV, ctx, ExH{ty}, Some{ExH{H.HRef{cr.f(ct.get(ct, k)), s, False{}}}}, s, Some{lhs.dn(lhs)}, None{}, g),
                    K.err(KV, ctx, ExS{"a declared constructor (" ++ S.name.key(h.adt.k(tw)) ++ " declares " ++ cr.names(cs) ++ ")"}, Some{ExH{H.HCtr{k, xs, s}}}, s, Some{lhs.dn(lhs)}, None{}, 0))))(st),
              st => (do K<KV>:
                K.nop()
                +fam : Maybe<&2, String> = fam.of(ct, k)
                K.err(KV, ctx, ExH{ty}, Some{fam.obs(fam, s)}, s, Some{lhs.dn(lhs)}, dt.note(fam, dt.find(bk, k)), g))(st))
        # check-lit
        case H.HNat{+v, +s}:
          ck.go(p, JLit{"Nat", H.HNat{v, s}, lhs, qt, ty, g, ctx, d})
        case H.HU32{+v, +s}:
          ck.go(p, JLit{"U32", H.HU32{v, s}, lhs, qt, ty, g, ctx, d})
        case H.HF32{+v, +s}:
          ck.go(p, JLit{"F32", H.HF32{v, s}, lhs, qt, ty, g, ctx, d})
        case H.HStr{+v, +s}:
          ck.go(p, JLit{"String", H.HStr{v, s}, lhs, qt, ty, g, ctx, d})
        # check-mat, check-efq
        case H.HMat{+k, +h, +m, +s}:
          ck.go(p, JMat{H.HMat{k, h, m, s}, s, lhs, qt, ty, g, ctx, d})
        case H.HEfq{+s}:
          ck.go(p, JMat{H.HEfq{s}, s, lhs, qt, ty, g, ctx, d})
        # check-rfl
        case H.HRfl{+s}:
          do K<KV>:
            +w : W.W <- K.w()
            +tw : H.H = W.wnf(w, ty)
            K.if(KV, h.is_eql(tw),
              st => K.if(KV, W.compare(True{}, w, h.eql.a(tw), h.eql.b(tw), d),
                st2 => (do K<KV>:
                  K.ref(ty)
                  return VU{UsTip{}, EsNo{}})(st2),
                K.err(KV, ctx, ExH{h.eql.a(tw)}, Some{ExH{h.eql.b(tw)}}, s, Some{lhs.dn(lhs)}, Some{"Note: the left side of the equality is the expected, the right side is the observed."}, 0), st),
              K.err(KV, ctx, ExH{ty}, Some{ExS{"non-inferrable term"}}, s, Some{lhs.dn(lhs)}, None{}, g))
        # check-hol
        case H.HHol{+k, +s}:
          K.if(KV, String.eq(k, "TODO"),
            st => (do K<KV>:
              K.ref(ty)
              return VU{UsTip{}, EsNo{}})(st),
            K.err(KV, ctx, ExH{ty}, Some{ExH{H.HHol{k, s}}}, s, Some{lhs.dn(lhs)}, None{}, g))
        # check-rwt
        case H.HRwt{+e, +pm, +f, +s}:
          do K<KV>:
            +ei : KV <- ck.go(p, JInf{lhs, e, qt, ctx, d, Nil{}})
            +w : W.W <- K.w()
            +ew : H.H = W.wnf(w, kv.ty(ei))
            K.if(KV, h.is_eql(ew),
              st => (do K<KV>:
                K.nop()
                +ea : H.H = h.eql.a(ew)
                +eT : H.H = h.eql.T(ew)
                pc : KV <- ck.go(p, JChk{lhs, pm, C.QN{}, H.HAll{C.QL{}, "_", 0, eT, H.ClRwt{ea, eT, s}, s}, 0, ctx, d})
                +w2 : W.W <- K.w()
                +bgol : H.H = W.ap(W.ap(pm, h.eql.b(ew), C.NoSp{}), e, C.NoSp{})
                K.if(KV, W.compare(False{}, w2, bgol, ty, d),
                  st2 => (do K<KV>:
                    +fc : KV <- ck.go(p, JChk{lhs, f, qt, W.ap(W.ap(pm, ea, C.NoSp{}), H.HRfl{s}, C.NoSp{}), 0, ctx, d})
                    K.ref(ty)
                    return VU{us.add(kv.us(ei), kv.us(fc)), EsNo{}})(st2),
                  K.err(KV, ctx, ExH{ty}, Some{ExH{bgol}}, s, Some{lhs.dn(lhs)}, None{}, g)))(st),
              K.err(KV, ctx, ExS{"an equation {a == b : T}"}, Some{ExH{kv.ty(ei)}}, C.sp.or(H.h.s(e), s), Some{lhs.dn(lhs)}, None{}, 0))
        # check-any
        case t:
          ck.go(p, JAny{t, lhs, qt, ty, g, ctx, d})

    case 1n+p JLit{+lk, +tm, +lhs, +qt, +ty, +g, +ctx, +d}:
      do K<KV>:
        +w : W.W <- K.w()
        +bk : Map<&2, W.Td> <- K.tl()
        +tw : H.H = W.wnf(w, ty)
        K.if(KV, Bool.and(Bool.and(h.is_adt(tw), String.eq(h.adt.k(tw), lk)), Bool.and(List.is_empty(&2, String, h.adt.r(tw)), td.b(W.td.get(bk, lk)))),
          st => (do K<KV>:
            K.ref(ty)
            return VU{UsTip{}, EsNo{}})(st),
          st => ck.go(p, JChk{lhs, W.lit_step(tm), qt, ty, g, ctx, d}, st))

    case 1n+p JMat{+tm, +s, +lhs, +qt, +ty, +g, +ctx, +d}:
      do K<KV>:
        +w : W.W <- K.w()
        +tw : H.H = W.wnf(w, ty)
        K.if(KV, h.is_all(tw),
          K.if(KV, Bool.and(Bool.not(C.q.is_none(qt)), C.q.is_none(h.all.q(tw))),
            K.err(KV, ctx, ExS{"a live scrutinee (a - scrutinee matches only in a dead region)"}, None{}, s, Some{lhs.dn(lhs)}, None{}, 0),
            st => (do K<KV>:
              K.nop()
              +aw : H.H = W.wnf(w, h.all.A(tw))
              K.if(KV, h.is_adt(aw),
                st2 => (do K<KV>:
                  +bk : Map<&2, W.Td> <- K.tl()
                  +a : KV <- kadt(W.td.get(bk, h.adt.k(aw)), h.adt.k(aw), h.adt.r(aw), H.h.s(aw), ctx, Some{lhs.dn(lhs)})
                  ck.go(p, JMat2{tm, s, tw, aw, kv.c(a), lhs, qt, ty, ctx, d}))(st2),
                K.err(KV, ctx, ExS{"a datatype"}, Some{ExH{h.all.A(tw)}}, s, Some{lhs.dn(lhs)}, None{}, 0)))(st)),
          K.err(KV, ctx, ExH{ty}, Some{ExS{"non-inferrable term"}}, s, Some{lhs.dn(lhs)}, None{}, g))

    case 1n+p JMat2{tm, +s, +tw, +aw, +rem, +lhs, +qt, +ty, +ctx, +d}:
      match tm:
        case H.HMat{+mk, +mh, +mm, ms}:
          K.if(KV, cr.has(rem, mk),
            st => (do K<KV>:
              K.nop()
              +c : W.Cr = cr.get(rem, mk)
              +tel : H.H <- kfill(h.adt.x(aw), cr.T(c), ctx, Some{lhs.dn(lhs)}, s)
              +w : W.W <- K.w()
              +tq : C.Q = h.all.q(tw)
              +tcl : H.Cl = h.all.cl(tw)
              gl : H.H <- K.if(H.H, U32.is_eq(cr.n(c), 0),
                st2 => K.pure(H.H, W.apc(W.w.real(w), tcl, H.HCtr{mk, Nil{}, s}), st2),
                st2 => (do K<H.H>:
                  +ca : H.H <- khead(tel, ctx, Some{lhs.dn(lhs)}, s)
                  return H.HAll{W.c.dem(h.all.q(ca), tq), h.all.k(ca), h.all.i(ca), h.all.A(ca), H.ClMat{tq, tcl, h.all.cl(ca), (cr.n(c) - 1 : U32), Nil{}, mk, s}, s})(st2))
              +hc : KV <- ck.go(p, JChk{lhs.ext(lhs, mk, cr.n(c)), mh, qt, gl, 0, ctx, d})
              +mgol : H.H = H.HAll{tq, h.all.k(tw), h.all.i(tw), H.HAdt{h.adt.k(aw), h.adt.x(aw), List.append(&2, String, h.adt.r(aw), [cr.k(c)]), s}, tcl, s}
              +mc : KV <- K.if(KV, Bool.and(U32.is_eq(U32.from_nat(List.length(&2, W.Cr, rem)), 1), Bool.not(h.is_mat(mm))),
                st2 => (do K<KV>:
                  K.ref(mgol)
                  return VU{UsTip{}, EsNo{}})(st2),
                st2 => ck.go(p, JChk{lhs, mm, qt, mgol, 0, ctx, d}, st2))
              K.ref(ty)
              return VU{us.join(kv.us(hc), kv.us(mc)), EsNo{}})(st),
            K.err(KV, ctx, ExS{"a constructor of " ++ S.name.key(h.adt.k(aw)) ++ " (missing, or already matched)"}, Some{ExH{H.HMat{mk, mh, mm, s}}}, s, Some{lhs.dn(lhs)}, None{}, 0))
        case _:
          K.if(KV, List.is_empty(&2, W.Cr, rem),
            st => (do K<KV>:
              K.ref(ty)
              return VU{UsTip{}, EsNo{}})(st),
            st => (do K<KV>:
              +dv : KV <- ck.go(p, JDead{cx.pre(ctx), ctx})
              K.if(KV, kv.b(dv),
                st2 => (do K<KV>:
                  K.ref(ty)
                  return VU{UsTip{}, EsNo{}})(st2),
                K.err(KV, ctx, ExS{"this match doesn't cover " ++ cr.names(rem)}, None{}, s, Some{lhs.dn(lhs)}, Some{"Note: add the missing cases, or a catch-all case."}, 0)))(st))

    # check-any
    case 1n+p JAny{+tm, +lhs, +qt, +ty, +g, +ctx, +d}:
      do K<KV>:
        +xi : KV <- ck.go(p, JInf{lhs, tm, qt, ctx, d, Nil{}})
        +w : W.W <- K.w()
        +bk : Map<&2, W.Td> <- K.tl()
        K.if(KV, W.compare(False{}, w, kv.ty(xi), ty, d),
          K.pure(KV, VU{kv.us(xi), kv.es(xi)}),
          st => K.err(KV, ctx, ExH{ty}, Some{ExH{kv.ty(xi)}}, H.h.s(tm), Some{lhs.dn(lhs)}, any.note(w, bk, kv.es(xi), kv.ty(xi), ty, tm), g, st))

    # check-let, binding by binding (each value in the outer context)
    case 1n+p JLet{bs, +j, +us, +fctx, +all, +cl, +s, +lhs, +qt, +ty, +g, +ctx, +d}:
      match bs:
        case Nil{}:
          do K<KV>:
            +fc : KV <- ck.go(p, JChk{lhs, W.apL(cl, let.xs(all, d)), qt, ty, g, fctx, (d + hbs.len(all) : U32)})
            fu : Us <- uses.closes(all, ctx, kv.us(fc), d, s, lhs.dn(lhs))
            K.ref(ty)
            return VU{us.add(us, fu), EsNo{}}
        case Con{H.HB{+k, i, +q, v}, t}:
          do K<KV>:
            +vi : KV <- ck.go(p, JInf{lhs, v, C.q.dem(q, qt), ctx, d, Nil{}})
            +vty : H.H = kv.ty(vi)
            r0 : KV <- K.if(KV, C.q.is_many(lhs.kind(lhs, q)), st => K.quiet(ck.go(p, JKind{lhs, vty, q, k, ctx, d, s}), st), K.pure(KV, VN{}))
            ck.go(p, JLet{t, (j + 1 : U32), us.add(us, kv.us(vi)), cx.set(fctx, (d + j : U32), An{q, k, vty}), all, cl, s, lhs, qt, ty, g, ctx, d})

    # tele_check
    case 1n+p JTele{+lhs, +tel, xs, +qt, +ctx, +d, +s, +us}:
      match xs:
        case Nil{}:
          K.pure(KV, VT{us, tel})
        case Con{+x, rest}:
          do K<KV>:
            +ta : H.H <- khead(tel, ctx, Some{lhs.dn(lhs)}, s)
            +xc : KV <- ck.go(p, JChk{lhs, x, C.q.dem(h.all.q(ta), qt), h.all.A(ta), 0, ctx, d})
            +w : W.W <- K.w()
            ck.go(p, JTele{lhs, W.apc(W.w.real(w), h.all.cl(ta), x), rest, qt, ctx, d, s, us.add(us, kv.us(xc))})

    # term_check_kind
    case 1n+p JKind{+lhs, T, +q, +k, +ctx, +d, +s}:
      do K<KV>:
        +gid : U32 <- K.gid()
        K.catch(ck.go(p, JChk{lhs, T, C.QN{}, H.HTyp{H.HQua{lhs.kind(lhs, q), C.NoSp{}}, s}, gid, ctx, d}), e => kind.fix(e, gid, q, k, s))

    # ctx_dead: a live binder at an emptied datatype
    case 1n+p JDead{as, +ctx}:
      match as:
        case Nil{}:
          K.pure(KV, VB{False{}})
        case Con{An{q, k, +A}, +rest}:
          K.if(KV, C.q.is_none(q),
            st => ck.go(p, JDead{rest, ctx}, st),
            st => (do K<KV>:
              +w : W.W <- K.w()
              +t : H.H = W.wnf(w, A)
              K.if(KV, h.is_adt(t),
                st2 => (do K<KV>:
                  +bk : Map<&2, W.Td> <- K.tl()
                  +a : KV <- kadt(W.td.get(bk, h.adt.k(t)), h.adt.k(t), h.adt.r(t), H.h.s(t), ctx, None{})
                  K.if(KV, List.is_empty(&2, W.Cr, kv.c(a)), K.pure(KV, VB{True{}}), st3 => ck.go(p, JDead{rest, ctx}, st3)))(st2),
                st2 => ck.go(p, JDead{rest, ctx}, st2)))(st))

    # def_inst
    case 1n+p JInst{+lhs, +k, +s, +b, +td, +sp, +ctx, +d}:
      +x = td.x(td)
      +xs = hs.take(sp, x)
      K.if(KV, U32.is_lt(hs.len(xs), x),
        K.err(KV, ctx, ExS{"a template applied to closed ~ arguments (a def parameter is not comptime)"}, Some{ExH{H.HRef{k, s, b}}}, s, Some{lhs.dn(lhs)}, None{}, 0),
        st => (do K<KV>:
          +tv : KV <- K.catch(K.quiet(ck.go(p, JTele{lhs, td.T(td), xs, C.QN{}, CxTip{}, d, s, UsTip{}})), e => inst.var(e, k, s, b, ctx, d, lhs.dn(lhs)))
          +key : String = tkey(xs)
          K.if(KV, Nat.is_gt(String.length(key), 32768n),
            K.err(KV, ctx, ExS{"a ~ argument that stops growing"}, Some{ExH{H.HRef{k, s, b}}}, s, Some{lhs.dn(lhs)}, None{}, 0),
            st2 => (do K<KV>:
              +tp : Map<&2, String> <- K.tp(k)
              +o : String = Pair.snd(Map<&2, String>, String, Map.get(String, "", tp, key))
              K.if(KV, String.is_empty(o),
                st3 => (do K<KV>:
                  K.nop()
                  +z : U32 = (lhs.z(lhs) + 1 : U32)
                  K.if(KV, U32.is_gt(z, 64),
                    K.err(KV, ctx, ExS{"a template that stops instantiating itself (64 levels at most)"}, Some{ExH{H.HRef{k, s, b}}}, s, Some{lhs.dn(lhs)}, None{}, 0),
                    st4 => (do K<KV>:
                      K.nop()
                      +o2 : String = k ++ "~" ++ U32.show(U32.from_nat(Map.size(&2, String, tp)))
                      K.set_tp(k, Map.set(&2, String, tp, key, o2))
                      +n : U32 = (W.td.n(td) - x : U32)
                      +T : H.H = kv.ret(tv)
                      +v : H.H = hs.apply(td.v(td), xs)
                      K.set_td(o2, W.TdDef{n, 0, T, None{}, False{}, td.u(td), False{}, False{}, None{}})
                      rs0 : Map<&2, Bool> <- K.rs_swap(Map.new(&2, Bool))
                      r : KV <- ck.go(p, JDef{o2, W.TdDef{n, 0, T, Some{v}, False{}, td.u(td), False{}, False{}, None{}}, z})
                      rsi : Map<&2, Bool> <- K.rs_swap(rs0)
                      K.set_td(o2, W.TdDef{n, 0, T, Some{v}, False{}, td.u(td), False{}, False{}, Some{rsi}})
                      return VK{o2})(st4)))(st3),
                st3 => (do K<KV>:
                  +bk : Map<&2, W.Td> <- K.tl()
                  K.if(KV, Bool.and(Bool.not(td.has_v(W.td.get(bk, o))), Bool.not(String.eq(o, lhs.dn(lhs)))),
                    K.err(KV, ctx, ExS{"a decreasing self-call (arguments are read left to right: each passed unchanged until one shrinks)"}, Some{ExH{H.HRef{k, s, b}}}, s, Some{lhs.dn(lhs)}, None{}, 0),
                    K.pure(KV, VK{o})))(st3)))(st2)))(st))

    # def_check (a template's ~ binders as opaque constants: see JDefT)
    case 1n+p JDef{+k, +td, +z}:
      do K<KV>:
        +w : W.W <- K.w()
        +qs : List<&2, C.Q> = tele.qs(w, td.T(td))
        +x : U32 = td.x(td)
        K.if(KV, U32.is_eq(x, 0),
          st => ck.go(p, JChk{Lhs{H.HRef{k, C.NoSp{}, False{}}, W.td.n(td), k, qs, td.u(td), z}, td.v(td), C.QL{}, td.T(td), 0, CxTip{}, 0}, st),
          st => (do K<KV>:
            +tl0 : Map<&2, W.Td> <- K.tl()
            r : KV <- ck.go(p, JDefT{x, H.HRef{k, C.NoSp{}, False{}}, td.v(td), td.T(td), k, (W.td.n(td) - x : U32), qs, td.u(td), z})
            K.set_tl(tl0)
            return r)(st))

    # def_check's ~ binders: gen.tlds[k~x], a bodiless Base-like def
    case 1n+p JDefT{+j, +t, +v, +T, +k, +n, +qs, +u, +z}:
      K.if(KV, U32.is_eq(j, 0),
        st => ck.go(p, JChk{Lhs{t, n, k, qs, u, z}, v, C.QL{}, T, 0, CxTip{}, 0}, st),
        st => (do K<KV>:
          +w : W.W <- K.w()
          +tw : H.H = W.wnf(w, T)
          +bk : Map<&2, W.Td> <- K.tl()
          +o : String = k ++ "~" ++ h.all.k(tw)
          K.if(KV, h.is_all(tw),
            K.if(KV, td.has(bk, o),
              K.err(KV, CxTip{}, ExS{"a fresh ~ binder name"}, Some{ExS{h.all.k(tw)}}, H.h.s(tw), None{}, None{}, 0),
              st2 => (do K<KV>:
                K.set_td(o, W.TdDef{0, 0, h.all.A(tw), None{}, True{}, False{}, False{}, False{}, None{}})
                +r : H.H = H.HRef{o, C.NoSp{}, False{}}
                ck.go(p, JDefT{(j - 1 : U32), H.HApp{t, r, C.NoSp{}}, W.ap(v, r, C.NoSp{}), W.apc(W.w.real(w), h.all.cl(tw), r), k, n, qs, u, z}))(st2)),
            K.err(KV, CxTip{}, ExS{"unreachable (a telescope binds its parameters and fields)"}, None{}, C.NoSp{}, Some{k}, None{}, 0)))(st))

# the checker on a job
def ck(j: KJ) -> K(KV):
  ck.go(4294967295n, j)

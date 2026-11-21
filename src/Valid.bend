import Base
import ./Core.bend as C
import ./Text.bend as T
import ./Lex.bend as L
import ./High.bend as H
import ./Show.bend as S
import ./Err.bend as E
import ./Load.bend as Ld
import ./Wnf.bend as W
import ./Check.bend as K

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Valid: the book the loader read, checked as bend.ts's book_valid checks
# it, and main.ts's verdict on it: book_read's TODO count, cli_verdict and
# book_promises, and err_show for a checker's error (its context).
#
# Base checks the same in every book (it names nothing of the entry's, and
# no file before it names anything of Base's but its datatypes, which are
# declared up front): it is checked once a process, and where an entry's
# book reaches Base's place, Base's checked defs, instances and refs join
# the book, as bend.ts's own events would have left them.

# The book
# --------

# an event of book.order: a name, or Base's place
type Ev is Data:
  EvK{k: String}
  EvBase{}

# a book being read: its entries with bodies (tl), as book_valid first
# shows them (bodies hidden, th), its constructors, events (newest first)
# and files
type Bb is Data:
  Bb{tl: Map<&2, W.Td>, th: Map<&2, W.Td>, ct: Map<&2, W.Cr>, evs: List<&2, Ev>, fs: List<&2, K.Fi>}

def hi(+txt: List<&2, U32>, t: C.Tm) -> H.H:
  W.hr.h(H.hm.go(W.FUEL(), txt, H.JH{t, H.EmTip{}}))

def hi.m(+txt: List<&2, U32>, v: Maybe<&2, C.Tm>) -> Maybe<&2, H.H>:
  match v:
    case None{}:
      None{}
    case Some{t}:
      Some{hi(txt, t)}

def cns.of(+txt: List<&2, U32>, cs: List<&2, C.Cn>, +f: String) -> List<&2, W.Cr>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{C.Cn{k, n, T}, t}:
      W.Cr{k, n, hi(txt, T), f} <> cns.of(txt, t, f)

def cns.put(cs: List<&2, W.Cr>, m: Map<&2, W.Cr>) -> Map<&2, W.Cr>:
  match cs:
    case Nil{}:
      m
    case Con{W.Cr{+k, n, T, f}, t}:
      cns.put(t, Map.set(&2, W.Cr, m, k, W.Cr{k, n, T, f}))

def td.hide(t: W.Td) -> W.Td:
  match t:
    case W.TdDef{n, x, T, v, b, u, ffi, l, rs}:
      W.TdDef{n, x, T, None{}, b, u, ffi, l, rs}
    case t:
      t

# a fill: the law's entry takes the fill's arity, body (or foreign code)
# and @unsafe
def td.fill(t: W.Td, +n: U32, v: Maybe<&2, H.H>, u: Bool, ffi: Bool) -> W.Td:
  match t:
    case W.TdDef{n0, x, T, v0, b, u0, ffi0, l, rs}:
      W.TdDef{n, x, T, v, b, Bool.or(u0, u), Bool.or(ffi0, ffi), l, rs}
    case t:
      t

def bb.put(+k: String, +t: W.Td, bb: Bb) -> Bb:
  match bb:
    case Bb{tl, th, ct, evs, fs}:
      Bb{Map.set(&2, W.Td, tl, k, t), Map.set(&2, W.Td, th, k, td.hide(t)), ct, EvK{k} <> evs, fs}

def bb.ctrs(cs: List<&2, W.Cr>, bb: Bb) -> Bb:
  match bb:
    case Bb{tl, th, ct, evs, fs}:
      Bb{tl, th, cns.put(cs, ct), evs, fs}

def bb.tl(bb: Bb) -> Map<&2, W.Td>:
  match bb:
    case Bb{tl, th, ct, evs, fs}:
      tl

def bb.th(bb: Bb) -> Map<&2, W.Td>:
  match bb:
    case Bb{tl, th, ct, evs, fs}:
      th

def bb.ct(bb: Bb) -> Map<&2, W.Cr>:
  match bb:
    case Bb{tl, th, ct, evs, fs}:
      ct

def bb.evs(bb: Bb) -> List<&2, Ev>:
  match bb:
    case Bb{tl, th, ct, evs, fs}:
      List.reverse(&2, Ev, evs)

def bb.fs(bb: Bb) -> List<&2, K.Fi>:
  match bb:
    case Bb{tl, th, ct, evs, fs}:
      fs

def bb.base(bb: Bb) -> Bb:
  match bb:
    case Bb{tl, th, ct, evs, fs}:
      Bb{tl, th, ct, EvBase{} <> evs, fs}

def bb.file(f: K.Fi, bb: Bb) -> Bb:
  match bb:
    case Bb{tl, th, ct, evs, fs}:
      Bb{tl, th, ct, evs, f <> fs}

# a declaration joins the book (b: it is Base's)
def bb.dcl(+txt: List<&2, U32>, +b: Bool, d: C.Dcl, +bb: Bb) -> Bb:
  match d:
    case C.DAdt{+k, n, g, T, cs}:
      +crs = cns.of(txt, cs, k)
      bb.ctrs(crs, bb.put(k, W.TdAdt{n, g, hi(txt, T), crs, b}, bb))
    case C.DDef{+k, n, x, T, v, u, ffi, islaw, False{}}:
      bb.put(k, W.TdDef{n, x, hi(txt, T), hi.m(txt, v), b, u, Bool.not(List.is_empty(&2, String, ffi)), islaw, None{}}, bb)
    case C.DDef{+k, +n, x, T, v, u, ffi, islaw, True{}}:
      bb.put(k, td.fill(W.td.get(bb.tl(bb), k), n, hi.m(txt, v), u, Bool.not(List.is_empty(&2, String, ffi))), bb)

def bb.dcls(+txt: List<&2, U32>, +b: Bool, ds: List<&2, C.Dcl>, bb: Bb) -> Bb:
  match ds:
    case Nil{}:
      bb
    case Con{d, t}:
      bb.dcls(txt, b, t, bb.dcl(txt, b, d, bb))

def al2.of(al: List<&2, L.Al>) -> List<&2, S.Al2>:
  match al:
    case Nil{}:
      Nil{}
    case Con{L.Al{a, ns}, t}:
      S.Al2{a, ns} <> al2.of(t)

def bb.fr(z: Bool, f: Ld.Fr, +base: String, bb: Bb) -> Bb:
  match z f:
    case True{} f:
      bb.base(bb)
    case False{} Ld.Fr{+p, ns, +al, ds, +txt, +fid}:
      bb.dcls(txt, String.eq(p, base), ds, bb.file(K.Fi{fid, txt, S.Fl{ns, al2.of(al)}}, bb))

# the files in load order (Base's place a mark), into the book
def bb.frs(frs: List<&2, Ld.Fr>, +base: String, bb: Bb) -> Bb:
  match frs:
    case Nil{}:
      bb
    case Con{Ld.Fr{+p, ns, al, ds, txt, fid}, t}:
      bb.frs(t, base, bb.fr(String.is_empty(p), Ld.Fr{p, ns, al, ds, txt, fid}, base, bb))

def bb.nil() -> Bb:
  Bb{Map.new(&2, W.Td), Map.new(&2, W.Td), Map.new(&2, W.Cr), Nil{}, Nil{}}

# book_valid
# ----------

# each name's last event
def last.go(evs: List<&2, Ev>, +i: U32, m: Map<&2, U32>) -> Map<&2, U32>:
  match evs:
    case Nil{}:
      m
    case Con{EvK{+k}, t}:
      last.go(t, (i + 1 : U32), Map.set(&2, U32, m, k, i))
    case Con{EvBase{}, t}:
      last.go(t, (i + 1 : U32), m)

def last.of(+m: Map<&2, U32>, +k: String) -> U32:
  C.mp.get(U32, C.NONE(), m, k)

def lhs.at(+k: String, u: Bool) -> K.Lhs:
  K.Lhs{H.HRef{k, C.NoSp{}, False{}}, 0, k, Nil{}, u, 0}

# a def's or a datatype's type against Type
def bv.type(+k: String, u: Bool, T: H.H) -> K.K(K.KV):
  K.K.quiet(K.ck(K.JChk{lhs.at(k, u), T, C.QN{}, K.HTYPE(C.NoSp{}), 0, K.CxTip{}, 0}))

def kv.unit(m: K.K(K.KV)) -> K.K(Unit):
  K.K.bind(K.KV, Unit, m, v => K.K.pure(Unit, Unit{}))

def k.nop() -> K.K(Unit):
  K.K.pure(Unit, Unit{})

# tele_unbind's doms, as a context, and its ret
type Ub is Data:
  Ub{ctx: K.Cx, ret: H.H}

def unbind.go(fuel: Nat, +w: W.W, t: H.H, +d: U32, ctx: K.Cx) -> Ub:
  match fuel t:
    case 0n t:
      Ub{ctx, t}
    case 1n+f H.HAll{+q, +k, i, +A, cl, s}:
      unbind.go(f, w, W.wnf(w, W.apc(W.w.real(w), cl, H.HVar{k, d, C.NoSp{}})), (d + 1 : U32), K.cx.set(ctx, d, K.An{q, k, A}))
    case _ t:
      Ub{ctx, t}

def unbind(+w: W.W, t: H.H) -> Ub:
  unbind.go(4294967295n, w, W.wnf(w, t), 0, K.CxTip{})

def ub.ctx(u: Ub) -> K.Cx:
  match u:
    case Ub{ctx, ret}:
      ctx

def ub.ret(u: Ub) -> H.H:
  match u:
    case Ub{ctx, ret}:
      ret

def h.is_typ(t: H.H) -> Bool:
  match t:
    case H.HTyp{g, s}:
      True{}
    case _:
      False{}

# a constructor's telescope so far: its rest and the context it binds
type Tc is Data:
  Tc{tel: H.H, ctx: K.Cx}

def tc.tel(t: Tc) -> H.H:
  match t:
    case Tc{tel, ctx}:
      tel

def tc.ctx(t: Tc) -> K.Cx:
  match t:
    case Tc{tel, ctx}:
      ctx

# each domain of a constructor's telescope (parameters, then fields)
# against its goal: Kind(G) for a live field, Kind(q) otherwise
def bv.tel(m: Nat, +d: U32, +tel: H.H, +ctx: K.Cx, +n: U32, +kind: H.H, +c: String) -> K.K(Tc):
  match m:
    case 0n:
      K.K.pure(Tc, Tc{tel, ctx})
    case 1n+r:
      do K.K<Tc>:
        +ta : H.H <- K.khead(tel, ctx, Some{c}, C.NoSp{})
        +q : C.Q = K.h.all.q(ta)
        +A : H.H = K.h.all.A(ta)
        +goal : H.H = Bool.pick(H.H, Bool.and(U32.is_ge(d, n), C.q.is_lone(q)), kind, H.HTyp{H.HQua{q, C.NoSp{}}, C.NoSp{}})
        r0 : K.KV <- K.K.quiet(K.ck(K.JChk{lhs.at(c, False{}), A, C.QN{}, goal, 0, ctx, d}))
        +w : W.W <- K.K.w()
        bv.tel(r, (d + 1 : U32), W.apc(W.w.real(w), K.h.all.cl(ta), H.HVar{K.h.all.k(ta), d, C.NoSp{}}), K.cx.set(ctx, d, K.An{q, K.h.all.k(ta), A}), n, kind, c)

# the tip's arguments, each the parameter at its place
def tip.var(x: H.H, +d: U32) -> Bool:
  match x:
    case H.HVar{k, +i, s}:
      U32.is_eq(i, d)
    case _:
      False{}

def tip.vars(+w: W.W, xs: List<&2, H.H>, +d: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(tip.var(W.wnf(w, x), d), tip.vars(w, t, (d + 1 : U32)))

def tip.ok(+w: W.W, +tip: H.H, +k: String, +n: U32) -> Bool:
  Bool.and(Bool.and(Bool.and(K.h.is_adt(tip), String.eq(K.h.adt.k(tip), k)), Bool.and(U32.is_eq(K.hs.len(K.h.adt.x(tip)), n), List.is_empty(&2, String, K.h.adt.r(tip)))), tip.vars(w, K.h.adt.x(tip), 0))

def bv.ctr(+k: String, +n: U32, +kind: H.H, c: W.Cr) -> K.K(Unit):
  match c:
    case W.Cr{+ck, cn, cT, f}:
      do K.K<Unit>:
        +tc : Tc <- bv.tel(U32.to_nat((n + cn : U32)), 0, cT, K.CxTip{}, n, kind, ck)
        +w : W.W <- K.K.w()
        +tip : H.H = W.wnf(w, tc.tel(tc))
        K.K.if(Unit, tip.ok(w, tip, k, n), k.nop(),
          K.K.err(Unit, tc.ctx(tc), K.ExS{"a telescope tipped at " ++ S.name.key(k) ++ " applied to its own parameters"}, Some{K.ExH{tip}}, C.NoSp{}, Some{ck}, None{}, 0))

def bv.ctrs(+k: String, +n: U32, +kind: H.H, cs: List<&2, W.Cr>) -> K.K(Unit):
  match cs:
    case Nil{}:
      k.nop()
    case Con{c, t}:
      do K.K<Unit>:
        bv.ctr(k, n, kind, c)
        bv.ctrs(k, n, kind, t)

# a datatype's event: its signature, its kind, its constructors
def bv.adt(+k: String, +n: U32, +T: H.H, cs: List<&2, W.Cr>) -> K.K(Unit):
  do K.K<Unit>:
    r0 : K.KV <- bv.type(k, False{}, T)
    +w : W.W <- K.K.w()
    +ub : Ub = unbind(w, T)
    +kind : H.H = ub.ret(ub)
    K.K.if(Unit, h.is_typ(kind), bv.ctrs(k, n, kind, cs),
      K.K.err(Unit, ub.ctx(ub), K.ExS{"a kind (type " ++ S.name.key(k) ++ "<..> is Kind(g))"}, Some{K.ExH{kind}}, C.sp.or(H.h.s(kind), H.h.s(T)), Some{k}, None{}, 0))

# a foreign def's type: its return, past its binders, is base IO(..)
def ffi.ret(fuel: Nat, +w: W.W, t: H.H, +d: U32) -> H.H:
  match fuel t:
    case 0n t:
      t
    case 1n+f H.HAll{q, +k, i, A, cl, s}:
      ffi.ret(f, w, H.h.strip(W.apc(W.w.real(w), cl, H.HVar{k, d, C.NoSp{}})), (d + 1 : U32))
    case _ t:
      t

def h.head(t: H.H) -> H.H:
  match t:
    case H.HApp{f, x, s}:
      h.head(f)
    case t:
      t

def head.io(t: H.H) -> Bool:
  match t:
    case H.HRef{k, s, b}:
      String.eq(k, "IO")
    case _:
      False{}

def bv.ffi(+k: String, T: H.H) -> K.K(Unit):
  do K.K<Unit>:
    +w : W.W <- K.K.w()
    +bk : Map<&2, W.Td> <- K.K.tl()
    +tel : H.H = ffi.ret(4294967295n, w, H.h.strip(T), 0)
    +io : W.Td = W.td.get(bk, "IO")
    K.K.if(Unit, Bool.and(head.io(h.head(tel)), Bool.and(K.td.is_def(io), K.td.b(io))), k.nop(),
      K.K.err(Unit, K.CxTip{}, K.ExS{"a foreign definition returning base IO(...) directly (return type aliases are not unfolded)"}, Some{K.ExS{k}}, H.h.s(tel), Some{k}, None{}, 0))

def td.with_rs(t: W.Td, rs: Map<&2, Bool>) -> W.Td:
  match t:
    case W.TdDef{n, x, T, v, b, u, ffi, l, r0}:
      W.TdDef{n, x, T, v, b, u, ffi, l, Some{rs}}
    case t:
      t

# def_check at a def's last event, its names kept (bend.ts's tld.e)
def bv.body(+k: String, +t: W.Td) -> K.K(Unit):
  do K.K<Unit>:
    rs0 : Map<&2, Bool> <- K.K.rs_swap(Map.new(&2, Bool))
    r : K.KV <- K.ck(K.JDef{k, t, 0})
    rs : Map<&2, Bool> <- K.K.rs_swap(rs0)
    K.K.set_td(k, td.with_rs(t, rs))

# a def's event: a law left unfilled counts as a TODO; its type; a foreign
# def's return; its body at its last event, where it becomes visible
def bv.def(+k: String, +fin: Bool, +t: W.Td) -> K.K(Unit):
  do K.K<Unit>:
    K.K.if(Unit, Bool.and(Bool.and(fin, K.td.bodiless(t)), Bool.not(K.td.b(t))), K.K.hol(), k.nop())
    r0 : K.KV <- bv.type(k, K.td.u(t), K.td.T(t))
    K.K.if(Unit, K.td.ffi(t), bv.ffi(k, K.td.T(t)), k.nop())
    K.K.if(Unit, fin, K.K.if(Unit, K.td.has_v(t), bv.body(k, t), K.K.set_td(k, t)), k.nop())

def bv.ev(+k: String, fin: Bool, t: W.Td) -> K.K(Unit):
  match t:
    case W.TdAdt{+n, g, +T, cs, b}:
      bv.adt(k, n, T, cs)
    case W.TdDef{n, x, T, v, b, u, ffi, l, rs}:
      bv.def(k, fin, W.TdDef{n, x, T, v, b, u, ffi, l, rs})
    case W.TdNo{}:
      k.nop()

# Base's place: its checked entries and instances join the book
def tl.into(m: Map<&2, W.Td>, acc: Map<&2, W.Td>) -> Map<&2, W.Td>:
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Map.set(&2, W.Td, acc, k, v)
    case MNode{pos, lo, hi}:
      tl.into(hi, tl.into(lo, acc))

def tp.into(m: Map<&2, Map<&2, String>>, acc: Map<&2, Map<&2, String>>) -> Map<&2, Map<&2, String>>:
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Map.set(&2, Map<&2, String>, acc, k, v)
    case MNode{pos, lo, hi}:
      tp.into(hi, tp.into(lo, acc))

def bv.base.go(fin: Map<&2, W.Td>, tp: Map<&2, Map<&2, String>>, st: K.Ks) -> K.KR<Unit>:
  match st:
    case K.Ks{tl, ct, tp0, rs, g, fs, hols}:
      K.KOk{Unit{}, K.Ks{tl.into(fin, tl), ct, tp.into(tp, tp0), rs, g, fs, hols}}

def bv.base(fin: Map<&2, W.Td>, tp: Map<&2, Map<&2, String>>) -> K.K(Unit):
  st => bv.base.go(fin, tp, st)

# Base, checked: its entries and instances, and its templates' instances
type Bc is Data:
  Bc{th: Map<&2, W.Td>, ct: Map<&2, W.Cr>, fin: Map<&2, W.Td>, tp: Map<&2, Map<&2, String>>, fi: List<&2, K.Fi>}

def bc.fin(b: Bc) -> Map<&2, W.Td>:
  match b:
    case Bc{th, ct, fin, tp, fi}:
      fin

def bc.tp(b: Bc) -> Map<&2, Map<&2, String>>:
  match b:
    case Bc{th, ct, fin, tp, fi}:
      tp

def bv.go(evs: List<&2, Ev>, +i: U32, +last: Map<&2, U32>, +tl: Map<&2, W.Td>, +bc: Bc) -> K.K(Unit):
  match evs:
    case Nil{}:
      k.nop()
    case Con{EvBase{}, t}:
      do K.K<Unit>:
        bv.base(bc.fin(bc), bc.tp(bc))
        bv.go(t, (i + 1 : U32), last, tl, bc)
    case Con{EvK{+k}, t}:
      do K.K<Unit>:
        bv.ev(k, U32.is_eq(last.of(last, k), i), W.td.get(tl, k))
        bv.go(t, (i + 1 : U32), last, tl, bc)

# book_valid over the events evs of a book whose entries are tl
def book.valid(+evs: List<&2, Ev>, tl: Map<&2, W.Td>, bc: Bc) -> K.K(Unit):
  bv.go(evs, 0, last.go(evs, 0, Map.new(&2, U32)), tl, bc)

def bc.nil() -> Bc:
  Bc{Map.new(&2, W.Td), Map.new(&2, W.Cr), Map.new(&2, W.Td), Map.new(&2, Map<&2, String>), Nil{}}

def ks.of(tl: Map<&2, W.Td>, ct: Map<&2, W.Cr>, fs: List<&2, K.Fi>) -> K.Ks:
  K.Ks{tl, ct, Map.new(&2, Map<&2, String>), Map.new(&2, Bool), 0, fs, 0}

# what Base's check answers: Base checked, or its error
type Br is Data:
  BrOk{bc: Bc}
  BrErr{e: K.Ek, fs: List<&2, K.Fi>}

def base.got(r: K.KR<Unit>, +bb: Bb) -> Br:
  match r:
    case K.KOk{v, K.Ks{tl, ct, tp, rs, g, fs, hols}}:
      BrOk{Bc{bb.th(bb), bb.ct(bb), tl, tp, bb.fs(bb)}}
    case K.KErr{e}:
      BrErr{e, bb.fs(bb)}

# Base's book, checked once
def base.check(frs: List<&2, Ld.Fr>, +base: String) -> Br:
  +bb = bb.frs(List.reverse(&2, Ld.Fr, frs), base, bb.nil())
  base.got(book.valid(bb.evs(bb), bb.tl(bb), bc.nil(), ks.of(bb.th(bb), bb.ct(bb), bb.fs(bb))), bb)

# book_promises
# -------------

def trs.go(fuel: Nat, ts: List<&2, C.Tm>, acc: List<&2, String>) -> List<&2, String>:
  match fuel ts:
    case 0n _:
      acc
    case _ Nil{}:
      acc
    case 1n+f Con{t, r}:
      match t:
        case C.TRef{k, s, b}:
          trs.go(f, r, k <> acc)
        case C.TAdt{k, xs, rr, s}:
          trs.go(f, List.append(&2, C.Tm, xs, r), k <> acc)
        case C.TSub{i, v, b, s}:
          trs.go(f, b <> r, acc)
        case C.TLet{bs, b, s}:
          trs.go(f, List.append(&2, C.Tm, C.bnd.vals(bs), b <> r), acc)
        case C.TTyp{g, s}:
          trs.go(f, g <> r, acc)
        case C.TMin{a, b, s}:
          trs.go(f, a <> b <> r, acc)
        case C.TAll{q, k, i, A, B, s}:
          trs.go(f, A <> B <> r, acc)
        case C.TLam{k, i, b, s, q}:
          trs.go(f, b <> r, acc)
        case C.TApp{a, b, s}:
          trs.go(f, a <> b <> r, acc)
        case C.TCtr{k, xs, s}:
          trs.go(f, List.append(&2, C.Tm, xs, r), acc)
        case C.TMat{k, h, b, s}:
          trs.go(f, h <> b <> r, acc)
        case C.TEql{a, b, A, s}:
          trs.go(f, a <> b <> A <> r, acc)
        case C.TRwt{e, a, b, s}:
          trs.go(f, e <> a <> b <> r, acc)
        case C.TAnn{x, A, s}:
          trs.go(f, x <> A <> r, acc)
        case _:
          trs.go(f, r, acc)

# term_refs(term_lower(T))
def trs(T: H.H, acc: List<&2, String>) -> List<&2, String>:
  trs.go(4294967295n, [K.low(T, 0)], acc)

def crs.refs(cs: List<&2, W.Cr>, acc: List<&2, String>) -> List<&2, String>:
  match cs:
    case Nil{}:
      acc
    case Con{W.Cr{k, n, T, f}, t}:
      crs.refs(t, trs(T, acc))

def rs.keys(m: Maybe<&2, Map<&2, Bool>>, acc: List<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      acc
    case Some{r}:
      List.append(&2, String, Map.keys(&2, Bool, r), acc)

# the names an entry's type (a datatype's constructors' too) and checked
# body refer to
def td.refs(t: W.Td) -> List<&2, String>:
  match t:
    case W.TdNo{}:
      Nil{}
    case W.TdAdt{n, g, T, cs, b}:
      crs.refs(cs, trs(T, Nil{}))
    case W.TdDef{n, x, T, v, b, u, ffi, l, rs}:
      trs(T, rs.keys(rs, Nil{}))

def has(+m: Map<&2, Bool>, +k: String) -> Bool:
  C.mp.has(Bool, m, k)

def uses.get(+m: Map<&2, List<&2, String>>, +k: String) -> List<&2, String>:
  C.mp.get(List<&2, String>, Nil{}, m, k)

def uses.add(+m: Map<&2, List<&2, String>>, +r: String, k: String) -> Map<&2, List<&2, String>>:
  Map.set(&2, List<&2, String>, m, r, k <> uses.get(m, r))

# a walk from the defs outside Base: who names whom (uses[r]: the
# entries that name r)
type Wk is Data:
  Wk{seen: Map<&2, Bool>, todo: List<&2, String>, uses: Map<&2, List<&2, String>>}

def wk.at(z: Bool, +r: String, w: Wk) -> Wk:
  match z w:
    case True{} w:
      w
    case False{} Wk{seen, todo, uses}:
      Wk{Map.set(&2, Bool, seen, r, True{}), r <> todo, uses}

def wk.refs(rs: List<&2, String>, +k: String, w: Wk) -> Wk:
  match rs w:
    case Nil{} w:
      w
    case Con{+r, t} Wk{+seen, todo, uses}:
      wk.refs(t, k, wk.at(has(seen, r), r, Wk{seen, todo, uses.add(uses, r, k)}))

def wk.go(fuel: Nat, +tl: Map<&2, W.Td>, w: Wk) -> Map<&2, List<&2, String>>:
  match fuel w:
    case 0n Wk{seen, todo, uses}:
      uses
    case 1n+f Wk{seen, Nil{}, uses}:
      uses
    case 1n+f Wk{seen, Con{+k, t}, uses}:
      wk.go(f, tl, wk.refs(td.refs(W.td.get(tl, k)), k, Wk{seen, t, uses}))

def seen.of(ks: List<&2, String>, m: Map<&2, Bool>) -> Map<&2, Bool>:
  match ks:
    case Nil{}:
      m
    case Con{k, t}:
      seen.of(t, Map.set(&2, Bool, m, k, True{}))

# the flood back along uses from the promises
# k put first, unless z
def put.if(z: Bool, k: String, rest: List<&2, String>) -> List<&2, String>:
  match z:
    case True{}:
      rest
    case False{}:
      k <> rest

# the names of js not in bad, onto todo (each once)
def flood.add(js: List<&2, String>, todo: List<&2, String>, +bad: Map<&2, Bool>) -> List<&2, String>:
  match js:
    case Nil{}:
      todo
    case Con{+j, t}:
      put.if(has(bad, j), j, flood.add(t, todo, Map.set(&2, Bool, bad, j, True{})))

def flood.set(js: List<&2, String>, bad: Map<&2, Bool>) -> Map<&2, Bool>:
  match js:
    case Nil{}:
      bad
    case Con{j, t}:
      flood.set(t, Map.set(&2, Bool, bad, j, True{}))

def flood.go(fuel: Nat, +uses: Map<&2, List<&2, String>>, todo: List<&2, String>, +bad: Map<&2, Bool>) -> Map<&2, Bool>:
  match fuel todo:
    case 0n _:
      bad
    case _ Nil{}:
      bad
    case 1n+f Con{+k, t}:
      flood.go(f, uses, flood.add(uses.get(uses, k), t, bad), flood.set(uses.get(uses, k), bad))

def own.filter(ks: List<&2, String>, +bad: Map<&2, Bool>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+k, +t}:
      put.if(Bool.not(has(bad, k)), k, own.filter(t, bad))

# the promises: @unsafe defs, and foreign ones outside Base
type Pr is Data:
  Pr{u: List<&2, String>, f: List<&2, String>}

def pr.go(m: Map<&2, W.Td>, p: Pr) -> Pr:
  match m p:
    case MTip{} p:
      p
    case MLeaf{+k, +v} Pr{+u, +f}:
      Pr{Bool.pick(List<&2, String>, K.td.u(v), k <> u, u), Bool.pick(List<&2, String>, Bool.and(K.td.ffi(v), Bool.not(K.td.b(v))), k <> f, f)}
    case MNode{pos, lo, hi} p:
      pr.go(hi, pr.go(lo, p))

# book.order, each name once, Base's left out
def own.go(evs: List<&2, Ev>, +tl: Map<&2, W.Td>, +seen: Map<&2, Bool>) -> List<&2, String>:
  match evs:
    case Nil{}:
      Nil{}
    case Con{EvBase{}, +t}:
      own.go(t, tl, seen)
    case Con{EvK{+k}, t}:
      put.if(Bool.or(has(seen, k), K.td.b(W.td.get(tl, k))), k, own.go(t, tl, Map.set(&2, Bool, seen, k, True{})))

def keys.str(ks: List<&2, String>) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{k, Nil{}}:
      S.name.key(k)
    case Con{k, t}:
      S.name.key(k) ++ ", " ++ keys.str(t)

def uniq(ks: List<&2, String>, +seen: Map<&2, Bool>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+k, +t}:
      put.if(has(seen, k), k, uniq(t, Map.set(&2, Bool, seen, k, True{})))

def td.law(t: W.Td) -> Bool:
  match t:
    case W.TdDef{n, x, T, v, b, u, ffi, l, rs}:
      l
    case _:
      False{}

def own.law(+tl: Map<&2, W.Td>, ks: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{+k, t}:
      Bool.or(Bool.or(Bool.not(S.colon.has(k)), td.law(W.td.get(tl, k))), own.law(tl, t))

def line.if(+on: String, ks: List<&2, String>) -> String:
  match ks:
    case Nil{}:
      ""
    case ks:
      "defs that depend on " ++ on ++ ": " ++ keys.str(ks) ++ "\n"

# cli_verdict, without the kernel: None when every def outside Base is
# free of promises, else FAIL's text
def verdict.go(+tl: Map<&2, W.Td>, +own: List<&2, String>, +uses: Map<&2, List<&2, String>>, pr: Pr) -> Maybe<&2, String>:
  match pr:
    case Pr{+u, +f}:
      +ou = own.filter(own, flood.go(4294967295n, uses, u, seen.of(u, Map.new(&2, Bool))))
      +of = own.filter(own, flood.go(4294967295n, uses, f, seen.of(f, Map.new(&2, Bool))))
      +all = uniq(List.append(&2, String, ou, of), Map.new(&2, Bool))
      +n = U32.from_nat(List.length(&2, String, all))
      Bool.pick(Maybe<&2, String>, U32.is_eq(n, 0), None{},
        Some{"SOME PROOFS FAIL\nError: " ++ U32.show(n) ++ " def" ++ Bool.pick(String, U32.is_eq(n, 1), " relies", "s rely") ++ " on unsafe or foreign code:\n"
          ++ line.if("@unsafe", ou) ++ line.if("foreign effects", of)
          ++ Bool.pick(String, own.law(tl, all), "", "Hint: no law or proof uses these defs. Move them to a file this proof does not import, and the proofs will check: " ++ keys.str(all) ++ "\n")})

def pr.none(p: Pr) -> Bool:
  match p:
    case Pr{u, f}:
      Bool.and(List.is_empty(&2, String, u), List.is_empty(&2, String, f))

def verdict.at(z: Bool, +tl: Map<&2, W.Td>, evs: List<&2, Ev>, pr: Pr) -> Maybe<&2, String>:
  match z:
    case True{}:
      None{}
    case False{}:
      +own = own.go(evs, tl, Map.new(&2, Bool))
      verdict.go(tl, own, wk.go(4294967295n, tl, Wk{seen.of(own, Map.new(&2, Bool)), own, Map.new(&2, List<&2, String>)}), pr)

def verdict(+tl: Map<&2, W.Td>, evs: List<&2, Ev>) -> Maybe<&2, String>:
  +pr = pr.go(tl, Pr{Nil{}, Nil{}})
  verdict.at(pr.none(pr), tl, evs, pr)

# err_show
# --------

def ex.show(+w: W.W, +fl: S.Fl, x: K.Ex, +d: U32, +rb: List<&2, String>) -> String:
  match x:
    case K.ExS{s}:
      s
    case K.ExH{h}:
      S.term.show(fl, W.snfl(w, h, d), 0, rb)

def ci.wid(xs: List<&2, K.Ci>, +n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{K.Ci{i, K.An{q, +k, A}}, t}:
      ci.wid(t, Bool.pick(Nat, Nat.is_gt(String.length(k), n), String.length(k), n))

def pad.end(+s: String, +n: Nat) -> String:
  s ++ String.repeat(" ", Nat.sub(n, String.length(s)))

def ctx.lines(xs: List<&2, K.Ci>, +w: W.W, +fl: S.Fl, +bnd: List<&2, String>, +wid: Nat) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{K.Ci{+i, K.An{q, +k, A}}, t}:
      +pre = List.take(&2, String, bnd, U32.to_nat(i))
      "\n- " ++ pad.end(k, wid) ++ " : " ++ ex.show(w, fl, K.ExH{A}, i, List.reverse(&2, String, pre)) ++ Bool.pick(String, U32.is_eq(S.bnd.last(List.reverse(&2, String, bnd), k), i), "", " (shadowed)") ++ ctx.lines(t, w, fl, bnd, wid)

# err_lost_type reads exp: a text, or a Typ term (as "a defined name" reads)
def ex.lost(x: K.Ex) -> String:
  match x:
    case K.ExS{s}:
      s
    case K.ExH{H.HTyp{g, s}}:
      "a defined name"
    case _:
      ""

def spn.show(+fs: List<&2, K.Fi>, s: C.Sp, +exp: String, nte: Maybe<&2, String>, +dl: String) -> String:
  match s:
    case C.NoSp{}:
      Bool.pick(String, String.is_empty(dl), "", "\nLocation:" ++ dl) ++ E.note.line(nte)
    case C.Sp{+f, +beg, +end}:
      +txt = K.fi.txt(fs, f)
      "\nLocation:" ++ dl ++ E.span.show(txt, beg, end) ++ E.note.line(nte) ++ E.note.line(E.lost.note(exp, txt, beg, end))

def dn.show(+fl: S.Fl, d: Maybe<&2, String>) -> String:
  match d:
    case None{}:
      ""
    case Some{k}:
      " " ++ S.name.show(fl, k)

def obs.show(+w: W.W, +fl: S.Fl, +exp: String, o: Maybe<&2, K.Ex>, +n: U32, +rb: List<&2, String>) -> String:
  match o:
    case None{}:
      "\n- message  : " ++ exp
    case Some{x}:
      "\n- expected : " ++ exp ++ "\n- observed : " ++ ex.show(w, fl, x, n, rb)

# err_show, for an error the checker threw
def ek.show(+fs: List<&2, K.Fi>, e: K.Ek) -> String:
  match e:
    case K.Ek{+bk, +ctx, +exp, obs, +spn, dn, nte, g}:
      +w : W.W = W.W{bk, bk}
      +fl = K.sp.fl(fs, spn)
      +bnd = K.cx.scope(ctx)
      +n = U32.from_nat(List.length(&2, String, bnd))
      +rb = List.reverse(&2, String, bnd)
      +anns = K.cx.sorted(ctx)
      "Error:" ++ obs.show(w, fl, ex.show(w, fl, exp, n, rb), obs, n, rb) ++ Bool.pick(String, List.is_empty(&2, K.Ci, anns), "", "\nContext:") ++ ctx.lines(anns, w, fl, bnd, ci.wid(anns, 0n)) ++ spn.show(fs, spn, ex.lost(exp), nte, dn.show(fl, dn))

# The check of an entry
# ---------------------

# what `bend FILE --check-only` prints: its text, to stdout or stderr, and
# its exit code
type Out is Data:
  Out{txt: String, err: Bool, rc: U32}

def PASS() -> String:
  "ALL PROOFS CHECK\nUse --verdict for mathematical validity.\n"

def out.fail(s: String) -> Out:
  Out{"SOME PROOFS FAIL\n" ++ s ++ "\n", True{}, 1}

def todo.msg(+n: U32) -> String:
  "Error: " ++ U32.show(n) ++ " TODO" ++ Bool.pick(String, U32.is_eq(n, 1), "", "s") ++ " found.\nThe code is incomplete, and not a valid proof yet."

def out.verdict(m: Maybe<&2, String>) -> Out:
  match m:
    case None{}:
      Out{PASS(), False{}, 0}
    case Some{s}:
      Out{s, True{}, 1}

def out.valid(r: K.KR<Unit>, +hols: U32, evs: List<&2, Ev>, +fs: List<&2, K.Fi>) -> Out:
  match r:
    case K.KErr{e}:
      out.fail(ek.show(fs, e))
    case K.KOk{v, K.Ks{tl, ct, tp, rs, g, f2, h}}:
      +n = (hols + h : U32)
      Bool.pick(Out, U32.is_gt(n, 0), out.fail(todo.msg(n)), out.verdict(verdict(tl, evs)))

def has.base(evs: List<&2, Ev>) -> Bool:
  match evs:
    case Nil{}:
      False{}
    case Con{EvBase{}, t}:
      True{}
    case Con{e, t}:
      has.base(t)

def bc.th(b: Bc) -> Map<&2, W.Td>:
  match b:
    case Bc{th, ct, fin, tp, fi}:
      th

def bc.ct(b: Bc) -> Map<&2, W.Cr>:
  match b:
    case Bc{th, ct, fin, tp, fi}:
      ct

def bc.fi(b: Bc) -> List<&2, K.Fi>:
  match b:
    case Bc{th, ct, fin, tp, fi}:
      fi

# the book an entry's files make: Base's declarations first where Base is
# loaded (book_valid declares every entry up front)
def bb.over(z: Bool, +bc: Bc) -> Bb:
  match z:
    case True{}:
      Bb{Map.new(&2, W.Td), bc.th(bc), bc.ct(bc), Nil{}, bc.fi(bc)}
    case False{}:
      bb.nil()

def frs.has.base(frs: List<&2, Ld.Fr>) -> Bool:
  match frs:
    case Nil{}:
      False{}
    case Con{Ld.Fr{+p, ns, al, ds, txt, fid}, t}:
      Bool.or(String.is_empty(p), frs.has.base(t))

def ld.hols(ld: Ld.Ld) -> U32:
  L.bk.hols(Ld.ld.bk(ld))

# book_read and cli_verdict on an entry the loader read
def check.ld(+ld: Ld.Ld, +base: String, +bc: Bc) -> Out:
  +frs = List.reverse(&2, Ld.Fr, Ld.ld.files(ld))
  +bb = bb.frs(frs, base, bb.over(frs.has.base(frs), bc))
  +evs = bb.evs(bb)
  out.valid(book.valid(evs, bb.tl(bb), bc, ks.of(bb.th(bb), bb.ct(bb), bb.fs(bb))), ld.hols(ld), evs, bb.fs(bb))

import Base
import ./Text.bend as T
import ./Core.bend as C
import ./Lex.bend as L
import ./Res.bend as R
import ./Num.bend as N
import ./Flat.bend as F
import ./High.bend as H
import ./PHelp.bend as X
import ./Show.bend as S

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Parse: bend.ts's parser, from parse_term to parse_book, as one recursive
# def, ps.go, on the fuel's predecessor: bend.ts's mutually recursive
# functions are its jobs (PJ), each a do-block in the parser's monad. A
# choice on a computed value hands its branches, unrun, to X.ps.if; a
# loop is a job that asks for itself again.

type PJ is Data:
  PjTerm{lvl: U32}
  PjBase{beg: U32}
  PjBaseC{cls: Nat, beg: U32}
  PjName{cls: Nat, k: String, beg: U32}
  PjCtr{k: String}
  PjNum{beg: U32}
  PjNumPlus{n: U32, beg: U32}
  PjAll{exi: Bool}
  PjPlus{beg: U32}
  PjMat{beg: U32, arms: List<&2, X.Am>}
  PjMatArm{beg: U32, arms: List<&2, X.Am>}
  PjRwt{beg: U32}
  PjRwt2{beg: U32, e0: C.Tm, k: String, e: C.Tm}
  PjBrace{beg: U32}
  PjBrace2{beg: U32, a: C.Tm, ne: Bool, ns: C.Sp}
  PjTup{beg: U32}
  PjList{beg: U32}
  PjArr{beg: U32, x: C.Tm}
  PjArgsList{beg: U32, xs: List<&2, C.Tm>}
  PjDoHead{beg: U32}
  PjDo{m: String, ts: List<&2, C.Tm>, col: U32}
  PjDoStmt{m: String, ts: List<&2, C.Tm>, col: U32, beg: U32, t: C.Tm, typed: Bool, step: Bool}
  PjDoBind{m: String, ts: List<&2, C.Tm>, col: U32, beg: U32, t: C.Tm, typed: Bool, step: Bool, A: C.Tm, asg: Bool}
  PjOps{out: C.Tm, beg: U32, lvl: U32}
  PjOpsGo{op: X.Op, out: C.Tm, beg: U32, lvl: U32}
  PjCall{out: C.Tm, beg: U32, lvl: U32}
  PjTpl{out: C.Tm, beg: U32, lvl: U32, x: U32, ts: List<&2, C.Tm>}
  PjIndex{out: C.Tm, beg: U32, lvl: U32}
  PjLam{out: C.Tm, beg: U32, lvl: U32}
  PjOp{o: Nat, gl: Bool, out: C.Tm, beg: U32, lvl: U32}
  PjOpTy{out: C.Tm, b: C.Tm, s: C.Sp, beg: U32, lvl: U32}
  PjArgs{close: U32, acc: List<&2, C.Tm>}
  PjTerms{acc: List<&2, C.Tm>}
  PjBlock{}
  PjBody{col: U32}
  PjMatch{col: U32, beg: U32}
  PjRows{col: U32, ccol: U32, es: List<&2, C.Tm>, beg: U32, acc: List<&2, C.Row>}
  PjRow{col: U32, ccol: U32, es: List<&2, C.Tm>, beg: U32, acc: List<&2, C.Row>}
  PjLocal{col: U32, beg: U32, bcol: U32}
  PjLocalTs{col: U32, beg: U32, bcol: U32, q: C.Q, ts: List<&2, C.Tm>}
  PjLocalT{col: U32, beg: U32, bcol: U32, q: C.Q, ts: List<&2, C.Tm>}
  PjLocalU{col: U32, beg: U32, bcol: U32, q: C.Q, ts: List<&2, C.Tm>, T: Maybe<&2, C.Tm>}
  PjLocalW{col: U32, beg: U32, q: C.Q, t: C.Tm, w: Maybe<&2, C.Tm>, more: Bool}
  PjLocalV{col: U32, beg: U32, q: C.Q, ts: List<&2, C.Tm>, T: Maybe<&2, C.Tm>, vs: List<&2, C.Tm>}
  PjPats{ts: List<&2, C.Tm>, names: Bool, acc: List<&2, C.Pat>}
  PjPat{t: C.Tm}
  PjTele{close: U32, tk: U32, te: List<&2, X.Te>}
  PjTeleCell{close: U32, tk: U32, te: List<&2, X.Te>, ct: Bool, q: C.Q}
  PjDef{u: Bool}
  PjDefTele{u: Bool, nm: String, k: String, islaw: Bool, lx: U32}
  PjDefBody{k: String, islaw: Bool, te: List<&2, X.Te>, x: U32, u: Bool, T: C.Tm}
  PjType{}
  PjTypeCtrs{k: String, te: List<&2, X.Te>, T: C.Tm, cs: List<&2, C.Cn>}
  PjLaw{}
  PjLawCls{k: String, cl: List<&2, X.Cl>, tc: U32}
  PjBook{}

def ps.pure(v: X.PV) -> L.P(X.PV):
  L.P.pure(X.PV, v)

def ps.fail(e: String) -> L.P(X.PV):
  L.P.fail(X.PV, e)

def ps.fail.from(e: String, beg: U32) -> L.P(X.PV):
  L.P.fail.from(X.PV, e, beg)

def ps.err(e: String, s: C.Sp) -> L.P(X.PV):
  L.P.err(X.PV, e, None{}, s)

# the closing unit's text, for parse_eat
def close.text(c: U32) -> String:
  T.str([c])

def quas.of(c: U32) -> Maybe<&2, C.Q>:
  match c:
    case 48:
      Some{C.QN{}}
    case 49:
      Some{C.QL{}}
    case 50:
      Some{C.QM{}}
    case _:
      None{}

def amp.qua(q: Maybe<&2, C.Q>, all: L.P(X.PV)) -> L.P(X.PV):
  match q:
    case Some{q}:
      do L.P<X.PV>:
        L.P.bump()
        L.P.bump()
        return X.PvT{C.TQua{q, C.NoSp{}}}
    case None{}:
      all

def chr.lit.end(z: Bool, n: U32, beg: U32) -> L.P(X.PV):
  match z:
    case False{}:
      L.P.fail(X.PV, "a closing '")
    case True{}:
      do L.P<X.PV>:
        +spn : C.Sp <- R.P.span(beg)
        return X.PvT{C.TCtr{"Chr", [C.TU32{n, spn}], spn}}

def chr.lit(+beg: U32) -> L.P(X.PV):
  do L.P<X.PV>:
    L.P.bump()
    n : U32 <- X.P.char()
    z : Bool <- L.P.take([39])
    chr.lit.end(z, n, beg)

def str.lit(+beg: U32) -> L.P(X.PV):
  do L.P<X.PV>:
    L.P.bump()
    +c : L.Cur <- L.P.cur()
    cs : List<&2, U32> <- X.str.go(1n+T.len(L.cur.rest(c)), Nil{})
    spn : C.Sp <- R.P.span(beg)
    return X.PvT{X.lit.of(cs, spn)}

def hole.todo(z: Bool) -> L.P(Unit):
  match z:
    case True{}:
      R.P.add_hol()
    case False{}:
      L.P.pure(Unit, Unit{})

def hole.lit() -> L.P(X.PV):
  do L.P<X.PV>:
    L.P.bump()
    +k : String <- L.P.name()
    hole.todo(String.eq(k, "TODO"))
    return X.PvT{C.THol{k, C.NoSp{}}}

# NUMBER at pos: U32, F32, or Nat (and its n+T)
def num.u32.chk(name: Bool, over: Bool, v: U32, ds: List<&2, U32>, beg: U32) -> L.P(X.PV):
  match name over:
    case True{} _:
      L.P.fail(X.PV, "a numeric literal (NUMBER is U32, NUMBER n is Nat)")
    case False{} True{}:
      L.P.fail.from(X.PV, "a u32 literal up to 4294967295 (got " ++ T.str(ds) ++ ")", beg)
    case False{} False{}:
      L.P.pure(X.PV, X.PvT{C.TU32{v, C.NoSp{}}})

def num.u32.vo(name: Bool, vo: U32 & Bool, ds: List<&2, U32>, beg: U32) -> L.P(X.PV):
  (v, over) = vo
  num.u32.chk(name, over, v, ds, beg)

def num.u32(+nm: X.Nm, +beg: U32) -> L.P(X.PV):
  match nm:
    case X.Nm{+ds, kind, fs, neg, xs, len}:
      do L.P<X.PV>:
        c : U32 <- L.P.peek()
        num.u32.vo(T.is_name(c), X.dig.val(ds, 0, False{}), ds, beg)

def num.f32.fail(+beg: U32) -> L.P(X.PV):
  do L.P<X.PV>:
    pos : U32 <- L.P.pos()
    e : L.Env <- L.P.env()
    L.P.fail.from(X.PV, "a float literal with a finite f32 value (got " ++ T.str(T.slice(L.env.txt(e), beg, pos)) ++ ")", beg)

def num.f32(+nm: X.Nm, +beg: U32) -> L.P(X.PV):
  match nm:
    case X.Nm{+ds, kind, +fs, neg, +xs, len}:
      +bits = N.f32.of_dec(ds, fs, neg, xs)
      Bool.pick(L.P(X.PV), U32.is_eq(bits, 2139095040),
        num.f32.fail(beg),
        L.P.pure(X.PV, X.PvT{C.TF32{bits, C.NoSp{}}}))

def num.nat.after(z: Bool, +n: U32) -> L.P(X.PV):
  match z:
    case True{}:
      L.P.fail(X.PV, "a nat literal (NUMBER n)")
    case False{}:
      L.P.pure(X.PV, X.PvT{C.TNat{n, C.NoSp{}}})

def num.nat.add(out: C.Tm, n: U32, +spn: C.Sp) -> L.P(X.PV):
  do L.P<X.PV>:
    k : String <- R.P.own_t("Nat.add")
    return X.PvT{C.TApp{C.TApp{C.TRef{k, spn, False{}}, C.TNat{n, spn}, spn}, out, spn}}

def num.nat.plus(+out: C.Tm, +n: U32, +spn: C.Sp) -> L.P(X.PV):
  Bool.pick(L.P(X.PV), Bool.and(X.tm.is_lit_nat(out), U32.is_le(X.tm.nat_v(out), (4294967295 - n : U32))),
    L.P.pure(X.PV, X.PvT{C.TNat{(n + X.tm.nat_v(out) : U32), spn}}),
    Bool.pick(L.P(X.PV), U32.is_gt(n, 256), num.nat.add(out, n, spn),
      L.P.pure(X.PV, X.PvT{X.succs(U32.to_nat(n), spn, out)})))

# the scope's depth now, to close down to after a binder's body
def ps.close(n: U32, v: X.PV) -> L.P(X.PV):
  do L.P<X.PV>:
    R.P.close(n)
    return v

# Rows of a match: the count check
def rows.succ.note(m: Maybe<&2, U32>) -> String:
  match m:
    case Some{v}:
      "; a successor takes no spaces: " ++ U32.show(v) ++ "n+p"
    case None{}:
      ""

def rows.count.fail(+txt: List<&2, U32>, qs: List<&2, C.Tm>, +n: U32, +qbeg: U32) -> L.P(X.PV):
  do L.P<X.PV>:
    pos : U32 <- L.P.pos()
    L.P.fail.at(X.PV, U32.show(n) ++ " patterns (one per scrutinee" ++ rows.succ.note(X.succ.lit(txt, qs)) ++ ")", qbeg, (pos - 1 : U32))

# the while condition of parse_body's rows: ccol > col, then a case at a
# column of at least ccol (parse_at_word skips first)
def rows.cond.if(z: Bool, +ccol: U32) -> L.P(Bool):
  match z:
    case False{}:
      L.P.pure(Bool, False{})
    case True{}:
      do L.P<Bool>:
        w : Bool <- L.P.at_word("case")
        c : U32 <- L.P.col()
        return Bool.and(w, U32.is_ge(c, ccol))

def rows.cond(+col: U32, +ccol: U32) -> L.P(Bool):
  rows.cond.if(U32.is_gt(ccol, col), ccol)

# the extra binders of a parallel let: !nl, a name or a +, and no keyword
def local.more(+q: C.Q) -> L.P(Bool):
  do L.P<Bool>:
    +c : L.Cur <- L.P.cur()
    +xs : List<&2, U32> = L.cur.rest(c)
    return Bool.and(Bool.and(Bool.not(L.cur.nl(c)), Bool.or(T.is_head(L.cur.peek(c)), Bool.and(C.q.is_lone(q), T.prefix(xs, [43])))), Bool.not(X.at.keyword(xs)))

def maybe.is(m: Maybe<&2, C.Tm>) -> Bool:
  Maybe.is_some(&2, C.Tm, m)

def tm.or_efq(m: Maybe<&2, C.Tm>) -> C.Tm:
  match m:
    case Some{t}:
      t
    case None{}:
      C.TEfq{C.NoSp{}}

def tms.first(ts: List<&2, C.Tm>) -> C.Tm:
  match ts:
    case Con{t, r}:
      t
    case Nil{}:
      C.TEfq{C.NoSp{}}

# the do-block's last statement: its value at M<ts..>'s type
def do.last.ty(z: Bool, k: String, m: String, ts: List<&2, C.Tm>, s: C.Sp) -> L.P(C.Tm):
  match z:
    case True{}:
      L.P.pure(C.Tm, C.TAdt{k, ts, Nil{}, s})
    case False{}:
      R.P.call(m, ts, s)

def do.last(+m: String, +ts: List<&2, C.Tm>, +t: C.Tm) -> L.P(X.PV):
  do L.P<X.PV>:
    R.P.do_end()
    +k : String <- R.P.reso_t(m)
    tld : C.Tld <- R.P.tld(k)
    +s : C.Sp = C.tm.s(t)
    T : C.Tm <- do.last.ty(R.tld.is_adt(tld), k, m, ts, s)
    return X.PvT{C.TAnn{t, T, s}}

# [...ts.slice(0, -1), A, ...ts.slice(-1), v, lam]
def do.bind.rev(rs: List<&2, C.Tm>, A: C.Tm, v: C.Tm, f: C.Tm) -> List<&2, C.Tm>:
  match rs:
    case Nil{}:
      [A, v, f]
    case Con{l, r}:
      List.append(&2, C.Tm, List.reverse(&2, C.Tm, r), [A, l, v, f])

def do.bind.args(ts: List<&2, C.Tm>, A: C.Tm, v: C.Tm, f: C.Tm) -> List<&2, C.Tm>:
  do.bind.rev(List.reverse(&2, C.Tm, ts), A, v, f)

# units up to a " or the end
def ffi.len(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{34, t}:
      n
    case Con{c, t}:
      ffi.len(t, 1n+n)

def def.ffi.ok(z: Bool, path: String, acc: List<&2, String>, k: List<&2, String> -> L.P(List<&2, String>)) -> L.P(List<&2, String>):
  match z:
    case False{}:
      L.P.fail(List<&2, String>, "a .c or .js path")
    case True{}:
      k(path <> acc)

# /\.(c|js)$/
def ffi.ext.rev(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{99, Con{46, t}}:
      True{}
    case Con{115, Con{106, Con{46, t}}}:
      True{}
    case _:
      False{}

def ffi.ext(+xs: List<&2, U32>) -> Bool:
  ffi.ext.rev(List.reverse(&2, U32, xs))

def def.ffi.if(z: Bool, acc: List<&2, String>, k: List<&2, String> -> L.P(List<&2, String>)) -> L.P(List<&2, String>):
  match z:
    case False{}:
      L.P.pure(List<&2, String>, List.reverse(&2, String, acc))
    case True{}:
      do L.P<List<&2, String>>:
        L.P.eat("\"")
        +c : L.Cur <- L.P.cur()
        +n : Nat = ffi.len(L.cur.rest(c), 0n)
        L.P.mod_cur(L.cur.adv(n))
        L.P.eat("\"")
        +eff : List<&2, U32> = T.take(L.cur.rest(c), n)
        e : L.Env <- L.P.env()
        def.ffi.ok(ffi.ext(eff), L.env.dir(e) ++ T.str(eff), acc, k)

def def.ffi.go(fuel: Nat, acc: List<&2, String>) -> L.P(List<&2, String>):
  match fuel:
    case 0n:
      L.P.pure(List<&2, String>, List.reverse(&2, String, acc))
    case 1n+f:
      do L.P<List<&2, String>>:
        z : Bool <- L.P.word("import")
        def.ffi.if(z, acc, def.ffi.go(f))

# the law a def fills: a body-less def, not Base's, not foreign
def tld.law(t: C.Tld) -> Bool:
  match t:
    case C.TlDef{n, x, False{}, False{}, False{}}:
      True{}
    case _:
      False{}

def tld.x(t: C.Tld) -> U32:
  match t:
    case C.TlDef{n, x, v, b, f}:
      x
    case _:
      0

def env.tld(k: String, t: C.Tld, e: L.Env) -> L.Env:
  match e:
    case L.Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      L.Env{txt, fid, ns, al, dir, frs, sc, dep, ann, L.bk.set_tld(k, t, bk), ds}

def env.ctr(k: String, n: U32, e: L.Env) -> L.Env:
  match e:
    case L.Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      L.Env{txt, fid, ns, al, dir, frs, sc, dep, ann, L.bk.set_ctr(k, n, bk), ds}

def P.set_tld(k: String, t: C.Tld) -> L.P(Unit):
  L.P.mod_env(env.tld(k, t))

def P.set_ctr(k: String, n: U32) -> L.P(Unit):
  L.P.mod_env(env.ctr(k, n))

def P.decl(d: C.Dcl) -> L.P(Unit):
  L.P.mod_env(L.env.push_d(d))

# a fill takes the law's T: the parser keeps none, so a fill's Dcl holds an
# Efq; the law's own Dcl holds the type
def env.reset(e: L.Env) -> L.Env:
  match e:
    case L.Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      L.Env{txt, fid, ns, al, dir, 0, Nil{}, 0, Nil{}, bk, ds}

def P.reset() -> L.P(Unit):
  L.P.mod_env(env.reset)

# parse_term_ns(p, tm, h): an operator under (.. : T) takes T's head as its
# namespace; nested ops and Bool.and, Bool.or and String.append pass it on
type NJ is Data:
  NjT{tm: C.Tm, h: C.Tm}
  NjM{m: Nk, tm: C.Tm, h: C.Tm}
  NjS{tm: C.Tm, h: C.Tm, k: Maybe<&2, String>}

# what parse_term_ns does with a spine: nothing, or each argument (and the
# head renamed, for an operator)
type Nk is Data:
  NkSkip{}
  NkGo{k: Maybe<&2, String>}

def ns.op.at(m: Maybe<&2, String>, +op: String, s: C.Sp) -> L.P(Nk):
  match m:
    case Some{k}:
      do L.P<Nk>:
        q : String <- R.P.reso_t(k ++ op)
        return NkGo{Some{q}}
    case None{}:
      L.P.err(Nk, "a type name after : (the operators' namespace)", None{}, s)

# the head of a type: a Var, a Ref or an ADT names the namespace
def ty.name(t: C.Tm) -> Maybe<&2, String>:
  match t:
    case C.TVar{k, i, s}:
      Some{k}
    case C.TVr{k, i, s, r}:
      Some{k}
    case C.TRef{k, s, b}:
      Some{k}
    case C.TAdt{k, x, r, s}:
      Some{k}
    case _:
      None{}

def ns.op(+h: C.Tm, +op: String) -> L.P(Nk):
  ns.op.at(ty.name(h), op, C.tm.s(h))

def ns.pass(+k: String) -> L.P(Nk):
  do L.P<Nk>:
    a : String <- R.P.own_t("Bool.and")
    o : String <- R.P.own_t("Bool.or")
    s : String <- R.P.own_t("String.append")
    return Bool.pick(Nk, Bool.or(Bool.or(String.eq(a, k), String.eq(o, k)), String.eq(s, k)), NkGo{None{}}, NkSkip{})

def ns.mode.ref(z: Bool, +k: String, h: C.Tm) -> L.P(Nk):
  match z:
    case True{}:
      ns.op(h, k)
    case False{}:
      ns.pass(k)

def ns.mode(f: C.Tm, h: C.Tm) -> L.P(Nk):
  match f:
    case C.TRef{+k, s, b}:
      ns.mode.ref(H.is_op(k), k, h)
    case _:
      L.P.pure(Nk, NkSkip{})

def ns.go(+fuel: Nat, j: NJ) -> L.P(C.Tm):
  match fuel j:
    case 0n _:
      L.P.throw(C.Tm, C.ErRaw{"bendbis: parse_term_ns ran out of fuel"})
    case 1n+p NjT{tm, +h}:
      match tm:
        case C.TLet{bs, f, s}:
          do L.P<C.Tm>:
            g : C.Tm <- ns.go(p, NjT{f, h})
            return C.TLet{bs, g, s}
        case +tm:
          do L.P<C.Tm>:
            m : Nk <- ns.mode(C.tm.head(tm), h)
            ns.go(p, NjM{m, tm, h})
    case 1n+p NjM{m, tm, h}:
      match m:
        case NkSkip{}:
          L.P.pure(C.Tm, tm)
        case NkGo{k}:
          ns.go(p, NjS{tm, h, k})
    case 1n+p NjS{tm, +h, +k}:
      match tm:
        case C.TApp{f, x, s}:
          do L.P<C.Tm>:
            g : C.Tm <- ns.go(p, NjS{f, h, k})
            y : C.Tm <- ns.go(p, NjT{x, h})
            return C.TApp{g, y, s}
        case C.TRef{r, s, b}:
          L.P.pure(C.Tm, C.TRef{Maybe.default(&2, String, k, r), s, b})
        case tm:
          L.P.pure(C.Tm, tm)

def ns.of(tm: C.Tm, h: C.Tm) -> L.P(C.Tm):
  ns.go(4294967295n, NjT{tm, h})

def name.var(+k: String, beg: U32) -> L.P(X.PV):
  do L.P<X.PV>:
    s : C.Sp <- R.P.span(beg)
    t : C.Tm <- R.P.var(k, s)
    return X.PvT{t}

def num.len(nm: X.Nm) -> Nat:
  match nm:
    case X.Nm{ds, kind, fs, neg, xs, len}:
      len

def num.kind(nm: X.Nm) -> Nat:
  match nm:
    case X.Nm{ds, kind, fs, neg, xs, len}:
      kind

def num.val(nm: X.Nm) -> U32:
  match nm:
    case X.Nm{ds, kind, fs, neg, xs, len}:
      Pair.fst(U32, Bool, X.dig.val(ds, 0, False{}))

def num.over(nm: X.Nm) -> Bool:
  match nm:
    case X.Nm{ds, kind, fs, neg, xs, len}:
      Pair.snd(U32, Bool, X.dig.val(ds, 0, False{}))

def num.ds(nm: X.Nm) -> List<&2, U32>:
  match nm:
    case X.Nm{ds, kind, fs, neg, xs, len}:
      ds

def num.nat.plus.if(z: Bool, plus: L.P(X.PV), +n: U32) -> L.P(X.PV):
  match z:
    case True{}:
      plus
    case False{}:
      do L.P<X.PV>:
        c : U32 <- L.P.peek()
        num.nat.after(T.is_name(c), n)

def num.nat.ok(over: Bool, +nm: X.Nm, plus: L.P(X.PV)) -> L.P(X.PV):
  match over:
    case True{}:
      L.P.fail(X.PV, "a nat literal up to 4294967295n (got " ++ T.str(num.ds(nm)) ++ "n)")
    case False{}:
      do L.P<X.PV>:
        z : Bool <- L.P.take([43])
        num.nat.plus.if(z, plus, num.val(nm))

def num.nat(+nm: X.Nm, plus: L.P(X.PV)) -> L.P(X.PV):
  num.nat.ok(num.over(nm), nm, plus)

def num.go(k: Nat, +nm: X.Nm, +beg: U32, plus: L.P(X.PV)) -> L.P(X.PV):
  match k:
    case 0n:
      num.u32(nm, beg)
    case 1n:
      num.nat(nm, plus)
    case _:
      num.f32(nm, beg)

def all.quant(exi: Bool) -> L.P(C.Q):
  match exi:
    case True{}:
      L.P.pure(C.Q, C.QL{})
    case False{}:
      R.P.quant()

def all.fin(exi: Bool, q: C.Q, k: String, i: U32, A: C.Tm, B: C.Tm, beg: U32) -> L.P(X.PV):
  match exi:
    case True{}:
      do L.P<X.PV>:
        +s : C.Sp <- R.P.span(beg)
        ex : String <- R.P.own_t("Exists")
        return X.PvT{C.TApp{C.TApp{C.TRef{ex, s, False{}}, A, s}, C.TLam{k, i, B, s, C.QL{}}, s}}
    case False{}:
      X.ps.ret(C.TAll{q, k, i, A, B, C.NoSp{}})

# the name +D's term resolves to ("" for any other term)
def plus.key(t: C.Tm) -> L.P(String):
  match t:
    case C.TAdt{k, x, r, s}:
      L.P.pure(String, k)
    case C.TVar{k, i, s}:
      R.P.reso_t(k)
    case C.TVr{k, i, s, r}:
      R.P.reso_t(k)
    case C.TRef{k, s, b}:
      R.P.reso_t(k)
    case _:
      L.P.pure(String, "")

def plus.adt(t: C.Tm) -> Bool:
  match t:
    case C.TAdt{k, x, r, s}:
      True{}
    case _:
      False{}

def plus.xs(t: C.Tm, n: U32, +s: C.Sp) -> List<&2, C.Tm>:
  match t:
    case C.TAdt{k, x, r, u}:
      x
    case _:
      List.replicate(C.Tm, U32.to_nat(n), C.TQua{C.QL{}, s})

def plus.many(xs: List<&2, C.Tm>, +g: U32, +s: C.Sp, +i: U32) -> List<&2, C.Tm>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Bool.pick(C.Tm, U32.is_lt(i, g), C.TQua{C.QM{}, s}, x) <> plus.many(t, g, s, (i + 1 : U32))

def plus.fail(+prev: U32, +beg: U32) -> L.P(X.PV):
  L.P.fail.at(X.PV, "a quantified datatype after + (" ++ Bool.pick(String, X.glued(prev), X.OP_SPACES(), "+D<..> sets D's leading quantities to &2") ++ ")", beg, (beg + 1 : U32))

def plus.var(m: Maybe<&2, String>, s: C.Sp, +prev: U32, +beg: U32) -> L.P(X.PV):
  match m:
    case Some{k}:
      X.ps.ret(C.TVar{k, C.MINUS(), s})
    case None{}:
      plus.fail(prev, beg)

def plus.fin(+t: C.Tm, +s: C.Sp, +beg: U32, +prev: U32, +k: String, tld: C.Tld) -> L.P(X.PV):
  match tld:
    case C.TlAdt{+n, +g}:
      Bool.pick(L.P(X.PV), Bool.or(U32.is_eq(g, 0), Bool.and(U32.is_lt(g, n), Bool.not(plus.adt(t)))),
        plus.fail(prev, beg),
        X.ps.ret(C.TAdt{k, plus.many(plus.xs(t, n, s), g, s, 0), Nil{}, s}))
    case _:
      plus.var(X.tm.var.k(t), s, prev, beg)

def mat.end(beg: U32, arms: List<&2, X.Am>, tail: C.Tm) -> L.P(X.PV):
  do L.P<X.PV>:
    +s : C.Sp <- R.P.span(beg)
    return X.PvT{X.mat.build(List.reverse(&2, X.Am, arms), s, C.tm.or_sp(tail, s))}

def mat.colon(z: Bool) -> L.P(Bool):
  match z:
    case True{}:
      L.P.take([58])
    case False{}:
      L.P.pure(Bool, False{})

def rwt.name(m: Maybe<&2, String>) -> L.P(String):
  match m:
    case Some{k}:
      L.P.pure(String, k)
    case None{}:
      L.P.fail(String, "a name before @ (a rewrite binder is one name: %e@E : P)")

def brace.eq(ne: Bool) -> L.P(Bool):
  match ne:
    case True{}:
      L.P.pure(Bool, True{})
    case False{}:
      L.P.take([61, 61])

def brace.b(z: Bool, t: L.P(X.PV)) -> L.P(Maybe<&2, C.Tm>):
  match z:
    case True{}:
      do L.P<Maybe<&2, C.Tm>>:
        v : X.PV <- t
        return Some{X.pv.t(v)}
    case False{}:
      L.P.pure(Maybe<&2, C.Tm>, None{})

def brace.fin(b: Maybe<&2, C.Tm>, ne: Bool, a: C.Tm, T: C.Tm, ns: C.Sp, beg: U32) -> L.P(X.PV):
  match b ne:
    case None{} _:
      X.ps.ret(C.TAnn{a, T, C.NoSp{}})
    case Some{x} False{}:
      X.ps.ret(C.TEql{a, x, T, C.NoSp{}})
    case Some{x} True{}:
      do L.P<X.PV>:
        +s : C.Sp <- R.P.span(beg)
        i : U32 <- R.P.open("_")
        e : String <- R.P.own_t("Empty")
        return X.PvT{C.TAll{C.QL{}, "_", i, C.TEql{a, x, T, s}, C.TRef{e, ns, False{}}, s}}

def body.is_term(b: C.Body) -> Bool:
  match b:
    case C.BTm{t}:
      True{}
    case _:
      False{}

def body.term(b: C.Body) -> C.Tm:
  match b:
    case C.BTm{t}:
      t
    case _:
      C.TEfq{C.NoSp{}}

def tup.comma(z: Bool) -> L.P(Bool):
  match z:
    case True{}:
      L.P.take([44])
    case False{}:
      L.P.pure(Bool, False{})

def tup.ann(an: Bool, out: C.Tm, t: L.P(X.PV)) -> L.P(C.Tm):
  match an:
    case True{}:
      do L.P<C.Tm>:
        T : X.PV <- t
        ns.of(out, C.tm.head(X.pv.t(T)))
    case False{}:
      L.P.pure(C.Tm, out)

def arr.caret(cnt: Bool) -> L.P(Unit):
  match cnt:
    case True{}:
      L.P.pure(Unit, Unit{})
    case False{}:
      L.P.eat("^")

def arr.depth(cnt: Bool, +n: C.Tm) -> L.P(C.Tm):
  match cnt:
    case False{}:
      L.P.pure(C.Tm, n)
    case True{}:
      +k = X.log2.pow(X.nat.of(n, 0))
      Bool.pick(L.P(C.Tm), U32.is_eq(k, C.NONE()),
        L.P.err(C.Tm, "a power of two count (^d takes a depth)", None{}, C.tm.s(n)),
        L.P.pure(C.Tm, C.TNat{k, C.tm.s(n)}))

def list.build(ys: List<&2, C.Tm>, +con: String, +s: C.Sp, nil: C.Tm) -> C.Tm:
  match ys:
    case Nil{}:
      nil
    case Con{y, t}:
      C.TCtr{con, [y, list.build(t, con, s, nil)], s}

def do.lt(lt: Bool, m: String) -> L.P(Unit):
  match lt:
    case True{}:
      L.P.pure(Unit, Unit{})
    case False{}:
      L.P.fail(Unit, "'<' (a do block is written do " ++ m ++ "<...>:)")

def do.typed(z: Bool) -> L.P(Bool):
  match z:
    case True{}:
      L.P.take([58])
    case False{}:
      L.P.pure(Bool, False{})

def do.step(typed: Bool, +col: U32) -> L.P(Bool):
  match typed:
    case True{}:
      L.P.pure(Bool, False{})
    case False{}:
      R.P.more(col)

def do.ty(typed: Bool, step: Bool, +t: C.Tm, term: L.P(X.PV)) -> L.P(X.PV):
  match typed step:
    case True{} _:
      term
    case False{} True{}:
      do L.P<X.PV>:
        u : C.Tm <- R.P.var("Unit", C.tm.s(t))
        return X.PvT{u}
    case False{} False{}:
      X.ps.ret(t)

def do.asg.eq(ee: Bool) -> L.P(Bool):
  match ee:
    case True{}:
      L.P.pure(Bool, False{})
    case False{}:
      L.P.take([61])

def do.asg(typed: Bool) -> L.P(Bool):
  match typed:
    case True{}:
      do L.P<Bool>:
        ee : Bool <- L.P.at([61, 61])
        do.asg.eq(ee)
    case False{}:
      L.P.pure(Bool, False{})

# typed and no = : eat <-; untyped and no step: whether a <- follows
def do.arrow(typed: Bool, asg: Bool, step: Bool) -> L.P(Bool):
  match typed asg step:
    case True{} False{} _:
      do L.P<Bool>:
        L.P.eat("<-")
        return True{}
    case False{} _ False{}:
      L.P.take([60, 45])
    case _ _ _:
      L.P.pure(Bool, True{})

def do.val(step: Bool, t: C.Tm, term: L.P(X.PV)) -> L.P(X.PV):
  match step:
    case True{}:
      X.ps.ret(t)
    case False{}:
      term

def do.binder(typed: Bool, t: C.Tm) -> C.Tm:
  match typed:
    case True{}:
      t
    case False{}:
      C.TVar{"_", 0, C.NoSp{}}

def do.fin.go(asg: Bool, m: String, ts: List<&2, C.Tm>, k: String, i: U32, q: C.Q, v: C.Tm, A: C.Tm, f: C.Tm, +s: C.Sp) -> L.P(X.PV):
  match asg:
    case True{}:
      X.ps.ret(C.TLet{[C.Bnd{k, i, q, C.TAnn{v, A, s}}], f, s})
    case False{}:
      do L.P<X.PV>:
        t : C.Tm <- R.P.call(m ++ ".bind", do.bind.args(ts, A, v, C.TLam{k, i, f, s, q}), s)
        return X.PvT{t}

def do.fin(asg: Bool, m: String, ts: List<&2, C.Tm>, x: C.Pat, v: C.Tm, A: C.Tm, f: C.Tm, +s: C.Sp) -> L.P(X.PV):
  match x:
    case C.PVar{k, i, q, u}:
      do.fin.go(asg, m, ts, k, i, q, v, A, f, s)
    case _:
      L.P.throw(X.PV, C.ErRaw{"bendbis: do binder"})

# a free name before ( is its Ref (out.v)
def call.unvar(t: C.Tm) -> C.Tm:
  match t:
    case C.TVr{k, i, s, r}:
      C.TRef{r, s, False{}}
    case t:
      t

def call.bang(t: C.Tm) -> L.P(C.Tm):
  match t:
    case C.TRef{k, s, b}:
      do L.P<C.Tm>:
        L.P.bump()
        return C.TRef{k, s, True{}}
    case _:
      L.P.fail(C.Tm, "a named def before ! (only f!(..) offloads)")

def call.key(t: C.Tm) -> String:
  match t:
    case C.TRef{k, s, b}:
      k
    case _:
      ""

def tpl.full(z: Bool, out: C.Tm, x: U32) -> L.P(Unit):
  match z:
    case True{}:
      L.P.fail(Unit, "a term (" ++ S.name.key(call.key(out)) ++ " takes " ++ U32.show(x) ++ " ~)")
    case False{}:
      L.P.pure(Unit, Unit{})

def idx.set(nl: Bool) -> L.P(Bool):
  match nl:
    case True{}:
      L.P.pure(Bool, False{})
    case False{}:
      L.P.take([60, 45])

def lam.of(x: C.Pat, f: C.Tm) -> C.Tm:
  match x:
    case C.PVar{k, i, q, s}:
      C.TLam{k, i, f, s, q}
    case _:
      f

def op.tyarg(z: Bool) -> L.P(Unit):
  match z:
    case True{}:
      L.P.fail(Unit, "'>' or ',' (a compound type argument takes parens: F<(A & B)>)")
    case False{}:
      L.P.pure(Unit, Unit{})

# k[0] === "." ? k : parse_own(p, k)
def op.fn(k: String) -> L.P(String):
  match k:
    case SCon{Chr{46}, t}:
      L.P.pure(String, SCon{Chr{46}, t})
    case k:
      R.P.own_t(k)

def op.build(o: Nat, out: C.Tm, b: C.Tm, +s: C.Sp, t: C.Sp) -> L.P(C.Tm):
  match o:
    case 1n:
      do L.P<C.Tm>:
        i : U32 <- R.P.open("_")
        return C.TAll{C.QL{}, "_", i, out, b, s}
    case 12n:
      L.P.pure(C.Tm, C.TMin{out, b, s})
    case 10n:
      do L.P<C.Tm>:
        k : String <- R.P.own_c("Con")
        return C.TCtr{k, [out, b], s}
    case +o:
      do L.P<C.Tm>:
        f : String <- op.fn(R.op.k(o))
        +rs : C.Sp = Bool.pick(C.Sp, Bool.or(Nat.is_eq(o, 2n), Nat.is_eq(o, 3n)), s, t)
        return C.TApp{C.TApp{C.TRef{f, rs, False{}}, out, s}, b, s}

def opty.name(m: Maybe<&2, String>) -> L.P(String):
  match m:
    case Some{k}:
      L.P.pure(String, k)
    case None{}:
      L.P.fail(String, "a family name before <..> (a comparison here needs parens)")

def local.write.more(z: Bool, +bcol: U32) -> L.P(Bool):
  match z:
    case True{}:
      R.P.more(bcol)
    case False{}:
      L.P.pure(Bool, False{})

def local.plus(+g: U32, z: Bool) -> L.P(Unit):
  Bool.pick(L.P(Unit), Bool.and(Bool.not(U32.is_eq(g, C.NONE())), z),
    L.P.fail.at(Unit, "'=' (" ++ X.OP_SPACES() ++ ")", g, (g + 1 : U32)), L.P.pure(Unit, Unit{}))

def local.typed(T: Maybe<&2, C.Tm>, +beg: U32, term: L.P(X.PV)) -> L.P(List<&2, C.Tm>):
  match T:
    case Some{A}:
      do L.P<List<&2, C.Tm>>:
        v : X.PV <- term
        s : C.Sp <- R.P.span(beg)
        return [C.TAnn{X.pv.t(v), A, s}]
    case None{}:
      L.P.pure(List<&2, C.Tm>, Nil{})

def pat.var(ok: Bool, t: C.Tm, k: String, s: C.Sp) -> L.P(X.PV):
  match ok:
    case True{}:
      do L.P<X.PV>:
        x : C.Pat <- X.P.bind(t)
        return X.PvP{x}
    case False{}:
      +n = S.name.key(k)
      L.P.err(X.PV, "a braced constructor pattern (" ++ n ++ " is a constructor: write " ++ n ++ "{}, or rename the binder)", None{}, s)

def pat.ctr.fail(+n: U32, +k: String, +s: C.Sp) -> L.P(X.PV):
  Bool.pick(L.P(X.PV), U32.is_eq(n, C.NONE()),
    L.P.err(X.PV, "a declared constructor (unknown: " ++ S.name.key(k) ++ ")", None{}, s),
    L.P.err(X.PV, "a " ++ S.name.key(k) ++ " pattern with " ++ U32.show(n) ++ Bool.pick(String, U32.is_eq(n, 1), " field", " fields"), None{}, s))

def pat.op(h: C.Tm) -> String:
  match h:
    case C.TRef{k, s, b}:
      k
    case _:
      ""

def pat.succ(+op: String, xs: List<&2, C.Tm>) -> Maybe<&2, U32>:
  match xs:
    case Con{C.TNat{v, s}, t}:
      Bool.pick(Maybe<&2, U32>, Bool.or(String.eq(op, ".add"), String.eq(op, "Nat.add")), Some{v}, None{})
    case _:
      None{}

def pat.other.go(m: Maybe<&2, U32>, isop: Bool, +t: C.Tm) -> L.P(X.PV):
  match m isop:
    case Some{v} _:
      L.P.err(X.PV, "a pattern (a successor takes no spaces: " ++ U32.show(v) ++ "n+p)", None{}, C.tm.s(t))
    case None{} True{}:
      L.P.err(X.PV, "a pattern (a binder or a constructor)", None{}, C.tm.s(t))
    case None{} False{}:
      do L.P<X.PV>:
        o : String <- X.P.show_low(t)
        L.P.err(X.PV, "a pattern (a binder or a constructor)", Some{o}, C.tm.s(t))

def pat.other(hx: C.Tm & List<&2, C.Tm>, +t: C.Tm) -> L.P(X.PV):
  (h, xs) = hx
  +op = pat.op(h)
  pat.other.go(pat.succ(op, xs), H.is_op(op), t)

def tele.tilde(z: Bool) -> L.P(Unit):
  match z:
    case True{}:
      L.P.fail(Unit, "a plain binder (only leading binders take ~)")
    case False{}:
      L.P.pure(Unit, Unit{})

def tele.ct(z: Bool) -> L.P(Bool):
  match z:
    case True{}:
      L.P.take([126])
    case False{}:
      L.P.pure(Bool, False{})

def tele.q(ct: Bool) -> L.P(C.Q):
  match ct:
    case True{}:
      L.P.pure(C.Q, C.QN{})
    case False{}:
      R.P.quant()

def tele.dup(z: Bool, +k: String) -> L.P(Unit):
  match z:
    case True{}:
      do L.P<Unit>:
        pos : U32 <- L.P.pos()
        L.P.fail.from(Unit, "a fresh field name (duplicate declaration: " ++ k ++ ")", (pos - U32.from_nat(String.length(k)) : U32))
    case False{}:
      L.P.pure(Unit, Unit{})

def tele.colon(bare: Bool) -> L.P(Unit):
  match bare:
    case True{}:
      L.P.pure(Unit, Unit{})
    case False{}:
      L.P.eat(":")

def tele.ty(bare: Bool, s: C.Sp, term: L.P(X.PV)) -> L.P(X.PV):
  match bare:
    case True{}:
      X.ps.ret(C.TQnt{s})
    case False{}:
      term

def def.key(isl: Bool, q: String, nm: String) -> L.P(String):
  match isl:
    case True{}:
      L.P.pure(String, q)
    case False{}:
      R.P.fresh(True{}, "a fresh name", nm)

def def.tilde(z: Bool) -> L.P(Unit):
  match z:
    case True{}:
      L.P.fail(Unit, "a name")
    case False{}:
      L.P.pure(Unit, Unit{})

def def.fill.chk(allq: Bool, short: Bool, lx: U32) -> L.P(Unit):
  match allq short:
    case False{} _:
      L.P.fail(Unit, "a name")
    case True{} True{}:
      L.P.fail(Unit, "a name for each ~ clause of the law (" ++ U32.show(lx) ++ ")")
    case True{} False{}:
      L.P.pure(Unit, Unit{})

def def.arrow(ar: Bool, nm: String) -> L.P(Unit):
  match ar:
    case True{}:
      L.P.pure(Unit, Unit{})
    case False{}:
      L.P.fail(Unit, "'->' (a def with no return type fills a law; no law named " ++ nm ++ " is in scope)")

def def.tpl(z: Bool) -> L.P(Unit):
  match z:
    case True{}:
      L.P.fail(Unit, "a body (a template is not foreign)")
    case False{}:
      L.P.pure(Unit, Unit{})

def type.params(lt: Bool, tele: L.P(X.PV)) -> L.P(X.PV):
  match lt:
    case True{}:
      tele
    case False{}:
      L.P.pure(X.PV, X.PvTe{Nil{}, 0})

def type.is(z: Bool) -> L.P(Unit):
  match z:
    case True{}:
      L.P.pure(Unit, Unit{})
    case False{}:
      L.P.fail(Unit, "'is'")

def type.stop.or(z: Bool, next: L.P(Bool)) -> L.P(Bool):
  match z:
    case True{}:
      L.P.pure(Bool, True{})
    case False{}:
      next

def type.stop(head: Bool) -> L.P(Bool):
  match head:
    case False{}:
      L.P.pure(Bool, True{})
    case True{}:
      do L.P<Bool>:
        d : Bool <- L.P.at_word("def")
        type.stop.or(d, st => (do L.P<Bool>:
          t : Bool <- L.P.at_word("type")
          type.stop.or(t, L.P.at_word("law")))(st))

def law.exs(f: Bool) -> L.P(Bool):
  match f:
    case True{}:
      L.P.pure(Bool, False{})
    case False{}:
      L.P.at_word("exs")

def law.exs.take(all: Bool) -> L.P(Unit):
  match all:
    case True{}:
      L.P.pure(Unit, Unit{})
    case False{}:
      do L.P<Unit>:
        w : Bool <- L.P.word("exs")
        return Unit{}

def law.tilde(z: Bool) -> L.P(Unit):
  match z:
    case True{}:
      L.P.fail(Unit, "a plain clause (only leading clauses take ~)")
    case False{}:
      L.P.pure(Unit, Unit{})

def law.ct(all: Bool) -> L.P(Bool):
  match all:
    case True{}:
      L.P.take([126])
    case False{}:
      L.P.pure(Bool, False{})

def law.q(ct: Bool, all: Bool) -> L.P(C.Q):
  match ct all:
    case True{} _:
      L.P.pure(C.Q, C.QN{})
    case False{} True{}:
      R.P.quant()
    case False{} False{}:
      L.P.pure(C.Q, C.QL{})

def law.where(wh: Bool, +c: String, +s: C.Sp, A: C.Tm, term: L.P(X.PV)) -> L.P(C.Tm):
  match wh:
    case True{}:
      do L.P<C.Tm>:
        +b : U32 <- L.P.pos()
        _ : Bool <- L.P.word("where")
        ws : C.Sp <- R.P.span(b)
        +n1 : U32 <- R.P.depth()
        i : U32 <- R.P.open(c)
        w : X.PV <- term
        R.P.close(n1)
        ex : String <- R.P.own_t("Exists")
        return C.TApp{C.TApp{C.TRef{ex, ws, False{}}, A, s}, C.TLam{c, i, X.pv.t(w), s, C.QL{}}, s}
    case False{}:
      L.P.pure(C.Tm, A)

def book.unsafe(z: Bool) -> L.P(Unit):
  match z:
    case True{}:
      L.P.pure(Unit, Unit{})
    case False{}:
      L.P.fail(Unit, "'unsafe' (the one decorator)")

def book.def(z: Bool) -> L.P(Unit):
  match z:
    case True{}:
      L.P.pure(Unit, Unit{})
    case False{}:
      L.P.fail(Unit, "'def' (@unsafe marks the def below it)")

# The parser
# ----------

def ps.go(+fuel: Nat, j: PJ) -> L.P(X.PV):
  match fuel j:
    case 0n _:
      L.P.throw(X.PV, C.ErRaw{"bendbis: the parser ran out of fuel"})

    # parse_term(p, lvl): lvl is bend.ts's plus one
    case 1n+p PjTerm{+lvl}:
      do L.P<X.PV>:
        L.P.skip()
        +beg : U32 <- L.P.pos()
        b : X.PV <- ps.go(p, PjBase{beg})
        s : C.Sp <- R.P.span(beg)
        +t : C.Tm = C.tm.or_sp(X.pv.t(b), s)
        ps.go(p, PjOps{t, C.sp.beg(C.tm.s(t)), lvl})

    case 1n+p PjBase{+beg}:
      do L.P<X.PV>:
        c : U32 <- L.P.peek()
        ps.go(p, PjBaseC{X.base.cls(c), beg})

    case 1n+p PjBaseC{cls, +beg}:
      match cls:
        case 0n:
          do L.P<X.PV>:
            +k : String <- L.P.lexeme()
            ps.go(p, PjName{X.kw.cls(k), k, beg})
        case 1n:
          ps.go(p, PjNum{beg})
        case 2n:
          ps.go(p, PjAll{False{}})
        case 3n:
          do L.P<X.PV>:
            c : U32 <- L.P.ahead(1)
            amp.qua(quas.of(c), st => ps.go(p, PjAll{True{}}, st))
        case 4n:
          ps.go(p, PjPlus{beg})
        case 5n:
          do L.P<X.PV>:
            L.P.bump()
            L.P.eat("{")
            ps.go(p, PjMat{beg, Nil{}})
        case 6n:
          ps.go(p, PjRwt{beg})
        case 7n:
          ps.go(p, PjBrace{beg})
        case 8n:
          do L.P<X.PV>:
            L.P.bump()
            ps.go(p, PjTup{beg})
        case 9n:
          ps.go(p, PjList{beg})
        case 10n:
          chr.lit(beg)
        case 11n:
          str.lit(beg)
        case 12n:
          hole.lit()
        case _:
          L.P.fail(X.PV, "a term")

    case 1n+p PjName{cls, +k, +beg}:
      match cls:
        case 0n:
          X.ps.ret(C.TTyp{C.TQua{C.QL{}, C.NoSp{}}, C.NoSp{}})
        case 1n:
          X.ps.ret(C.TTyp{C.TQua{C.QM{}, C.NoSp{}}, C.NoSp{}})
        case 2n:
          X.ps.ret(C.TQnt{C.NoSp{}})
        case 3n:
          do L.P<X.PV>:
            L.P.eat("(")
            g : X.PV <- ps.go(p, PjTerm{1})
            L.P.eat(")")
            return X.PvT{C.TTyp{X.pv.t(g), C.NoSp{}}}
        case 4n:
          ps.go(p, PjDoHead{beg})
        case 5n:
          L.P.fail.from(X.PV, "a term (a match heads a def body, not a term)", beg)
        case 6n:
          L.P.fail.from(X.PV, "a match heading this case (this case is orphaned)", beg)
        case 7n:
          L.P.fail.from(X.PV, "a do-block heading this return", beg)
        case 8n:
          L.P.fail.from(X.PV, "a term (the keyword '" ++ k ++ "' cannot head one)", beg)
        case _:
          do L.P<X.PV>:
            z : Bool <- L.P.take([123])
            X.ps.if(z, st => ps.go(p, PjCtr{k}, st), name.var(k, beg))

    case 1n+p PjCtr{+k}:
      do L.P<X.PV>:
        xs : X.PV <- ps.go(p, PjArgs{125, Nil{}})
        c : String <- R.P.reso_c(k)
        return X.PvT{C.TCtr{c, X.pv.ts(xs), C.NoSp{}}}

    case 1n+p PjNum{+beg}:
      do L.P<X.PV>:
        +c : L.Cur <- L.P.cur()
        +nm : X.Nm = X.num.read(L.cur.rest(c))
        L.P.mod_cur(L.cur.adv(num.len(nm)))
        num.go(num.kind(nm), nm, beg, st => ps.go(p, PjNumPlus{num.val(nm), beg}, st))

    case 1n+p PjNumPlus{+n, +beg}:
      do L.P<X.PV>:
        out : X.PV <- ps.go(p, PjTerm{1})
        spn : C.Sp <- R.P.span(beg)
        num.nat.plus(X.pv.t(out), n, spn)

    # parse_term_all(p, exi)
    case 1n+p PjAll{+exi}:
      do L.P<X.PV>:
        +beg : U32 <- L.P.pos()
        L.P.bump()
        q : C.Q <- all.quant(exi)
        +k : String <- L.P.name()
        L.P.eat(":")
        A : X.PV <- ps.go(p, PjTerm{2})
        L.P.eat("->")
        +n0 : U32 <- R.P.depth()
        i : U32 <- R.P.open(k)
        B : X.PV <- ps.go(p, PjTerm{1})
        R.P.close(n0)
        all.fin(exi, q, k, i, X.pv.t(A), X.pv.t(B), beg)

    # + D: a reusable binder's mark, or a datatype's leading quantities at &2
    case 1n+p PjPlus{+beg}:
      do L.P<X.PV>:
        +c : L.Cur <- L.P.cur()
        L.P.bump()
        +r : X.PV <- ps.go(p, PjTerm{13})
        +s : C.Sp <- R.P.span(beg)
        +t : C.Tm = X.pv.t(r)
        +k : String <- plus.key(t)
        +tld : C.Tld <- R.P.tld(k)
        plus.fin(t, s, beg, L.cur.prev(c), k, tld)

    # \{K: h; ...; tail}
    case 1n+p PjMat{+beg, +arms}:
      do L.P<X.PV>:
        L.P.skip()
        z : Bool <- L.P.take([125])
        X.ps.if(z, mat.end(beg, arms, C.TEfq{C.NoSp{}}), st => ps.go(p, PjMatArm{beg, arms}, st))

    case 1n+p PjMatArm{+beg, +arms}:
      do L.P<X.PV>:
        tv : X.PV <- ps.go(p, PjTerm{1})
        L.P.skip()
        +t : C.Tm = X.pv.t(tv)
        +nm : Maybe<&2, String> = X.tm.vr(t)
        z : Bool <- mat.colon(Maybe.is_some(&2, String, nm))
        X.ps.if(z,
          st => (do L.P<X.PV>:
            h : X.PV <- ps.go(p, PjTerm{1})
            c : String <- R.P.reso_c(Maybe.default(&2, String, nm, ""))
            L.P.skip()
            _ : Bool <- L.P.take([59])
            ps.go(p, PjMat{beg, X.Am{c, X.pv.t(h)} <> arms}))(st),
          st => (do L.P<X.PV>:
            L.P.skip()
            _ : Bool <- L.P.take([59])
            L.P.eat("}")
            mat.end(beg, arms, t))(st))

    # %e@E : P; f
    case 1n+p PjRwt{+beg}:
      do L.P<X.PV>:
        L.P.bump()
        e0 : X.PV <- ps.go(p, PjTerm{1})
        L.P.skip()
        at : Bool <- L.P.take([64])
        +t : C.Tm = X.pv.t(e0)
        X.ps.if(at,
          st => (do L.P<X.PV>:
            +k : String <- rwt.name(X.tm.var.k(t))
            e : X.PV <- ps.go(p, PjTerm{1})
            ps.go(p, PjRwt2{beg, t, k, X.pv.t(e)}))(st),
          st => ps.go(p, PjRwt2{beg, t, "", t}, st))

    case 1n+p PjRwt2{+beg, e0, +k, e}:
      do L.P<X.PV>:
        L.P.eat(":")
        +n0 : U32 <- R.P.depth()
        +xi : U32 <- R.P.fresh_index()
        R.P.push("_", xi)
        ei : U32 <- R.P.open(k)
        P : X.PV <- ps.go(p, PjTerm{1})
        R.P.close(n0)
        L.P.skip()
        _ : Bool <- L.P.take([59])
        f : X.PV <- ps.go(p, PjBlock{})
        +s : C.Sp <- R.P.span(beg)
        return X.PvT{C.TRwt{e, C.TLam{"_", xi, C.TLam{k, ei, X.pv.t(P), C.tm.s(e0), C.QL{}}, s, C.QL{}}, X.pv.t(f), s}}

    # {==}, {x : T}, {a == b : T}, {a != b : T}
    case 1n+p PjBrace{+beg}:
      do L.P<X.PV>:
        L.P.bump()
        L.P.skip()
        rf : Bool <- L.P.take([61, 61])
        X.ps.if(rf,
          st => (do L.P<X.PV>:
            L.P.eat("}")
            return X.PvT{C.TRfl{C.NoSp{}}})(st),
          st => (do L.P<X.PV>:
            a : X.PV <- ps.go(p, PjTerm{1})
            L.P.skip()
            ne : Bool <- L.P.take([33, 61])
            pos : U32 <- L.P.pos()
            ns : C.Sp <- R.P.span((pos - 2 : U32))
            ps.go(p, PjBrace2{beg, X.pv.t(a), ne, ns}))(st))

    case 1n+p PjBrace2{+beg, a, +ne, ns}:
      do L.P<X.PV>:
        eq : Bool <- brace.eq(ne)
        b : Maybe<&2, C.Tm> <- brace.b(Bool.or(ne, eq), st => ps.go(p, PjTerm{1}, st))
        L.P.eat(":")
        T : X.PV <- ps.go(p, PjTerm{1})
        L.P.eat("}")
        brace.fin(b, ne, a, X.pv.t(T), ns, beg)

    # ( body ), (a, b, ..), (x : T)
    case 1n+p PjTup{+beg}:
      do L.P<X.PV>:
        L.P.skip()
        c : U32 <- L.P.col()
        b : X.PV <- ps.go(p, PjBody{(c - 1 : U32)})
        L.P.skip()
        +bd : C.Body = X.pv.b(b)
        cm : Bool <- tup.comma(body.is_term(bd))
        X.ps.if(cm,
          st => (do L.P<X.PV>:
            rest : X.PV <- ps.go(p, PjTup{beg})
            k : String <- R.P.own_c("Tuple")
            s : C.Sp <- R.P.span(beg)
            return X.PvT{C.TCtr{k, [body.term(bd), X.pv.t(rest)], s}})(st),
          st => (do L.P<X.PV>:
            out : C.Tm <- F.flatten(bd, Nil{})
            an : Bool <- L.P.take([58])
            o2 : C.Tm <- tup.ann(an, out, st2 => ps.go(p, PjTerm{1}, st2))
            L.P.eat(")")
            return X.PvT{o2})(st))

    # [a, b], [x : T*n], [x : T^d]
    case 1n+p PjList{+beg}:
      do L.P<X.PV>:
        L.P.bump()
        L.P.skip()
        e : Bool <- L.P.at([93])
        X.ps.if(e,
          st => ps.go(p, PjArgsList{beg, Nil{}}, st),
          st => (do L.P<X.PV>:
            +x : X.PV <- ps.go(p, PjTerm{1})
            L.P.skip()
            col : Bool <- L.P.take([58])
            X.ps.if(col, st2 => ps.go(p, PjArr{beg, X.pv.t(x)}, st2), st2 => (do L.P<X.PV>:
              _ : Bool <- L.P.take([44])
              ps.go(p, PjArgsList{beg, [X.pv.t(x)]}))(st2)))(st))

    case 1n+p PjArr{+beg, x}:
      do L.P<X.PV>:
        Tv : X.PV <- ps.go(p, PjTerm{13})
        L.P.skip()
        +cnt : Bool <- L.P.take([42])
        arr.caret(cnt)
        n : X.PV <- ps.go(p, PjTerm{1})
        L.P.eat("]")
        +s : C.Sp <- R.P.span(beg)
        +T : C.Tm = X.pv.t(Tv)
        x0 : C.Tm <- ns.of(x, C.tm.head(T))
        d : C.Tm <- arr.depth(cnt, X.pv.t(n))
        k : String <- R.P.own_t("Array.new")
        return X.PvT{C.TApp{C.TApp{C.TApp{C.TRef{k, s, False{}}, T, s}, d, s}, x0, s}}

    case 1n+p PjArgsList{+beg, xs}:
      do L.P<X.PV>:
        ys : X.PV <- ps.go(p, PjArgs{93, List.reverse(&2, C.Tm, xs)})
        +spn : C.Sp <- R.P.span(beg)
        +con : String <- R.P.own_c("Con")
        nil : String <- R.P.own_c("Nil")
        return X.PvT{list.build(X.pv.ts(ys), con, spn, C.TCtr{nil, Nil{}, spn})}

    # do M<ts..>: statements
    case 1n+p PjDoHead{+beg}:
      do L.P<X.PV>:
        +m : String <- L.P.name()
        L.P.skip()
        lt : Bool <- L.P.take([60])
        do.lt(lt, m)
        +k : String <- R.P.reso_t(m)
        xs : X.PV <- ps.go(p, PjArgs{62, Nil{}})
        s : C.Sp <- R.P.span(beg)
        ts : List<&2, C.Tm> <- R.P.fill(k, X.pv.ts(xs), s)
        L.P.eat(":")
        L.P.skip()
        c : U32 <- L.P.col()
        ps.go(p, PjDo{m, ts, c})

    # parse_term_do_stmt(p, m, ts, col)
    case 1n+p PjDo{+m, +ts, +col}:
      do L.P<X.PV>:
        L.P.skip()
        +beg : U32 <- L.P.pos()
        r : Bool <- L.P.word("return")
        X.ps.if(r,
          st => (do L.P<X.PV>:
            e : X.PV <- ps.go(p, PjTerm{1})
            R.P.do_end()
            s : C.Sp <- R.P.span(beg)
            t : C.Tm <- R.P.call(m ++ ".pure", List.append(&2, C.Tm, ts, [X.pv.t(e)]), s)
            return X.PvT{t})(st),
          st => (do L.P<X.PV>:
            tv : X.PV <- ps.go(p, PjTerm{1})
            L.P.skip()
            +t : C.Tm = X.pv.t(tv)
            +typed : Bool <- do.typed(Maybe.is_some(&2, String, X.tm.var.k(t)))
            step : Bool <- do.step(typed, col)
            ps.go(p, PjDoStmt{m, ts, col, beg, t, typed, step}))(st))

    case 1n+p PjDoStmt{+m, +ts, +col, +beg, +t, +typed, +step}:
      do L.P<X.PV>:
        A : X.PV <- do.ty(typed, step, t, st => ps.go(p, PjTerm{2}, st))
        L.P.skip()
        +asg : Bool <- do.asg(typed)
        arrow : Bool <- do.arrow(typed, asg, step)
        X.ps.if(Bool.and(Bool.and(Bool.not(typed), Bool.not(step)), Bool.not(arrow)),
          do.last(m, ts, t),
          st => ps.go(p, PjDoBind{m, ts, col, beg, t, typed, step, X.pv.t(A), asg}, st))

    case 1n+p PjDoBind{+m, +ts, +col, +beg, +t, typed, +step, A, asg}:
      do L.P<X.PV>:
        vv : X.PV <- do.val(step, t, st => ps.go(p, PjTerm{1}, st))
        L.P.skip()
        _ : Bool <- L.P.take([59])
        +s : C.Sp <- R.P.span(beg)
        +n0 : U32 <- R.P.depth()
        +x : C.Pat <- X.P.bind(do.binder(typed, t))
        f : X.PV <- ps.go(p, PjDo{m, ts, col})
        R.P.close(n0)
        do.fin(asg, m, ts, x, X.pv.t(vv), A, X.pv.t(f), s)

    # parse_term_ops(p, tm, beg, lvl)
    case 1n+p PjOps{out, +beg, +lvl}:
      do L.P<X.PV>:
        L.P.skip()
        c : L.Cur <- L.P.cur()
        ps.go(p, PjOpsGo{X.ops.next(c, lvl), out, beg, lvl})

    case 1n+p PjOpsGo{op, out, +beg, +lvl}:
      match op:
        case X.OpStop{}:
          X.ps.ret(out)
        case X.OpCall{}:
          ps.go(p, PjCall{out, beg, lvl})
        case X.OpIndex{}:
          ps.go(p, PjIndex{out, beg, lvl})
        case X.OpLam{}:
          ps.go(p, PjLam{out, beg, lvl})
        case X.OpInfix{o, gl}:
          ps.go(p, PjOp{o, gl, out, beg, lvl})

    case 1n+p PjCall{out, +beg, +lvl}:
      do L.P<X.PV>:
        +o : C.Tm = call.unvar(out)
        bang : Bool <- L.P.at([33])
        X.ps.if(bang,
          st => (do L.P<X.PV>:
            b : C.Tm <- call.bang(o)
            ps.go(p, PjOps{b, beg, lvl}))(st),
          st => (do L.P<X.PV>:
            L.P.bump()
            tld : C.Tld <- R.P.tld(call.key(o))
            L.P.skip()
            ps.go(p, PjTpl{o, beg, lvl, R.tld.def_x(tld), Nil{}}))(st))

    case 1n+p PjTpl{+out, +beg, +lvl, +x, +ts}:
      do L.P<X.PV>:
        tl : Bool <- L.P.at([126])
        X.ps.if(Bool.and(U32.is_gt(x, 0), tl),
          st => (do L.P<X.PV>:
            tpl.full(U32.is_eq(X.tms.len(ts), x), out, x)
            L.P.bump()
            a : X.PV <- ps.go(p, PjTerm{1})
            L.P.skip()
            _ : Bool <- L.P.take([44])
            L.P.skip()
            ps.go(p, PjTpl{out, beg, lvl, x, X.pv.t(a) <> ts}))(st),
          st => (do L.P<X.PV>:
            xs : X.PV <- ps.go(p, PjArgs{41, Nil{}})
            +s : C.Sp <- R.P.span(beg)
            ps.go(p, PjOps{C.tm.app(out, List.append(&2, C.Tm, List.reverse(&2, C.Tm, ts), X.pv.ts(xs)), s), beg, lvl}))(st))

    case 1n+p PjIndex{+out, +beg, +lvl}:
      do L.P<X.PV>:
        L.P.bump()
        ix : X.PV <- ps.go(p, PjTerm{1})
        L.P.eat("]")
        +s : C.Sp <- R.P.span(beg)
        uk : String <- R.P.own_t("U32")
        +u : C.Tm = C.TRef{uk, s, False{}}
        +i : C.Tm <- ns.of(X.pv.t(ix), u)
        L.P.skip()
        nl : Bool <- L.P.nl()
        w : Bool <- idx.set(nl)
        X.ps.if(w,
          st => (do L.P<X.PV>:
            v : X.PV <- ps.go(p, PjTerm{3})
            k : String <- R.P.own_t("Array.set")
            ps.go(p, PjOps{C.tm.app(C.TRef{k, s, False{}}, [u, out, i, X.pv.t(v)], s), beg, lvl}))(st),
          st => (do L.P<X.PV>:
            k : String <- R.P.own_t("Array.get")
            ps.go(p, PjOps{C.tm.app(C.TRef{k, s, False{}}, [u, out, i], s), beg, lvl}))(st))

    case 1n+p PjLam{out, +beg, +lvl}:
      do L.P<X.PV>:
        L.P.mod_cur(L.cur.adv(2n))
        +n0 : U32 <- R.P.depth()
        x : C.Pat <- X.P.bind(out)
        f : X.PV <- ps.go(p, PjBlock{})
        R.P.close(n0)
        ps.go(p, PjOps{lam.of(x, X.pv.t(f)), beg, lvl})

    case 1n+p PjOp{+o, +gl, +out, +beg, +lvl}:
      do L.P<X.PV>:
        +n : Nat = T.len(R.op.text(o))
        L.P.mod_cur(L.cur.adv(n))
        +pos : U32 <- L.P.pos()
        +t : C.Sp <- R.P.span2((pos - U32.from_nat(n) : U32), pos)
        +b : X.PV <- ps.go(p, PjTerm{Bool.pick(U32, R.op.right(o), R.op.prc(o), (R.op.prc(o) + 1 : U32))})
        +s : C.Sp <- R.P.span(beg)
        L.P.skip()
        +c : L.Cur <- L.P.cur()
        op.tyarg(Bool.and(Bool.and(Nat.is_eq(o, 6n), gl), X.tyarg.bad(L.cur.rest(c))))
        +ty : Bool = Bool.and(Nat.is_eq(o, 6n), Bool.or(T.prefix(L.cur.rest(c), [62]), T.prefix(L.cur.rest(c), [44])))
        X.ps.if(ty,
          st => ps.go(p, PjOpTy{out, X.pv.t(b), s, beg, lvl}, st),
          st => (do L.P<X.PV>:
            r : C.Tm <- op.build(o, out, X.pv.t(b), s, t)
            ps.go(p, PjOps{r, beg, lvl}))(st))

    case 1n+p PjOpTy{out, b, +s, +beg, +lvl}:
      do L.P<X.PV>:
        k : String <- opty.name(X.tm.vr(out))
        _ : Bool <- L.P.take([44])
        +d : String <- R.P.reso_t(k)
        rest : X.PV <- ps.go(p, PjArgs{62, Nil{}})
        xs : List<&2, C.Tm> <- R.P.fill(d, b <> X.pv.ts(rest), s)
        ps.go(p, PjOps{C.TAdt{d, xs, Nil{}, s}, beg, lvl})

    # parse_term_args(p, close)
    case 1n+p PjArgs{+close, +acc}:
      do L.P<X.PV>:
        L.P.skip()
        z : Bool <- L.P.take([close])
        X.ps.if(z, L.P.pure(X.PV, X.PvTs{List.reverse(&2, C.Tm, acc)}),
          st => (do L.P<X.PV>:
            x : X.PV <- ps.go(p, PjTerm{1})
            L.P.skip()
            _ : Bool <- L.P.take([44])
            ps.go(p, PjArgs{close, X.pv.t(x) <> acc}))(st))

    # parse_terms
    case 1n+p PjTerms{acc}:
      do L.P<X.PV>:
        x : X.PV <- ps.go(p, PjTerm{1})
        L.P.skip()
        z : Bool <- L.P.take([58])
        +acc2 : List<&2, C.Tm> = X.pv.t(x) <> acc
        X.ps.if(z, L.P.pure(X.PV, X.PvTs{List.reverse(&2, C.Tm, acc2)}),
          st => (do L.P<X.PV>:
            _ : Bool <- L.P.take([44])
            ps.go(p, PjTerms{acc2}))(st))

    # parse_block
    case 1n+p PjBlock{}:
      do L.P<X.PV>:
        L.P.skip()
        c : U32 <- L.P.col()
        b : X.PV <- ps.go(p, PjBody{(c - 1 : U32)})
        t : C.Tm <- F.flatten(X.pv.b(b), Nil{})
        return X.PvT{t}

    # parse_body(p, col)
    case 1n+p PjBody{+col}:
      do L.P<X.PV>:
        L.P.skip()
        +beg : U32 <- L.P.pos()
        +bcol : U32 <- L.P.col()
        m : Bool <- L.P.word("match")
        X.ps.if(m, st => ps.go(p, PjMatch{col, beg}, st), st => ps.go(p, PjLocal{col, beg, bcol}, st))

    case 1n+p PjMatch{+col, +beg}:
      do L.P<X.PV>:
        es : X.PV <- ps.go(p, PjTerms{Nil{}})
        L.P.skip()
        c : U32 <- L.P.col()
        ps.go(p, PjRows{col, c, X.pv.ts(es), beg, Nil{}})

    case 1n+p PjRows{+col, +ccol, +es, +beg, +acc}:
      do L.P<X.PV>:
        z : Bool <- rows.cond(col, ccol)
        X.ps.if(z, st => ps.go(p, PjRow{col, ccol, es, beg, acc}, st),
          st => (do L.P<X.PV>:
            s : C.Sp <- R.P.span(beg)
            return X.PvB{C.BMat{es, List.reverse(&2, C.Row, acc), s}})(st))

    case 1n+p PjRow{+col, +ccol, +es, +beg, +acc}:
      do L.P<X.PV>:
        +rcol : U32 <- L.P.col()
        _ : Bool <- L.P.word("case")
        L.P.skip()
        +qbeg : U32 <- L.P.pos()
        qv : X.PV <- ps.go(p, PjTerms{Nil{}})
        +qs : List<&2, C.Tm> = X.pv.ts(qv)
        +e : L.Env <- L.P.env()
        X.ps.if(U32.is_eq(X.tms.len(qs), X.tms.len(es)),
          st => (do L.P<X.PV>:
            +n0 : U32 <- R.P.depth()
            pp : X.PV <- ps.go(p, PjPats{qs, False{}, Nil{}})
            f : X.PV <- ps.go(p, PjBody{rcol})
            R.P.close(n0)
            ps.go(p, PjRows{col, ccol, es, beg, C.Row{X.pv.ps(pp), X.pv.b(f)} <> acc}))(st),
          rows.count.fail(L.env.txt(e), qs, X.tms.len(es), qbeg))

    case 1n+p PjLocal{+col, +beg, +bcol}:
      do L.P<X.PV>:
        neg : Bool <- L.P.take([45])
        X.ps.if(neg,
          st => (do L.P<X.PV>:
            k : String <- L.P.name()
            s : C.Sp <- R.P.span(beg)
            L.P.skip()
            ps.go(p, PjLocalTs{col, beg, bcol, C.QN{}, [C.TVar{k, 0, s}]}))(st),
          st => (do L.P<X.PV>:
            t : X.PV <- ps.go(p, PjTerm{1})
            L.P.skip()
            ps.go(p, PjLocalTs{col, beg, bcol, C.QL{}, [X.pv.t(t)]}))(st))

    case 1n+p PjLocalTs{+col, +beg, +bcol, +q, +ts}:
      do L.P<X.PV>:
        z : Bool <- local.more(q)
        X.ps.if(z,
          st => (do L.P<X.PV>:
            t : X.PV <- ps.go(p, PjTerm{1})
            L.P.skip()
            ps.go(p, PjLocalTs{col, beg, bcol, q, X.pv.t(t) <> ts}))(st),
          st => ps.go(p, PjLocalT{col, beg, bcol, q, List.reverse(&2, C.Tm, ts)}, st))

    case 1n+p PjLocalT{+col, +beg, +bcol, +q, +ts}:
      do L.P<X.PV>:
        +at : U32 <- L.P.pos()
        +hs : U32 <- R.P.hols()
        +c0 : L.Cur <- L.P.cur()
        colon : Bool <- L.P.at([58])
        seen : Bool <- R.P.ann_has(at)
        X.ps.if(Bool.and(Bool.and(U32.is_eq(X.tms.len(ts), 1), colon), Bool.not(seen)),
          st => (do L.P<X.PV>:
            L.P.bump()
            T : X.PV <- ps.go(p, PjTerm{1})
            L.P.skip()
            eq : Bool <- L.P.at([61])
            X.ps.if(eq,
              st2 => ps.go(p, PjLocalU{col, beg, bcol, q, ts, Some{X.pv.t(T)}}, st2),
              st2 => (do L.P<X.PV>:
                R.P.ann_add(at)
                L.P.set_cur(c0)
                R.P.set_hols(hs)
                ps.go(p, PjLocalU{col, beg, bcol, q, ts, None{}}))(st2)))(st),
          st => (do L.P<X.PV>:
            L.P.skip()
            ps.go(p, PjLocalU{col, beg, bcol, q, ts, None{}}))(st))

    case 1n+p PjLocalU{+col, +beg, +bcol, +q, +ts, +T}:
      do L.P<X.PV>:
        +eq : Bool <- L.P.at([61])
        +eqeq : Bool <- L.P.at([61, 61])
        X.ps.if(Bool.and(Bool.and(Bool.not(maybe.is(T)), C.q.is_lone(q)), Bool.and(U32.is_eq(X.tms.len(ts), 1), Bool.not(Bool.and(eq, Bool.not(eqeq))))),
          st => (do L.P<X.PV>:
            +w : Maybe<&2, C.Tm> <- X.P.term_write(tms.first(ts), beg)
            +t : C.Tm = tms.first(ts)
            more : Bool <- local.write.more(maybe.is(w), bcol)
            ps.go(p, PjLocalW{col, beg, q, t, w, more}))(st),
          st => (do L.P<X.PV>:
            e : L.Env <- L.P.env()
            local.plus(X.plus.first(L.env.txt(e), List.drop(&2, C.Tm, ts, 1n)), Bool.or(Bool.not(eq), eqeq))
            L.P.eat("=")
            vs : List<&2, C.Tm> <- local.typed(T, beg, st2 => ps.go(p, PjTerm{1}, st2))
            ps.go(p, PjLocalV{col, beg, q, ts, T, vs}))(st))

    case 1n+p PjLocalW{+col, +beg, +q, +t, w, more}:
      match w more:
        case Some{v} True{}:
          ps.go(p, PjLocalV{col, beg, q, [v], None{}, [t]})
        case _ _:
          L.P.pure(X.PV, X.PvB{C.BTm{t}})

    case 1n+p PjLocalV{+col, +beg, +q, +ts, +T, +vs}:
      X.ps.if(U32.is_lt(X.tms.len(vs), X.tms.len(ts)),
        st => (do L.P<X.PV>:
          v : X.PV <- ps.go(p, PjTerm{1})
          ps.go(p, PjLocalV{col, beg, q, ts, T, X.pv.t(v) <> vs}))(st),
        st => (do L.P<X.PV>:
          L.P.skip()
          _ : Bool <- L.P.take([59])
          +n0 : U32 <- R.P.depth()
          ks : X.PV <- ps.go(p, PjPats{ts, Bool.or(U32.is_gt(X.tms.len(ts), 1), maybe.is(T)), Nil{}})
          f : X.PV <- ps.go(p, PjBody{col})
          R.P.close(n0)
          return X.PvB{C.BLoc{X.pv.ps(ks), q, List.reverse(&2, C.Tm, vs), X.pv.b(f)}})(st))

    # the patterns of a case or a let, in order
    case 1n+p PjPats{ts, +names, acc}:
      match ts:
        case Nil{}:
          L.P.pure(X.PV, X.PvPs{List.reverse(&2, C.Pat, acc)})
        case Con{+t, r}:
          X.ps.if(Bool.and(names, Bool.not(Maybe.is_some(&2, String, X.tm.var.k(t)))),
            L.P.err(X.PV, "a name (a parallel or typed let binds names; destructure in its body)", None{}, C.tm.s(t)),
            st => (do L.P<X.PV>:
              x : X.PV <- ps.go(p, PjPat{t})
              ps.go(p, PjPats{r, names, X.pv.p(x) <> acc}))(st))

    # parse_patt(p, t)
    case 1n+p PjPat{t}:
      match t:
        case C.TVar{+k, +i, +s}:
          do L.P<X.PV>:
            c : String <- R.P.reso_c(k)
            n : U32 <- R.P.ctr_n(c)
            pat.var(U32.is_eq(n, C.NONE()), C.TVar{k, i, s}, k, s)
        case C.TVr{+k, +i, +s, +r}:
          do L.P<X.PV>:
            c : String <- R.P.reso_c(k)
            n : U32 <- R.P.ctr_n(c)
            pat.var(U32.is_eq(n, C.NONE()), C.TVr{k, i, s, r}, k, s)
        case C.TCtr{+k, +xs, +s}:
          do L.P<X.PV>:
            +n : U32 <- R.P.ctr_n(k)
            X.ps.if(Bool.and(Bool.not(U32.is_eq(n, C.NONE())), U32.is_eq(n, X.tms.len(xs))),
              st => (do L.P<X.PV>:
                ps : X.PV <- ps.go(p, PjPats{xs, False{}, Nil{}})
                return X.PvP{C.PCtr{k, X.pv.ps(ps), s}})(st),
              pat.ctr.fail(n, k, s))
        case C.TNat{v, s}:
          ps.go(p, PjPat{X.lit.step(C.TNat{v, s})})
        case C.TU32{v, s}:
          ps.go(p, PjPat{X.lit.step(C.TU32{v, s})})
        case C.TF32{v, s}:
          ps.go(p, PjPat{X.lit.step(C.TF32{v, s})})
        case C.TStr{v, s}:
          ps.go(p, PjPat{X.lit.step(C.TStr{v, s})})
        case +t:
          pat.other(C.tm.unapp(t), t)

    # parse_tele(p, close, tk)
    case 1n+p PjTele{+close, +tk, +te}:
      do L.P<X.PV>:
        L.P.skip()
        z : Bool <- L.P.take([close])
        X.ps.if(z, L.P.pure(X.PV, X.PvTe{List.reverse(&2, X.Te, te), tk}),
          st => (do L.P<X.PV>:
            tl : Bool <- L.P.at([126])
            tele.tilde(Bool.and(Bool.and(U32.is_eq(close, 41), tl), U32.is_lt(tk, X.tele.len(te))))
            +ct : Bool <- tele.ct(U32.is_eq(close, 41))
            q : C.Q <- tele.q(ct)
            ps.go(p, PjTeleCell{close, tk, te, ct, q}))(st))

    case 1n+p PjTeleCell{+close, +tk, +te, +ct, +q}:
      do L.P<X.PV>:
        +beg : U32 <- L.P.pos()
        +k : String <- L.P.name()
        tele.dup(Bool.and(U32.is_eq(close, 125), X.tele.has(te, k)), k)
        +s : C.Sp <- R.P.span(beg)
        L.P.skip()
        colon : Bool <- L.P.at([58])
        +bare : Bool = Bool.and(C.q.is_lone(q), Bool.not(colon))
        tele.colon(bare)
        Tv : X.PV <- tele.ty(bare, s, st => ps.go(p, PjTerm{1}, st))
        i : U32 <- R.P.open(k)
        L.P.skip()
        _ : Bool <- L.P.take([44])
        ps.go(p, PjTele{close, Bool.pick(U32, ct, (tk + 1 : U32), tk), X.Te{Bool.pick(C.Q, bare, C.QN{}, q), k, i, X.pv.t(Tv), s} <> te})

    # parse_def(p, u)
    case 1n+p PjDef{+u}:
      do L.P<X.PV>:
        +nm : String <- L.P.name()
        +q : String <- R.P.reso_t(nm)
        +tld : C.Tld <- R.P.tld(q)
        +isl : Bool = tld.law(tld)
        k : String <- def.key(isl, q, nm)
        un : Bool <- L.P.take([63])
        L.P.eat("(")
        L.P.skip()
        tl : Bool <- L.P.at([126])
        def.tilde(Bool.and(isl, tl))
        ps.go(p, PjDefTele{Bool.or(un, u), nm, k, isl, tld.x(tld)})

    case 1n+p PjDefTele{+u, +nm, +k, +islaw, +lx}:
      do L.P<X.PV>:
        +tv : X.PV <- ps.go(p, PjTele{41, 0, Nil{}})
        L.P.skip()
        +te : List<&2, X.Te> = X.pv.te(tv)
        +tk : U32 = X.pv.tk(tv)
        X.ps.if(islaw,
          st => (do L.P<X.PV>:
            def.fill.chk(X.tele.all_qnt(te), U32.is_lt(X.tele.len(te), lx), lx)
            P.set_tld(k, C.TlDef{X.tele.len(te), lx, False{}, False{}, False{}})
            ps.go(p, PjDefBody{k, True{}, te, lx, u, C.TEfq{C.NoSp{}}}))(st),
          st => (do L.P<X.PV>:
            ar : Bool <- L.P.take([45, 62])
            def.arrow(ar, nm)
            rv : X.PV <- ps.go(p, PjTerm{1})
            +T : C.Tm = X.tele.bind(te, X.pv.t(rv))
            X.P.higher(T)
            P.set_tld(k, C.TlDef{X.tele.len(te), tk, False{}, False{}, False{}})
            ps.go(p, PjDefBody{k, False{}, te, tk, u, T}))(st))

    case 1n+p PjDefBody{+k, +islaw, +te, +x, +u, +T}:
      do L.P<X.PV>:
        L.P.eat(":")
        imp : Bool <- L.P.at_word("import")
        X.ps.if(imp,
          st => (do L.P<X.PV>:
            def.tpl(U32.is_gt(x, 0))
            P.set_tld(k, C.TlDef{X.tele.len(te), x, False{}, False{}, True{}})
            +c : L.Cur <- L.P.cur()
            fs : List<&2, String> <- def.ffi.go(1n+T.len(L.cur.rest(c)), Nil{})
            P.decl(C.DDef{k, X.tele.len(te), x, T, None{}, u, fs, False{}, islaw})
            return X.PvU{})(st),
          st => (do L.P<X.PV>:
            b : X.PV <- ps.go(p, PjBody{0})
            t : C.Tm <- F.flatten(X.pv.b(b), X.tele.vars(te))
            v : C.Tm <- X.P.norm(t)
            P.set_tld(k, C.TlDef{X.tele.len(te), x, True{}, False{}, False{}})
            P.decl(C.DDef{k, X.tele.len(te), x, T, Some{v}, u, Nil{}, False{}, islaw})
            return X.PvU{})(st))

    # type K<params> is Kind: constructors
    case 1n+p PjType{}:
      do L.P<X.PV>:
        nm : String <- L.P.name()
        +k : String <- R.P.fresh(True{}, "a fresh name", nm)
        L.P.skip()
        lt : Bool <- L.P.take([60])
        pv : X.PV <- type.params(lt, st => ps.go(p, PjTele{62, 0, Nil{}}, st))
        isw : Bool <- L.P.word("is")
        type.is(isw)
        K : X.PV <- ps.go(p, PjTerm{1})
        L.P.eat(":")
        +te : List<&2, X.Te> = X.pv.te(pv)
        +T : C.Tm = X.tele.bind(te, X.pv.t(K))
        X.P.higher(T)
        P.set_tld(k, C.TlAdt{X.tele.len(te), X.tele.g(te, 0)})
        ps.go(p, PjTypeCtrs{k, te, T, Nil{}})

    case 1n+p PjTypeCtrs{+k, +te, +T, +cs}:
      do L.P<X.PV>:
        L.P.skip()
        c : U32 <- L.P.peek()
        stop : Bool <- type.stop(T.is_head(c))
        X.ps.if(stop,
          st => (do L.P<X.PV>:
            P.decl(C.DAdt{k, X.tele.len(te), X.tele.g(te, 0), T, List.reverse(&2, C.Cn, cs)})
            return X.PvU{})(st),
          st => (do L.P<X.PV>:
            cn : String <- L.P.name()
            +c : String <- R.P.fresh(False{}, "a fresh constructor name", cn)
            L.P.eat("{")
            +n1 : U32 <- R.P.depth()
            fv : X.PV <- ps.go(p, PjTele{125, 0, Nil{}})
            +fs : List<&2, X.Te> = X.pv.te(fv)
            +cT : C.Tm = X.tele.bind(List.append(&2, X.Te, te, fs), C.TAdt{k, X.tele.tip(te), Nil{}, C.NoSp{}})
            X.P.higher(cT)
            R.P.close(n1)
            P.set_ctr(c, X.tele.len(fs))
            ps.go(p, PjTypeCtrs{k, te, T, C.Cn{c, X.tele.len(fs), cT} <> cs}))(st))

    # law K: clauses, then the claim
    case 1n+p PjLaw{}:
      do L.P<X.PV>:
        nm : String <- L.P.name()
        k : String <- R.P.fresh(True{}, "a fresh name", nm)
        L.P.eat(":")
        ps.go(p, PjLawCls{k, Nil{}, 0})

    case 1n+p PjLawCls{+k, +cl, +tc}:
      do L.P<X.PV>:
        +f : Bool <- L.P.at_word("for")
        e : Bool <- law.exs(f)
        X.ps.if(Bool.or(f, e),
          st => (do L.P<X.PV>:
            +all : Bool <- L.P.word("for")
            law.exs.take(all)
            L.P.skip()
            tl : Bool <- L.P.at([126])
            law.tilde(Bool.and(Bool.and(all, tl), U32.is_lt(tc, U32.from_nat(List.length(&2, X.Cl, cl)))))
            +ct : Bool <- law.ct(all)
            q : C.Q <- law.q(ct, all)
            +beg : U32 <- L.P.pos()
            +c : String <- L.P.name()
            +s : C.Sp <- R.P.span(beg)
            L.P.eat(":")
            A : X.PV <- ps.go(p, PjTerm{1})
            wh : Bool <- L.P.at_word("where")
            A2 : C.Tm <- law.where(wh, c, s, X.pv.t(A), st2 => ps.go(p, PjTerm{1}, st2))
            i : U32 <- R.P.open(c)
            ps.go(p, PjLawCls{k, X.Cl{all, q, c, i, A2, s} <> cl, Bool.pick(U32, ct, (tc + 1 : U32), tc)}))(st),
          st => (do L.P<X.PV>:
            bv : X.PV <- ps.go(p, PjBlock{})
            ex : String <- R.P.own_t("Exists")
            +cs : List<&2, X.Cl> = List.reverse(&2, X.Cl, cl)
            +T : C.Tm = X.law.type(ex, cs, X.pv.t(bv))
            X.P.higher(T)
            +n : U32 = X.law.n(cs, 0)
            P.set_tld(k, C.TlDef{n, tc, False{}, False{}, False{}})
            P.decl(C.DDef{k, n, tc, T, None{}, False{}, Nil{}, True{}, False{}})
            return X.PvU{})(st))

    # parse_book: def, @unsafe def, type, law, until the end
    case 1n+p PjBook{}:
      do L.P<X.PV>:
        L.P.skip()
        c : L.Cur <- L.P.cur()
        X.ps.if(List.is_empty(&2, U32, L.cur.rest(c)), L.P.pure(X.PV, X.PvU{}),
          st => (do L.P<X.PV>:
            P.reset()
            at : Bool <- L.P.take([64])
            X.ps.if(at,
              st2 => (do L.P<X.PV>:
                un : Bool <- L.P.word("unsafe")
                book.unsafe(un)
                d : Bool <- L.P.word("def")
                book.def(d)
                _ : X.PV <- ps.go(p, PjDef{True{}})
                ps.go(p, PjBook{}))(st2),
              st2 => (do L.P<X.PV>:
                d : Bool <- L.P.word("def")
                X.ps.if(d,
                  st3 => (do L.P<X.PV>:
                    _ : X.PV <- ps.go(p, PjDef{False{}})
                    ps.go(p, PjBook{}))(st3),
                  st3 => (do L.P<X.PV>:
                    ty : Bool <- L.P.word("type")
                    X.ps.if(ty,
                      st4 => (do L.P<X.PV>:
                        _ : X.PV <- ps.go(p, PjType{})
                        ps.go(p, PjBook{}))(st4),
                      st4 => (do L.P<X.PV>:
                        lw : Bool <- L.P.word("law")
                        X.ps.if(lw,
                          st5 => (do L.P<X.PV>:
                            _ : X.PV <- ps.go(p, PjLaw{})
                            ps.go(p, PjBook{}))(st5),
                          L.P.fail(X.PV, "'def', 'type' or 'law'")))(st4)))(st3)))(st2)))(st))

# parse_book(book, dir, src, ns, al)
def parse.book(st: L.St) -> L.R<X.PV>:
  ps.go(4294967295n, PjBook{}, st)

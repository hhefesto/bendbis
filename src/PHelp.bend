import Base
import ./Text.bend as T
import ./Core.bend as C
import ./Lex.bend as L
import ./Res.bend as R
import ./Num.bend as N
import ./High.bend as H
import ./Show.bend as S

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# PHelp: what the parser's one recursive def (Parse.bend, ps.go) answers,
# and the parts of bend.ts's parser that need no recursion into it: the
# decisions read off the cursor, literals (parse_char, NUMBER, lit_of,
# lit_step, word_to_term), term_write, parse_bind, and the pattern error
# that shows its term.

# a telescope cell: quantity, name, index, type, span
type Te is Data:
  Te{q: C.Q, k: String, i: U32, T: C.Tm, s: C.Sp}

# a law clause: for (all) or exs, quantity, name, index, type, span
type Cl is Data:
  Cl{all: Bool, q: C.Q, c: String, i: U32, A: C.Tm, s: C.Sp}

# a lambda-match arm
type Am is Data:
  Am{k: String, h: C.Tm}

type PV is Data:
  PvT{t: C.Tm}
  PvTs{ts: List<&2, C.Tm>}
  PvB{b: C.Body}
  PvP{p: C.Pat}
  PvPs{ps: List<&2, C.Pat>}
  PvTe{te: List<&2, Te>, tk: U32}
  PvU{}
  PvCl{cl: List<&2, Cl>, tc: U32}

def pv.t(v: PV) -> C.Tm:
  match v:
    case PvT{t}:
      t
    case _:
      C.TEfq{C.NoSp{}}

def pv.ts(v: PV) -> List<&2, C.Tm>:
  match v:
    case PvTs{ts}:
      ts
    case _:
      Nil{}

def pv.b(v: PV) -> C.Body:
  match v:
    case PvB{b}:
      b
    case _:
      C.BTm{C.TEfq{C.NoSp{}}}

def pv.p(v: PV) -> C.Pat:
  match v:
    case PvP{p}:
      p
    case _:
      C.PCtr{"", Nil{}, C.NoSp{}}

def pv.ps(v: PV) -> List<&2, C.Pat>:
  match v:
    case PvPs{ps}:
      ps
    case _:
      Nil{}

def pv.te(v: PV) -> List<&2, Te>:
  match v:
    case PvTe{te, tk}:
      te
    case _:
      Nil{}

def pv.tk(v: PV) -> U32:
  match v:
    case PvTe{te, tk}:
      tk
    case _:
      0

def pv.cl(v: PV) -> List<&2, Cl>:
  match v:
    case PvCl{cl, tc}:
      cl
    case _:
      Nil{}

def pv.tc(v: PV) -> U32:
  match v:
    case PvCl{cl, tc}:
      tc
    case _:
      0

# Choices, their branches unrun
# -----------------------------

def ps.if(z: Bool, a: L.P(PV), b: L.P(PV)) -> L.P(PV):
  match z:
    case True{}:
      a
    case False{}:
      b

def ps.ifm(z: Maybe<&2, String>, a: String -> L.P(PV), b: L.P(PV)) -> L.P(PV):
  match z:
    case Some{s}:
      a(s)
    case None{}:
      b

def ps.ret(t: C.Tm) -> L.P(PV):
  L.P.pure(PV, PvT{t})

# Decisions read off the cursor
# -----------------------------

# parse_term_base's dispatch on the head unit
def base.punct(c: U32) -> Nat:
  match c:
    case 64:
      2n
    case 38:
      3n
    case 43:
      4n
    case 92:
      5n
    case 37:
      6n
    case 123:
      7n
    case 40:
      8n
    case 91:
      9n
    case 39:
      10n
    case 34:
      11n
    case 63:
      12n
    case _:
      13n

def base.cls(+c: U32) -> Nat:
  Bool.pick(Nat, T.is_head(c), 0n,
  Bool.pick(Nat, T.is_digit(c), 1n,
    base.punct(c)))

# a name's role at a term's head: 0-7 the keywords that head a form or a
# refusal (Type Data Quant Kind do match case return), 8 another keyword,
# 9 none
def kw.cls(+k: String) -> Nat:
  Bool.pick(Nat, String.eq(k, "Type"), 0n,
  Bool.pick(Nat, String.eq(k, "Data"), 1n,
  Bool.pick(Nat, String.eq(k, "Quant"), 2n,
  Bool.pick(Nat, String.eq(k, "Kind"), 3n,
  Bool.pick(Nat, String.eq(k, "do"), 4n,
  Bool.pick(Nat, String.eq(k, "match"), 5n,
  Bool.pick(Nat, String.eq(k, "case"), 6n,
  Bool.pick(Nat, String.eq(k, "return"), 7n,
  Bool.pick(Nat, L.is_keyword(k), 8n, 9n)))))))))

# \S on a unit (NONE, past the start, is no unit)
def non.space(+c: U32) -> Bool:
  Bool.and(Bool.not(U32.is_eq(c, C.NONE())), Bool.not(T.is_space(c)))

# what parse_term_ops does next: 0 stop at a newline before ( or [, 1 a
# call, 2 an index, 3 a lambda, 4 an operator (o), 5 stop
type Op is Data:
  OpStop{}
  OpCall{}
  OpIndex{}
  OpLam{}
  OpInfix{o: Nat, gl: Bool}

def ops.starts(xs: List<&2, U32>, s: List<&2, U32>) -> Bool:
  T.prefix(xs, s)

# an operator whose text starts with >
def op.gt(+o: Nat) -> Bool:
  Bool.or(Bool.or(Nat.is_eq(o, 8n), Nat.is_eq(o, 9n)), Nat.is_eq(o, 17n))

def ops.fires(+o: Nat, +lvl: U32, +gl: Bool, +nx: U32) -> Bool:
  +prc = R.op.prc(o)
  Bool.not(Bool.or(Bool.or(Bool.and(U32.is_lt(prc, lvl), Bool.not(Bool.and(Nat.is_eq(o, 6n), gl))),
    Bool.and(Bool.or(Nat.is_eq(o, 19n), Nat.is_eq(o, 18n)), Bool.or(U32.is_eq(nx, 62), T.is_head(nx)))),
    Bool.or(Bool.and(op.gt(o), gl), Bool.and(Nat.is_eq(o, 22n), Bool.not(T.is_space(nx))))))

def ops.infix(+xs: List<&2, U32>, +lvl: U32, +gl: Bool) -> Op:
  +o = R.op.find(xs)
  Bool.pick(Op, Bool.and(Bool.not(Nat.is_eq(o, 23n)), ops.fires(o, lvl, gl, T.at(xs, U32.from_nat(T.len(R.op.text(o)))))), OpInfix{o, gl}, OpStop{})

def ops.next(+c: L.Cur, +lvl: U32) -> Op:
  +xs = L.cur.rest(c)
  +nl = L.cur.nl(c)
  +gl = non.space(L.cur.prev(c))
  Bool.pick(Op, Bool.and(nl, Bool.or(T.prefix(xs, [40]), T.prefix(xs, [91]))), OpStop{},
  Bool.pick(Op, Bool.or(T.prefix(xs, [40]), T.prefix(xs, [33, 40])), OpCall{},
  Bool.pick(Op, T.prefix(xs, [91]), OpIndex{},
  Bool.pick(Op, Bool.and(U32.is_eq(lvl, 1), T.prefix(xs, [61, 62])), OpLam{},
    ops.infix(xs, lvl, gl)))))

# /^(->|[&|](?![&|]))/ on the next two units
def tyarg.bad(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{45, Con{62, t}}:
      True{}
    case Con{38, Con{38, t}}:
      False{}
    case Con{38, Con{124, t}}:
      False{}
    case Con{124, Con{38, t}}:
      False{}
    case Con{124, Con{124, t}}:
      False{}
    case Con{38, t}:
      True{}
    case Con{124, t}:
      True{}
    case _:
      False{}

# Literals
# --------

# word_to_term(n, s): bit 0 outermost
def word.go(+k: Nat, +n: U32, +s: C.Sp, out: C.Tm) -> C.Tm:
  match k:
    case 0n:
      out
    case 1n+i:
      word.go(i, n, s, C.TCtr{"WCon", [C.TCtr{Bool.pick(String, U32.is_eq(((n >> i : U32) .&. 1 : U32), 1), "True", "False"), Nil{}, s}, out], s})

def word.term(n: U32, +s: C.Sp) -> C.Tm:
  word.go(32n, n, s, C.TCtr{"WNil", Nil{}, s})

# lit_step: a literal's first constructor layer
def lit.step(t: C.Tm) -> C.Tm:
  match t:
    case C.TNat{+v, +s}:
      Bool.pick(C.Tm, U32.is_eq(v, 0), C.TCtr{"Zero", Nil{}, s}, C.TCtr{"Succ", [C.TNat{(v - 1 : U32), s}], s})
    case C.TU32{v, +s}:
      C.TCtr{"U32", [word.term(v, s)], s}
    case C.TF32{v, +s}:
      C.TCtr{"F32", [word.term(v, s)], s}
    case C.TStr{Nil{}, s}:
      C.TCtr{"SNil", Nil{}, s}
    case C.TStr{Con{c, r}, +s}:
      C.TCtr{"SCon", [C.TCtr{"Chr", [C.TU32{c, s}], s}, C.TStr{r, s}], s}
    case t:
      t

def is.scalar(+c: U32) -> Bool:
  Bool.and(U32.is_le(c, 1114111), Bool.or(U32.is_lt(c, 55296), U32.is_gt(c, 57343)))

def all.scalar(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Bool.and(is.scalar(c), all.scalar(t))

def lit.chain(cs: List<&2, U32>, +s: C.Sp) -> C.Tm:
  match cs:
    case Nil{}:
      C.TCtr{"SNil", Nil{}, s}
    case Con{c, t}:
      C.TCtr{"SCon", [C.TCtr{"Chr", [C.TU32{c, s}], s}, lit.chain(t, s)], s}

# lit_of(cs, s)
def lit.of(+cs: List<&2, U32>, +s: C.Sp) -> C.Tm:
  Bool.pick(C.Tm, all.scalar(cs), C.TStr{cs, s}, lit.chain(cs, s))

def esc.code(c: U32) -> U32:
  match c:
    case 110:
      10
    case 116:
      9
    case 114:
      13
    case 48:
      0
    case 92:
      92
    case 39:
      39
    case 34:
      34
    case _:
      C.NONE()

def esc.fin(+c: U32) -> L.P(U32):
  Bool.pick(L.P(U32), U32.is_eq(c, C.NONE()), L.P.fail(U32, "an escape (\\n \\t \\r \\0 \\\\ \\' \\\" \\u{1F600})"), L.P.pure(U32, c))

def esc.go.if(z: Bool, v: U32, n: Nat) -> L.P(U32):
  match z:
    case False{}:
      do L.P<U32>:
        L.P.mod_cur(L.cur.adv(n))
        return v
    case True{}:
      do L.P<U32>:
        c : U32 <- L.P.peek()
        L.P.bump()
        esc.fin(esc.code(c))

def esc.go(hx: U32 & Nat) -> L.P(U32):
  (+v, +n) = hx
  esc.go.if(Nat.is_eq(n, 0n), v, n)

def chr.pair(z: Bool, +h: U32, t: List<&2, U32>) -> L.P(U32):
  match z t:
    case True{} Con{+l, r}:
      do L.P<U32>:
        L.P.mod_cur(L.cur.adv(2n))
        return (((h - 55296 : U32) << 10n : U32) + ((l - 56320 : U32) + 65536 : U32) : U32)
    case _ _:
      do L.P<U32>:
        L.P.bump()
        return h

def chr.lo(t: List<&2, U32>) -> Bool:
  match t:
    case Con{+l, r}:
      Bool.and(U32.is_le(56320, l), U32.is_le(l, 57343))
    case Nil{}:
      False{}

def chr.unit(+h: U32, +t: List<&2, U32>) -> L.P(U32):
  chr.pair(Bool.and(Bool.and(U32.is_le(55296, h), U32.is_le(h, 56319)), chr.lo(t)), h, t)

def chr.plain.go(xs: List<&2, U32>) -> L.P(U32):
  match xs:
    case Nil{}:
      L.P.fail(U32, "a character")
    case Con{+h, t}:
      chr.unit(h, t)

# parse_char
def char.go(bs: Bool, +c: L.Cur) -> L.P(U32):
  match bs:
    case True{}:
      esc.go(L.hex.esc(T.take(L.cur.rest(c), 11n)))
    case False{}:
      chr.plain.go(L.cur.rest(c))

def P.char() -> L.P(U32):
  do L.P<U32>:
    bs : Bool <- L.P.take([92])
    +c : L.Cur <- L.P.cur()
    char.go(bs, c)

# the units of a string literal, up to its closing quote
def str.step(z: Bool, end: Bool, acc: List<&2, U32>, k: List<&2, U32> -> L.P(List<&2, U32>)) -> L.P(List<&2, U32>):
  match z end:
    case True{} _:
      L.P.pure(List<&2, U32>, List.reverse(&2, U32, acc))
    case False{} True{}:
      L.P.fail(List<&2, U32>, "a closing \"")
    case False{} False{}:
      do L.P<List<&2, U32>>:
        n : U32 <- P.char()
        k(n <> acc)

def str.go(fuel: Nat, acc: List<&2, U32>) -> L.P(List<&2, U32>):
  match fuel:
    case 0n:
      L.P.fail(List<&2, U32>, "a closing \"")
    case 1n+f:
      do L.P<List<&2, U32>>:
        z : Bool <- L.P.take([34])
        +c : L.Cur <- L.P.cur()
        str.step(z, List.is_empty(&2, U32, L.cur.rest(c)), acc, str.go(f))

# NUMBER = /(\d+)(n|\.\d+([eE][+-]?\d+)?)?/y at pos: its parts
type Nm is Data:
  Nm{ds: List<&2, U32>, kind: Nat, fs: List<&2, U32>, neg: Bool, xs: List<&2, U32>, len: Nat}

def digits.go(xs: List<&2, U32>, on: Bool) -> List<&2, U32>:
  match xs on:
    case _ False{}:
      Nil{}
    case Nil{} True{}:
      Nil{}
    case Con{+d, t} True{}:
      +z = T.is_digit(d)
      Bool.pick(List<&2, U32>, z, d <> digits.go(t, z), Nil{})

def digits.run(xs: List<&2, U32>) -> List<&2, U32>:
  digits.go(xs, True{})

def num.exp(xs: List<&2, U32>) -> Bool & List<&2, U32>:
  match xs:
    case Con{45, t}:
      (True{}, digits.run(t))
    case Con{43, t}:
      (False{}, digits.run(t))
    case t:
      (False{}, digits.run(t))

def num.exp.sign(xs: List<&2, U32>) -> Nat:
  match xs:
    case Con{45, t}:
      1n
    case Con{43, t}:
      1n
    case _:
      0n

def num.frac.x(+ds: List<&2, U32>, +fs: List<&2, U32>, +nd: Nat, +sg: Nat, ex: Bool & List<&2, U32>) -> Nm:
  (neg, +xs) = ex
  Bool.pick(Nm, List.is_empty(&2, U32, xs), Nm{ds, 2n, fs, False{}, Nil{}, nd},
    Nm{ds, 2n, fs, neg, xs, Nat.add(Nat.add(nd, 1n), Nat.add(sg, T.len(xs)))})

def num.frac.e(+ds: List<&2, U32>, +fs: List<&2, U32>, after: List<&2, U32>, +nd: Nat) -> Nm:
  match after:
    case Con{101, +t}:
      num.frac.x(ds, fs, nd, num.exp.sign(t), num.exp(t))
    case Con{69, t}:
      num.frac.x(ds, fs, nd, num.exp.sign(t), num.exp(t))
    case _:
      Nm{ds, 2n, fs, False{}, Nil{}, nd}

def num.frac(+ds: List<&2, U32>, +fs: List<&2, U32>, +after: List<&2, U32>) -> Nm:
  +nd = Nat.add(Nat.add(T.len(ds), 1n), T.len(fs))
  num.frac.e(ds, fs, after, nd)

# kind 0 U32, 1 Nat, 2 F32
def num.after(+ds: List<&2, U32>, rest: List<&2, U32>) -> Nm:
  match rest:
    case Con{110, t}:
      Nm{ds, 1n, Nil{}, False{}, Nil{}, 1n+T.len(ds)}
    case Con{46, +t}:
      +fs = digits.run(t)
      Bool.pick(Nm, List.is_empty(&2, U32, fs), Nm{ds, 0n, Nil{}, False{}, Nil{}, T.len(ds)}, num.frac(ds, fs, T.drop(t, T.len(fs))))
    case _:
      Nm{ds, 0n, Nil{}, False{}, Nil{}, T.len(ds)}

def num.read(+xs: List<&2, U32>) -> Nm:
  +ds = digits.run(xs)
  num.after(ds, T.drop(xs, T.len(ds)))

# the digits' value, and whether it passes 4294967295
def dig.val(ds: List<&2, U32>, +acc: U32, over: Bool) -> U32 & Bool:
  match ds:
    case Nil{}:
      (acc, over)
    case Con{+d, t}:
      +v = (d - 48 : U32)
      +big = Bool.or(U32.is_gt(acc, 429496729), Bool.and(U32.is_eq(acc, 429496729), U32.is_gt(v, 5)))
      dig.val(t, ((acc * 10 : U32) + v : U32), Bool.or(over, big))

# Succ{..out} n times, at span s
def succs(n: Nat, +s: C.Sp, out: C.Tm) -> C.Tm:
  match n:
    case 0n:
      out
    case 1n+m:
      succs(m, s, C.TCtr{"Succ", [out], s})

# term_write(p, t, beg): a[i] <- v heading a statement is the write's array
def write.unapp(n: Nat, t: C.Tm, xs: List<&2, C.Tm>) -> C.Tm & List<&2, C.Tm>:
  match n t:
    case 1n+m C.TApp{f, x, s}:
      write.unapp(m, f, x <> xs)
    case _ t:
      (t, xs)

def write.var(xs: List<&2, C.Tm>, +beg: U32) -> Maybe<&2, C.Tm>:
  match xs:
    case Con{a, Con{C.TVar{k, i, +s}, Con{c, Con{d, Nil{}}}}}:
      Bool.pick(Maybe<&2, C.Tm>, Bool.and(C.sp.has(s), U32.is_eq(C.sp.beg(s), beg)), Some{C.TVar{k, i, s}}, None{})
    case Con{a, Con{C.TVr{k, i, +s, r}, Con{c, Con{d, Nil{}}}}}:
      Bool.pick(Maybe<&2, C.Tm>, Bool.and(C.sp.has(s), U32.is_eq(C.sp.beg(s), beg)), Some{C.TVr{k, i, s, r}}, None{})
    case _:
      None{}

def write.head(h: C.Tm, xs: List<&2, C.Tm>, +set: String, +beg: U32) -> Maybe<&2, C.Tm>:
  match h:
    case C.TRef{k, s, b}:
      Bool.pick(Maybe<&2, C.Tm>, String.eq(k, set), write.var(xs, beg), None{})
    case _:
      None{}

def write.of(hx: C.Tm & List<&2, C.Tm>, +set: String, +beg: U32) -> Maybe<&2, C.Tm>:
  (h, xs) = hx
  write.head(h, xs, set, beg)

def P.term_write(+t: C.Tm, +beg: U32) -> L.P(Maybe<&2, C.Tm>):
  do L.P<Maybe<&2, C.Tm>>:
    set : String <- R.P.own_t("Array.set")
    return write.of(write.unapp(5n, t, Nil{}), set, beg)

# parse_bind(p, t): a lambda's binder
def P.bind(t: C.Tm) -> L.P(C.Pat):
  match t:
    case C.TVar{+k, +i, s}:
      do L.P<C.Pat>:
        j : U32 <- R.P.open(k)
        return C.PVar{k, j, Bool.pick(C.Q, U32.is_eq(i, C.MINUS()), C.QM{}, C.QL{}), s}
    case C.TVr{+k, i, s, r}:
      do L.P<C.Pat>:
        j : U32 <- R.P.open(k)
        return C.PVar{k, j, C.QL{}, s}
    case _:
      L.P.fail(C.Pat, "a lambda binder (one name: k => body)")

# term_show(term_lower(term_higher(t), 0)): the higher pass may throw
def show.low.got(r: H.HR) -> L.P(String):
  match r:
    case H.HRT{t}:
      L.P.pure(String, S.term.show(S.NoFl{}, t, 0, Nil{}))
    case H.HRE{e}:
      L.P.throw(String, e)
    case _:
      L.P.throw(String, C.ErRaw{"bendbis: show_low"})

def P.show_low(t: C.Tm) -> L.P(String):
  do L.P<String>:
    +e : L.Env <- L.P.env()
    show.low.got(H.hm.go(4294967295n, L.env.txt(e), H.JLB{H.hm.go(4294967295n, L.env.txt(e), H.JH{t, H.EmTip{}}), 0}))

# term_higher(t) for its errors (the parts outside binders)
def higher.got(r: H.HR) -> L.P(Unit):
  match r:
    case H.HRE{e}:
      L.P.throw(Unit, e)
    case _:
      L.P.pure(Unit, Unit{})

def P.higher(t: C.Tm) -> L.P(Unit):
  do L.P<Unit>:
    e : L.Env <- L.P.env()
    higher.got(H.hm.go(4294967295n, L.env.txt(e), H.JH{t, H.EmTip{}}))

# term_lower(term_higher(t)): the normal LTerm, and every operator error
def norm.got(r: H.HR) -> L.P(C.Tm):
  match r:
    case H.HRT{t}:
      L.P.pure(C.Tm, t)
    case H.HRE{e}:
      L.P.throw(C.Tm, e)
    case _:
      L.P.throw(C.Tm, C.ErRaw{"bendbis: norm"})

def P.norm(t: C.Tm) -> L.P(C.Tm):
  do L.P<C.Tm>:
    +e : L.Env <- L.P.env()
    norm.got(H.hm.go(4294967295n, L.env.txt(e), H.JLB{H.hm.go(4294967295n, L.env.txt(e), H.JH{t, H.EmTip{}}), 0}))

# tele_bind(tele, end)
def tele.bind(te: List<&2, Te>, end: C.Tm) -> C.Tm:
  match te:
    case Nil{}:
      end
    case Con{Te{q, k, i, A, s}, t}:
      C.TAll{q, k, i, A, tele.bind(t, end), s}

def tele.vars(te: List<&2, Te>) -> List<&2, C.Pat>:
  match te:
    case Nil{}:
      Nil{}
    case Con{Te{q, k, i, A, s}, t}:
      C.PVar{k, i, C.QL{}, s} <> tele.vars(t)

def tele.tip(te: List<&2, Te>) -> List<&2, C.Tm>:
  match te:
    case Nil{}:
      Nil{}
    case Con{Te{q, k, i, A, s}, t}:
      C.TVar{k, i, C.NoSp{}} <> tele.tip(t)

def tele.all_qnt(te: List<&2, Te>) -> Bool:
  match te:
    case Nil{}:
      True{}
    case Con{Te{q, k, i, C.TQnt{s}, u}, t}:
      tele.all_qnt(t)
    case _:
      False{}

# params.findIndex(cell => cell.T is not Qnt): the leading quantity count
def tele.g(te: List<&2, Te>, n: U32) -> U32:
  match te:
    case Nil{}:
      n
    case Con{Te{q, k, i, C.TQnt{s}, u}, t}:
      tele.g(t, (n + 1 : U32))
    case _:
      n

def tele.len(te: List<&2, Te>) -> U32:
  U32.from_nat(List.length(&2, Te, te))

def tele.has(te: List<&2, Te>, +k: String) -> Bool:
  match te:
    case Nil{}:
      False{}
    case Con{Te{q, j, i, A, s}, t}:
      Bool.or(String.eq(j, k), tele.has(t, k))

# a law's type: All for a for, Exists(A, c => T) for an exs
def law.clause(all: Bool, q: C.Q, c: String, i: U32, A: C.Tm, +s: C.Sp, ex: String, out: C.Tm) -> C.Tm:
  match all:
    case True{}:
      C.TAll{q, c, i, A, out, s}
    case False{}:
      C.TApp{C.TApp{C.TRef{ex, s, False{}}, A, s}, C.TLam{c, i, out, s, C.QL{}}, s}

def law.type(+ex: String, cl: List<&2, Cl>, body: C.Tm) -> C.Tm:
  match cl:
    case Nil{}:
      body
    case Con{Cl{all, q, c, i, A, +s}, t}:
      law.clause(all, q, c, i, A, s, ex, law.type(ex, t, body))

def law.n(cl: List<&2, Cl>, n: U32) -> U32:
  match cl:
    case Nil{}:
      n
    case Con{Cl{True{}, q, c, i, A, s}, t}:
      law.n(t, (n + 1 : U32))
    case _:
      n

# the arms of a lambda-match around its tail
def mat.build(arms: List<&2, Am>, +s: C.Sp, tail: C.Tm) -> C.Tm:
  match arms:
    case Nil{}:
      tail
    case Con{Am{k, h}, t}:
      C.TMat{k, h, mat.build(t, s, tail), s}

# nat_from_term on an LTerm, NONE when it is none
def nat.of(t: C.Tm, +n: U32) -> U32:
  match t:
    case C.TCtr{k, Con{x, Nil{}}, s}:
      Bool.pick(U32, String.eq(k, "Succ"), nat.of(x, (n + 1 : U32)), C.NONE())
    case C.TCtr{k, Nil{}, s}:
      Bool.pick(U32, String.eq(k, "Zero"), n, C.NONE())
    case C.TNat{+v, s}:
      Bool.pick(U32, U32.is_le(v, (4294967295 - n : U32)), (n + v : U32), C.NONE())
    case _:
      C.NONE()

# log2 of a power of two, NONE for anything else (0 included)
def log2.go(k: Nat, +n: U32, +i: U32) -> U32:
  match k:
    case 0n:
      C.NONE()
    case 1n+m:
      Bool.pick(U32, U32.is_eq(n, 1), i, log2.go(m, (n >> 1n : U32), (i + 1 : U32)))

def log2.pow(+n: U32) -> U32:
  Bool.pick(U32, Bool.and(Bool.not(U32.is_eq(n, 0)), U32.is_eq((n .&. (n - 1 : U32) : U32), 0)), log2.go(33n, n, 0), C.NONE())

# a Var's or Ref's name, or none
def tm.vr(t: C.Tm) -> Maybe<&2, String>:
  match t:
    case C.TVar{k, i, s}:
      Some{k}
    case C.TVr{k, i, s, r}:
      Some{k}
    case C.TRef{k, s, b}:
      Some{k}
    case _:
      None{}

# a Var's name (TVar or TVr), or none
def tm.var.k(t: C.Tm) -> Maybe<&2, String>:
  match t:
    case C.TVar{k, i, s}:
      Some{k}
    case C.TVr{k, i, s, r}:
      Some{k}
    case _:
      None{}

def tm.is_lit_nat(t: C.Tm) -> Bool:
  match t:
    case C.TNat{v, s}:
      True{}
    case _:
      False{}

def tm.nat_v(t: C.Tm) -> U32:
  match t:
    case C.TNat{v, s}:
      v
    case _:
      0

# the first extra binder whose span starts with +: its span's offset
def plus.first(+txt: List<&2, U32>, ts: List<&2, C.Tm>) -> U32:
  match ts:
    case Nil{}:
      C.NONE()
    case Con{+t, r}:
      +b = C.sp.beg(C.tm.s(t))
      Bool.pick(U32, Bool.and(C.sp.has(C.tm.s(t)), U32.is_eq(T.at(txt, b), 43)), b, plus.first(txt, r))

# qs.find((q, i) => q is a Nat Lit and the next one's span starts with +)
def succ.next(+txt: List<&2, U32>, rest: List<&2, C.Tm>) -> Bool:
  match rest:
    case Con{n, r}:
      U32.is_eq(T.at(txt, C.sp.beg(C.tm.s(n))), 43)
    case Nil{}:
      False{}

def succ.lit(+txt: List<&2, U32>, qs: List<&2, C.Tm>) -> Maybe<&2, U32>:
  match qs:
    case Con{C.TNat{v, s}, +rest}:
      Bool.pick(Maybe<&2, U32>, succ.next(txt, rest), Some{v}, succ.lit(txt, rest))
    case Con{q, r}:
      succ.lit(txt, r)
    case Nil{}:
      None{}

def tms.len(ts: List<&2, C.Tm>) -> U32:
  U32.from_nat(List.length(&2, C.Tm, ts))

# the run of name units at pos is a keyword
def at.keyword(+xs: List<&2, U32>) -> Bool:
  L.is_keyword(T.str(T.take(xs, L.name.run(xs))))

def OP_SPACES() -> String:
  "an operator takes spaces on both sides and a type: (a + b : T)"

# /[\w)\]}"']/ on a unit
def glued(+c: U32) -> Bool:
  Bool.or(T.is_word(c), Bool.or(Bool.or(U32.is_eq(c, 41), U32.is_eq(c, 93)), Bool.or(Bool.or(U32.is_eq(c, 125), U32.is_eq(c, 34)), U32.is_eq(c, 39))))

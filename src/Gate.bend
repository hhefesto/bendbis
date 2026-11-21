import Base
import ./Core.bend as C
import ./Text.bend as T
import ./Lex.bend as L
import ./High.bend as H
import ./Show.bend as S
import ./Err.bend as E
import ./Print.bend as Pr
import ./Load.bend as Ld
import ./Path.bend as Pa

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Gate: milestone 1's gate, file by file, against upstream's output saved
# beside (UP/<the file's path, / as _>.out: `bend FILE --check-only`, its
# stdout and stderr). For a file bendbis rejects, its output must be
# upstream's, byte for byte. For a file bendbis parses, upstream must not
# have rejected it at parse time, and every term of its declarations
# (types, values, constructors), printed by Print and parsed again where
# the file is, must come back the same (spans and binder names aside).
#
# Upstream rejected a file at parse time when its error has no context and
# no def at its location: every error the loader, the parser and the
# flattener throw (ctx_nil, no def); every error the checker throws names
# its def, but "a fresh ~ binder name" (def_check), which is excluded; and
# main.ts's "PROOF.bend must import ./LAWS.bend".

def mangle.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{47}, t}:
      SCon{Chr{95}, mangle.go(t)}
    case SCon{c, t}:
      SCon{c, mangle.go(t)}

def mangle(s: String) -> String:
  mangle.go(s)

# Lines of a byte list, as strings of code points
def lines.str(ls: List<&2, List<&2, U32>>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      T.str(l) <> lines.str(t)

def lines.of(bytes: List<&2, U32>) -> List<&2, String>:
  lines.str(E.Err.lines(T.of_bytes(bytes)))

def any.starts(ls: List<&2, String>, +p: String) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{+l, t}:
      Bool.or(String.starts_with(l, p), any.starts(t, p))

# a "Location: def" line (a check-time error names its def)
def any.def.loc(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{+l, t}:
      Bool.or(String.starts_with(l, "Location: "), any.def.loc(t))

def is.parse.err(ls: List<&2, String>) -> Bool:
  match ls:
    case Con{+a, Con{+b, +t}}:
      Bool.and(String.eq(a, "SOME PROOFS FAIL"),
        Bool.or(String.starts_with(b, "Error: PROOF.bend must import"),
          Bool.and(Bool.and(String.eq(b, "Error:"), Bool.not(any.starts(t, "Context:"))),
            Bool.and(Bool.not(any.def.loc(t)), Bool.not(any.starts(t, "- expected : a fresh ~ binder name"))))))
    case _:
      False{}

# Comparing terms: spans, binder names and a bound variable's name aside
# -----------------------------------------------------------------------

type Pr2 is Data:
  Pr2{a: C.Tm, b: C.Tm}

def pairs(xs: List<&2, C.Tm>, ys: List<&2, C.Tm>, acc: List<&2, Pr2>) -> Maybe<&2, List<&2, Pr2>>:
  match xs ys:
    case Nil{} Nil{}:
      Some{acc}
    case Con{x, s} Con{y, t}:
      pairs(s, t, Pr2{x, y} <> acc)
    case _ _:
      None{}

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

def strs.eq(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, s} Con{b, t}:
      Bool.and(String.eq(a, b), strs.eq(s, t))
    case _ _:
      False{}

def u32s.eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{+a, s} Con{+b, t}:
      Bool.and(U32.is_eq(a, b), u32s.eq(s, t))
    case _ _:
      False{}

# the pairs to compare next, or None when the two nodes differ here
def guard(ok: Bool, rest: List<&2, Pr2>) -> Maybe<&2, List<&2, Pr2>>:
  match ok:
    case True{}:
      Some{rest}
    case False{}:
      None{}

def guard.then(ok: Bool, m: Maybe<&2, List<&2, Pr2>>) -> Maybe<&2, List<&2, Pr2>>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

def let.eq.and(ok: Bool, m: Maybe<&2, List<&2, Pr2>>) -> Maybe<&2, List<&2, Pr2>>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

def let.eq(xs: List<&2, C.Bnd>, ys: List<&2, C.Bnd>, acc: List<&2, Pr2>) -> Maybe<&2, List<&2, Pr2>>:
  match xs ys:
    case Nil{} Nil{}:
      Some{acc}
    case Con{C.Bnd{k1, +i1, q1, v1}, s} Con{C.Bnd{k2, +i2, q2, v2}, t}:
      let.eq.and(Bool.and(U32.is_eq(i1, i2), q.eq(q1, q2)), let.eq(s, t, Pr2{v1, v2} <> acc))
    case _ _:
      None{}

def node.eq(a: C.Tm, b: C.Tm, rest: List<&2, Pr2>) -> Maybe<&2, List<&2, Pr2>>:
  match a b:
    case C.TVar{k1, +i1, s1} C.TVar{k2, +i2, s2}:
      guard(Bool.and(U32.is_eq(i1, i2), Bool.or(Bool.not(U32.is_eq(i1, C.MINUS())), String.eq(k1, k2))), rest)
    case C.TAdt{+k1, Nil{}, Nil{}, s1} C.TRef{+k2, s2, False{}}:
      guard(String.eq(k1, k2), rest)
    case C.TRef{+k1, s1, b1} C.TRef{+k2, s2, b2}:
      guard(Bool.and(String.eq(k1, k2), Bool.not(Bool.xor(b1, b2))), rest)
    case C.TTyp{g1, s1} C.TTyp{g2, s2}:
      Some{Pr2{g1, g2} <> rest}
    case C.TQnt{s1} C.TQnt{s2}:
      Some{rest}
    case C.TQua{q1, s1} C.TQua{q2, s2}:
      guard(q.eq(q1, q2), rest)
    case C.TMin{a1, b1, s1} C.TMin{a2, b2, s2}:
      Some{Pr2{a1, a2} <> Pr2{b1, b2} <> rest}
    case C.TAll{q1, k1, +i1, A1, B1, s1} C.TAll{q2, k2, +i2, A2, B2, s2}:
      guard(Bool.and(q.eq(q1, q2), U32.is_eq(i1, i2)), Pr2{A1, A2} <> Pr2{B1, B2} <> rest)
    case C.TLam{k1, +i1, f1, s1, q1} C.TLam{k2, +i2, f2, s2, q2}:
      guard(Bool.and(q.eq(q1, q2), U32.is_eq(i1, i2)), Pr2{f1, f2} <> rest)
    case C.TApp{f1, x1, s1} C.TApp{f2, x2, s2}:
      Some{Pr2{f1, f2} <> Pr2{x1, x2} <> rest}
    case C.TAdt{+k1, xs1, r1, s1} C.TAdt{+k2, xs2, r2, s2}:
      guard.then(Bool.and(String.eq(k1, k2), strs.eq(r1, r2)), pairs(xs1, xs2, rest))
    case C.TCtr{+k1, xs1, s1} C.TCtr{+k2, xs2, s2}:
      guard.then(String.eq(k1, k2), pairs(xs1, xs2, rest))
    case C.TNat{+v1, s1} C.TNat{+v2, s2}:
      guard(U32.is_eq(v1, v2), rest)
    case C.TU32{+v1, s1} C.TU32{+v2, s2}:
      guard(U32.is_eq(v1, v2), rest)
    case C.TF32{+v1, s1} C.TF32{+v2, s2}:
      guard(U32.is_eq(v1, v2), rest)
    case C.TStr{v1, s1} C.TStr{v2, s2}:
      guard(u32s.eq(v1, v2), rest)
    case C.TMat{+k1, h1, m1, s1} C.TMat{+k2, h2, m2, s2}:
      guard(String.eq(k1, k2), Pr2{h1, h2} <> Pr2{m1, m2} <> rest)
    case C.TEfq{s1} C.TEfq{s2}:
      Some{rest}
    case C.TEql{a1, b1, A1, s1} C.TEql{a2, b2, A2, s2}:
      Some{Pr2{a1, a2} <> Pr2{b1, b2} <> Pr2{A1, A2} <> rest}
    case C.TRfl{s1} C.TRfl{s2}:
      Some{rest}
    case C.TRwt{e1, p1, f1, s1} C.TRwt{e2, p2, f2, s2}:
      Some{Pr2{e1, e2} <> Pr2{p1, p2} <> Pr2{f1, f2} <> rest}
    case C.THol{+k1, s1} C.THol{+k2, s2}:
      guard(String.eq(k1, k2), rest)
    case C.TAnn{x1, A1, s1} C.TAnn{x2, A2, s2}:
      Some{Pr2{x1, x2} <> Pr2{A1, A2} <> rest}
    case C.TLet{bs1, f1, s1} C.TLet{bs2, f2, s2}:
      let.eq(bs1, bs2, Pr2{f1, f2} <> rest)
    case _ _:
      None{}

# the comparison's state: pairs left, or the first pair that differs
type Es is Data:
  EsGo{ps: List<&2, Pr2>}
  EsBad{a: C.Tm, b: C.Tm}

def es.step(m: Maybe<&2, List<&2, Pr2>>, a: C.Tm, b: C.Tm) -> Es:
  match m:
    case Some{ps}:
      EsGo{ps}
    case None{}:
      EsBad{a, b}

def short(s: String) -> String:
  String.take(s, 160n)

def eq.go(fuel: Nat, s: Es) -> Maybe<&2, String>:
  match fuel s:
    case 0n _:
      Some{"bendbis: the comparison ran out of fuel"}
    case _ EsBad{a, b}:
      Some{short(S.term.show(S.NoFl{}, a, 0, Nil{})) ++ "  vs  " ++ short(S.term.show(S.NoFl{}, b, 0, Nil{}))}
    case _ EsGo{Nil{}}:
      None{}
    case 1n+f EsGo{Con{Pr2{+a, +b}, r}}:
      eq.go(f, es.step(node.eq(a, b, r), a, b))

# None when a and b are the same term, else where they first differ
def tm.diff(a: C.Tm, b: C.Tm) -> Maybe<&2, String>:
  eq.go(4294967295n, EsGo{[Pr2{a, b}]})

# The round trip
# --------------

# a declaration's terms, the ones the parser normalized (values) and the
# ones it did not (types, constructors)
type Tz is Data:
  Tz{t: C.Tm, norm: Bool}

def cns.terms(cs: List<&2, C.Cn>) -> List<&2, Tz>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{C.Cn{k, n, T}, t}:
      Tz{T, False{}} <> cns.terms(t)

def dcl.terms(ds: List<&2, C.Dcl>) -> List<&2, Tz>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{C.DAdt{k, n, g, T, cs}, t}:
      Tz{T, False{}} <> List.append(&2, Tz, cns.terms(cs), dcl.terms(t))
    case Con{C.DDef{k, n, x, T, None{}, u, ffi, l, fl}, t}:
      Tz{T, False{}} <> dcl.terms(t)
    case Con{C.DDef{k, n, x, T, Some{v}, u, ffi, l, fl}, t}:
      Tz{T, False{}} <> Tz{v, True{}} <> dcl.terms(t)

# term_lower(term_higher(t)), or None on an operator error
def norm.of(r: H.HR) -> Maybe<&2, C.Tm>:
  match r:
    case H.HRT{t}:
      Some{t}
    case _:
      None{}

def norm(t: C.Tm) -> Maybe<&2, C.Tm>:
  norm.of(H.hm.go(4294967295n, Nil{}, H.JLB{H.hm.go(4294967295n, Nil{}, H.JH{t, H.EmTip{}}), 0}))

def tz.norm(z: Tz) -> Maybe<&2, C.Tm>:
  match z:
    case Tz{t, True{}}:
      Some{t}
    case Tz{t, False{}}:
      norm(t)

# the terms compared: the normalized ones under the size cap
type Rt is Data:
  Rt{ts: List<&2, C.Tm>, op: U32, big: U32}

def rt.add.size(z: Bool, t: C.Tm, ts: List<&2, C.Tm>, op: U32, big: U32) -> Rt:
  match z:
    case True{}:
      Rt{ts, op, (big + 1 : U32)}
    case False{}:
      Rt{t <> ts, op, big}

def rt.add(m: Maybe<&2, C.Tm>, +cap: U32, r: Rt) -> Rt:
  match m r:
    case None{} Rt{ts, op, big}:
      Rt{ts, (op + 1 : U32), big}
    case Some{+t} Rt{ts, op, big}:
      rt.add.size(U32.is_gt(C.tm.size(t), cap), t, ts, op, big)

def rt.terms(zs: List<&2, Tz>, +cap: U32, r: Rt) -> Rt:
  match zs:
    case Nil{}:
      r
    case Con{z, t}:
      rt.terms(t, cap, rt.add(tz.norm(z), cap, r))

def al2.of(al: List<&2, L.Al>) -> List<&2, S.Al2>:
  match al:
    case Nil{}:
      Nil{}
    case Con{L.Al{a, ns}, t}:
      S.Al2{a, ns} <> al2.of(t)

def print.defs(+fl: S.Fl, ts: List<&2, C.Tm>, +j: U32) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      ("def __bb" ++ U32.show(j) ++ "() -> Type:\n  " ++ Pr.print.term(fl, t) ++ "\n\n") <> print.defs(fl, r, (j + 1 : U32))

# the file's import header: its lines up to its first declaration
def header.at(stop: Bool, l: List<&2, U32>, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match stop:
    case True{}:
      Nil{}
    case False{}:
      l <> rest

def header.go(ls: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{+l, t}:
      header.at(Nat.is_eq(Ld.line.role(Ld.trim(l)), 2n), l, header.go(t))

def header(bytes: List<&2, U32>) -> List<&2, U32>:
  Ld.join.lines(header.go(E.Err.lines(T.of_bytes(bytes))))

def entry.fr(fs: List<&2, Ld.Fr>) -> Ld.Fr:
  match fs:
    case Con{f, t}:
      f
    case Nil{}:
      Ld.Fr{"", "", Nil{}, Nil{}, Nil{}, 0}

def fr.ds(f: Ld.Fr) -> List<&2, C.Dcl>:
  match f:
    case Ld.Fr{p, ns, al, ds, tx, fi}:
      ds

def fr.al(f: Ld.Fr) -> List<&2, L.Al>:
  match f:
    case Ld.Fr{p, ns, al, ds, tx, fi}:
      al

def dcl.vals(ds: List<&2, C.Dcl>) -> List<&2, C.Tm>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{C.DDef{k, n, x, T, Some{v}, u, ffi, l, fl}, t}:
      v <> dcl.vals(t)
    case Con{d, t}:
      dcl.vals(t)

def diff.at(+j: U32, d: Maybe<&2, String>) -> Maybe<&2, String>:
  match d:
    case None{}:
      None{}
    case Some{m}:
      Some{"term " ++ U32.show(j) ++ ": " ++ m}

# the terms against what came back: how many matched before the first
# difference, and that difference
def cmp.all(xs: List<&2, C.Tm>, ys: List<&2, C.Tm>, +j: U32, bad: Maybe<&2, String>) -> U32 & Maybe<&2, String>:
  match xs ys bad:
    case _ _ Some{m}:
      ((j - 1 : U32), Some{m})
    case Nil{} Nil{} None{}:
      (j, None{})
    case Con{x, s} Con{y, t} None{}:
      cmp.all(s, t, (j + 1 : U32), diff.at(j, tm.diff(x, y)))
    case _ _ None{}:
      (j, Some{"the printed file came back with another number of terms"})

# The driver
# ----------

def put.fin(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, e) = r
  File.close(f)

def put.opened(r: Result<&1, &1, U32 & String, File>, s: String) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.pure(Unit, Unit{})
    case Done{f}:
      IO.bind(File & Result<&1, &1, U32 & String, Unit>, Unit, File.write(f, s), put.fin)

# write s to path (a failure is ignored: the file is a debugging aid)
def put.text(path: String, s: String) -> IO(Unit):
  IO.bind(Result<&1, &1, U32 & String, File>, Unit, File.open(path, "w"), r => put.opened(r, s))

type Ct is Data:
  Ct{same: U32, diff: U32, missed: U32, ok: U32, rtfail: U32, noup: U32, terms: U32, op: U32, big: U32}

def ct.show(c: Ct) -> String:
  match c:
    case Ct{a, b, m, o, r, n, t, op, big}:
      "gate1: " ++ U32.show(a) ++ " rejected as upstream, " ++ U32.show(b) ++ " rejected otherwise, "
        ++ U32.show(m) ++ " parsed that upstream rejects at parse time, " ++ U32.show(o) ++ " parsed and round-tripped, "
        ++ U32.show(r) ++ " round trips failed, " ++ U32.show(n) ++ " with no upstream output; terms round-tripped "
        ++ U32.show(t) ++ ", not normalizable " ++ U32.show(op) ++ ", over the size cap " ++ U32.show(big)

def ct.same(c: Ct) -> Ct:
  match c:
    case Ct{a, b, m, o, r, n, t, op, big}:
      Ct{(a + 1 : U32), b, m, o, r, n, t, op, big}

def ct.diff(c: Ct) -> Ct:
  match c:
    case Ct{a, b, m, o, r, n, t, op, big}:
      Ct{a, (b + 1 : U32), m, o, r, n, t, op, big}

def ct.missed(c: Ct) -> Ct:
  match c:
    case Ct{a, b, m, o, r, n, t, op, big}:
      Ct{a, b, (m + 1 : U32), o, r, n, t, op, big}

def ct.noup(c: Ct) -> Ct:
  match c:
    case Ct{a, b, m, o, r, n, t, op, big}:
      Ct{a, b, m, o, r, (n + 1 : U32), t, op, big}

def ct.rt(+ok: Bool, +k: U32, +op2: U32, +big2: U32, c: Ct) -> Ct:
  match c:
    case Ct{a, b, m, +o, +r, n, t, op, big}:
      Ct{a, b, m, Bool.pick(U32, ok, (o + 1 : U32), o), Bool.pick(U32, ok, r, (r + 1 : U32)), n, (t + k : U32), (op + op2 : U32), (big + big2 : U32)}

def line.of(s: String) -> String:
  String.join(List.take(&2, String, String.lines(s), 6n), " | ")

def rt.cmp(+f: String, +out: String, +text: String, r: U32 & Maybe<&2, String>, +op: U32, +big: U32, c: Ct) -> IO(Ct):
  (+n, d) = r
  match d:
    case None{}:
      do IO<Ct>:
        IO.print("ok\t" ++ f ++ "\t" ++ U32.show(n) ++ " terms" ++ Bool.pick(String, U32.is_eq((op + big : U32), 0), "", ", " ++ U32.show(op) ++ " not normalizable, " ++ U32.show(big) ++ " over the cap"))
        return ct.rt(True{}, n, op, big, c)
    case Some{m}:
      do IO<Ct>:
        put.text(out ++ "/" ++ mangle(f) ++ ".rt.bend", text)
        IO.print("RT-FAIL\t" ++ f ++ "\t" ++ m)
        return ct.rt(False{}, n, op, big, c)

def rt.report(+f: String, +out: String, +text: String, r2: Ld.LR, +ts: List<&2, C.Tm>, +op: U32, +big: U32, c: Ct) -> IO(Ct):
  match r2:
    case Ld.LErr{e}:
      do IO<Ct>:
        put.text(out ++ "/" ++ mangle(f) ++ ".rt.bend", text)
        IO.print("RT-PARSE\t" ++ f ++ "\t" ++ line.of(E.Err.show(e)))
        return ct.rt(False{}, 0, op, big, c)
    case Ld.LOk{ld2}:
      rt.cmp(f, out, text, cmp.all(ts, dcl.vals(fr.ds(entry.fr(Ld.ld.files(ld2)))), 0, None{}), op, big, c)

# parse what the printer wrote, where the file is, and compare
def rt.go.at(+f: String, +real: String, +bp: String, base: L.Bk, +lib: String, +out: String, +fr: Ld.Fr, rt: Rt, c: Ct) -> IO(Ct):
  match rt:
    case Rt{ts, +op, +big}:
      +tl = List.reverse(&2, C.Tm, ts)
      do IO<Ct>:
        mb : Maybe<&2, List<&2, U32>> <- Ld.slurp(real)
        +text : String = T.str(header(Maybe.default(&2, List<&2, U32>, mb, Nil{}))) ++ "\n\n" ++ String.concat(print.defs(S.Fl{"", al2.of(fr.al(fr))}, tl, 0))
        r2 : Ld.LR <- Ld.load.text(real, T.units(text), Ld.ld.entry(bp, base, lib))
        rt.report(f, out, text, r2, tl, op, big, c)

def rt.go(+f: String, +real: String, +bp: String, base: L.Bk, +lib: String, +out: String, +cap: U32, ld: Ld.Ld, c: Ct) -> IO(Ct):
  +fr = entry.fr(Ld.ld.files(ld))
  +rt = rt.terms(dcl.terms(fr.ds(fr)), cap, Rt{Nil{}, 0, 0})
  rt.go.at(f, real, bp, base, lib, out, fr, rt, c)

def gate.err.cmp(same: Bool, +f: String, +out: String, mine: String, c: Ct) -> IO(Ct):
  match same:
    case True{}:
      do IO<Ct>:
        IO.print("same-error\t" ++ f)
        return ct.same(c)
    case False{}:
      do IO<Ct>:
        put.text(out ++ "/" ++ mangle(f) ++ ".bb", mine)
        IO.print("DIFF-error\t" ++ f)
        return ct.diff(c)

def gate.err(+f: String, +out: String, +mine: String, u: Maybe<&2, List<&2, U32>>, c: Ct) -> IO(Ct):
  match u:
    case None{}:
      do IO<Ct>:
        IO.print("NO-UP\t" ++ f)
        return ct.noup(c)
    case Some{ub}:
      gate.err.cmp(u32s.eq(T.utf8(mine), ub), f, out, mine, c)

def gate.ok.at(missed: Bool, +f: String, +real: String, +bp: String, base: L.Bk, +lib: String, +out: String, +cap: U32, ld: Ld.Ld, ub: List<&2, U32>, c: Ct) -> IO(Ct):
  match missed:
    case True{}:
      do IO<Ct>:
        IO.print("MISSED\t" ++ f ++ "\t" ++ line.of(T.str(T.of_bytes(ub))))
        return ct.missed(c)
    case False{}:
      rt.go(f, real, bp, base, lib, out, cap, ld, c)

def gate.ok(+f: String, +real: String, +bp: String, base: L.Bk, +lib: String, +out: String, +cap: U32, ld: Ld.Ld, u: Maybe<&2, List<&2, U32>>, c: Ct) -> IO(Ct):
  match u:
    case None{}:
      do IO<Ct>:
        IO.print("NO-UP\t" ++ f)
        return ct.noup(c)
    case Some{+ub}:
      gate.ok.at(is.parse.err(lines.of(ub)), f, real, bp, base, lib, out, cap, ld, ub, c)

def gate.got(r: Ld.LR, +f: String, +real: String, +bp: String, base: L.Bk, +lib: String, +out: String, +cap: U32, u: Maybe<&2, List<&2, U32>>, c: Ct) -> IO(Ct):
  match r:
    case Ld.LErr{e}:
      gate.err(f, out, "SOME PROOFS FAIL\n" ++ E.Err.show(e) ++ "\n", u, c)
    case Ld.LOk{ld}:
      gate.ok(f, real, bp, base, lib, out, cap, ld, u, c)

# the gate over files fs: upstream's outputs in up, bendbis's own (where
# they differ) into out
def gate.each(fs: List<String>, +cwd: String, +bp: String, +base: L.Bk, +lib: String, +up: String, +out: String, +cap: U32, c: Ct) -> IO(Ct):
  match fs:
    case Nil{}:
      IO.pure(Ct, c)
    case Con{+f, t}:
      +real = Pa.p.resolve(cwd, f)
      do IO<Ct>:
        r : Ld.LR <- Ld.load.entry(f, real, Ld.ld.entry(bp, base, lib))
        u : Maybe<&2, List<&2, U32>> <- Ld.slurp(up ++ "/" ++ mangle(f) ++ ".out")
        c2 : Ct <- gate.got(r, f, real, bp, base, lib, out, cap, u, c)
        gate.each(t, cwd, bp, base, lib, up, out, cap, c2)

def gate.run(fs: List<String>, +cwd: String, +bp: String, base: L.Bk, +lib: String, +up: String, +out: String, +cap: U32) -> IO(Unit):
  do IO<Unit>:
    c : Ct <- gate.each(fs, cwd, bp, base, lib, up, out, cap, Ct{0, 0, 0, 0, 0, 0, 0, 0, 0})
    IO.print(ct.show(c))

# The guide's examples
# --------------------

# the ```python blocks of a markdown text, each a list of lines
def blocks.go(ls: List<&2, String>, on: Bool, +cur: List<&2, String>, +acc: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match ls on:
    case Nil{} _:
      List.reverse(&2, List<&2, String>, acc)
    case Con{+l, t} False{}:
      blocks.go(t, String.eq(l, "```python"), Nil{}, acc)
    case Con{+l, t} True{}:
      +e = String.starts_with(l, "```")
      blocks.go(t, Bool.not(e), Bool.pick(List<&2, String>, e, Nil{}, l <> cur), Bool.pick(List<&2, List<&2, String>>, e, List.reverse(&2, String, cur) <> acc, acc))

def pad2(+n: U32) -> String:
  Bool.pick(String, U32.is_lt(n, 10), "0", "") ++ U32.show(n)

def lines.join(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      x ++ "\n" ++ lines.join(t)

def blocks.write(bs: List<&2, List<&2, String>>, +stem: String, +n: U32) -> IO(Unit):
  match bs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{b, t}:
      do IO<Unit>:
        put.text(stem ++ "_" ++ pad2(n) ++ ".bend", lines.join(b))
        blocks.write(t, stem, (n + 1 : U32))

# OUTDIR/<STEM>_NN.bend for each ```python block of the markdown file MD,
# NN counting from 01
def blocks(+md: String, +stem: String) -> IO(Unit):
  do IO<Unit>:
    mb : Maybe<&2, List<&2, U32>> <- Ld.slurp(md)
    blocks.write(blocks.go(lines.of(Maybe.default(&2, List<&2, U32>, mb, Nil{})), False{}, Nil{}, Nil{}), stem, 1)

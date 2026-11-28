import Base
import ./Text.bend as T
import ./Core.bend as C
import ./Lex.bend as L

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Res: the parser's names and binders (bend.ts parse_open to parse_call,
# parse_quant, parse_fresh, parse_fill, parse_more, parse_do_end), the
# operator table (INFIX, INFIX_BY_HEAD), and the small reads the parser
# makes of its state.

# Spans and columns
# -----------------

# parse_span(p, beg): beg up to pos, in this file
def P.span(+beg: U32) -> L.P(C.Sp):
  do L.P<C.Sp>:
    c : L.Cur <- L.P.cur()
    e : L.Env <- L.P.env()
    return C.Sp{L.env.fid(e), beg, L.cur.pos(c)}

def P.span2(+beg: U32, +end: U32) -> L.P(C.Sp):
  do L.P<C.Sp>:
    e : L.Env <- L.P.env()
    return C.Sp{L.env.fid(e), beg, end}

# the source unit at offset n (4294967295 past the end)
def P.char_at(+n: U32) -> L.P(U32):
  do L.P<U32>:
    e : L.Env <- L.P.env()
    return T.at(L.env.txt(e), n)

# parse_col(src, n), for an offset before pos
def col.go(n: Nat, xs: List<&2, U32>, col: U32) -> U32:
  match n xs:
    case 0n _:
      col
    case 1n+m Con{10, t}:
      col.go(m, t, 1)
    case 1n+m Con{c, t}:
      col.go(m, t, (col + 1 : U32))
    case _ Nil{}:
      col

def P.col_at(+n: U32) -> L.P(U32):
  do L.P<U32>:
    e : L.Env <- L.P.env()
    return col.go(U32.to_nat(n), L.env.txt(e), 1)

# Names
# -----

# the first alias named a: the last one's test a parameter, so the rest of
# the list is asked only on a miss (as sc.find.go)
def al.get.go(al: List<&2, L.Al>, +a: String, hit: Bool, ns: String) -> Maybe<&2, String>:
  match al hit:
    case _ True{}:
      Some{ns}
    case Nil{} False{}:
      None{}
    case Con{L.Al{x, ns2}, t} False{}:
      al.get.go(t, a, String.eq(x, a), ns2)

def al.get(al: List<&2, L.Al>, +a: String) -> Maybe<&2, String>:
  al.get.go(al, a, False{}, "")

def al.has(+al: List<&2, L.Al>, a: String) -> Bool:
  Maybe.is_some(&2, String, al.get(al, a))

# parse_qual: ns:k, or k in the empty namespace
def qual(+ns: String, +k: String) -> String:
  Bool.pick(String, String.is_empty(ns), k, ns ++ ":" ++ k)

# in(tab, k) for the tlds (t true) or the ctrs
def tab.has(+bk: L.Bk, t: Bool, +k: String) -> Bool:
  Bool.pick(Bool, t, L.bk.has_tld(bk, k), L.bk.has_ctr(bk, k))

# q in tab || !(k in tab) ? q : k, k looked up only when q is not in tab
def reso.pick.k(z: Bool, q: String, k: String) -> String:
  match z:
    case True{}:
      k
    case False{}:
      q

def reso.pick.q(z: Bool, +bk: L.Bk, +t: Bool, q: String, +k: String) -> String:
  match z:
    case True{}:
      q
    case False{}:
      reso.pick.k(tab.has(bk, t, k), q, k)

def reso.pick(+bk: L.Bk, +t: Bool, +q: String, +k: String) -> String:
  reso.pick.q(tab.has(bk, t, q), bk, t, q, k)

def reso.amb(z: Bool, q: String, +k: String, r: String) -> L.P(String):
  match z:
    case True{}:
      L.P.fail(String, "an unambiguous name (the alias " ++ C.str.before_dot(k) ++ " shadows " ++ k ++ ")")
    case False{}:
      L.P.pure(String, r)

def reso.alias(m: Maybe<&2, String>, +e: L.Env, +t: Bool, +k: String) -> L.P(String):
  match m:
    case None{}:
      L.P.pure(String, reso.pick(L.env.bk(e), t, qual(L.env.ns(e), k), k))
    case Some{ns}:
      +q = ns ++ ":" ++ C.str.after_dot(k)
      +bk = L.env.bk(e)
      reso.amb(Bool.and(Bool.not(String.eq(q, k)), Bool.and(tab.has(bk, t, q), tab.has(bk, t, k))), q, k, reso.pick(bk, t, q, k))

# parse_reso(p, k, t): an alias's name, the file's own, or Base's
def P.reso(+t: Bool, +k: String) -> L.P(String):
  do L.P<String>:
    +e : L.Env <- L.P.env()
    reso.alias(Bool.pick(Maybe<&2, String>, C.str.has_dot(k), al.get(L.env.al(e), C.str.before_dot(k)), None{}), e, t, k)

def P.reso_t(k: String) -> L.P(String):
  P.reso(True{}, k)

def P.reso_c(k: String) -> L.P(String):
  P.reso(False{}, k)

# parse_own(p, k, t): the file's own k, else Base's
def P.own(+t: Bool, +k: String) -> L.P(String):
  do L.P<String>:
    +e : L.Env <- L.P.env()
    return reso.pick(L.env.bk(e), t, qual(L.env.ns(e), k), k)

def P.own_t(k: String) -> L.P(String):
  P.own(True{}, k)

def P.own_c(k: String) -> L.P(String):
  P.own(False{}, k)

# parse_fresh(p, nm, t, what)
def fresh.fail(z: Bool, +what: String, +isal: Bool, +a: String, +nm: String, +k: String) -> L.P(String):
  match z:
    case True{}:
      do L.P<String>:
        +pos : U32 <- L.P.pos()
        L.P.fail.from(String, what ++ " (" ++ Bool.pick(String, isal, a ++ " is an import's alias", "duplicate declaration: " ++ nm) ++ ")", (pos - U32.from_nat(String.length(nm)) : U32))
    case False{}:
      L.P.pure(String, k)

def P.fresh(+t: Bool, +what: String, +nm: String) -> L.P(String):
  do L.P<String>:
    +e : L.Env <- L.P.env()
    +k : String = qual(L.env.ns(e), nm)
    +a : String = Bool.pick(String, C.str.has_dot(nm), C.str.before_dot(nm), "")
    +isal : Bool = al.has(L.env.al(e), a)
    +bk : L.Bk = L.env.bk(e)
    fresh.fail(Bool.or(Bool.or(tab.has(bk, t, k), tab.has(bk, t, nm)), isal), what, isal, a, nm, k)

# Binders
# -------

# parse_open(p, k): a fresh index, k in scope at it unless k is _
def open.push(z: Bool, k: String, i: U32, e: L.Env) -> L.Env:
  match z:
    case True{}:
      e
    case False{}:
      L.env.push(k, i, e)

def P.open(+k: String) -> L.P(U32):
  do L.P<U32>:
    +e : L.Env <- L.P.env()
    +i : U32 = L.env.frs(e)
    L.P.set_env(open.push(String.eq(k, "_"), k, i, L.env.set_frs((i + 1 : U32), e)))
    return i

def P.push(k: String, i: U32) -> L.P(Unit):
  L.P.mod_env(L.env.push(k, i))

def P.depth() -> L.P(U32):
  do L.P<U32>:
    e : L.Env <- L.P.env()
    return L.env.dep(e)

def P.close(n: U32) -> L.P(Unit):
  L.P.mod_env(L.env.close(n))

# p.frs++
def P.fresh_index() -> L.P(U32):
  do L.P<U32>:
    +e : L.Env <- L.P.env()
    +i : U32 = L.env.frs(e)
    L.P.set_env(L.env.set_frs((i + 1 : U32), e))
    return i

def var.free(k: String, s: C.Sp, q: String) -> L.P(C.Tm):
  do L.P<C.Tm>:
    i : U32 <- P.fresh_index()
    return C.TVr{k, i, s, q}

# parse_var(p, k, s): a bound var, an alias's or Base's dotted Ref, or a
# free name: a Var that is its Ref unless something binds it later
def var.ref(z: Bool, k: String, s: C.Sp, q: String) -> L.P(C.Tm):
  match z:
    case True{}:
      L.P.pure(C.Tm, C.TRef{q, s, False{}})
    case False{}:
      var.free(k, s, q)

def var.at(z: Bool, +i: U32, +k: String, +s: C.Sp) -> L.P(C.Tm):
  match z:
    case False{}:
      L.P.pure(C.Tm, C.TVar{k, i, s})
    case True{}:
      do L.P<C.Tm>:
        +q : String <- P.reso_t(k)
        var.ref(C.str.has_dot(k), k, s, q)

def P.var(+k: String, +s: C.Sp) -> L.P(C.Tm):
  do L.P<C.Tm>:
    e : L.Env <- L.P.env()
    +i : U32 = L.sc.find(L.env.sc(e), k)
    var.at(U32.is_eq(i, C.NONE()), i, k, s)

# parse_call(p, k, xs, s)
def P.call(k: String, xs: List<&2, C.Tm>, +s: C.Sp) -> L.P(C.Tm):
  do L.P<C.Tm>:
    q : String <- P.reso_t(k)
    return C.tm.app(C.TRef{q, s, False{}}, xs, s)

# parse_quant
def quant.plus(m: Bool) -> L.P(C.Q):
  match m:
    case True{}:
      L.P.pure(C.Q, C.QN{})
    case False{}:
      do L.P<C.Q>:
        p : Bool <- L.P.take([43])
        return Bool.pick(C.Q, p, C.QM{}, C.QL{})

def P.quant() -> L.P(C.Q):
  do L.P<C.Q>:
    L.P.skip()
    m : Bool <- L.P.take([45])
    quant.plus(m)

# parse_fill(p, k, xs, s): Fill and Plus omit a datatype's leading quantities
def fill.quas(n: U32, +s: C.Sp, xs: List<&2, C.Tm>) -> List<&2, C.Tm>:
  List.append(&2, C.Tm, List.replicate(C.Tm, U32.to_nat(n), C.TQua{C.QL{}, s}), xs)

def fill.at(t: C.Tld, +xs: List<&2, C.Tm>, s: C.Sp) -> List<&2, C.Tm>:
  match t:
    case C.TlAdt{+n, +g}:
      Bool.pick(List<&2, C.Tm>, U32.is_eq((U32.from_nat(List.length(&2, C.Tm, xs)) + g : U32), n), fill.quas(g, s, xs), xs)
    case _:
      xs

def P.fill(+k: String, xs: List<&2, C.Tm>, s: C.Sp) -> L.P(List<&2, C.Tm>):
  do L.P<List<&2, C.Tm>>:
    e : L.Env <- L.P.env()
    return fill.at(L.bk.tld(L.env.bk(e), k), xs, s)

def P.tld(+k: String) -> L.P(C.Tld):
  do L.P<C.Tld>:
    e : L.Env <- L.P.env()
    return L.bk.tld(L.env.bk(e), k)

def P.ctr_n(+k: String) -> L.P(U32):
  do L.P<U32>:
    e : L.Env <- L.P.env()
    return L.bk.ctr(L.env.bk(e), k)

def tld.is_adt(t: C.Tld) -> Bool:
  match t:
    case C.TlAdt{n, g}:
      True{}
    case _:
      False{}

def tld.def_x(t: C.Tld) -> U32:
  match t:
    case C.TlDef{n, x, hv, b, f}:
      x
    case _:
      0

# parse_more(p, col): a ; next, or a line at col
def P.more(+col: U32) -> L.P(Bool):
  do L.P<Bool>:
    +c : L.Cur <- L.P.cur()
    return Bool.or(T.prefix(L.cur.rest(c), [59]), Bool.and(Bool.not(List.is_empty(&2, U32, L.cur.rest(c))), U32.is_eq(L.cur.col(c), col)))

# parse_do_end
def do_end.if(z: Bool) -> L.P(Unit):
  match z:
    case True{}:
      L.P.fail(Unit, "a do-block let with its type (write \"x : T = ...\")")
    case False{}:
      L.P.pure(Unit, Unit{})

def do_end.bad(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{61, Con{61, t}}:
      False{}
    case Con{61, Con{62, t}}:
      False{}
    case Con{61, t}:
      True{}
    case _:
      False{}

def P.do_end() -> L.P(Unit):
  do L.P<Unit>:
    L.P.skip()
    c : L.Cur <- L.P.cur()
    do_end.if(do_end.bad(L.cur.rest(c)))

# the hole count
def P.hols() -> L.P(U32):
  do L.P<U32>:
    e : L.Env <- L.P.env()
    return L.bk.hols(L.env.bk(e))

def env.hols(n: U32, e: L.Env) -> L.Env:
  match e:
    case L.Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      L.Env{txt, fid, ns, al, dir, frs, sc, dep, ann, L.bk.set_hols(n, bk), ds}

def P.set_hols(n: U32) -> L.P(Unit):
  L.P.mod_env(env.hols(n))

def env.add_hol(e: L.Env) -> L.Env:
  match e:
    case L.Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      L.Env{txt, fid, ns, al, dir, frs, sc, dep, ann, L.bk.add_hol(bk), ds}

def P.add_hol() -> L.P(Unit):
  L.P.mod_env(env.add_hol)

# p.ann: the offsets where a typed let's type was tried and refused
def P.ann_has(+n: U32) -> L.P(Bool):
  do L.P<Bool>:
    e : L.Env <- L.P.env()
    return List.contains(~U32, ~U32.is_eq, L.env.ann(e), n)

def env.ann_add(n: U32, e: L.Env) -> L.Env:
  match e:
    case L.Env{txt, fid, ns, al, dir, frs, sc, dep, ann, bk, ds}:
      L.Env{txt, fid, ns, al, dir, frs, sc, dep, n <> ann, bk, ds}

def P.ann_add(n: U32) -> L.P(Unit):
  L.P.mod_env(env.ann_add(n))

# Operators
# ---------

# INFIX: [prc + 1, right, k] by index; INFIX_BY_HEAD's order of trial
def op.text(i: Nat) -> List<&2, U32>:
  match i:
    case 0n:
      [60, 45]
    case 1n:
      [45, 62]
    case 2n:
      [38]
    case 3n:
      [124]
    case 4n:
      [124, 124]
    case 5n:
      [38, 38]
    case 6n:
      [60]
    case 7n:
      [60, 61]
    case 8n:
      [62]
    case 9n:
      [62, 61]
    case 10n:
      [60, 62]
    case 11n:
      [43, 43]
    case 12n:
      [60, 38, 62]
    case 13n:
      [46, 124, 46]
    case 14n:
      [46, 94, 46]
    case 15n:
      [46, 38, 46]
    case 16n:
      [60, 60]
    case 17n:
      [62, 62]
    case 18n:
      [43]
    case 19n:
      [45]
    case 20n:
      [42]
    case 21n:
      [47]
    case _:
      [37]

# precedence plus one (<- is -1)
def op.prc(i: Nat) -> U32:
  match i:
    case 0n:
      0
    case 1n:
      1
    case 2n:
      2
    case 3n:
      2
    case 4n:
      3
    case 5n:
      4
    case 6n:
      5
    case 7n:
      5
    case 8n:
      5
    case 9n:
      5
    case 10n:
      6
    case 11n:
      6
    case 12n:
      6
    case 13n:
      7
    case 14n:
      8
    case 15n:
      9
    case 16n:
      10
    case 17n:
      10
    case 18n:
      11
    case 19n:
      11
    case _:
      12

def op.right(i: Nat) -> Bool:
  match i:
    case 1n:
      True{}
    case 2n:
      True{}
    case 3n:
      True{}
    case 10n:
      True{}
    case 11n:
      True{}
    case 12n:
      True{}
    case _:
      False{}

def op.k(i: Nat) -> String:
  match i:
    case 2n:
      "Pair"
    case 3n:
      "Or"
    case 4n:
      "Bool.or"
    case 5n:
      "Bool.and"
    case 6n:
      ".is_lt"
    case 7n:
      ".is_le"
    case 8n:
      ".is_gt"
    case 9n:
      ".is_ge"
    case 10n:
      "Con"
    case 11n:
      "String.append"
    case 13n:
      ".or"
    case 14n:
      ".xor"
    case 15n:
      ".and"
    case 16n:
      ".shln"
    case 17n:
      ".shrn"
    case 18n:
      ".add"
    case 19n:
      ".sub"
    case 20n:
      ".mul"
    case 21n:
      ".div"
    case 22n:
      ".mod"
    case _:
      ""

# INFIX_BY_HEAD[peek]: the operators to try at a head unit, in order
def op.trials(c: U32) -> List<&2, Nat>:
  match c:
    case 60:
      [12n, 0n, 7n, 10n, 16n, 6n]
    case 45:
      [1n, 19n]
    case 38:
      [5n, 2n]
    case 124:
      [4n, 3n]
    case 62:
      [9n, 17n, 8n]
    case 46:
      [13n, 14n, 15n]
    case 43:
      [11n, 18n]
    case 42:
      [20n]
    case 47:
      [21n]
    case 37:
      [22n]
    case _:
      Nil{}

# the operator at the head of xs, 23n when there is none
# (the first trial whose text is a prefix: the last one's test a
# parameter, so the rest are asked only on a miss)
def op.find.go(os: List<&2, Nat>, +xs: List<&2, U32>, hit: Bool, +o: Nat) -> Nat:
  match os hit:
    case _ True{}:
      o
    case Nil{} False{}:
      23n
    case Con{+o2, t} False{}:
      op.find.go(t, xs, T.prefix(xs, op.text(o2)), o2)

def op.find(+xs: List<&2, U32>) -> Nat:
  op.find.go(op.trials(L.cur.peek.go(xs)), xs, False{}, 23n)

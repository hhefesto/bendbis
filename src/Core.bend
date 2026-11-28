import Base

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Core: bend.ts's types (its "Core" and "Constructors" sections), first
# order. An LTerm is a Tm; its optional span is NoSp or Sp. A Var index
# of -1 (a + binder's mark, a share cell) is 4294967295, MINUS. A Var
# whose v is a Ref (parse_var's free name) is TVr. A literal is one node
# per base type: TNat, TU32, TF32 (its bits) and TStr (code points).

# Quant: None (-), Lone (), Many (+)
type Q is Data:
  QN{}
  QL{}
  QM{}

# a span: UTF-16 offsets beg..end in the file numbered f, or none
type Sp is Data:
  NoSp{}
  Sp{f: U32, beg: U32, end: U32}

type Tm is Data:
  TVar{k: String, i: U32, s: Sp}
  TVr{k: String, i: U32, s: Sp, r: String}
  TRef{k: String, s: Sp, b: Bool}
  TSub{i: U32, v: Pat, f: Tm, s: Sp}
  TLet{bs: List<&2, Bnd>, f: Tm, s: Sp}
  TTyp{g: Tm, s: Sp}
  TQnt{s: Sp}
  TQua{q: Q, s: Sp}
  TMin{a: Tm, b: Tm, s: Sp}
  TAll{q: Q, k: String, i: U32, A: Tm, B: Tm, s: Sp}
  TLam{k: String, i: U32, f: Tm, s: Sp, q: Q}
  TApp{f: Tm, x: Tm, s: Sp}
  TAdt{k: String, x: List<&2, Tm>, r: List<&2, String>, s: Sp}
  TCtr{k: String, x: List<&2, Tm>, s: Sp}
  TNat{v: U32, s: Sp}
  TU32{v: U32, s: Sp}
  TF32{v: U32, s: Sp}
  TStr{v: List<&2, U32>, s: Sp}
  TMat{k: String, h: Tm, m: Tm, s: Sp}
  TEfq{s: Sp}
  TEql{a: Tm, b: Tm, T: Tm, s: Sp}
  TRfl{s: Sp}
  TRwt{e: Tm, p: Tm, f: Tm, s: Sp}
  THol{k: String, s: Sp}
  TAnn{x: Tm, T: Tm, s: Sp}

# one binding of a parallel let: x = v at index i, quantity q
type Bnd is Data:
  Bnd{k: String, i: U32, q: Q, v: Tm}

type Pat is Data:
  PVar{k: String, i: U32, q: Q, s: Sp}
  PCtr{k: String, x: List<&2, Pat>, s: Sp}

type Body is Data:
  BMat{e: List<&2, Tm>, r: List<&2, Row>, s: Sp}
  BLoc{k: List<&2, Pat>, q: Q, v: List<&2, Tm>, f: Body}
  BTm{t: Tm}

type Row is Data:
  Row{p: List<&2, Pat>, f: Body}

# what the parser asks of a declared name (book.tlds): a datatype's
# parameter count and leading quantity count, or a def's arity, template
# count, and whether it has a body, is Base's or is foreign
type Tld is Data:
  TlNone{}
  TlAdt{n: U32, g: U32}
  TlDef{n: U32, x: U32, hasv: Bool, base: Bool, ffi: Bool}

# a parsed declaration, as parse_book leaves it in the book (its terms
# before term_higher): a datatype with its constructors, or a def (a law
# when it has no body and is no fill)
type Cn is Data:
  Cn{k: String, n: U32, T: Tm}

type Dcl is Data:
  DAdt{k: String, n: U32, g: U32, T: Tm, cs: List<&2, Cn>}
  DDef{k: String, n: U32, x: U32, T: Tm, v: Maybe<&2, Tm>, u: Bool, ffi: List<&2, String>, islaw: Bool, fill: Bool}

# an error, as err_show prints one with no context: what was expected, what
# was observed, where (the file's text and the span) and a note
type Er is Data:
  Er{exp: String, obs: Maybe<&2, String>, spn: Sp, txt: List<&2, U32>, nte: Maybe<&2, String>}
  ErRaw{msg: String}

def MINUS() -> U32:
  4294967295

def NONE() -> U32:
  4294967295

# Quant
# -----

def q.add(a: Q, b: Q) -> Q:
  match a b:
    case QN{} b:
      b
    case a QN{}:
      a
    case _ _:
      QM{}

def q.join(a: Q, b: Q) -> Q:
  match a b:
    case QM{} _:
      QM{}
    case _ QM{}:
      QM{}
    case QN{} b:
      b
    case a _:
      a

def q.dem(q: Q, qt: Q) -> Q:
  match q:
    case QN{}:
      QN{}
    case _:
      qt

def q.show(q: Q) -> String:
  match q:
    case QN{}:
      "-"
    case QL{}:
      ""
    case QM{}:
      "+"

def q.is_none(q: Q) -> Bool:
  match q:
    case QN{}:
      True{}
    case _:
      False{}

def q.is_lone(q: Q) -> Bool:
  match q:
    case QL{}:
      True{}
    case _:
      False{}

def q.is_many(q: Q) -> Bool:
  match q:
    case QM{}:
      True{}
    case _:
      False{}

# Spans
# -----

def sp.has(s: Sp) -> Bool:
  match s:
    case NoSp{}:
      False{}
    case Sp{f, b, e}:
      True{}

def sp.or(s: Sp, t: Sp) -> Sp:
  match s:
    case NoSp{}:
      t
    case Sp{f, b, e}:
      Sp{f, b, e}

def sp.beg(s: Sp) -> U32:
  match s:
    case NoSp{}:
      0
    case Sp{f, b, e}:
      b

# Terms
# -----

# a term's own span
def tm.s(t: Tm) -> Sp:
  match t:
    case TVar{k, i, s}:
      s
    case TVr{k, i, s, r}:
      s
    case TRef{k, s, b}:
      s
    case TSub{i, v, f, s}:
      s
    case TLet{bs, f, s}:
      s
    case TTyp{g, s}:
      s
    case TQnt{s}:
      s
    case TQua{q, s}:
      s
    case TMin{a, b, s}:
      s
    case TAll{q, k, i, A, B, s}:
      s
    case TLam{k, i, f, s, q}:
      s
    case TApp{f, x, s}:
      s
    case TAdt{k, x, r, s}:
      s
    case TCtr{k, x, s}:
      s
    case TNat{v, s}:
      s
    case TU32{v, s}:
      s
    case TF32{v, s}:
      s
    case TStr{v, s}:
      s
    case TMat{k, h, m, s}:
      s
    case TEfq{s}:
      s
    case TEql{a, b, T, s}:
      s
    case TRfl{s}:
      s
    case TRwt{e, p, f, s}:
      s
    case THol{k, s}:
      s
    case TAnn{x, T, s}:
      s

# t with its span set to s if it has none (x.s ??= s)
def tm.or_sp(t: Tm, s: Sp) -> Tm:
  match t:
    case TVar{k, i, u}:
      TVar{k, i, sp.or(u, s)}
    case TVr{k, i, u, r}:
      TVr{k, i, sp.or(u, s), r}
    case TRef{k, u, b}:
      TRef{k, sp.or(u, s), b}
    case TSub{i, v, f, u}:
      TSub{i, v, f, sp.or(u, s)}
    case TLet{bs, f, u}:
      TLet{bs, f, sp.or(u, s)}
    case TTyp{g, u}:
      TTyp{g, sp.or(u, s)}
    case TQnt{u}:
      TQnt{sp.or(u, s)}
    case TQua{q, u}:
      TQua{q, sp.or(u, s)}
    case TMin{a, b, u}:
      TMin{a, b, sp.or(u, s)}
    case TAll{q, k, i, A, B, u}:
      TAll{q, k, i, A, B, sp.or(u, s)}
    case TLam{k, i, f, u, q}:
      TLam{k, i, f, sp.or(u, s), q}
    case TApp{f, x, u}:
      TApp{f, x, sp.or(u, s)}
    case TAdt{k, x, r, u}:
      TAdt{k, x, r, sp.or(u, s)}
    case TCtr{k, x, u}:
      TCtr{k, x, sp.or(u, s)}
    case TNat{v, u}:
      TNat{v, sp.or(u, s)}
    case TU32{v, u}:
      TU32{v, sp.or(u, s)}
    case TF32{v, u}:
      TF32{v, sp.or(u, s)}
    case TStr{v, u}:
      TStr{v, sp.or(u, s)}
    case TMat{k, h, m, u}:
      TMat{k, h, m, sp.or(u, s)}
    case TEfq{u}:
      TEfq{sp.or(u, s)}
    case TEql{a, b, T, u}:
      TEql{a, b, T, sp.or(u, s)}
    case TRfl{u}:
      TRfl{sp.or(u, s)}
    case TRwt{e, p, f, u}:
      TRwt{e, p, f, sp.or(u, s)}
    case THol{k, u}:
      THol{k, sp.or(u, s)}
    case TAnn{x, T, u}:
      TAnn{x, T, sp.or(u, s)}

# the head of an application spine and its arguments (term_unapply)
def tm.unapp.go(t: Tm, acc: List<&2, Tm>) -> Tm & List<&2, Tm>:
  match t:
    case TApp{f, x, s}:
      tm.unapp.go(f, x <> acc)
    case t:
      (t, acc)

def tm.unapp(t: Tm) -> Tm & List<&2, Tm>:
  tm.unapp.go(t, Nil{})

def tm.head(t: Tm) -> Tm:
  match t:
    case TApp{f, x, s}:
      tm.head(f)
    case t:
      t

# is t a Var (TVar or TVr)
def tm.is_var(t: Tm) -> Bool:
  match t:
    case TVar{k, i, s}:
      True{}
    case TVr{k, i, s, r}:
      True{}
    case _:
      False{}

# the name a Var or a Ref spells, "" for any other term
def tm.name(t: Tm) -> String:
  match t:
    case TVar{k, i, s}:
      k
    case TVr{k, i, s, r}:
      k
    case TRef{k, s, b}:
      k
    case TAdt{k, x, r, s}:
      k
    case _:
      ""

def tm.app.go(xs: List<&2, Tm>, f: Tm, +s: Sp) -> Tm:
  match xs:
    case Nil{}:
      f
    case Con{x, r}:
      tm.app.go(r, TApp{f, x, s}, s)

def tm.app(f: Tm, xs: List<&2, Tm>, s: Sp) -> Tm:
  tm.app.go(xs, f, s)

# Strings
# -------

def str.eq(a: String, b: String) -> Bool:
  String.eq(a, b)

def str.has_dot(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{Chr{46}, t}:
      True{}
    case SCon{c, t}:
      str.has_dot(t)

# the part before the first dot ("" when there is none)
def str.before_dot.go(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{Chr{46}, t}:
      String.reverse(acc)
    case SCon{c, t}:
      str.before_dot.go(t, SCon{c, acc})

def str.before_dot(s: String) -> String:
  str.before_dot.go(s, "")

# the part after the first dot ("" when there is none)
def str.after_dot(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{46}, t}:
      t
    case SCon{c, t}:
      str.after_dot(t)

# Sizes
# -----

def bnd.vals(bs: List<&2, Bnd>) -> List<&2, Tm>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{Bnd{k, i, q, v}, t}:
      v <> bnd.vals(t)

# the nodes of a list of terms, n plus (a work list, so on fuel: one step
# a node)
def tms.size(fuel: Nat, ts: List<&2, Tm>, +n: U32) -> U32:
  match fuel ts:
    case 0n _:
      n
    case _ Nil{}:
      n
    case 1n+f Con{t, r}:
      match t:
        case TSub{i, v, b, s}:
          tms.size(f, b <> r, (n + 1 : U32))
        case TLet{bs, b, s}:
          tms.size(f, List.append(&2, Tm, bnd.vals(bs), b <> r), (n + 1 : U32))
        case TTyp{g, s}:
          tms.size(f, g <> r, (n + 1 : U32))
        case TMin{a, b, s}:
          tms.size(f, a <> b <> r, (n + 1 : U32))
        case TAll{q, k, i, A, B, s}:
          tms.size(f, A <> B <> r, (n + 1 : U32))
        case TLam{k, i, b, s, q}:
          tms.size(f, b <> r, (n + 1 : U32))
        case TApp{a, b, s}:
          tms.size(f, a <> b <> r, (n + 1 : U32))
        case TAdt{k, xs, rs, s}:
          tms.size(f, List.append(&2, Tm, xs, r), (n + 1 : U32))
        case TCtr{k, xs, s}:
          tms.size(f, List.append(&2, Tm, xs, r), (n + 1 : U32))
        case TMat{k, h, b, s}:
          tms.size(f, h <> b <> r, (n + 1 : U32))
        case TEql{a, b, A, s}:
          tms.size(f, a <> b <> A <> r, (n + 1 : U32))
        case TRwt{e, p, b, s}:
          tms.size(f, e <> p <> b <> r, (n + 1 : U32))
        case TAnn{x, A, s}:
          tms.size(f, x <> A <> r, (n + 1 : U32))
        case _:
          tms.size(f, r, (n + 1 : U32))

def tm.size(t: Tm) -> U32:
  tms.size(4294967295n, [t], 0)

# Index occurrence
# ----------------

# whether the index i occurs in ps or ts, hit or not: as a Var's, a Var
# Ref's or a Sub's, or in a Sub's pattern (a work list, so on fuel: one
# step a node; out of fuel, yes). Binders don't count: only a Var, a Var
# Ref or a pattern's var reads an environment.
def tms.has(fuel: Nat, hit: Bool, ps: List<&2, Pat>, ts: List<&2, Tm>, +i: U32) -> Bool:
  match fuel hit ps ts:
    case 0n _ _ _:
      True{}
    case _ True{} _ _:
      True{}
    case 1n+f False{} Con{p, r} us:
      match p:
        case PVar{k, j, q, s}:
          tms.has(f, U32.is_eq(i, j), r, us, i)
        case PCtr{k, xs, s}:
          tms.has(f, False{}, List.append(&2, Pat, xs, r), us, i)
    case _ False{} Nil{} Nil{}:
      False{}
    case 1n+f False{} Nil{} Con{t, r}:
      match t:
        case TVar{k, j, s}:
          tms.has(f, U32.is_eq(i, j), Nil{}, r, i)
        case TVr{k, j, s, x}:
          tms.has(f, U32.is_eq(i, j), Nil{}, r, i)
        case TSub{j, v, b, s}:
          tms.has(f, U32.is_eq(i, j), [v], b <> r, i)
        case TLet{bs, b, s}:
          tms.has(f, False{}, Nil{}, List.append(&2, Tm, bnd.vals(bs), b <> r), i)
        case TTyp{g, s}:
          tms.has(f, False{}, Nil{}, g <> r, i)
        case TMin{a, b, s}:
          tms.has(f, False{}, Nil{}, a <> b <> r, i)
        case TAll{q, k, j, A, B, s}:
          tms.has(f, False{}, Nil{}, A <> B <> r, i)
        case TLam{k, j, b, s, q}:
          tms.has(f, False{}, Nil{}, b <> r, i)
        case TApp{a, b, s}:
          tms.has(f, False{}, Nil{}, a <> b <> r, i)
        case TAdt{k, xs, rs, s}:
          tms.has(f, False{}, Nil{}, List.append(&2, Tm, xs, r), i)
        case TCtr{k, xs, s}:
          tms.has(f, False{}, Nil{}, List.append(&2, Tm, xs, r), i)
        case TMat{k, h, b, s}:
          tms.has(f, False{}, Nil{}, h <> b <> r, i)
        case TEql{a, b, A, s}:
          tms.has(f, False{}, Nil{}, a <> b <> A <> r, i)
        case TRwt{e, p, b, s}:
          tms.has(f, False{}, Nil{}, e <> p <> b <> r, i)
        case TAnn{x, A, s}:
          tms.has(f, False{}, Nil{}, x <> A <> r, i)
        case _:
          tms.has(f, False{}, Nil{}, r, i)

def tm.has(t: Tm, +i: U32) -> Bool:
  tms.has(4294967295n, False{}, Nil{}, [t], i)

# Reading a map the caller keeps
# ------------------------------

# Base's Map.get answers the map too, a copy of the path it walked, which
# a caller that keeps its own (dup'd) map only drops: mp.find walks the
# same trie (the same cursor into the key) and answers the value alone
def mp.leaf(-V: Data, v: V, +key: String, k: String) -> Maybe<&2, V>:
  Bool.pick(Maybe<&2, V>, String.eq(key, k), Some{v}, None{})

def mp.go(-V: Data, fuel: Nat, b: Bool, lo: Map<&2, V>, hi: Map<&2, V>, +key: String, rest: String, ci: Nat) -> Maybe<&2, V>:
  match fuel b lo hi:
    case 0n _ _ _:
      None{}
    case 1n+f False{} MLeaf{k, v} _:
      mp.leaf(V, v, key, k)
    case 1n+f False{} MNode{+q, x, y} _:
      +cq = Nat.div(q, 33n)
      +r2 = Map.get.skip(Nat.sub(cq, ci), rest)
      mp.go(V, f, Map.get.bit(r2, Nat.mod(q, 33n)), x, y, key, r2, cq)
    case 1n+f True{} _ MLeaf{k, v}:
      mp.leaf(V, v, key, k)
    case 1n+f True{} _ MNode{+q, x, y}:
      +cq = Nat.div(q, 33n)
      +r2 = Map.get.skip(Nat.sub(cq, ci), rest)
      mp.go(V, f, Map.get.bit(r2, Nat.mod(q, 33n)), x, y, key, r2, cq)
    case _ _ _ _:
      None{}

def mp.find(-V: Data, m: Map<&2, V>, +key: String) -> Maybe<&2, V>:
  match m:
    case MTip{}:
      None{}
    case MLeaf{k, v}:
      mp.leaf(V, v, key, k)
    case MNode{+pos, lo, hi}:
      +cq = Nat.div(pos, 33n)
      +rest = String.drop(key, cq)
      mp.go(V, 4294967295n, Map.get.bit(rest, Nat.mod(pos, 33n)), lo, hi, key, rest, cq)

# Map.get(V, d, m, key)'s value
def mp.get(-V: Data, d: V, m: Map<&2, V>, +key: String) -> V:
  Maybe.default(&2, V, mp.find(V, m, key), d)

# Map.has(&2, V, m, key)'s answer
def mp.has(-V: Data, m: Map<&2, V>, +key: String) -> Bool:
  Maybe.is_some(&2, V, mp.find(V, m, key))

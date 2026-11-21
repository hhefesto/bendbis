import Base
import ./Text.bend as T
import ./Core.bend as C
import ./Num.bend as N

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Show: bend.ts's "Show" section: name_key, name_show and term_show, with
# its sugars (Exists, Nat, lists, tuples, arrays, chars, strings, words).
# A precedence p of bend.ts (-1 to 2) is p + 1 here. Text is UTF-16 units.

# the file a term is shown for: its namespace and import aliases
type Fl is Data:
  NoFl{}
  Fl{ns: String, al: List<&2, Al2>}

type Al2 is Data:
  Al2{a: String, ns: String}

# Names
# -----

def key.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{58}, t}:
      SCon{Chr{46}, t}
    case SCon{c, t}:
      SCon{c, key.go(t)}

# name_key: ns:name is shown ns.name
def name.key(k: String) -> String:
  key.go(k)

def colon.has(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{Chr{58}, t}:
      True{}
    case SCon{c, t}:
      colon.has(t)

def colon.before(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{58}, t}:
      SNil{}
    case SCon{c, t}:
      SCon{c, colon.before(t)}

# what follows the first colon, up to a second one (split(":")[1])
def colon.after.go(s: String, on: Bool) -> String:
  match s on:
    case SNil{} _:
      SNil{}
    case SCon{Chr{58}, t} False{}:
      colon.after.go(t, True{})
    case SCon{Chr{58}, t} True{}:
      SNil{}
    case SCon{c, t} True{}:
      SCon{c, colon.after.go(t, True{})}
    case SCon{c, t} False{}:
      colon.after.go(t, False{})

def colon.after(s: String) -> String:
  colon.after.go(s, False{})

def al.find(al: List<&2, Al2>, +ns: String) -> Maybe<&2, String>:
  match al:
    case Nil{}:
      None{}
    case Con{Al2{a, n}, t}:
      Maybe.or(&2, String, Bool.pick(Maybe<&2, String>, String.eq(n, ns), Some{a}, None{}), al.find(t, ns))

def name.show.fin(own: Bool, nm: String, a: Maybe<&2, String>, k: String) -> String:
  match own a:
    case True{} _:
      nm
    case False{} None{}:
      name.key(k)
    case False{} Some{x}:
      x ++ "." ++ nm

def name.show.at(+fns: String, al: List<&2, Al2>, +k: String) -> String:
  +ns = Bool.pick(String, colon.has(k), colon.before(k), "")
  +nm = Bool.pick(String, colon.has(k), colon.after(k), k)
  name.show.fin(String.eq(ns, fns), nm, al.find(al, ns), k)

# name_show: a file's own names bare, an imported file's through its alias
def name.show(f: Fl, +k: String) -> String:
  match f:
    case NoFl{}:
      name.key(k)
    case Fl{ns, al}:
      name.show.at(ns, al, k)

# Bound names
# -----------

# bnd as a stack (top first) with its length: lastIndexOf(k) is the
# length less one less k's depth from the top, -1 when absent
def bnd.depth(xs: List<&2, String>, +k: String, +d: U32) -> U32:
  match xs:
    case Nil{}:
      C.NONE()
    case Con{h, t}:
      Bool.pick(U32, String.eq(h, k), d, bnd.depth(t, k, (d + 1 : U32)))

def bnd.last(+xs: List<&2, String>, +k: String) -> U32:
  +d = bnd.depth(xs, k, 0)
  Bool.pick(U32, U32.is_eq(d, C.NONE()), C.NONE(), ((U32.from_nat(List.length(&2, String, xs)) - 1 : U32) - d : U32))

def bnd.has(xs: List<&2, String>, k: String) -> Bool:
  Bool.not(U32.is_eq(bnd.depth(xs, k, 0), C.NONE()))

def int.show(+i: U32) -> String:
  Bool.pick(String, U32.is_eq(i, C.MINUS()), "-1", U32.show(i))

# Characters
# ----------

# chr_show(n, quote): an escape, \u{hex} for a control or a non-scalar,
# else the character (q the quote, 39 or 34, that takes an escape)
def chr.esc(+n: U32, +q: U32) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, U32.is_eq(n, 10), Some{"\\n"},
  Bool.pick(Maybe<&2, String>, U32.is_eq(n, 9), Some{"\\t"},
  Bool.pick(Maybe<&2, String>, U32.is_eq(n, 13), Some{"\\r"},
  Bool.pick(Maybe<&2, String>, U32.is_eq(n, 0), Some{"\\0"},
  Bool.pick(Maybe<&2, String>, U32.is_eq(n, 92), Some{"\\\\"},
  Bool.pick(Maybe<&2, String>, Bool.and(U32.is_eq(n, 39), U32.is_eq(q, 39)), Some{"\\'"},
  Bool.pick(Maybe<&2, String>, Bool.and(U32.is_eq(n, 34), U32.is_eq(q, 34)), Some{"\\\""}, None{})))))))

def hex.digits(fuel: Nat, +n: U32, acc: String) -> String:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      +d = (n .&. 15 : U32)
      +c : String = SCon{Chr{Bool.pick(U32, U32.is_lt(d, 10), (48 + d : U32), (87 + d : U32))}, acc}
      Bool.pick(String, U32.is_lt(n, 16), c, hex.digits(f, (n >> 4n : U32), c))

def chr.plain(+n: U32) -> String:
  Bool.pick(String, Bool.or(Bool.or(U32.is_lt(n, 32), U32.is_eq(n, 127)), Bool.or(Bool.and(U32.is_le(55296, n), U32.is_le(n, 57343)), U32.is_gt(n, 1114111))),
    "\\u{" ++ hex.digits(8n, n, "") ++ "}", T.str.cps([n]))

def chr.show(+n: U32, q: U32) -> String:
  Maybe.default(&2, String, chr.esc(n, q), chr.plain(n))

# lit_text: a string's code points shown inside double quotes
def lit.text(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{c, t}:
      chr.show(c, 34) ++ lit.text(t)

# Sugars (structural; none shows a subterm)
# ------

def word.bit(b: C.Tm) -> U32:
  match b:
    case C.TCtr{+k, Nil{}, s}:
      Bool.pick(U32, String.eq(k, "True"), 1, Bool.pick(U32, String.eq(k, "False"), 0, 2))
    case _:
      2

def word.go(t: C.Tm, +i: Nat, +acc: U32) -> Maybe<&2, U32>:
  match t:
    case C.TCtr{+k, Nil{}, s}:
      Bool.pick(Maybe<&2, U32>, Bool.and(String.eq(k, "WNil"), Nat.is_eq(i, 32n)), Some{acc}, None{})
    case C.TCtr{+k, Con{b, Con{w, Nil{}}}, s}:
      +v = word.bit(b)
      Bool.pick(Maybe<&2, U32>, Bool.and(String.eq(k, "WCon"), Bool.and(U32.is_lt(v, 2), Nat.is_lt(i, 32n))),
        word.go(w, 1n+i, (acc + (v << i : U32) : U32)), None{})
    case _:
      None{}

# u32_from_term(t, k): a word literal of base type k, or a k{word}
def u32.of(+k: String, t: C.Tm) -> Maybe<&2, U32>:
  match t:
    case C.TU32{v, s}:
      Bool.pick(Maybe<&2, U32>, String.eq(k, "U32"), Some{v}, None{})
    case C.TF32{v, s}:
      Bool.pick(Maybe<&2, U32>, String.eq(k, "F32"), Some{v}, None{})
    case C.TCtr{c, Con{w, Nil{}}, s}:
      Bool.pick(Maybe<&2, U32>, String.eq(c, k), word.go(w, 0n, 0), None{})
    case C.TAnn{x, A, s}:
      u32.of(k, x)
    case _:
      None{}

# nat_from_term: Succ{..Zero{}} or Succ{..lit}
def nat.of(t: C.Tm, +n: U32) -> Maybe<&2, U32>:
  match t:
    case C.TCtr{k, Con{x, Nil{}}, s}:
      Bool.pick(Maybe<&2, U32>, String.eq(k, "Succ"), nat.of(x, (n + 1 : U32)), None{})
    case C.TCtr{k, Nil{}, s}:
      Bool.pick(Maybe<&2, U32>, String.eq(k, "Zero"), Some{n}, None{})
    case C.TNat{+v, s}:
      Bool.pick(Maybe<&2, U32>, U32.is_le(v, (4294967295 - n : U32)), Some{(n + v : U32)}, None{})
    case _:
      None{}

# term_show_chain(t, k, n): the first fields of nested k{..}s, and the rest
# term_show_chain(t, k, n): the first fields of nested k{..}s, and the rest
# a chain step: on (k matches) go on with next, else stop at t
def chain.at(z: Bool, t: C.Tm, acc: List<&2, C.Tm>, rest: Unit -> List<&2, C.Tm> & C.Tm) -> List<&2, C.Tm> & C.Tm:
  match z:
    case True{}:
      rest(Unit{})
    case False{}:
      (List.reverse(&2, C.Tm, acc), t)

def chain(+k: String, +n: U32, t: C.Tm, +acc: List<&2, C.Tm>) -> List<&2, C.Tm> & C.Tm:
  match t:
    case C.TCtr{+c, Con{+h, Con{+r, Nil{}}}, +s}:
      chain.at(Bool.and(String.eq(c, k), U32.is_eq(n, 2)), C.TCtr{c, [h, r], s}, acc, u => chain(k, n, r, h <> acc))
    case C.TCtr{+c, Con{+h, Nil{}}, +s}:
      chain.at(Bool.and(String.eq(c, k), U32.is_eq(n, 1)), C.TCtr{c, [h], s}, acc, u => chain(k, n, h, h <> acc))
    case t:
      (List.reverse(&2, C.Tm, acc), t)

# the char of a Chr{word} (term_show_sugar_chr)
def chr.of(t: C.Tm) -> Maybe<&2, U32>:
  match t:
    case C.TCtr{k, Con{x, Nil{}}, s}:
      Bool.pick(Maybe<&2, U32>, String.eq(k, "Chr"), u32.of("U32", x), None{})
    case _:
      None{}

def chrs.put(c: Maybe<&2, U32>, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match c r:
    case Some{c} Some{r}:
      Some{c <> r}
    case _ _:
      None{}

def chrs.of(ts: List<&2, C.Tm>) -> Maybe<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Some{Nil{}}
    case Con{h, t}:
      chrs.put(chr.of(h), chrs.of(t))

def str.tail(t: C.Tm) -> Maybe<&2, String>:
  match t:
    case C.TStr{v, s}:
      Some{lit.text(v)}
    case C.TCtr{k, Nil{}, s}:
      Bool.pick(Maybe<&2, String>, String.eq(k, "SNil"), Some{""}, None{})
    case _:
      None{}

def str.chars(cs: List<&2, U32>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{c, t}:
      chr.show(c, 34) ++ str.chars(t)

def str.sugar.fin(cs: Maybe<&2, List<&2, U32>>, tl: Maybe<&2, String>) -> Maybe<&2, String>:
  match cs tl:
    case Some{cs} Some{tl}:
      Some{"\"" ++ str.chars(cs) ++ tl ++ "\""}
    case _ _:
      None{}

def str.sugar.of(r: List<&2, C.Tm> & C.Tm) -> Maybe<&2, String>:
  (cs, t) = r
  str.sugar.fin(chrs.of(cs), str.tail(t))

# term_show_sugar_str
def str.sugar(t: C.Tm) -> Maybe<&2, String>:
  str.sugar.of(chain("SCon", 2, t, Nil{}))

# term_show_sugar_arr: the leaves of an ALeaf/ANode tree
def arr.cat(a: Maybe<&2, List<&2, C.Tm>>, b: Maybe<&2, List<&2, C.Tm>>) -> Maybe<&2, List<&2, C.Tm>>:
  match a b:
    case Some{x} Some{y}:
      Some{List.append(&2, C.Tm, x, y)}
    case _ _:
      None{}

def arr.node(z: Bool, rest: Unit -> Maybe<&2, List<&2, C.Tm>>) -> Maybe<&2, List<&2, C.Tm>>:
  match z:
    case True{}:
      rest(Unit{})
    case False{}:
      None{}

def arr.of(t: C.Tm) -> Maybe<&2, List<&2, C.Tm>>:
  match t:
    case C.TCtr{k, Con{x, Nil{}}, s}:
      Bool.pick(Maybe<&2, List<&2, C.Tm>>, String.eq(k, "ALeaf"), Some{[x]}, None{})
    case C.TCtr{k, Con{l, Con{r, Nil{}}}, s}:
      arr.node(String.eq(k, "ANode"), u => arr.cat(arr.of(l), arr.of(r)))
    case _:
      None{}

def is.lam(t: C.Tm) -> Bool:
  match t:
    case C.TLam{k, i, f, s, q}:
      True{}
    case _:
      False{}

def is.nil(t: C.Tm) -> Bool:
  match t:
    case C.TCtr{k, Nil{}, s}:
      String.eq(k, "Nil")
    case _:
      False{}

# term_strip, on an LTerm: through annotations
def strip(t: C.Tm) -> C.Tm:
  match t:
    case C.TAnn{x, A, s}:
      strip(x)
    case t:
      t

# Show
# ----

def paren(z: Bool, s: String) -> String:
  match z:
    case True{}:
      "(" ++ s ++ ")"
    case False{}:
      s

def typ.lit(g: C.Tm) -> Maybe<&2, String>:
  match g:
    case C.TQua{C.QL{}, s}:
      Some{"Type"}
    case C.TQua{C.QM{}, s}:
      Some{"Data"}
    case _:
      None{}

def qua.show(q: C.Q) -> String:
  match q:
    case C.QN{}:
      "&0"
    case C.QL{}:
      "&1"
    case C.QM{}:
      "&2"

type Arm is Data:
  Arm{k: String, h: C.Tm}

# the Mat chain's arms, and its tail when that is no Efq
def mat.arms(t: C.Tm, acc: List<&2, Arm>) -> List<&2, Arm> & Maybe<&2, C.Tm>:
  match t:
    case C.TMat{k, h, m, s}:
      mat.arms(m, Arm{k, h} <> acc)
    case C.TEfq{s}:
      (List.reverse(&2, Arm, acc), None{})
    case t:
      (List.reverse(&2, Arm, acc), Some{t})

# term_show_sugar_exi: Exists(A, x => B)
type ExP is Data:
  ExN{}
  ExY{A: C.Tm, k: String, f: C.Tm}

def ex.chk(h: C.Tm, xs: List<&2, C.Tm>) -> ExP:
  match h xs:
    case C.TRef{k, s, b} Con{a, Con{C.TLam{x, i, f, u, q}, Nil{}}}:
      Bool.pick(ExP, String.eq(k, "Exists"), ExY{a, x, f}, ExN{})
    case _ _:
      ExN{}

def ex.of(hx: C.Tm & List<&2, C.Tm>) -> ExP:
  (h, xs) = hx
  ex.chk(h, xs)

# a constructor's sugar, decided before any subterm is shown
type Cs is Data:
  CsStr{s: String}
  CsSucc{n: U32, t: C.Tm}
  CsList{xs: List<&2, C.Tm>}
  CsCons{xs: List<&2, C.Tm>, t: C.Tm}
  CsTup{xs: List<&2, C.Tm>}
  CsPlain{k: String, xs: List<&2, C.Tm>}

def cs.arr(a: Maybe<&2, List<&2, C.Tm>>, +k: String, xs: List<&2, C.Tm>, +fl: Fl) -> Cs:
  match a:
    case Some{ys}:
      CsList{ys}
    case None{}:
      CsPlain{name.show(fl, k), xs}

def cs.tup(r: List<&2, C.Tm> & C.Tm, +k: String, +xs: List<&2, C.Tm>, +fl: Fl) -> Cs:
  (ys, t) = r
  match ys:
    case Nil{}:
      cs.arr(arr.of(C.TCtr{k, xs, C.NoSp{}}), k, xs, fl)
    case Con{y, r}:
      CsTup{List.append(&2, C.Tm, Con{y, r}, [t])}

# no Con: Nil{} alone is [], anything else may be a tuple
def cs.lst.nil(z: Bool, +k: String, +xs: List<&2, C.Tm>, +fl: Fl) -> Cs:
  match z:
    case True{}:
      CsList{Nil{}}
    case False{}:
      cs.tup(chain("Tuple", 2, C.TCtr{k, xs, C.NoSp{}}, Nil{}), k, xs, fl)

def cs.lst(r: List<&2, C.Tm> & C.Tm, +k: String, +xs: List<&2, C.Tm>, +fl: Fl) -> Cs:
  (ys, +t) = r
  match ys:
    case Nil{}:
      cs.lst.nil(is.nil(t), k, xs, fl)
    case Con{+y, +r}:
      Bool.pick(Cs, is.nil(t), CsList{Con{y, r}}, CsCons{Con{y, r}, t})

def cs.str(m: Maybe<&2, String>, +k: String, +xs: List<&2, C.Tm>, +fl: Fl) -> Cs:
  match m:
    case Some{s}:
      CsStr{s}
    case None{}:
      cs.lst(chain("Con", 2, C.TCtr{k, xs, C.NoSp{}}, Nil{}), k, xs, fl)

def cs.chr(m: Maybe<&2, U32>, +k: String, +xs: List<&2, C.Tm>, +fl: Fl) -> Cs:
  match m:
    case Some{c}:
      CsStr{"'" ++ chr.show(c, 39) ++ "'"}
    case None{}:
      cs.str(str.sugar(C.TCtr{k, xs, C.NoSp{}}), k, xs, fl)

def cs.succ(r: List<&2, C.Tm> & C.Tm, +k: String, +xs: List<&2, C.Tm>, +fl: Fl) -> Cs:
  (ys, t) = r
  match ys:
    case Nil{}:
      cs.chr(chr.of(C.TCtr{k, xs, C.NoSp{}}), k, xs, fl)
    case Con{y, r}:
      CsSucc{U32.from_nat(List.length(&2, C.Tm, Con{y, r})), t}

def cs.nat(m: Maybe<&2, U32>, +k: String, +xs: List<&2, C.Tm>, +fl: Fl) -> Cs:
  match m:
    case Some{n}:
      CsStr{U32.show(n) ++ "n"}
    case None{}:
      cs.succ(chain("Succ", 1, C.TCtr{k, xs, C.NoSp{}}, Nil{}), k, xs, fl)

def cs.f32(m: Maybe<&2, U32>, +k: String, +xs: List<&2, C.Tm>, +fl: Fl) -> Cs:
  match m:
    case Some{v}:
      CsStr{T.str(N.f32.show(v))}
    case None{}:
      cs.nat(nat.of(C.TCtr{k, xs, C.NoSp{}}, 0), k, xs, fl)

def cs.u32(m: Maybe<&2, U32>, +k: String, +xs: List<&2, C.Tm>, +fl: Fl) -> Cs:
  match m:
    case Some{v}:
      CsStr{U32.show(v)}
    case None{}:
      cs.f32(u32.of("F32", C.TCtr{k, xs, C.NoSp{}}), k, xs, fl)

def cs.of(+k: String, +xs: List<&2, C.Tm>, +fl: Fl) -> Cs:
  cs.u32(u32.of("U32", C.TCtr{k, xs, C.NoSp{}}), k, xs, fl)

# a rewrite's motive: _ => e => P, its names and P, or neither
type Rw is Data:
  RwN{}
  RwY{a: String, b: String, P: C.Tm}

def rw.inner(+a: String, t: C.Tm) -> Rw:
  match t:
    case C.TLam{b, i, f, s, q}:
      RwY{a, b, f}
    case _:
      RwN{}

def rw.of(t: C.Tm) -> Rw:
  match t:
    case C.TLam{a, i, f, s, q}:
      rw.inner(a, strip(f))
    case _:
      RwN{}

def let.names(bs: List<&2, C.Bnd>, bnd: List<&2, String>) -> List<&2, String>:
  match bs:
    case Nil{}:
      bnd
    case Con{C.Bnd{k, i, q, v}, t}:
      let.names(t, k <> bnd)

def let.vals(bs: List<&2, C.Bnd>) -> List<&2, C.Tm>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{C.Bnd{k, i, q, v}, t}:
      v <> let.vals(t)

def let.keys(bs: List<&2, C.Bnd>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{C.Bnd{k, i, q, v}, Nil{}}:
      C.q.show(q) ++ k
    case Con{C.Bnd{k, i, q, v}, t}:
      C.q.show(q) ++ k ++ " " ++ let.keys(t)

def adt.rs(+fl: Fl, rs: List<&2, String>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{c, t}:
      " - " ++ name.show(fl, c) ++ "{}" ++ adt.rs(fl, t)

def sep.if(more: Bool, s: String) -> String:
  match more:
    case True{}:
      s
    case False{}:
      ""

def has.more(xs: List<&2, Arm>, t: Maybe<&2, C.Tm>) -> Bool:
  match xs:
    case Con{h, r}:
      True{}
    case Nil{}:
      Maybe.is_some(&2, C.Tm, t)

# what term_show's go is asked
type Sj is Data:
  SjT{t: C.Tm, prc: U32, bnd: List<&2, String>}
  SjL{ts: List<&2, C.Tm>, prc: U32, sep: String, bnd: List<&2, String>}
  SjEx{ex: ExP, h: C.Tm, xs: List<&2, C.Tm>, prc: U32, bnd: List<&2, String>}
  SjCs{cs: Cs, prc: U32, bnd: List<&2, String>}
  SjMat{arms: List<&2, Arm>, tl: Maybe<&2, C.Tm>, bnd: List<&2, String>}
  SjRw{rw: Rw, e: C.Tm, p: C.Tm, f: C.Tm, prc: U32, bnd: List<&2, String>}

def ex.job(hx: C.Tm & List<&2, C.Tm>, prc: U32, bnd: List<&2, String>) -> Sj:
  (+h, +xs) = hx
  SjEx{ex.chk(h, xs), h, xs, prc, bnd}

def mat.job(am: List<&2, Arm> & Maybe<&2, C.Tm>, bnd: List<&2, String>) -> Sj:
  (a, t) = am
  SjMat{a, t, bnd}

def show.go(+fuel: Nat, +fl: Fl, j: Sj) -> String:
  match fuel j:
    case 0n _:
      "..."
    case 1n+p SjL{ts, +prc, +sep, +bnd}:
      match ts:
        case Nil{}:
          ""
        case Con{h, Nil{}}:
          show.go(p, fl, SjT{h, prc, bnd})
        case Con{h, t}:
          show.go(p, fl, SjT{h, prc, bnd}) ++ sep ++ show.go(p, fl, SjL{t, prc, sep, bnd})
    case 1n+p SjEx{ex, h, xs, +prc, +bnd}:
      match ex:
        case ExY{A, +k, f}:
          paren(U32.is_gt(prc, 2), "&" ++ k ++ ":" ++ show.go(p, fl, SjT{A, 3, bnd}) ++ " -> " ++ show.go(p, fl, SjT{f, 2, k <> bnd}))
        case ExN{}:
          show.go(p, fl, SjT{h, 3, bnd}) ++ "(" ++ show.go(p, fl, SjL{xs, 1, ", ", bnd}) ++ ")"
    case 1n+p SjCs{cs, +prc, +bnd}:
      match cs:
        case CsStr{s}:
          s
        case CsSucc{n, t}:
          paren(U32.is_gt(prc, 2), U32.show(n) ++ "n+" ++ show.go(p, fl, SjT{t, 2, bnd}))
        case CsList{xs}:
          "[" ++ show.go(p, fl, SjL{xs, 1, ", ", bnd}) ++ "]"
        case CsCons{xs, t}:
          paren(U32.is_gt(prc, 2), show.go(p, fl, SjL{xs, 3, " <> ", bnd}) ++ " <> " ++ show.go(p, fl, SjT{t, 2, bnd}))
        case CsTup{xs}:
          "(" ++ show.go(p, fl, SjL{xs, 1, ", ", bnd}) ++ ")"
        case CsPlain{k, xs}:
          k ++ "{" ++ show.go(p, fl, SjL{xs, 1, ", ", bnd}) ++ "}"
    case 1n+p SjMat{arms, +tl, +bnd}:
      match arms:
        case Con{Arm{k, h}, +r}:
          name.show(fl, k) ++ ": " ++ show.go(p, fl, SjT{h, 2, bnd}) ++ sep.if(has.more(r, tl), "; ") ++ show.go(p, fl, SjMat{r, tl, bnd})
        case Nil{}:
          match tl:
            case Some{t}:
              show.go(p, fl, SjT{t, 2, bnd})
            case None{}:
              ""
    case 1n+p SjRw{rw, e, m, f, +prc, +bnd}:
      match rw:
        case RwY{a, +b, P}:
          paren(U32.is_gt(prc, 1), "%" ++ Bool.pick(String, String.is_empty(b), "", b ++ "@") ++ show.go(p, fl, SjT{e, 2, bnd}) ++ " : " ++ show.go(p, fl, SjT{P, 2, b <> a <> bnd}) ++ "; " ++ show.go(p, fl, SjT{f, 0, bnd}))
        case RwN{}:
          paren(U32.is_gt(prc, 1), "%" ++ show.go(p, fl, SjT{e, 2, bnd}) ++ " : " ++ show.go(p, fl, SjT{m, 2, bnd}) ++ "; " ++ show.go(p, fl, SjT{f, 0, bnd}))
    case 1n+p SjT{t, +prc, +bnd}:
      match t:
        case C.TVar{+k, +i, s}:
          Bool.pick(String, U32.is_eq(bnd.last(bnd, k), i), k, k ++ "^" ++ int.show(i))
        case C.TVr{+k, +i, s, r}:
          Bool.pick(String, U32.is_eq(bnd.last(bnd, k), i), k, k ++ "^" ++ int.show(i))
        case C.TRef{k, s, b}:
          +n = name.show(fl, k)
          Bool.pick(String, bnd.has(bnd, n), n ++ "^", n) ++ Bool.pick(String, b, "!", "")
        case C.TSub{i, v, f, s}:
          show.go(p, fl, SjT{f, prc, bnd})
        case C.TLet{+bs, f, s}:
          paren(U32.is_ge(prc, 1), let.keys(bs) ++ " = " ++ show.go(p, fl, SjL{let.vals(bs), 2, " ", bnd}) ++ "; " ++ show.go(p, fl, SjT{f, 0, let.names(bs, bnd)}))
        case C.TTyp{+g, s}:
          Maybe.default(&2, String, typ.lit(g), "Kind(" ++ show.go(p, fl, SjT{g, 1, bnd}) ++ ")")
        case C.TQnt{s}:
          "Quant"
        case C.TQua{q, s}:
          qua.show(q)
        case C.TMin{a, b, s}:
          paren(U32.is_gt(prc, 2), show.go(p, fl, SjT{a, 3, bnd}) ++ " <&> " ++ show.go(p, fl, SjT{b, 3, bnd}))
        case C.TAll{q, +k, i, A, B, s}:
          paren(U32.is_gt(prc, 2), "@" ++ C.q.show(q) ++ k ++ ":" ++ show.go(p, fl, SjT{A, 3, bnd}) ++ " -> " ++ show.go(p, fl, SjT{B, 2, k <> bnd}))
        case C.TLam{+k, i, f, s, q}:
          paren(U32.is_gt(prc, 1), C.q.show(q) ++ k ++ " => " ++ show.go(p, fl, SjT{f, 0, k <> bnd}))
        case C.TApp{f, x, s}:
          show.go(p, fl, ex.job(C.tm.unapp(C.TApp{f, x, s}), prc, bnd))
        case C.TAdt{+k, +xs, +rs, s}:
          +r = adt.rs(fl, rs)
          paren(Bool.and(Bool.not(String.is_empty(r)), U32.is_gt(prc, 2)), name.show(fl, k) ++ Bool.pick(String, Bool.and(List.is_empty(&2, C.Tm, xs), String.is_empty(r)), "", "<" ++ show.go(p, fl, SjL{xs, 1, ", ", bnd}) ++ ">") ++ r)
        case C.TCtr{k, xs, s}:
          show.go(p, fl, SjCs{cs.of(k, xs, fl), prc, bnd})
        case C.TNat{v, s}:
          U32.show(v) ++ "n"
        case C.TU32{v, s}:
          U32.show(v)
        case C.TF32{v, s}:
          T.str(N.f32.show(v))
        case C.TStr{v, s}:
          "\"" ++ lit.text(v) ++ "\""
        case C.TMat{k, h, m, s}:
          "\\{" ++ show.go(p, fl, mat.job(mat.arms(C.TMat{k, h, m, s}, Nil{}), bnd)) ++ "}"
        case C.TEfq{s}:
          "\\{}"
        case C.TEql{a, b, A, s}:
          "{" ++ show.go(p, fl, SjT{a, 2, bnd}) ++ " == " ++ show.go(p, fl, SjT{b, 2, bnd}) ++ " : " ++ show.go(p, fl, SjT{A, 2, bnd}) ++ "}"
        case C.TRfl{s}:
          "{==}"
        case C.TRwt{e, +m, f, s}:
          show.go(p, fl, SjRw{rw.of(strip(m)), e, m, f, prc, bnd})
        case C.THol{k, s}:
          "?" ++ k
        case C.TAnn{x, A, s}:
          "{" ++ show.go(p, fl, SjT{x, 2, bnd}) ++ " : " ++ show.go(p, fl, SjT{A, 2, bnd}) ++ "}"

# term_show(t, top, bnd, file): top is bend.ts's top + 1
def term.show(+fl: Fl, t: C.Tm, top: U32, bnd: List<&2, String>) -> String:
  show.go(4294967295n, fl, SjT{t, top, bnd})

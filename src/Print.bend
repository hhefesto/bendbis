import Base
import ./Core.bend as C
import ./Text.bend as T
import ./Num.bend as N
import ./Show.bend as S

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Print: a normalized term (the parser's output, after term_lower) as Bend
# source that parses back to it: every compound form in parentheses or its
# own brackets, constructors and calls in plain syntax (no sugar that reads
# back as another tree: 3n stays Succ{Succ{Succ{Zero{}}}} when it is one),
# every binder named by its depth (__v12), so no name shadows another. bend.ts
# has no such printer (term_show's sugars and its x^i do not read back); the
# milestone 1 gate prints each declaration's terms with it and parses them
# again. A datatype with no arguments (a constructor type's tip, D<> in a
# do block) has no source of its own: it prints as its name, which reads
# back as a reference to it, and the gate takes the two as one. An
# unprintable node (a Sub) prints as `<bendbis: ...>`, which no parse
# accepts.

# the name a binder at level i prints as
def var.name(+i: U32) -> String:
  "__v" ++ U32.show(i)

# a rewrite's motive binds `_` and its equation's name, read back by name
type Nm is Data:
  Nm{i: U32, k: String}

def nm.find.at(z: Bool, k: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match z:
    case True{}:
      Some{k}
    case False{}:
      rest

def nm.find(ns: List<&2, Nm>, +i: U32) -> Maybe<&2, String>:
  match ns:
    case Nil{}:
      None{}
    case Con{Nm{+j, k}, t}:
      nm.find.at(U32.is_eq(i, j), k, nm.find(t, i))

def q.mark(q: C.Q) -> String:
  match q:
    case C.QN{}:
      "-"
    case C.QL{}:
      ""
    case C.QM{}:
      "+"

def typ.word(g: C.Tm) -> Maybe<&2, String>:
  match g:
    case C.TQua{C.QL{}, s}:
      Some{"Type"}
    case C.TQua{C.QM{}, s}:
      Some{"Data"}
    case _:
      None{}

def qua.word(q: C.Q) -> String:
  match q:
    case C.QN{}:
      "&0"
    case C.QL{}:
      "&1"
    case C.QM{}:
      "&2"

# a let's binders: all erased (`-a b`), or each `+a` or `a`
def let.all_none(bs: List<&2, C.Bnd>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{C.Bnd{k, i, C.QN{}, v}, t}:
      let.all_none(t)
    case _:
      False{}

def let.mark(none: Bool, q: C.Q) -> String:
  match none:
    case True{}:
      ""
    case False{}:
      q.mark(q)

def let.name.list(bs: List<&2, C.Bnd>, +none: Bool) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{C.Bnd{k, +i, q, v}, t}:
      (let.mark(none, q) ++ var.name(i)) <> let.name.list(t, none)

def let.binders(+bs: List<&2, C.Bnd>) -> String:
  +none = let.all_none(bs)
  Bool.pick(String, none, "-", "") ++ String.join(let.name.list(bs, none), " ")

def let.vals(bs: List<&2, C.Bnd>) -> List<&2, C.Tm>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{C.Bnd{k, i, q, v}, t}:
      v <> let.vals(t)

# The printer: a work list of jobs, its output the pieces in reverse
# ---------------------------------------------------------------

type PJ is Data:
  PjT{t: C.Tm}
  PjS{s: String}
  PjArgs{ts: List<&2, C.Tm>}
  PjVals{ts: List<&2, C.Tm>}
  PjArms{t: C.Tm}
  PjNames{ns: List<&2, Nm>}
  PjPop{}

# the job list and the motive names in scope (a stack, PjNames and PjPop)
type Pw is Data:
  Pw{js: List<&2, PJ>, ns: List<&2, List<&2, Nm>>, out: List<&2, String>}

def ns.top(ns: List<&2, List<&2, Nm>>) -> List<&2, Nm>:
  match ns:
    case Con{h, t}:
      h
    case Nil{}:
      Nil{}

def ns.tail(ns: List<&2, List<&2, Nm>>) -> List<&2, List<&2, Nm>>:
  match ns:
    case Con{h, t}:
      t
    case Nil{}:
      Nil{}

# an application's head and arguments
def spine(t: C.Tm, xs: List<&2, C.Tm>) -> C.Tm & List<&2, C.Tm>:
  match t:
    case C.TApp{f, x, s}:
      spine(f, x <> xs)
    case t:
      (t, xs)

# Base's dotted name k cannot be spelled in a file with an alias named as
# its first word (the alias shadows it: "an unambiguous name"); the sugars
# that call it by Base's name still can, so those print as the sugar
def al2.has(al: List<&2, S.Al2>, +a: String) -> Bool:
  match al:
    case Nil{}:
      False{}
    case Con{S.Al2{x, n}, t}:
      Bool.or(String.eq(x, a), al2.has(t, a))

def shadowed(fl: S.Fl, +k: String) -> Bool:
  match fl:
    case S.NoFl{}:
      False{}
    case S.Fl{ns, al}:
      Bool.and(Bool.and(C.str.has_dot(k), Bool.not(S.colon.has(k))), al2.has(al, C.str.before_dot(k)))

def is.u32.ref(t: C.Tm) -> Bool:
  match t:
    case C.TRef{k, s, False{}}:
      String.eq(k, "U32")
    case _:
      False{}

def sugar.if(z: Bool, js: List<&2, PJ>) -> Maybe<&2, List<&2, PJ>>:
  match z:
    case True{}:
      Some{js}
    case False{}:
      None{}

def sugar.op(+k: String) -> String:
  Bool.pick(String, String.eq(k, "String.append"), "++",
    Bool.pick(String, String.eq(k, "Bool.and"), "&&", Bool.pick(String, String.eq(k, "Bool.or"), "||", "")))

def sugar.at(+k: String, xs: List<&2, C.Tm>, rest: List<&2, PJ>) -> Maybe<&2, List<&2, PJ>>:
  match xs:
    case Con{+T, Con{a, Con{i, Con{v, Nil{}}}}}:
      sugar.if(Bool.and(String.eq(k, "Array.set"), is.u32.ref(T)), PjS{"(("} <> PjT{a} <> PjS{")[("} <> PjT{i} <> PjS{")] <- ("} <> PjT{v} <> PjS{"))"} <> rest)
    case Con{+T, Con{a, Con{i, Nil{}}}}:
      sugar.if(Bool.and(String.eq(k, "Array.get"), is.u32.ref(T)), PjS{"(("} <> PjT{a} <> PjS{")[("} <> PjT{i} <> PjS{")])"} <> rest)
    case Con{C.TNat{+n, s}, Con{t, Nil{}}}:
      sugar.if(Bool.and(String.eq(k, "Nat.add"), U32.is_gt(n, 256)), PjS{"(" ++ U32.show(n) ++ "n+("} <> PjT{t} <> PjS{"))"} <> rest)
    case Con{a, Con{b, Nil{}}}:
      sugar.if(Bool.not(String.is_empty(sugar.op(k))), PjS{"(("} <> PjT{a} <> PjS{") " ++ sugar.op(k) ++ " ("} <> PjT{b} <> PjS{"))"} <> rest)
    case _:
      None{}

def spine.plain(h: C.Tm, xs: List<&2, C.Tm>, +fl: S.Fl, rest: List<&2, PJ>) -> List<&2, PJ>:
  match h:
    case C.TRef{k, s, True{}}:
      PjS{S.name.show(fl, k) ++ "!("} <> PjArgs{xs} <> PjS{")"} <> rest
    case h:
      PjT{h} <> PjS{"("} <> PjArgs{xs} <> PjS{")"} <> rest

def spine.sugar(m: Maybe<&2, List<&2, PJ>>, h: C.Tm, xs: List<&2, C.Tm>, +fl: S.Fl, rest: List<&2, PJ>) -> List<&2, PJ>:
  match m:
    case Some{js}:
      js
    case None{}:
      spine.plain(h, xs, fl, rest)

def spine.jobs(hx: C.Tm & List<&2, C.Tm>, +fl: S.Fl, +rest: List<&2, PJ>) -> List<&2, PJ>:
  (h, +xs) = hx
  match h:
    case C.TRef{+k, s, False{}}:
      spine.sugar(Bool.pick(Maybe<&2, List<&2, PJ>>, shadowed(fl, k), sugar.at(k, xs, rest), None{}), C.TRef{k, s, False{}}, xs, fl, rest)
    case h:
      spine.plain(h, xs, fl, rest)

def arms.jobs(t: C.Tm, +fl: S.Fl, rest: List<&2, PJ>) -> List<&2, PJ>:
  match t:
    case C.TMat{k, h, m, s}:
      PjS{S.name.show(fl, k) ++ ": "} <> PjT{h} <> PjS{"; "} <> PjArms{m} <> rest
    case C.TEfq{s}:
      rest
    case t:
      PjT{t} <> rest

def rwt.jobs(e: C.Tm, p: C.Tm, f: C.Tm, rest: List<&2, PJ>) -> List<&2, PJ>:
  match p:
    case C.TLam{a, +xi, C.TLam{+k, +ei, P, s2, q2}, s1, q1}:
      PjS{"(%" ++ Bool.pick(String, String.is_empty(k), "", k ++ "@")} <> PjT{e} <> PjS{" : "}
        <> PjNames{[Nm{xi, "_"}, Nm{ei, k}]} <> PjT{P} <> PjPop{} <> PjS{"; "} <> PjT{f} <> PjS{")"} <> rest
    case p:
      PjS{"(<bendbis: a rewrite motive not of the form _ => e => P>"} <> rest

def typ.jobs(w: Maybe<&2, String>, g: C.Tm, rest: List<&2, PJ>) -> List<&2, PJ> & String:
  match w:
    case Some{w}:
      (rest, w)
    case None{}:
      (PjT{g} <> PjS{")"} <> rest, "Kind(")

def pr.term(t: C.Tm, +fl: S.Fl, +ns: List<&2, Nm>, rest: List<&2, PJ>) -> List<&2, PJ> & String:
  match t:
    case C.TVar{k, +i, s}:
      (rest, Bool.pick(String, U32.is_eq(i, C.MINUS()), "+" ++ k, Maybe.default(&2, String, nm.find(ns, i), var.name(i))))
    case C.TVr{k, i, s, r}:
      (rest, S.name.show(fl, r))
    case C.TRef{k, s, b}:
      (rest, S.name.show(fl, k) ++ Bool.pick(String, b, "!()", ""))
    case C.TSub{i, v, f, s}:
      (rest, "<bendbis: a Sub>")
    case C.TLet{+bs, f, s}:
      (PjVals{let.vals(bs)} <> PjS{"; "} <> PjT{f} <> PjS{")"} <> rest, "(" ++ let.binders(bs) ++ " =")
    case C.TTyp{+g, s}:
      typ.jobs(typ.word(g), g, rest)
    case C.TQnt{s}:
      (rest, "Quant")
    case C.TQua{q, s}:
      (rest, qua.word(q))
    case C.TMin{a, b, s}:
      (PjT{a} <> PjS{" <&> "} <> PjT{b} <> PjS{")"} <> rest, "(")
    case C.TAll{q, k, +i, A, B, s}:
      (PjT{A} <> PjS{" -> "} <> PjT{B} <> PjS{")"} <> rest, "(@" ++ q.mark(q) ++ var.name(i) ++ ":")
    case C.TLam{k, +i, f, s, q}:
      (PjT{f} <> PjS{")"} <> rest, "(" ++ q.mark(q) ++ var.name(i) ++ " => ")
    case C.TApp{f, x, s}:
      (spine.jobs(spine(f, [x]), fl, rest), "")
    case C.TAdt{k, xs, r, s}:
      match xs:
        case Nil{}:
          (rest, S.name.show(fl, k))
        case xs:
          (PjArgs{xs} <> PjS{">"} <> rest, S.name.show(fl, k) ++ "<")
    case C.TCtr{k, xs, s}:
      (PjArgs{xs} <> PjS{"}"} <> rest, S.name.show(fl, k) ++ "{")
    case C.TNat{v, s}:
      (rest, U32.show(v) ++ "n")
    case C.TU32{v, s}:
      (rest, U32.show(v))
    case C.TF32{v, s}:
      (rest, T.str(N.f32.show(v)))
    case C.TStr{v, s}:
      (rest, "\"" ++ S.lit.text(v) ++ "\"")
    case C.TMat{k, h, m, s}:
      (arms.jobs(C.TMat{k, h, m, s}, fl, PjS{"}"} <> rest), "\\{")
    case C.TEfq{s}:
      (rest, "\\{}")
    case C.TEql{a, b, A, s}:
      (PjT{a} <> PjS{" == "} <> PjT{b} <> PjS{" : "} <> PjT{A} <> PjS{"}"} <> rest, "{")
    case C.TRfl{s}:
      (rest, "{==}")
    case C.TRwt{e, p, f, s}:
      (rwt.jobs(e, p, f, rest), "")
    case C.THol{k, s}:
      (rest, "?" ++ k)
    case C.TAnn{x, A, s}:
      (PjT{x} <> PjS{" : "} <> PjT{A} <> PjS{"}"} <> rest, "{")

def pr.step(r: List<&2, PJ> & String, ns: List<&2, List<&2, Nm>>, out: List<&2, String>) -> Pw:
  (js, s) = r
  Pw{js, ns, s <> out}

def pr.go(fuel: Nat, +fl: S.Fl, w: Pw) -> List<&2, String>:
  match fuel w:
    case 0n Pw{js, ns, out}:
      "<bendbis: the printer ran out of fuel>" <> out
    case 1n+f Pw{Nil{}, ns, out}:
      out
    case 1n+f Pw{Con{j, js}, +ns, out}:
      match j:
        case PjS{s}:
          pr.go(f, fl, Pw{js, ns, s <> out})
        case PjT{t}:
          pr.go(f, fl, pr.step(pr.term(t, fl, ns.top(ns), js), ns, out))
        case PjArgs{Nil{}}:
          pr.go(f, fl, Pw{js, ns, out})
        case PjArgs{Con{x, Nil{}}}:
          pr.go(f, fl, Pw{PjT{x} <> js, ns, out})
        case PjArgs{Con{x, xs}}:
          pr.go(f, fl, Pw{PjT{x} <> PjS{", "} <> PjArgs{xs} <> js, ns, out})
        case PjVals{Nil{}}:
          pr.go(f, fl, Pw{js, ns, out})
        case PjVals{Con{x, xs}}:
          pr.go(f, fl, Pw{PjS{"\n("} <> PjT{x} <> PjS{")"} <> PjVals{xs} <> js, ns, out})
        case PjArms{t}:
          pr.go(f, fl, Pw{arms.jobs(t, fl, js), ns, out})
        case PjNames{xs}:
          pr.go(f, fl, Pw{js, List.append(&2, Nm, xs, ns.top(ns)) <> ns, out})
        case PjPop{}:
          pr.go(f, fl, Pw{js, ns.tail(ns), out})

# a term's source
def print.term(fl: S.Fl, t: C.Tm) -> String:
  String.concat(List.reverse(&2, String, pr.go(4294967295n, fl, Pw{[PjT{t}], Nil{}, Nil{}})))

import Base
import ./Text.bend as T
import ./Core.bend as C

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Err: bend.ts's err_show and err_lost_type for an error with no context
# (every error the parser throws): the message or expected and observed,
# the location (the lines around the span, a caret under it, in UTF-16
# units as JavaScript counts them), and the notes.

# s.split("\n") of units
def lines.go(xs: List<&2, U32>, cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      List.reverse(&2, List<&2, U32>, List.reverse(&2, U32, cur) <> acc)
    case Con{10, t}:
      lines.go(t, Nil{}, List.reverse(&2, U32, cur) <> acc)
    case Con{c, t}:
      lines.go(t, c <> cur, acc)

def Err.lines(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  lines.go(xs, Nil{}, Nil{})

def pad.left(+s: String, +n: Nat) -> String:
  String.repeat(" ", Nat.sub(n, String.length(s))) ++ s

# lft.replace(/[^\t]/g, " ")
def blank.go(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{9, t}:
      9 <> blank.go(t)
    case Con{c, t}:
      32 <> blank.go(t)

def last.of(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, Nil{}}:
      x
    case Con{x, t}:
      last.of(t)

# the shown lines bg..end, the one at `at` with its caret line
def show.lines(ls: List<&2, List<&2, U32>>, +n: U32, +bg: U32, +end: U32, +at: U32, +num: Nat, +car: String) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{+l, t}:
      Bool.pick(String, Bool.or(U32.is_lt(n, bg), U32.is_gt(n, end)), "",
        "\n" ++ pad.left(U32.show(n), num) ++ Bool.pick(String, U32.is_eq(n, at), ">| " ++ T.str(l) ++ "\n" ++ car, " | " ++ T.str(l)))
      ++ Bool.pick(String, U32.is_lt(n, end), show.lines(t, (n + 1 : U32), bg, end, at, num, car), "")

def span.show(+txt: List<&2, U32>, +beg: U32, +end: U32) -> String:
  +lns = Err.lines(txt)
  +pre = Err.lines(T.take(txt, U32.to_nat(beg)))
  +at = U32.from_nat(List.length(&2, List<&2, U32>, pre))
  +nl = U32.from_nat(List.length(&2, List<&2, U32>, lns))
  +bg = U32.max(1, (at - 1 : U32))
  +last = U32.min(nl, (at + 1 : U32))
  +num = String.length(U32.show(last))
  +lft = last.of(pre)
  +line = Maybe.default(&2, List<&2, U32>, List.get(&2, List<&2, U32>, lns, U32.to_nat((at - 1 : U32))), Nil{})
  +w = U32.max(1, U32.min(Bool.pick(U32, U32.is_lt(end, beg), 0, (end - beg : U32)), (U32.from_nat(T.len(line)) - U32.from_nat(T.len(lft)) : U32)))
  +car = String.repeat(" ", num) ++ " | " ++ T.str(blank.go(lft)) ++ String.repeat("^", U32.to_nat(w))
  show.lines(lns, 1, bg, last, at, num, car)

# err_lost_type: a do-block statement whose binder lost its type
def lost.op(xs: List<&2, U32>) -> Nat:
  match xs:
    case Con{32, t}:
      lost.op(t)
    case Con{9, t}:
      lost.op(t)
    case Con{60, Con{45, t}}:
      1n
    case Con{61, Con{61, t}}:
      0n
    case Con{61, t}:
      2n
    case _:
      0n

def all.blank(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{32, t}:
      all.blank(t)
    case Con{9, t}:
      all.blank(t)
    case _:
      False{}

def name.tail(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Bool.and(T.is_name(c), name.tail(t))

def is.ident(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{+c, t}:
      Bool.and(T.is_head(c), name.tail(t))
    case Nil{}:
      False{}

# the start of beg's line (str.lastIndexOf("\n", beg - 1) + 1)
def line.start.go(xs: List<&2, U32>, +n: U32, +beg: U32, +last: U32) -> U32:
  match xs:
    case Nil{}:
      last
    case Con{10, t}:
      Bool.pick(U32, U32.is_lt(n, beg), line.start.go(t, (n + 1 : U32), beg, (n + 1 : U32)), last)
    case Con{c, t}:
      Bool.pick(U32, U32.is_lt(n, beg), line.start.go(t, (n + 1 : U32), beg, last), last)

def lost.note(+exp: String, +txt: List<&2, U32>, +beg: U32, +end: U32) -> Maybe<&2, String>:
  +k = T.slice(txt, beg, end)
  +at = T.slice(txt, line.start.go(txt, 0, beg, 0), beg)
  +op = lost.op(T.drop(txt, U32.to_nat(end)))
  +ks = T.str(k)
  Bool.pick(Maybe<&2, String>, Bool.or(Bool.or(Nat.is_eq(op, 0n), Bool.not(all.blank(at))), Bool.not(is.ident(k))), None{},
    Bool.pick(Maybe<&2, String>, Bool.and(Nat.is_eq(op, 1n), String.eq(exp, "a defined name")),
      Some{"Note: in a do-block, " ++ ks ++ " <- m runs m at type " ++ ks ++ "; to bind its result, write " ++ ks ++ " : A <- m."},
    Bool.pick(Maybe<&2, String>, Bool.and(Nat.is_eq(op, 2n), String.eq(exp, "a pattern (a binder or a constructor)")),
      Some{"Note: in a do-block, a let names its type: " ++ ks ++ " : A = v."}, None{})))

def note.line(m: Maybe<&2, String>) -> String:
  match m:
    case Some{s}:
      "\n" ++ s
    case None{}:
      ""

def msg.show(+exp: String, obs: Maybe<&2, String>) -> String:
  match obs:
    case None{}:
      "\n- message  : " ++ exp
    case Some{o}:
      "\n- expected : " ++ exp ++ "\n- observed : " ++ o

# err_show, for an error with no context and no def
def Err.show(e: C.Er) -> String:
  match e:
    case C.ErRaw{m}:
      m
    case C.Er{+exp, obs, C.NoSp{}, txt, nte}:
      "Error:" ++ msg.show(exp, obs) ++ note.line(nte)
    case C.Er{+exp, obs, C.Sp{f, +beg, +end}, +txt, nte}:
      "Error:" ++ msg.show(exp, obs) ++ "\nLocation:" ++ span.show(txt, beg, end) ++ note.line(nte) ++ note.line(lost.note(exp, txt, beg, end))

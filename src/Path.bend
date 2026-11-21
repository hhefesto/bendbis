import Base
import ./Text.bend as T

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Path: what bend.ts's loader asks of node's path.posix (normalize,
# resolve, relative), and its import path rule (book_load's `ok`). A path
# is a String. fs.realpathSync is taken as resolve: bendbis follows no
# symbolic link (DESIGN.md).

def seg.split(xs: List<&2, U32>, cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      List.reverse(&2, List<&2, U32>, List.reverse(&2, U32, cur) <> acc)
    case Con{47, t}:
      seg.split(t, Nil{}, List.reverse(&2, U32, cur) <> acc)
    case Con{c, t}:
      seg.split(t, c <> cur, acc)

def segs(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  seg.split(xs, Nil{}, Nil{})

def is.dot(s: List<&2, U32>) -> Bool:
  match s:
    case Con{46, Nil{}}:
      True{}
    case _:
      False{}

def is.dotdot(s: List<&2, U32>) -> Bool:
  match s:
    case Con{46, Con{46, Nil{}}}:
      True{}
    case _:
      False{}

def is.empty(s: List<&2, U32>) -> Bool:
  List.is_empty(&2, U32, s)

# the kept segments, reversed: ".." pops a plain one, stays at the front
# of a relative path, and drops at an absolute one's root
def norm.up(abs: Bool, s: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match acc:
    case Nil{}:
      Bool.pick(List<&2, List<&2, U32>>, abs, Nil{}, [s])
    case Con{+h, +t}:
      Bool.pick(List<&2, List<&2, U32>>, is.dotdot(h), s <> h <> t, t)

def norm.step(skip: Bool, up: Bool, abs: Bool, s: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match skip up:
    case True{} _:
      acc
    case False{} False{}:
      s <> acc
    case False{} True{}:
      norm.up(abs, s, acc)

def norm.go(ss: List<&2, List<&2, U32>>, +abs: Bool, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ss:
    case Nil{}:
      acc
    case Con{+s, t}:
      norm.go(t, abs, norm.step(Bool.or(is.empty(s), is.dot(s)), is.dotdot(s), abs, s, acc))

def join.go(ss: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, Nil{}}:
      s
    case Con{s, t}:
      List.append(&2, U32, s, 47 <> join.go(t))

def p.join(ss: List<&2, List<&2, U32>>) -> List<&2, U32>:
  join.go(ss)

def ends.slash.rev(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{47, t}:
      True{}
    case _:
      False{}

def ends.slash(xs: List<&2, U32>) -> Bool:
  ends.slash.rev(List.reverse(&2, U32, xs))

def starts.slash(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{47, t}:
      True{}
    case _:
      False{}

# the normal segments of a path
def norm.segs(+xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  List.reverse(&2, List<&2, U32>, norm.go(segs(xs), starts.slash(xs), Nil{}))

def norm.text(+abs: Bool, +ss: List<&2, List<&2, U32>>, +trail: Bool) -> List<&2, U32>:
  +body = join.go(ss)
  Bool.pick(List<&2, U32>, List.is_empty(&2, List<&2, U32>, ss), Bool.pick(List<&2, U32>, abs, [47], [46]),
    List.append(&2, U32, Bool.pick(List<&2, U32>, abs, 47 <> body, body), Bool.pick(List<&2, U32>, trail, [47], Nil{})))

# path.posix.normalize
def p.normalize(+p: String) -> String:
  +xs = T.cps.of(p)
  T.str.cps(Bool.pick(List<&2, U32>, List.is_empty(&2, U32, xs), [46], norm.text(starts.slash(xs), norm.segs(xs), ends.slash(xs))))

# path.posix.resolve(dir, rel), dir absolute: no trailing slash
def p.resolve(dir: String, +rel: String) -> String:
  +xs = T.cps.of(rel)
  +full = Bool.pick(List<&2, U32>, starts.slash(xs), xs, List.append(&2, U32, T.cps.of(dir), 47 <> xs))
  T.str.cps(norm.text(True{}, norm.segs(full), False{}))

def common.drop(a: List<&2, List<&2, U32>>, b: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>> & List<&2, List<&2, U32>>:
  match a b:
    case Con{+x, +s} Con{+y, +t}:
      Bool.pick(List<&2, List<&2, U32>> & List<&2, List<&2, U32>>, T.eq(x, y), common.drop(s, t), (x <> s, y <> t))
    case a b:
      (a, b)

def rel.of(ab: List<&2, List<&2, U32>> & List<&2, List<&2, U32>>) -> List<&2, U32>:
  (a, b) = ab
  join.go(List.append(&2, List<&2, U32>, List.replicate(List<&2, U32>, List.length(&2, List<&2, U32>, a), [46, 46]), b))

# path.posix.relative(from, to), both absolute
def p.relative(from: String, to: String) -> String:
  T.str.cps(rel.of(common.drop(norm.segs(T.cps.of(from)), norm.segs(T.cps.of(to)))))

# a path's directory with its slash (real.slice(0, real.lastIndexOf("/") + 1))
def dir.go(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{47, t}:
      47 <> t
    case Con{c, t}:
      dir.go(t)

def p.dir(p: String) -> String:
  T.str.cps(List.reverse(&2, U32, dir.go(List.reverse(&2, U32, T.cps.of(p)))))

def base.go(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{47, t}:
      Nil{}
    case Con{c, t}:
      c <> base.go(t)

def p.base(p: String) -> String:
  T.str.cps(List.reverse(&2, U32, base.go(List.reverse(&2, U32, T.cps.of(p)))))

# [A-Za-z_][\w-]*
def plain.tail(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Bool.and(Bool.or(T.is_word(c), U32.is_eq(c, 45)), plain.tail(t))

def plain(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{+c, t}:
      Bool.and(T.is_head(c), plain.tail(t))
    case Nil{}:
      False{}

def all.plain(ss: List<&2, List<&2, U32>>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      Bool.and(plain(s), all.plain(t))

# ^(\/|(\.\.\/)*)([A-Za-z_][\w-]*\/)*[A-Za-z_][\w-]*$ on the segments
def ok.ups(ss: List<&2, List<&2, U32>>) -> Bool:
  match ss:
    case Con{Con{46, Con{46, Nil{}}}, t}:
      ok.ups(t)
    case +ss:
      Bool.and(Bool.not(List.is_empty(&2, List<&2, U32>, ss)), all.plain(ss))

def ok.segs(ss: List<&2, List<&2, U32>>) -> Bool:
  match ss:
    case Con{Nil{}, +t}:
      Bool.and(Bool.not(List.is_empty(&2, List<&2, U32>, t)), all.plain(t))
    case +ss:
      ok.ups(ss)

def p.ok_rel(s: String) -> Bool:
  ok.segs(segs(T.cps.of(s)))

def hub.hex(xs: List<&2, U32>, any: Bool) -> Bool:
  match xs:
    case Con{47, t}:
      any
    case Con{+c, t}:
      Bool.and(Bool.or(T.is_digit(c), Bool.and(U32.is_le(97, c), U32.is_le(c, 102))), hub.hex(t, True{}))
    case Nil{}:
      False{}

def hub.go(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{48, Con{120, t}}:
      hub.hex(t, False{})
    case _:
      False{}

# /^0x[0-9a-f]+\//
def p.is_hub(s: String) -> Bool:
  hub.go(T.cps.of(s))

# ok(s, lib): hub(s) === lib and the plain-names rule on s less its hub
# prefix (no hub path is read here, so lib is false)
def p.ok(+s: String) -> Bool:
  Bool.and(Bool.not(p.is_hub(s)), p.ok_rel(s))

def ends.bend.rev(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{100, Con{110, Con{101, Con{98, Con{46, t}}}}}:
      True{}
    case _:
      False{}

def ends.bend(xs: List<&2, U32>) -> Bool:
  ends.bend.rev(List.reverse(&2, U32, xs))

def p.ends_bend(s: String) -> Bool:
  ends.bend(T.cps.of(s))

# s without ".bend" at its end
def p.unbend(+s: String) -> String:
  +xs = T.cps.of(s)
  Bool.pick(String, ends.bend(xs), T.str.cps(List.take(&2, U32, xs, Nat.sub(List.length(&2, U32, xs), 5n))), s)

# as.replace(/^\.\//, "").slice(0, -5)
def stem.dot(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{46, Con{47, t}}:
      t
    case xs:
      xs

def stem.go(+xs: List<&2, U32>) -> String:
  +ys = stem.dot(xs)
  T.str.cps(List.take(&2, U32, ys, Nat.sub(List.length(&2, U32, ys), 5n)))

def p.import_stem(s: String) -> String:
  +xs = T.cps.of(s)
  stem.go(xs)

def p.starts(s: String, p: String) -> Bool:
  T.prefix(T.cps.of(s), T.cps.of(p))

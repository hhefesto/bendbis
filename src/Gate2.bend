import Base
import ./Core.bend as C
import ./Text.bend as T
import ./Lex.bend as L
import ./Path.bend as Pa
import ./Err.bend as E
import ./Load.bend as Ld
import ./Gate.bend as G
import ./Check.bend as K
import ./Valid.bend as V

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Gate2: `bendbis FILE --check-only`, and milestone 2's gate: for each file,
# bendbis's output (its text, stdout or stderr, and its exit code) against
# upstream's saved beside (UP/<the file's path, / as _>.out, stdout and
# stderr together, and .t, its exit code), byte for byte.

# Base, read and checked once a process
type Pb is Data:
  PbOk{bk: L.Bk, bc: V.Bc}
  PbErr{msg: String}

def base.prep.got(r: V.Br, bk: L.Bk) -> Pb:
  match r:
    case V.BrOk{bc}:
      PbOk{bk, bc}
    case V.BrErr{e, fs}:
      PbErr{"bendbis: Base did not check:\n" ++ V.ek.show(fs, e)}

def base.prep(r: Ld.LR, +bp: String) -> Pb:
  match r:
    case Ld.LOk{+ld}:
      base.prep.got(V.base.check(Ld.ld.files(ld), bp), Ld.ld.bk(ld))
    case Ld.LErr{e}:
      PbErr{"bendbis: Base did not parse:\n" ++ E.Err.show(e)}

def proof.fin(z: Bool, +ld: Ld.Ld, +bp: String, +bc: V.Bc) -> V.Out:
  match z:
    case True{}:
      V.out.fail("Error: PROOF.bend must import ./LAWS.bend")
    case False{}:
      V.check.ld(ld, bp, bc)

# main.ts's book_read: a PROOF.bend beside a LAWS.bend imports it
def proof.at(z: Bool, +ld: Ld.Ld, +real: String, +bp: String, +bc: V.Bc) -> IO(V.Out):
  match z:
    case False{}:
      IO.pure(V.Out, V.check.ld(ld, bp, bc))
    case True{}:
      +laws = Pa.p.dir(real) ++ "LAWS.bend"
      do IO<V.Out>:
        mb : Maybe<&2, List<&2, U32>> <- Ld.slurp(laws)
        return proof.fin(Bool.and(Maybe.is_some(&2, List<&2, U32>, mb), Nat.is_eq(Ld.ld.seen(laws, ld), 0n)), ld, bp, bc)

def check.got(r: Ld.LR, +real: String, +bp: String, +bc: V.Bc) -> IO(V.Out):
  match r:
    case Ld.LErr{e}:
      IO.pure(V.Out, V.out.fail(E.Err.show(e)))
    case Ld.LOk{ld}:
      proof.at(String.eq(Pa.p.base(real), "PROOF.bend"), ld, real, bp, bc)

# `bend f --check-only`, f at real
def check.entry(+f: String, +real: String, +bp: String, base: L.Bk, +lib: String, +bc: V.Bc) -> IO(V.Out):
  do IO<V.Out>:
    r : Ld.LR <- Ld.load.entry(f, real, Ld.ld.entry(bp, base, lib))
    check.got(r, real, bp, bc)

# s less its last "\n" (IO.print_err adds one)
def chomp.rev(s: String) -> String:
  match s:
    case SCon{Chr{10}, t}:
      t
    case s:
      s

def chomp(s: String) -> String:
  String.reverse(chomp.rev(String.reverse(s)))

def out.say(o: V.Out) -> IO(Unit):
  match o:
    case V.Out{txt, True{}, +rc}:
      do IO<Unit>:
        IO.print_err(chomp(txt))
        IO.exit(rc)
    case V.Out{txt, False{}, +rc}:
      do IO<Unit>:
        IO.write(txt)
        IO.exit(rc)

def check.main.at(p: Pb, +f: String, +real: String, +bp: String, +lib: String) -> IO(Unit):
  match p:
    case PbErr{m}:
      IO.die(Unit, 2, m)
    case PbOk{bk, bc}:
      do IO<Unit>:
        o : V.Out <- check.entry(f, real, bp, bk, lib, bc)
        out.say(o)

def is.need(r: Ld.LR) -> Bool:
  match r:
    case Ld.LErr{C.ErRaw{m}}:
      String.eq(m, Ld.NEED_BASE())
    case _:
      False{}

def check.main.r(z: Bool, r: Ld.LR, +f: String, +real: String, +bp: String, +lib: String) -> IO(Unit):
  match z:
    case True{}:
      do IO<Unit>:
        br : Ld.LR <- Ld.base.load(bp, lib)
        check.main.at(base.prep(br, bp), f, real, bp, lib)
    case False{}:
      do IO<Unit>:
        o : V.Out <- check.got(r, real, bp, V.bc.nil())
        out.say(o)

# bendbis FILE --check-only: the entry read first with no Base, Base read
# and checked only when a file imports it
def check.main(+f: String, +cwd: String, +bp: String, +lib: String) -> IO(Unit):
  +real = Pa.p.resolve(cwd, f)
  do IO<Unit>:
    +r : Ld.LR <- Ld.load.entry(f, real, Ld.ld.entry("", L.bk.nil(), lib))
    check.main.r(is.need(r), r, f, real, bp, lib)

# The gate
# --------

# a .t line's exit code: "file\trc\tms"
def rc.go(xs: List<&2, U32>, on: Bool, +n: U32) -> U32:
  match xs on:
    case Nil{} _:
      n
    case Con{9, t} False{}:
      rc.go(t, True{}, n)
    case Con{9, t} True{}:
      n
    case Con{+c, t} True{}:
      rc.go(t, True{}, ((n * 10 : U32) + (c - 48 : U32) : U32))
    case Con{c, t} False{}:
      rc.go(t, False{}, n)

def rc.of(m: Maybe<&2, List<&2, U32>>) -> U32:
  match m:
    case None{}:
      C.NONE()
    case Some{xs}:
      rc.go(xs, False{}, 0)

def u32s.eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{+a, s} Con{+b, t}:
      Bool.and(U32.is_eq(a, b), u32s.eq(s, t))
    case _ _:
      False{}

type Gc is Data:
  Gc{same: U32, diff: U32, noup: U32}

def gc.add(n: Nat, c: Gc) -> Gc:
  match n c:
    case 0n Gc{s, d, u}:
      Gc{(s + 1 : U32), d, u}
    case 1n Gc{s, d, u}:
      Gc{s, (d + 1 : U32), u}
    case _ Gc{s, d, u}:
      Gc{s, d, (u + 1 : U32)}

def out.txt(o: V.Out) -> String:
  match o:
    case V.Out{txt, e, rc}:
      txt

def out.rc(o: V.Out) -> U32:
  match o:
    case V.Out{txt, e, rc}:
      rc

def gate.cmp(+o: V.Out, u: Maybe<&2, List<&2, U32>>, +rc: U32) -> Nat:
  match u:
    case None{}:
      2n
    case Some{ub}:
      Bool.pick(Nat, Bool.and(u32s.eq(T.utf8(out.txt(o)), ub), U32.is_eq(out.rc(o), rc)), 0n, 1n)

def gate.say(n: Nat, +f: String, +out: String, +o: V.Out, +ms: Nat) -> IO(Unit):
  match n:
    case 0n:
      IO.print("same\t" ++ f ++ "\t" ++ U32.show(U32.from_nat(ms)))
    case 1n:
      do IO<Unit>:
        G.put.text(out ++ "/" ++ G.mangle(f) ++ ".bb", out.txt(o) ++ "[rc " ++ U32.show(out.rc(o)) ++ "]\n")
        IO.print("DIFF\t" ++ f ++ "\t" ++ U32.show(U32.from_nat(ms)))
    case _:
      IO.print("NO-UP\t" ++ f)

def gate.each(fs: List<String>, +cwd: String, +bp: String, +bk: L.Bk, +lib: String, +bc: V.Bc, +up: String, +out: String, c: Gc) -> IO(Gc):
  match fs:
    case Nil{}:
      IO.pure(Gc, c)
    case Con{+f, t}:
      +stem = up ++ "/" ++ G.mangle(f)
      do IO<Gc>:
        +t0 : Nat <- IO.now()
        +o : V.Out <- check.entry(f, Pa.p.resolve(cwd, f), bp, bk, lib, bc)
        +t1 : Nat <- IO.now()
        u : Maybe<&2, List<&2, U32>> <- Ld.slurp(stem ++ ".out")
        ut : Maybe<&2, List<&2, U32>> <- Ld.slurp(stem ++ ".t")
        +n : Nat = gate.cmp(o, u, rc.of(ut))
        gate.say(n, f, out, o, Nat.sub(t1, t0))
        gate.each(t, cwd, bp, bk, lib, bc, up, out, gc.add(n, c))

def gc.show(c: Gc) -> String:
  match c:
    case Gc{s, d, u}:
      "gate2: " ++ U32.show(s) ++ " as upstream, " ++ U32.show(d) ++ " otherwise, " ++ U32.show(u) ++ " with no upstream output"

def gate.at(p: Pb, fs: List<String>, +cwd: String, +bp: String, +lib: String, +up: String, +out: String) -> IO(Unit):
  match p:
    case PbErr{m}:
      IO.die(Unit, 2, m)
    case PbOk{bk, bc}:
      do IO<Unit>:
        c : Gc <- gate.each(fs, cwd, bp, bk, lib, bc, up, out, Gc{0, 0, 0})
        IO.print(gc.show(c))

# bendbis gate2 UP OUT FILE..
def gate.run(fs: List<String>, +cwd: String, +bp: String, +lib: String, +up: String, +out: String) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    br : Ld.LR <- Ld.base.load(bp, lib)
    +p : Pb = base.prep(br, bp)
    +t1 : Nat <- IO.now()
    IO.print("base\t" ++ U32.show(U32.from_nat(Nat.sub(t1, t0))))
    gate.at(p, fs, cwd, bp, lib, up, out)

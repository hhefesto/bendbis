import Base
import ./Text.bend as T
import ./Core.bend as C
import ./Lex.bend as L
import ./Path.bend as Pa
import ./Err.bend as E
import ./Load.bend as Ld
import ./Gate.bend as G
import ./Gate2.bend as G2

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# Main: the command line.
#
#   bendbis FILE --check-only   bend FILE --check-only: upstream's verdict,
#                               its text, stream and exit code
#   bendbis parse FILE..   read each FILE as bend would (its imports, Base
#                          once), print upstream's error or what it read
#   bendbis gate2 UP OUT FILE..   milestone 2's gate (Gate2.bend)
#
# The environment: BENDBIS_BASE, the base.bend to read (default
# $HOME/src/bend2-upstream/bend2/base.bend); BEND_LIB as bend reads it.

def env.or(r: Result<&1, &1, U32 & String, String>, d: String) -> String:
  match r:
    case Done{v}:
      v
    case Fail{e}:
      d

def env(name: String, d: String) -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env(name)
    return env.or(r, d)

type Cfg is Data:
  Cfg{cwd: String, base: String, lib: String}

def cfg() -> IO(Cfg):
  do IO<Cfg>:
    +home : String <- env("HOME", "/")
    +cwd : String <- env("PWD", "/")
    base : String <- env("BENDBIS_BASE", home ++ "/src/bend2-upstream/bend2/base.bend")
    lib : String <- env("BEND_LIB", home ++ "/.bend/lib")
    return Cfg{cwd, Pa.p.resolve(cwd, base), Pa.p.resolve(cwd, lib) ++ "/"}

def fr.count(fs: List<&2, Ld.Fr>, n: U32) -> U32:
  match fs:
    case Nil{}:
      n
    case Con{Ld.Fr{p, ns, al, ds, tx, fi}, t}:
      fr.count(t, (n + U32.from_nat(List.length(&2, C.Dcl, ds)) : U32))

# the term nodes of a file's declarations: types and values
def ds.size(ds: List<&2, C.Dcl>, +n: U32) -> U32:
  match ds:
    case Nil{}:
      n
    case Con{C.DAdt{k, a, g, T, cs}, t}:
      ds.size(t, C.tms.size(4294967295n, [T], n))
    case Con{C.DDef{k, a, x, T, v, u, ffi, l, fl}, t}:
      ds.size(t, C.tms.size(4294967295n, T <> Maybe.default(&2, List<&2, C.Tm>, Maybe.map(&2, C.Tm, List<&2, C.Tm>, x => [x], v), Nil{}), n))

def fr.size(fs: List<&2, Ld.Fr>, +n: U32) -> U32:
  match fs:
    case Nil{}:
      n
    case Con{Ld.Fr{p, ns, al, ds, tx, fi}, t}:
      fr.size(t, ds.size(ds, n))

def show.ok(+file: String, ld: Ld.Ld) -> String:
  +fs = Ld.ld.files(ld)
  "parsed " ++ file ++ ": " ++ U32.show(U32.from_nat(List.length(&2, Ld.Fr, fs))) ++ " files, " ++ U32.show(fr.count(fs, 0)) ++ " declarations, " ++ U32.show(fr.size(fs, 0)) ++ " term nodes"

def report(+file: String, r: Ld.LR) -> IO(U32):
  match r:
    case Ld.LOk{ld}:
      do IO<U32>:
        IO.print(show.ok(file, ld))
        return 0
    case Ld.LErr{e}:
      do IO<U32>:
        IO.print_err("SOME PROOFS FAIL\n" ++ E.Err.show(e))
        return 1

def parse.each(fs: List<String>, +c: Cfg, +base: L.Bk, +rc: U32) -> IO(U32):
  match fs:
    case Nil{}:
      IO.pure(U32, rc)
    case Con{+f, t}:
      match c:
        case Cfg{+cwd, +bp, +lib}:
          do IO<U32>:
            r : Ld.LR <- Ld.load.entry(f, Pa.p.resolve(cwd, f), Ld.ld.entry(bp, base, lib))
            n : U32 <- report(f, r)
            parse.each(t, Cfg{cwd, bp, lib}, base, U32.max(rc, n))

def base.of(r: Ld.LR) -> L.Bk:
  match r:
    case Ld.LOk{ld}:
      Ld.ld.bk(ld)
    case Ld.LErr{e}:
      L.bk.nil()

def base.err(r: Ld.LR) -> Maybe<&2, String>:
  match r:
    case Ld.LOk{ld}:
      None{}
    case Ld.LErr{e}:
      Some{E.Err.show(e)}

def main.parse.go(e: Maybe<&2, String>, fs: List<String>, c: Cfg, base: L.Bk) -> IO(Unit):
  match e:
    case Some{m}:
      IO.die(Unit, 2, "bendbis: Base did not parse:\n" ++ m)
    case None{}:
      do IO<Unit>:
        rc : U32 <- parse.each(fs, c, base, 0)
        IO.exit(rc)

def main.parse(fs: List<String>, c: Cfg) -> IO(Unit):
  match c:
    case Cfg{+cwd, +bp, +lib}:
      do IO<Unit>:
        +br : Ld.LR <- Ld.base.load(bp, lib)
        main.parse.go(base.err(br), fs, Cfg{cwd, bp, lib}, base.of(br))

def USAGE() -> String:
  "usage: bendbis FILE --check-only\n       bendbis parse FILE..\n       bendbis gate2 UPDIR OUTDIR FILE..\n       bendbis gate1 UPDIR OUTDIR FILE.. (BENDBIS_RT_CAP: the round trip's term size cap)\n       bendbis blocks MD STEM (each ```python block of MD as STEM_NN.bend)"

def gate1.base(e: Maybe<&2, String>, fs: List<String>, c: Cfg, base: L.Bk, +cap: U32) -> IO(Unit):
  match e fs c:
    case Some{m} _ _:
      IO.die(Unit, 2, "bendbis: Base did not parse:\n" ++ m)
    case None{} Con{up, Con{out, files}} Cfg{cwd, bp, lib}:
      G.gate.run(files, cwd, bp, base, lib, up, out, cap)
    case None{} _ _:
      IO.die(Unit, 2, USAGE())

def main.gate1(fs: List<String>, c: Cfg) -> IO(Unit):
  match c:
    case Cfg{+cwd, +bp, +lib}:
      do IO<Unit>:
        +br : Ld.LR <- Ld.base.load(bp, lib)
        cs : String <- env("BENDBIS_RT_CAP", "2000000")
        gate1.base(base.err(br), fs, Cfg{cwd, bp, lib}, base.of(br), Maybe.default(&2, U32, U32.read(cs), 2000000))

def main.code(+cmd: String) -> Nat:
  Bool.pick(Nat, String.eq(cmd, "parse"), 1n, Bool.pick(Nat, String.eq(cmd, "gate1"), 2n, Bool.pick(Nat, String.eq(cmd, "blocks"), 3n, Bool.pick(Nat, String.eq(cmd, "gate2"), 4n, 0n))))

def main.blocks(fs: List<String>) -> IO(Unit):
  match fs:
    case Con{md, Con{stem, Nil{}}}:
      G.blocks(md, stem)
    case _:
      IO.die(Unit, 2, USAGE())

def main.check(+f: String, c: Cfg) -> IO(Unit):
  match c:
    case Cfg{cwd, bp, lib}:
      G2.check.main(f, cwd, bp, lib)

def main.gate2(fs: List<String>, c: Cfg) -> IO(Unit):
  match fs c:
    case Con{up, Con{out, files}} Cfg{cwd, bp, lib}:
      G2.gate.run(files, cwd, bp, lib, up, out)
    case _ _:
      IO.die(Unit, 2, USAGE())

def main.cmd(k: Nat, fs: List<String>, c: Cfg) -> IO(Unit):
  match k:
    case 1n:
      main.parse(fs, c)
    case 2n:
      main.gate1(fs, c)
    case 3n:
      main.blocks(fs)
    case 4n:
      main.gate2(fs, c)
    case _:
      IO.die(Unit, 2, USAGE())

def main.two(z: Bool, +f: String, +o: String, c: Cfg) -> IO(Unit):
  match z:
    case True{}:
      main.check(f, c)
    case False{}:
      main.cmd(main.code(f), [o], c)

def main.go(args: List<String>, c: Cfg) -> IO(Unit):
  match args:
    case Con{+f, Con{+o, Nil{}}}:
      main.two(String.eq(o, "--check-only"), f, o, c)
    case Con{+cmd, fs}:
      main.cmd(main.code(cmd), fs, c)
    case Nil{}:
      IO.die(Unit, 2, USAGE())

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    c : Cfg <- cfg()
    main.go(List.tail(&1, String, args), c)

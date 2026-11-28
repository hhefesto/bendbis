# bendbis

Bend implemented in Bend: a port of upstream Bend's `bend2/bend.ts` (and,
later, `bend2/comp.ts` and `bend2/main.ts`) from TypeScript to Bend, checked
against upstream `bend` as the oracle, and built to be a good fit for ana.
`DESIGN.md` has the architecture, the milestones, their gates and what ana
needs.

bendbis is a derivative work of Bend (bendlang/bend, Copyright 2026
HigherOrderCO), under the Apache License 2.0: see `LICENSE` and `NOTICE`.

## How good is it

Measured 2026-11-21 on the code of commit `daa5541` (unchanged since), on
one machine: an 11th Gen Intel Core i7-1160G7 laptop (4 cores, 8 threads,
15 GB), against upstream Bend at `0e2f38f7` (bendlang/bend, run from its
sources by bun 1.4.2) and, for ana's files, Bend 2.0.39 (the release ana
pins).

**Same answers as upstream.** `bendbis FILE --check-only` against
`bend FILE --check-only`: stdout and stderr and the exit code, byte for
byte, each file in its own process under a timeout (60 s a test, 300 s an
ana file):

| set | files | same as upstream | different | timed out |
|---|---|---|---|---|
| upstream's `tests/` and `bend2/base.bend` | 1,880 | 1,880 | 0 | 0 |
| the Bend blocks of upstream's `guide/*.md` | 28 | 28 | 0 | 0 |
| ana's `bend/` (d4cafc4), against 2.0.39 | 253 | 253 | 0 | 0 |

**Proofs, checked by upstream's proven kernel.** Inside `nix develop`
(which sets `$BENDTT` to BendTT built from upstream's `bend2/bendtt.lean`):
`bend src/LAWS.bend --verdict` prints `ALL PROOFS CHECK` for its 34 laws
(bendbis's quantity algebra, spans, application spines, the flattener's
row helpers), and `bend src/BendTT.bend --verdict` prints `ALL PROOFS
CHECK` for its 7 (the start of BendTT's port to Bend: renamings,
`up_ren`, `ren_ren`, `unspine_spine`). `gate/axioms.sh` has Lean v4.34.0
check upstream's `bendtt.lean` (sha256 `3e9b678d...`, 22 s, no error,
warning or `sorry`): its theorems `halts`, `consistent` and `adequate`
rest only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

**Speed** (wall time, no other heavy job running. A file set: 4 files at a
time, one process a file, twice, back to back, bendbis first and then
upstream first; both runs shown. A single file: 7 runs interleaved with
upstream's, the median):

| input | upstream | bendbis | bendbis / upstream |
|---|---|---|---|
| upstream's tests and base.bend (1,880 files) | 249.9 s, 201.3 s | 169.7 s, 192.9 s | 0.68, 0.96 |
| the guide's examples (28) | 2.89 s, 2.04 s | 2.95 s, 1.93 s | 1.02, 0.95 |
| `bend2/base.bend` alone | 0.122 s | 0.215 s | 1.76 |
| ana's `bend/Everything.bend` (2.0.39) | 1.035 s | 3.885 s | 3.75 |

bendbis is faster on the test suite (0.68 to 0.96 of upstream's time:
whichever runs second runs on a hotter, slower laptop), even on the guide,
and slower on a big file: 1.8 times upstream's time on `base.bend`, 3.8
times on ana's `Everything.bend`. Where the time goes, and the plan to
close the gap: `DESIGN.md`, "Speed".

**Since then** (commit `fbad9c0`, 2026-11-28, on olimpo, a Ryzen 7 3700X,
against upstream at bendbis's pin; two runs each, nothing else running):
the checker's share cells are a flat array, its hot paths build no unused
value, and Base's U32 operations on literals run as natives (`DESIGN.md`,
"U32 natives"; `gate/u32n.sh`). The adjunction's gates pass (1,880 + 28 +
253 files byte for byte upstream's).

| input | upstream | bendbis | bendbis / upstream |
|---|---|---|---|
| upstream's tests and base.bend (1,880, 12 at a time) | 1,091 s | 594 s | 0.54 |
| ana's 253 files (12 at a time) | 622 s | 617 s | 0.99 |
| ana's `CorpusV2/ExlawText.bend` | 2.7 s | 1.6 s | 0.59 |
| ana's `Walk.bend` | 2.4 s | 2.4 s | 1.0 |
| ana's `Everything.bend` (mostly parsing) | 1.3 s | 3.0 s | 2.3 |
| a law summing 8,000 U32s | 4.7 s | 0.30 s | 0.06 |

Still slower: parsing (a 16-case match on string literals parses in 1.3 s
against upstream's 0.26 s for the whole check), and ana files built on such
matches (`tests/Sim.bend` 1.95, `Box/Act.bend` 1.92, `tests/chain.bend`
1.70 of upstream's time in the gate).

**Not done yet.** bendbis has no `--verdict` of its own: its checker,
like upstream's `--check-only`, is exact against upstream on the files
above and is not claimed sound (the laws above are checked by upstream's
kernel). It does not yet run programs (milestone 4), emit C (5) or run
on a GPU (6), and does not yet check ana's tree faster than upstream
(milestone 3). The BendTT port has bendtt.lean's first lemmas, not its
theorems.

**To reproduce**, in `nix develop` (`R` this checkout, `UP` an upstream
checkout at `0e2f38f7`, `ANA` ana's tree, `B039` a bend 2.0.39, `W` a new
scratch directory; all absolute paths):

    W=$W UPSTREAM=$UP ANA=$ANA BEND=bend BEND039=$B039 $R/gate/m1.sh
        # builds $W/bendbis, saves upstream's outputs in $W/up and $W/up039
        # (and runs milestone 1's gate: about 30 min)
    cd $UP && $R/gate/m2.sh $W/bendbis 60 $W/upstream.txt $W/up $W/m2t
    $R/gate/m2.sh $W/bendbis 60 $W/guide.txt $W/up $W/m2g
    cd $ANA && P=3 $R/gate/m2.sh $W/bendbis 300 $W/ana.txt $W/up039 $W/m2a
    cd $R && bend src/LAWS.bend --verdict && bend src/BendTT.bend --verdict
    $R/gate/axioms.sh $UP/bend2/bendtt.lean $W/ax
    cd $UP && $R/gate/time.sh 4 60 $W/upstream.txt $W/bendbis +RTS --threads 1 -RTS
    cd $UP && $R/gate/time.sh 4 60 $W/upstream.txt bend

`gate/m2.sh` prints the tally (`same`, `DIFF`, `TIMEOUT`) and writes one
line a file in its new output directory.

## Now: milestone 2, the checker

    bend src/Main.bend -o bendbis      # upstream bend builds it (clang 14+)
    ./bendbis FILE --check-only        # bend FILE --check-only: upstream's
                                       # verdict and messages, its exit code
    ./bendbis gate2 UPDIR OUTDIR FILE..  # milestone 2's gate, one process
    ./bendbis parse FILE..             # read FILE as bend does: upstream's
                                       # error, or what was read
    ./bendbis gate1 UPDIR OUTDIR FILE..  # milestone 1's gate (gate/)

`nix develop` gives upstream `bend` at the commit bendbis is gated against,
with its proven kernel, so `bend src/LAWS.bend --verdict` works (Lean
v4.34.0 and BendTT in the store, nothing in `~/.elan`). There,
`gate/axioms.sh ~/src/bend2-upstream/bend2/bendtt.lean NEWDIR` has Lean
check BendTT's proofs and print the axioms they rest on (DESIGN.md, "No
proof of False").

`BENDBIS_BASE` names the `base.bend` to read (default
`$HOME/src/bend2-upstream/bend2/base.bend`); `BEND_LIB` is read as bend
reads it. Milestone 1's gate driver is `gate/m1.sh`; milestone 2's runs
`gate/m2file.sh` on each file.

## F64, bendbis's first addition

What ana needs beyond upstream Bend is added to bendbis, each addition
delimited by laws (DESIGN.md, "bend and bendbis: the adjunction"). The
first is IEEE 754 binary64:

    import Base
    import F64                     # bendbis's; upstream refuses it

    def area(+r: F64.F64) -> F64.F64:
      (3.141592653589793d * r * r : F64.F64)

    ./bendbis area.bend --check-only   # bendbis reads it as G(area.bend)
    ./bendbis lower area.bend          # G(area.bend): plain Bend that
                                       # upstream bend checks and runs

G (`src/Lower.bend`) turns `import F64` into an import of `lib/F64.bend`
(the operations in plain Bend, exactly rounded, over Base only; with
`lib/SPEC.bend`, the standard's definition, `lib/LAWS.bend`, proven, and
`lib/OPEN.bend`, stated) and each literal `1.5d` into its bits. It is the
identity on every program upstream has. `BENDBIS_LIB` names the directory
of `F64.bend` (default `$HOME/src/bendbis/lib`). The gates:
`gate/adj.sh` (F, eta, and G on `lib/tests/native/`) and
`lib/tests/run.zsh BEND N OUT` (F64.bend's arithmetic and its decimal
literals against the machine's double).

## Credits

bendbis exists because of [Bend](https://github.com/bendlang/bend), by
[HigherOrderCO](https://github.com/HigherOrderCO). Bend was created by
[Victor Taelin](https://github.com/VictorTaelin) and built by its team, as
upstream's README credits them: Lorenzo W Battistela, Paulo J Cavalcanti,
Nico Abril, Vanessa Ostroski, Vitor Chiarelli Neves and Alex Van de Sande,
along with everyone who has contributed to bendlang/bend.

What bendbis takes from Bend:

- the language and what it means: bendbis's lexer, parser, checker and
  error messages are a port of upstream's `bend2/bend.ts`, made from commit
  `0e2f38f7`, and the files under `src/` say so in their headers;
- `bend2/base.bend`, the base library bendbis reads;
- the oracle: upstream's `bend` decides what bendbis must answer, and
  upstream's `tests/` and the Bend blocks of its `guide/*.md` are bendbis's
  gate;
- BendTT, upstream's proven kernel (`bend2/bendtt.lean`): it checks
  bendbis's laws, and `src/BendTT.bend` is the start of its port to Bend;
- the compiler that builds bendbis: `bend src/Main.bend -o bendbis`.

Bend is shared under the Apache License 2.0, and so is bendbis: see
`LICENSE` and `NOTICE`. Mistakes in bendbis are bendbis's own; please
report them here, not upstream.

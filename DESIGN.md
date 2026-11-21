# bendbis: design

bendbis is Bend whose implementation is Bend programs: a port of upstream
Bend's `bend2/bend.ts` (the language: parser, theory, checker), then of
`bend2/comp.ts` (the compiler and runtimes) and `bend2/main.ts` (the CLI),
with upstream `bend` as the oracle. It is built to be a good fit for ana,
the user's denotationally specified transformer written in Bend.

Upstream is read-only: `~/src/bend2-upstream` (bendlang/bend at 0e2f38f7,
2026-11-18) on delfos, its tags v2.0.39 and v2.0.40 with it. ana pins the
release 2.0.39 (ana's flake.lock: bendlang/bend 0ba4e5ec, whose flake names
2.0.39), so for ana's files the oracle is 2.0.39, and for upstream's tests it
is HEAD. On all 253 of ana's files the two print the same `--check-only`
output (measured, olimpo, 2026-11-20).

## The order (the user's answer, 2026-11-21: "Both, the checker first")

1. **The checker, exact.** `bendbis FILE --check-only` prints upstream's
   verdict and messages byte for byte, on upstream's tests and on ana's
   tree. Parser first (milestone 1), then the checker (milestone 2).
2. **Then ana's training fast, all in Bend, with no `bulk.c`.** The dense
   trainer's bulk ops become Bend programs that bendbis compiles to the CPU
   and the GPU fast enough to replace `bulk.c` and cuBLAS (milestones 3-6).

## Architecture: bendbis's modules over bend.ts

bend.ts holds terms in two forms: an `LTerm` (first order, de Bruijn-ish
indices) and an `HTerm` (higher order: a binder's body is a JS closure).
Bend has closures but no mutable cells and no `typeof`, so bendbis keeps
one first-order term type, `Tm` (Core.bend), and an `HTerm` whose binders
are closures as data: an environment and the `Tm` body to read in it
(High.bend). The share cells bend.ts's checker mutates (`Var.v`, `Var.c`)
will be explicit maps threaded through the checker (milestone 2).

| bendbis module | bend.ts / main.ts | what |
|---|---|---|
| `src/Text.bend` | (JS strings) | a file as JS holds it: UTF-8 bytes decoded as WHATWG does, then UTF-16 code units, one `U32` each, so every offset, span and column counts what bend.ts counts |
| `src/Core.bend` | Core, Constructors (245-500) | `Tm` (bend.ts's 24 term forms; a span is `NoSp` or `Sp{file, beg, end}`), `Pat`, `Body`, `Row`, the declarations the parser leaves (`Dcl`), errors (`Er`), quantities |
| `src/Num.bend` | F32, `f32_round`, `f32_show` (1160-1240) | exact decimal to F32 (ties to even) and the shortest round-trip decimal, as JS's `String(Number(..))` spells it, over 16-bit-limb big naturals |
| `src/Show.bend` | Show: `name_key`, `name_show`, `term_show` (1199-1500) | names through a file's aliases; every sugar (Exists, Nat, lists, tuples, arrays, chars, strings, words) |
| `src/High.bend` | `term_higher`, `term_lower` (666-850) | one recursive machine (`hm.go`) over jobs; the environment is an index-keyed trie (see "What bendbis does differently") |
| `src/Lex.bend` | Parse: state, `parse_skip` .. `parse_name` (1540-1680) | the parser's state (`St`: cursor and environment) and monad `P(A) = St -> R<A>` (a value and the next state, or bend.ts's thrown `Err`) |
| `src/Res.bend` | Binders, Quant, `parse_reso`/`own`/`fresh`/`fill`, `INFIX` (1681-1760, 2050-2090) | names and binders, the operator table |
| `src/PHelp.bend` | literals, `parse_char`, NUMBER, `lit_of`, `lit_step`, `term_write`, `parse_bind`, `tele_bind` | the parser's parts that need no recursion into it |
| `src/Flat.bend` | Flatten: `body_sub`, `match_flatten`, `body_flatten` (2694-2880) | nested patterns to lambda-matches, one recursive def over jobs |
| `src/Parse.bend` | Term, Body, Tele, Book: `parse_term` .. `parse_book` (1807-2690) | one recursive def, `ps.go`, whose jobs are bend.ts's mutually recursive functions (Bend refuses mutual recursion) |
| `src/Err.bend` | `err_show`, `err_lost_type` (1500-1538) | errors as bend.ts prints them, the caret in UTF-16 columns |
| `src/Path.bend` | node's `path.posix` | normalize, resolve, relative; the import path rule |
| `src/Load.bend` | `book_load` (940-1040) | import lines, one load per real path, cycles; Base parsed once a process and shared as a layer |
| `src/Wnf.bend` | WNF, SNF, Compare (2880-3330), `term_apply`, `lhs_ext`, `lit_step` | the checker's book (`Td`), the whnf machine (frames, the stuck call it rebuilds), `term_snf` lowered (what errors print), `term_compare` as a work list (the rigid pass, then the book) |
| `src/Check.bend` | Check (3330-3917): `term_infer`, `term_check`, `tele_check`, `term_check_kind`, `uses_close`, `term_descend`, `book_adt`, `ctx_dead`, `def_check`, `def_inst`, `term_key` | one recursive def, `ck.go`, whose jobs are the rules' premises, in a state monad `K` (the book as it grows, template instances, the names a def refers to) |
| `src/Valid.bend` | `book_valid` (3917-4021); main.ts's `book_read` TODO count, `cli_verdict`, `book_promises`; `err_show` with a context | the book from the loader's files, its events, the verdict and its flood |
| `src/Gate2.bend` | main.ts `--check-only` | `bendbis FILE --check-only`, and `bendbis gate2` |
| `src/Main.bend` | main.ts | the command line |
| `src/LAWS.bend` | | laws about bendbis's own functions, proven in Bend |

To come, in this order:

| milestone | bend.ts / comp.ts | bendbis |
|---|---|---|
| 4 | `term_snf` run of `main`, IO's interpreter | `src/Run.bend` |
| 5 | comp.ts: layouts, ANF, Emit, the C emitter and the C runtime it carries as text (3132-6454) | `src/Comp*.bend` |
| 6 | comp.ts's device dialects (CUDA through NVRTC) | `src/Cuda*.bend` |

Each recursive pass is one def over a job type (bend.ts's mutually
recursive functions are its jobs), on fuel: `4294967295n` steps, a bound no
input reaches, so a pass ends only by answering (an exhausted fuel is a
`bendbis:` error, never a silent result). No `@unsafe` anywhere.

## The gates

Every gate compares against upstream's own output; nothing is a golden
written by hand. Gates run on delfos.

**Milestone 1, the front end.** The files: upstream's `bend2/base.bend`,
every `.bend` under `tests/` (1,879), the Bend code blocks of `guide/*.md`
(the guide holds no `.bend` file), and ana's `bend/` tree (253 files, at
d4cafc4).

1. N/N: every file upstream gets past parsing, bendbis parses.
2. The printer round trip: for every file bendbis parses, every term of its
   own declarations (each type, value and constructor type, normalized:
   `term_lower(term_higher(t))`), printed by `src/Print.bend` as Bend
   source and parsed again as the file, where the file is, under the
   file's own import lines, comes back the same term (spans and binder
   names aside; a datatype applied to no arguments, which has no spelling,
   comes back as a reference to it). The printer uses no sugar that reads
   back as another tree, names every binder by its depth, and spells a
   Base name an alias shadows through the sugar that reaches it. A term
   over the size cap (`BENDBIS_RT_CAP`, 2,000,000 nodes) is counted, not
   printed.
3. Every file upstream rejects at parse time, bendbis rejects with
   upstream's output byte for byte (`SOME PROOFS FAIL`, the message, the
   location and caret, the notes). Upstream's output marks a parse-time
   rejection: an error with no context and no def at its location (every
   error the loader, the parser and the flattener throw, and no error the
   checker throws but "a fresh ~ binder name", which is excluded by name),
   or main.ts's "PROOF.bend must import ./LAWS.bend". A file bendbis
   parses whose upstream output is such an error fails the gate.

The gate is `gate/m1.sh`: it builds bendbis, saves upstream's
`--check-only` output for every file (HEAD for upstream's, 2.0.39 for
ana's), and runs `bendbis gate1` over each set; bendbis decides every
verdict.

Status, 2026-11-21 (delfos, `gate/m1.sh`, 29.5 min): passed.

| set | files | rejected at parse time, as upstream (byte for byte) | parsed | of those, rejected by upstream at parse time | terms round-tripped | round trips failed |
|---|---|---|---|---|---|---|
| upstream's tests and base.bend (HEAD) | 1,880 | 214 | 1,666 | 0 | 21,496 | 0 |
| the guide's examples (HEAD) | 28 | 7 | 21 | 0 | 73 | 0 |
| ana's bend/ (2.0.39) | 253 | 0 | 253 | 0 | 30,062 | 0 |

Three of ana's terms are over the cap and were not printed: CorpusV2.bend's
`c2.args` (11,402,874 nodes) and one each in tests/Sim.bend and
tests/SimDrive.bend. Printing and reading `c2.args` back passed 9 GB in 3.5
min and was stopped (delfos has 15 GB); those three wait for milestone 3,
whose shared expansions should make them fit.

**Milestone 2, the checker.** `bendbis FILE --check-only` prints what
upstream prints, byte for byte (stdout and stderr, the exit code), on all
1,879 tests and ana's 253 files (2.0.39 for ana).

The gate is `gate/m2file.sh` over each set, 8 files at a time on delfos (one
bendbis process a file, as upstream is run): bendbis's output and exit
code against upstream's saved ones (milestone 1's), byte for byte.

Status, 2026-11-21 (delfos): passed. Every file gives upstream's output
and exit code, byte for byte, within its timeout (60 s a test, 300 s an
ana file).

| set | files | as upstream, byte for byte | otherwise | timed out | slowest |
|---|---|---|---|---|---|
| upstream's tests and base.bend (HEAD) | 1,880 | 1,880 | 0 | 0 | 6.2 s |
| the guide's examples (HEAD) | 28 | 28 | 0 | 0 | |
| ana's bend/ (2.0.39) | 253 | 253 | 0 | 0 | 152.8 s (CorpusV2.bend) |

Before share cells, 8 files gave no output in time (2 tests at 60 s, 6 of
ana's at 300 s); with them, `u32_native_model` takes 5.7 s and
`conversion_shared_cells_three_way` 0.5 s. Those two needed bend.ts's
share cells: in
`tests/base/u32_native_model.bend` Base's U32 ops run bit by bit on 32-bit
words and each carry is read twice; `conversion_shared_cells_three_way`
compares 18-deep chains of `+a(n) = m(a(n-1), a(n-1))`, which bend.ts
walks once by linking cells it found equal. ana's six are
CorpusV2.bend and the five files that import it (`c2.args`, milestone 1's
11,402,874-node expansion). bendbis's share cells are scoped to one
comparison (term_compare) and dropped when it answers, so no cell reaches
the checker's terms (below, "What bendbis does differently").

**Speed: bendbis against upstream.** The goal (2026-11-21): bendbis's wall
time under upstream bend's on the same inputs, every gate still exact.
Measured on delfos, both run one process a file (`gate/time.sh`, 4 files
at a time for a corpus; a single file three times, the middle run), upstream
at HEAD under bun (2.0.39 for ana):

| input | upstream | bendbis | bendbis / upstream |
|---|---|---|---|
| upstream's tests and base.bend (1,880 files) | 223.6 s, 263.5 s | 187.7 s, 193.6 s | 0.71 to 0.87 |
| the guide's examples (28) | 1.44 s | 1.40 s | 0.97 |
| base.bend | 0.126 s | 0.219 s | 1.74 |
| a file with no `import Base` (10 defs) | 0.030 s | 0.003 s | 0.10 |
| ana's bend/Everything.bend | 1.01 s | 4.10 s | 4.1 |

(2026-11-21, after share cells; the tests twice each, back to back,
bendbis first then upstream first; the no-Base row is from before. Before share cells the
tests took 272.3 s against upstream's 209.4 s, one file out at 120 s.)

Faster than upstream on the tests and the guide, not yet on base.bend or
ana. Where bendbis's time goes (perf, user space): reading
base.bend is about 180 ms of its 252, checking it about 70; of the reading,
half is the runtime freeing and sharing memory (`term_drop`, `span_fade`),
then closures (the parser's monad). Fixed so far, each the `Bool.pick` kind
of trap (both arms run): `Show.chain` and `Show.arr.of` walked a whole
term at every node it printed (the 3,000-deep error page took minutes),
five of Valid's list walks were 2^n (the verdict's own defs), and the
parser measured the rest of the file at each string literal and each
block line (`T.len` of the cursor: quadratic). Next, in this order: share
cells (above), the parser's state and text representation (the runtime's
memory traffic), and Base read once a build.

**Milestone 3, ana checked fast.** Milestone 2's outputs, with bendbis
checking ana's tree faster than upstream: `bend/Everything.bend` under
upstream's 1.08 s (delfos), and the 253 files' sum under upstream's (olimpo:
688.6 s, 2.0.39).

**Milestone 4, running.** For every test whose `main` returns a value,
bendbis's interpreted run prints its `#|` lines, as upstream's does.

**Milestone 5, C.** bendbis emits C for each runnable test; built with
clang and run, it prints the test's `#|` lines (upstream's `c` lane).

**Milestone 6, GPU, then ana's training.** The CUDA lane, gated like 5 on
the `!` tests; then ana's dense step with its bulk ops in Bend, gated on
ana's own checks (tests/dense.bend against the tree trainer, the
dense-identity losses) and timed against run 9's 858 ms a step.

**Laws, and BendTT in Bend (asked 2026-11-21).** bendbis's own functions
get laws proven in Bend (`src/LAWS.bend` and per module), each passing
`bend --verdict`; and BendTT, upstream's kernel proven in Lean
(`bend2/bendtt.lean`: confluence, halting, consistency, adequacy), is
ported to Bend, its terms, evaluator and checker as Bend data and defs and
its claims as Bend theorems, in bendtt.lean's lemma order: the milestone
after 2. Status: `src/LAWS.bend` holds 34 laws: the quantity algebra
the checker's usage rides on (`q.add`, `q.join`, `q.dem`, `q.show` and
the `q.is_*` predicates: units, absorption, commutativity, associativity,
idempotence, join below add), spans (`sp.or`, `sp.has`), application
spines (`tm.app`, `tm.unapp`, `tm.head`: splitting an applied term gives
its head and arguments back) and Flat's pattern and row helpers (by
induction over lists: `rows.tails` and `patt.terms` keep the length).
All 34 pass `bend src/LAWS.bend --verdict` (upstream at 0e2f38f7, its
kernel BendTT built from that commit's bendtt.lean; delfos, 2026-11-21,
7 s), and bendbis's own `--check-only` gives upstream's output on it.

**The devShell (the user, 2026-11-21: "Install in the devshell").**
`flake.nix`: `nix develop` gives `bend` (upstream at the commit bendbis is
gated against, 0e2f38f7, from its sources under bun) with `$BENDTT` set to
BendTT built from that commit's `bend2/bendtt.lean` as safe.ts's
`kernel_bin` builds it, and Lean v4.34.0 (`nix/lean4.nix`, from ana, on
ana's nixpkgs, so it is the store path ana's devShell built). Nothing goes
in `~/.elan` or `~/.bend/bendtt`. On 60 of upstream's tests its
`--check-only` output is bend-head's, byte for byte (bun 1.3.13 there,
1.4.2 in bend-head).

## What bendbis does differently (same output, other cost)

- **Share cells, inside one comparison.** bend.ts's machine wraps each
  argument in a cell it overwrites with the argument's whnf, and its
  comparison links two cells it found equal. bendbis makes cells only
  inside one term_compare (and check-rfl's whnf of its goal with the
  comparison after it), in a store (Wnf's Cm: a trie of cells, each a
  filled whnf and its class's link) made there and dropped when the
  comparison answers; a cell is an HVal whose index is 2^31 plus its
  number, and anywhere the store is not (term_lower, h.force, the error
  printer) it reads as its raw term, as bend.ts's term_force reads one.
  So no cell reaches the checker's terms, and every other whnf passes the
  argument itself (a value read twice there is evaluated twice). Every
  verdict and message is the same; what can differ is cost, and the
  identity shortcuts bend.ts's comparison takes (`a === b` before and
  after the whnfs): bendbis takes them on two cells of one class, and on
  two refs of one name before either is unfolded (`F() -> Type: @-x: F ->
  Empty` unfolds forever otherwise), which changes no answer the walk
  would give.
- **Map reads.** Base's `Map.get`/`Map.has` answer the map too (the path
  they walked, rebuilt); a caller that keeps its own map only drops it.
  Core's `mp.find`/`mp.get`/`mp.has` walk the same trie and answer the
  value alone; Check, Lex, Valid and Wnf read their maps through them.
- **Base, once a process, and only when imported.** Base names nothing of
  an entry's, and nothing before it in book.order names a def of Base's, so
  its check is the same in every book: bendbis checks it once (when a file
  imports it) and, at Base's place in book.order, joins its checked defs,
  instances and names to the book, as bend.ts's own events would have left
  them. An entry with no `import Base` reads no Base at all.
- **The elaborated term.** bend.ts's def_check returns an Ann-wrapped
  LTerm, read later only by book_promises (its names); bendbis keeps the
  names it would walk (each node's own name, and the first-order part of
  each node's type), counted only for premises whose term bend.ts keeps.

- **The environment of term_higher.** bend.ts walks a list of binders for
  each variable. A flattened match wraps each row's body in one `Sub` per
  split it passes, and every node a Sub-bound variable expands into walks
  that list again; in CorpusV2.bend's `c2.args` (31 string-literal cases
  and a catch-all that reads the scrutinee) that is quadratic in pattern
  depth for each of tens of thousands of leaves. bendbis keys the
  environment by binder index (a trie, as bend.ts's PMap): measured on that
  def alone, 56 s became 1.9 s for 3 cases, and the whole def parses in
  20.6 s (upstream, delfos: 4.1 s for the same def, parse and check to its
  first error). The normalized term itself has 11,402,874 nodes, as
  upstream's does: the catch-all's `c` is rebuilt from the string's bits
  at every leaf. Milestone 3 keeps those rebuilds shared instead (lazy
  Sub-bound variables, as bend.ts's closures are), which changes no output.
- **Strictness.** A Bend def's arguments are evaluated before the call, so
  `Bool.pick(T, c, a, b)` evaluates both `a` and `b`. With a recursive call
  in each arm that is 2^n calls: bendbis's first `rows.other` (match
  flattening) did that, and CorpusV2.bend's 32-case `c2.run` took 4 h 39
  min to parse. bendbis branches on a computed value through a def that
  matches on it, never through `Bool.pick` with recursive arms. ana uses
  `Bool.pick` 3,393 times (grep count), so the same trap is open there:
  milestone 3's profile of ana's checking will show whether it bites.

## A good fit for ana: what ana is, measured

**The tree** (d4cafc4, 2026-11-18; counts of source lines by grep, an
estimate until bendbis's own census replaces it): 253 files, 112,829 lines,
4.67 MB; 13,954 `def` lines, 232 laws, 871 types, 15 `@unsafe`, 20 foreign
`import "x.c"` lines, 8 `!` calls, 1,453 template (`~`) lines, 2,560 `do`
blocks, 314 rewrites, 7,739 `match` and 15,128 `case` lines, 425 `{==}`, 4
`?TODO`, 38 parallel lets, 761 lines with F32 literals. 234 distinct
Base-style names; the most used: `Bool.pick` 3,393, `Bool.and` 2,030,
`IO.pure` 1,476, `Nat.show` 1,228, `Nat.is_eq` 1,158, `Bool.or` 1,114,
`U32.is_eq` 1,095, `Nat.add` 1,063, `List.append` 855, `Bool.not` 791,
`List.length` 664, `IO.print` 574, `String.eq` 548.

**Checking it with upstream** (olimpo, Ryzen 7 3700X, bun 1.4.2):
`bend bend/Everything.bend` (64 files, 2,522 declarations) 1.42 s wall,
2.40 s CPU, 299 MB, ALL PROOFS CHECK (delfos, i7-1160G7: 1.08 s wall). Each
of the 253 files alone with `--check-only`: 147 ALL PROOFS CHECK, 105 SOME
PROOFS FAIL on promises only (@unsafe or foreign effects: the verdict, not
a check error), 1 check error (tests/planwin.bend: `P.sp.path` is not
defined). Sum 688.6 s (2.0.39) and 892.8 s (HEAD); median 0.72 s, p90 2.6
s; the slowest: CorpusV2.bend 194.6 s (HEAD 249.6), tests/chain.bend 83.4,
tests/Sim.bend 75.4, tests/SimDrive.bend 32.7, Box/Main.bend 18.9,
Box/Lint.bend 11.8. On delfos (2.0.39, 6 at a time, 2026-11-21) the same
253 outputs, byte for byte; sum 1,219 s, CorpusV2.bend 180.2 s,
tests/chain.bend 144.6, tests/Sim.bend 115.5, tests/SimDrive.bend 101.9. A
Bend process checks on one thread, so ana's checks fan out as processes.

**Parsing it with bendbis** (delfos, one thread a file, 8 at once): all 253
parse; the files' sum is 920 s (each file re-parses Base and its imports);
CorpusV2.bend 87.6 s, tests/chain.bend 80.1, tests/Sim.bend 64.2,
tests/SimDrive.bend 39.9, Box/Main.bend 29.6; Everything.bend 1.97 s, 30
MB. So bendbis's parser alone is slower than upstream's whole check today
(milestone 3's work): the big files pay for `c2.args`'s expansion and
Base's re-parse.

**Where ana's run time goes** (docs/r9/PLAN.md, run 9 on rented RTX 5090s
at 400 W): 858 ms a step, 38,200 tok/s (from 2,352 ms before the run's
speed work). A step issues 9,747 bulk ops through `bulk.c` (Bend's foreign
effects: cuBLAS for products, NVRTC kernels for einsums): products 507 ms
(near TF32's peak, ~90 TFLOP/s on the big ones), einsums 358 ms; the GPU is
busy only 51-80% of the step, so Bend's host loop issuing ~9,700 effects a
step bounds it as much as the GPU. Its honest ceiling at TF32 is ~0.65-0.7
s a step. ana's own Bend GPU kernels (`bend/Bang/`, upstream's `!`) on the
same 5090: a `!` with no work costs 1.30-1.48 ms; the GEMM 1.6-3.5 ms
against cuBLAS's 0.12-0.40 (9-25x slower); the GLA scan 1.16 ms against
`bulk.c`'s 0.28-0.52 (2.5-4x). Upstream's `!` runs one persistent grid of
128 x 2^CUBE_LOG lanes (at most 16,384; a 5090 holds 348,160 resident
threads), scalar F32 with no tensor cores and no FMA, and its F32.exp is the
host's double `exp` on the CPU but `expf` on the GPU.

**What ana needs from its Bend that upstream does not give:**

1. Checking ana's tree fast: upstream spends 194.6 s on CorpusV2.bend (one
   of its defs, `c2.args`, normalizes to 11.4 M nodes; how much of the
   194.6 s that costs is not measured yet); Base is re-read and re-checked
   by every process.
2. GPU code with no per-op launch: one `!` costs more than `bulk.c` takes
   for a whole op, so the dense step's ops must compile into few launches
   (a layer, a step) or a replayed graph, not one launch each.
3. Matrix products on tensor cores (TF32 or BF16) written in Bend, not
   cuBLAS: 507 ms of the 858 with every op timed alone.
4. Flat data-parallel kernels (einsums, scans, reductions) over every lane
   a card has, not a fork tree capped at 16,384 lanes.
5. One F32 semantics on every executor (exp, FMA), so a GPU run equals the
   CPU's bit for bit, as ana's tests demand.
6. Less strictness tax: `Bool.pick`'s both-arms evaluation (above).

The direction among these is the user's: the checker first (1), then
training fast all in Bend with no `bulk.c` (2-5). Milestones 3-6 are their
gates.

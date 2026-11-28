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

## bend and bendbis: the adjunction (the user's goal, 2026-11-27)

The user, 11-27: "apply what you've learned in cata to ~/src/bendbis. I
want you to apply the adjunction and all the levels of functor (meaning
homomorphism et al). The functor should go from regular bend to bendbis
(our bend version implemented in bend) and the other functor should go
from bendbis to bend. This should be useful to get a good implementation
of bend in bend. I want correctness and more speed than regular bend. I
would like bendbis to be a good fit for ~/src/ana, so things like 64 bit
floats (the one that's missing)." And, the same day: "Any addition to
regular bend, like U64 should be very well delimited by laws."

**The two categories.** `Bend`: upstream's programs (books) and functions,
with the meaning upstream gives them (its checker's verdict, its run).
`Bendbis`: bend's programs plus bendbis's additions (F64 first), with the
meaning bendbis gives them.

**F : Bend -> Bendbis, the inclusion.** A program of upstream's is a
program of bendbis's, unchanged. What F claims is bendbis's correctness:
bendbis gives F(p) the meaning upstream gives p. The gates (milestones 1
and 2: 1,880 + 28 + 253 files, byte for byte) are F at the level of the
checker's verdicts; milestone 4 adds runs. F is compositional over a
book's files (a file's check is fixed by it and its imports' checks),
which is what lets bendbis keep checks under the digest of a file and its
imports, as cata's cache does (`CATA_CACHE`): a speed lead, planned.

**G : Bendbis -> Bend, the lowering.** Every addition is replaced by its
definition in plain Bend: an F64 by `lib/F64.bend` (Base only, no
@unsafe), so a bendbis program runs on upstream bend before bendbis runs
anything itself, and every addition has a meaning in Bend that a law can
name. The levels, as in cata:

1. *Homomorphism.* G is a fold over the term algebra: the identity on
   every form upstream has, an addition's leaf (an F64 literal, an `F64.op`
   reference, the type) to the library's term. So G commutes with every
   constructor, and with substitution.
2. *Functor.* G keeps identities and composition (G(g . f) = G(g) . G(f)),
   from 1; and files: G of an import is the import of G.
3. *Naturality.* For F64, phi: native F64 -> library F64 is the identity on
   the bits (both are `F64{hi: U32, lo: U32}`), so a square is a law:
   native `op(x)` == library `op(x)`, for each operation.
4. *Adjunction F -| G.* The unit eta: P -> G(F(P)) is the identity (an
   upstream program has no addition; gate: G leaves every one of the
   2,161 files unchanged, byte for byte). The counit eps: F(G(Q)) -> Q is
   the squares of 3: Q's native additions agree with their definitions.
   The triangles: G(eps) . eta(G) = id (G is idempotent: G(G(Q)) = G(Q),
   a gate) and eps(F) . F(eta) = id (eps is the identity on an upstream
   program).

Since eps is an isomorphism (F64's definition is exact, not an
approximation), the adjunction is an equivalence of meanings: what the
additions change is cost (a native F64 is the machine's double; its
definition is big-natural arithmetic) and convenience (literals, names).

**Every addition, delimited by laws** (the user, 11-27). An addition comes
with four things, F64's the first:

1. its definition in plain Bend: `lib/F64.bend` (IEEE 754 binary64, round
   to nearest ties to even; add, sub, mul, div, sqrt, neg, abs, the
   comparisons, from_u32, from_f32, to_f32; a NaN result is the quiet NaN
   0x7FF8000000000000);
2. its specification as its standard states it, written to be read:
   `lib/SPEC.bend` (a finite value is its exact dyadic; a result is the
   exact real rounded by a binary search over the positive bit patterns,
   the midpoint compared exactly, ties to even, past the greatest finite
   value plus half its ulp infinity; zeros, infinities and NaN by IEEE
   754's tables). It shares only the big naturals with F64.bend; its
   rounding is another algorithm (search and compare, not shift, round
   bit and sticky bit);
3. laws: `lib/LAWS.bend`, proven (`bend lib/LAWS.bend --verdict`: ALL
   PROOFS CHECK, 21 s): for every input sub = add of the negation, is_ne =
   not is_eq, neg(neg(x)) = x, abs(abs(x)) = abs(x) (with Word and U32
   lemmas: xor twice, and idempotent), and IEEE 754's rule table at 23
   named inputs, each proven by computing it (signed zeros, ties to even
   both ways, overflow, gradual underflow, an underflow tie, division by
   zero, NaN's cases, -0 = +0, sqrt's). `lib/OPEN.bend`: the laws that
   delimit each operation, op(a, b) == SPEC's op(a, b) for every input,
   stated and not yet proven (8 TODOs);
4. gates against outside oracles, each with mutants:
   `lib/tests/run.zsh BEND N OUT` holds F64.bend against the machine's
   double (lib/tests/Oracle.hs: GHC's Double, x86-64 SSE2) on IEEE's
   special values (every pair of 30) and N pseudo-random cases in three
   sections (random bits; exponents near each other, for cancellation and
   every alignment; exponents at the range's ends, for overflow,
   underflow and subnormals, and F32's range for to_f32);
   `lib/tests/spec.bend N` holds OPEN.bend's laws on the same kinds of
   inputs.

Measured 2026-11-27 (olimpo, upstream bend 0e2f38f7):

| gate | cases | differ |
|---|---|---|
| F64.bend against the double, N = 200,000 | 5,606,360 lines | 0 |
| OPEN.bend's laws (F64.bend against SPEC.bend), N = 20,000 | 488,192 checks | 0 |
| mutant: ties away from zero, not to even | 62,360 lines; 12,992 checks | 122; 78 |
| mutant: the far operand stood in for from 52 bits apart, not 60 | 62,360 lines | 106 |
| mutant: the quotient one bit short | 62,360 lines | 4,993 |
| mutant law: add.tie_down claims 1 + 2^-52 | `--check-only` | refused |

**What ana needs that upstream Bend has but does not delimit** (11-27,
ana d4cafc4, bend 2.0.39):

1. *F32.* Base's F32 operations are laws with a type and nothing else
   (`law F32.add: for a: F32, for b: F32, F32`: "base's are native"),
   and ana calls them about a thousand times (F32.add 170, mul 141, div
   101, show 88, from_nat 69, sub 63, is_eq 52, neg 37, max 29, abs 27,
   exp 25, sqrt 19, log 16, is_le 16, is_lt 12, pow 7, ...). The checker
   does not compute them (a native is opaque to it); the compiler does
   (comp.ts 170-200): add, sub, mul and div as C float arithmetic, or in
   JS as the double's result rounded to F32 (`Math.fround`), both the
   correctly rounded F32 result (53 >= 2 * 24 + 2), and sqrt as the
   double's sqrt rounded to F32, correctly rounded too; so SPEC.bend's
   rounding at F32's format (already there for to_f32) states those five
   exactly. exp, log, pow, sin, cos, tanh and the rest are the double libm
   of the executor (C's, the JS engine's, CUDA's on the GPU, where ana's
   gate already saw expf differ) rounded to F32: no law holds for them
   today; delimiting them needs a definition (correctly rounded, through
   F64) that every executor computes.
2. *Foreign effects.* ana's `bend/effs/bulk.c` (2,822 lines) behind 9
   foreign defs in `bend/BulkIo.bend` (bk.gemm, bk.mm, bk.mm.q, bk.einsum,
   bk.einsum.q, bk.einsum.seq.q, bk.sync, bk.read_f32be,
   bk.write_f32be), and `wall.c` (the clock). upstream counts each as a
   promise (SOME PROOFS FAIL), and ana's tests hold the products and
   einsums bit for bit against Bend references (Bulk.bend's gemm,
   einsum.ref) on cases. The law to state for each: bk.op(x) ==
   ref.op(x), with the reference in plain Bend.
3. *The fork.* `~/src/bend2` ft-kernels (977a2d98) adds 501 lines of
   Base (File.read_f32be and write_f32be, ArrayView, Array.gemm, the
   einsum machinery Ex, Ix, View, Es with Array.einsum.ref and .prim,
   Array.mm) and 2,365 lines of comp.ts kernels. ana no longer pins it
   (upstream 2.0.39 and bulk.c instead); its content lives on in bulk.c.
4. *Upstream's own unchecked parts* ana leans on: Base's @unsafe
   Array.fork (Bang/Gemm.bend and Bang/GlaScan.bend) and `!`.

The user, 11-27, on these two readings of the functors: "F includes
upstream programs; G translates bendbis's additions back to plain Bend"
(confirmed); and on additions: "I said U64, but might be F64 what I was
referring to. Whatever ana needs should be what gets implemented extra to
what regular bend has." So the additions are what ana needs, each with
the four things above: F64 first; U64 only if ana comes to need it (it
does not today: ana's clock is a Nat, its counters U32).

**(a) F64 in bendbis: done 2026-11-27.** What a bendbis program writes:

    import Base
    import F64                     # the bare import upstream refuses

    def area(+r: F64.F64) -> F64.F64:
      (3.141592653589793d * r * r : F64.F64)

The type is `F64.F64`, the operations `F64.add`, `F64.sqrt`, ...
(`lib/F64.bend` under the alias F64), the operators `+ - * / < <= > >=`
through `(.. : F64.F64)` (the library's `F64.add` .. `F64.is_ge`, each
the operation itself), and a literal is F32's with a `d` after it and no
name character after the `d`: `1.5d`, `1.0e-3d`, `0.1d`, the nearest F64
to the decimal, ties to even (`F64.of_dec`: the exact rational rounded
once; a literal past the greatest finite F64 is left as written, and
upstream then refuses it as an F32 literal out of range).

- *G is `src/Lower.bend`*, on a file's text: a header line `import F64`
  (spaces and a comment after it at most) becomes `import REL as F64`,
  REL the path from the file's directory to `$BENDBIS_LIB/F64.bend`
  (default `$HOME/src/bendbis/lib`; upstream's import rule needs REL's
  segments to be plain names, so the lib may not sit under a dot-directory
  or the nix store); past the header, each `d` literal in code (not in a
  comment, a string or a char, not inside a name) becomes
  `F64.lit(HI, LO)`. A file with no bare `import F64` comes back as it
  is: that is eta. `bendbis lower FILE` prints G(FILE).
- *bendbis reads Q as G(Q)*: the loader lowers every file it reads, so
  bendbis's checks of Q are its checks of G(Q), by construction, and the
  messages quote G(Q)'s lines. In the checker an F64 is its definition
  (eps is the identity); a native F64, the machine's double, comes with
  bendbis's compiler (milestone 5), and then eps's squares are laws to
  prove or gate.
- *Homomorphism, at the text*: G moves no token but an addition's leaves
  (the bare import, a `d` literal), so the term bendbis parses from G(Q)
  is Q's with each leaf replaced: the fold over the term algebra of 1.
- *Gates*, `gate/adj.sh` (one machine, upstream at the pin for every
  set), measured below: F again (milestone 2's gate, byte for byte, with
  the loader lowering); eta (G the identity on every file, byte for
  byte); and on bendbis's own programs (`lib/tests/native/`: laws by
  computation, a failing law, the operators, a literal out of range, no
  import, the import twice, the lexer's corners): G(Q) has no bare import
  left, G(G(Q)) = G(Q), bendbis on Q prints what upstream prints on G(Q),
  byte for byte, exit codes too, and upstream refuses Q itself.
- *F64.of_dec's gate*: `lib/tests/dec.bend` against Oracle.hs's reading
  of the same decimal text (GHC's `read :: Double`: the exact rational,
  rounded to nearest, ties to even), on chosen decimals (the range's
  ends, the halfway point to the least subnormal and its neighbours,
  1e100000 and 1e-100000),
  random ones over the whole exponent range and past it, the exact
  midpoints between neighbouring doubles (normal and subnormal: up to
  770 digits) with the decimals one unit below and above each, and long
  ones: N = 50,000, 250,025 lines, 0 differ; two mutants (the sticky bit
  dropped; 50 bits of quotient, not 57) differ on 643 and 1,498 of
  10,025.

`gate/adj.sh`, olimpo (16 threads, 12 files at a time), 2026-11-27,
upstream at the pin (0e2f38f7, HEAD for ana's files too), ana at d4cafc4:

| gate | files | as required | otherwise |
|---|---|---|---|
| F: bendbis --check-only as upstream, byte for byte (tests and base.bend) | 1,880 | 1,880 | 0 |
| F: the guide's examples | 28 | 28 | 0 |
| F: ana's bend/ (slowest: CorpusV2.bend, 118.8 s) | 253 | 253 | 0 |
| eta: `bendbis lower FILE` is FILE, byte for byte | 2,161 | 2,161 | 0 |
| G on lib/tests/native: bendbis on Q as upstream on G(Q); no bare import in G(Q); G(G(Q)) = G(Q); upstream refuses Q | 7 | 7 | 0 |

On the way, a speed bug: bendbis's term_snf (what an error prints) shared
nothing, so printing the failing side of an F64 law reduced each shared
value once per path to it: `lib/tests/native/fail.bend` took about 550 s
(by difference, in a run of all seven; a twin whose sides are U32s did
not finish in 120 s), upstream 0.4 s. term_snf now keeps one store of cells, as term_compare
does, dropped when the normal form is done: 0.98 s, the same bytes.
Still slower than upstream on F64's heavy laws by computation (`F64.div`
6.9 s against 1.2 s, `F64.sqrt` 38.7 s against 4.5 s, each one law in
its own file): the store is a trie (`ct.get` 16% of the samples) and the
runtime's reference counting (`span_fade` and `term_drop`, 52%); R2 and
R4 below.

**Next, in order.** (b) F32 delimited: SPEC's F32 operations, and laws stating
Base's natives equal them: axioms to upstream (its natives are opaque),
held by running its C and JS targets against SPEC on inputs, and theorems
in bendbis once its F32 natives are F64.bend's code. (c) The proofs of
OPEN.bend, through the exact value: big naturals' arithmetic against
Nat's, then rounding. (d) Speed: DESIGN's
R1-R4 and the per-file cache that F's compositionality allows.

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

(2026-11-21, b612125, after share cells; the tests twice each, back to
back, bendbis first then upstream first; the no-Base row is from before.
Before share cells the tests took 272.3 s against upstream's 209.4 s, one
file out at 120 s.)

2026-11-21, daa5541 (lookups that stop where they answer), delfos quiet,
the single files five times each, the median:

| input | upstream | bendbis | bendbis / upstream |
|---|---|---|---|
| upstream's tests and base.bend (1,880 files, 4 at a time) | 250.8 s | 171.2 s | 0.68 |
| the guide's examples (28, 4 at a time) | 2.85 s | 2.74 s | 0.96 |
| base.bend | 0.118 s | 0.213 s | 1.81 |
| ana's bend/Everything.bend | 1.064 s | 3.879 s | 3.65 |

Everything.bend went from 4.030 s (d88b5bb, the same session) to 3.879 s.
Still faster on the tests and the guide; still slower on base.bend and
ana, the goal's two inputs.

**Where the time goes** (delfos, 2026-11-21, d88b5bb: perf on a build with
frame pointers (`$CC` a clang with `-fno-omit-frame-pointer`; bend honors
`$CC`), and a scratch build that prints `IO.now`
between phases):

| phase | base.bend | Everything.bend |
|---|---|---|
| reading Base (base.bend: reading the entry) | 149 ms | 144 ms |
| checking Base | about 70 ms | 75 ms |
| reading the entry's 63 other files | | 1,340 ms |
| the book's terms to HTerms, and the verdict | | 120 ms |
| book_valid, the checks themselves | | 2,330 ms |
| upstream's whole run | 118 ms | 1,064 ms |

By module (samples charged to the first Bend def on the stack), reading:
Lex 24%, Core 19% (map reads and their string compares), Load 9%, closure
calls 8%, Parse 7%, Text 6%, Res 6%, List 6%, String 5%. Checking: Wnf 44%
(the share-cell store about 17%, `ct.get` alone 11%; book reads, `td.get`
and its compares, about 14%), Check 15%, High 13% (term_higher, each time
a binder is opened, as bend.ts's closures do), Core 8%, Map 5%, String 5%.
Under all of it is the runtime: `term_drop` 37% and `span_fade` 18% of all
samples, freeing and reference counting (reading a shared cons cell costs
an atomic increment and decrement), so every name compare costs that per
character. There is no single hot spot left: the gap is spread over the
representation (names as cons-list Strings, in tries keyed by the
string's bits; HTerms rebuilt at each binder opened) and the runtime's
memory traffic. Upstream runs the same algorithms JIT-compiled with hashed
strings, and uses about 14 s of CPU on 8 threads for its 1.06 s (bun's
collector and compiler); bendbis uses 3.9 s on one.

**Parallel checking, tried and not kept.** Bend's parallel let (`a b =
f(x) g(y)`) runs on every thread: on delfos a pure loop split 16 ways ran
4.5x faster on 8 threads, reads of one shared map 3x. A parallel
book_valid was built (each event first tried, all at once, on the state it
would see if no earlier event had minted a template instance; then the
events in order, a try that minted nothing reused, any other checked
again): the tries took 1.05 s against 2.7 s on one thread. But 328 of
Everything's 2,196 bodies mint instances and were checked again, in order
(about 1.0 s); and once a fork is reachable from any closure, the runtime
runs every closure call (`Clo~apply` reaches every closure) as code that
may fork, which on 2 or more threads made the parser's and checker's
closure-heavy code about 30% slower (a closure loop alone: 45 ms on one
thread, 74 ms on eight; 42 ms on both with no fork in the program). Net:
4.04 s, no gain. Parallelism pays only once the monads (the parser's P,
the checker's K) carry no closures, or with a runtime that keeps closure
calls off the fork path.

**What closing the gap takes** (from the profile; estimates, not
measured), each touching most modules:

1. Names interned to U32 once, when read: the book, constructor and scope
   maps keyed by number, names spelled out only for messages. That removes
   the string compares and most map walking: about a fifth of reading and
   of checking.
2. The share-cell store and the scope maps as Base's Arrays (blocks the
   runtime updates in place when unshared) instead of tries.
3. The parser's and checker's monads without closures (the state passed
   and returned), which also lets parallel checking pay, and parallel
   reading of imports that do not depend on each other.
4. Base read once a build (its checked book in the binary), for files that
   import Base; not for base.bend itself, whose reading is the benchmark.

**The redesign, in order (the user, 2026-11-21: "names as numbers, the
parser and checker without closures, then parallel checking"; planned
here, not started in code).** base.bend's reading alone (149 ms) is over
upstream's whole run (118 ms), so the parser needs about 2x on its own,
and Everything's checking (2.33 s) about 3x.

R1. Names as numbers. Measured shares (Everything, d88b5bb, of all
samples): the checker's book reads (`td.get`: the trie walk, its
`String.drop`s and the leaf's string compare) about 9.6%; the parser's
table reads (`bk.tld`, `bk.ctr` from name resolution and the fresh-name
checks) about 7%. Giving refs an id alone is not enough, for two reasons
found while planning it (estimates from the profile, not measured):

- The id has to come out of a lookup the parser already does. A separate
  name-to-id read at each ref would add a third or so to the parser's
  map reads (P.reso already reads up to three tables a ref), which would
  eat most of what the checker saves. So the id lives in the table entry (`Tld`)
  and `P.reso` answers the name and its id together.
- The checker's book changes while it checks (a def's body becomes
  visible at its last event, Base joins at its place, instances are
  minted), so an id-keyed copy beside the string map needs every write
  mirrored, or reads go stale. One store instead: the book as an id trie,
  with a name-to-id map only for the string-keyed paths (errors, the
  verdict, minted names). Ids: Base's parse first, the entry's after;
  names minted while checking take ids from a counter above the parser's
  range, Base's minted range carried in `Bc`, so no two names share one.
  A ref the parser made before its name was declared, or made up itself
  (sugar), carries `NONE()` and is read by name.

Then the lexer interns every name it reads (the scope, the alias table
and the parser's tables by id; names spelled out only to print), which is
where most of the parser's 7% is. A first edit (not built, set aside)
that added an id to every `TRef`/`HRef` by sed showed one trap: a site that matches a ref and
builds it again with a literal flag (`call.bang`) must keep the id, not
reset it.

R2. The parser's and checker's monads (`L.P`, `K.K`) without closures: a
do-block's continuation as a frame on an explicit job stack, as `ck.go`'s
jobs already are for a rule's premises (defunctionalized). It removes
the closure calls (`Clo~apply`: 4% of all samples, 8% of reading's) and,
above all, the runtime's fork penalty ("Parallel checking, tried and not
kept", above), which R3 needs.

R3. Parallel book_valid: the prototype (a scratch copy on olimpo,
`/tmp/bendbis-scratch/spm/keep/`, not in the repo) checks each event on
the state it would see if no earlier event minted an instance, then
replays in order. Its tries took 1.05 s
against 2.7 s on one thread; it pays once R2 has removed the closures.

R4. The runtime's traffic (term_drop and span_fade, 55% of samples):
fewer `+` (shared) values read many times, maps and stores updated where
they are not shared, so a read does not bump and drop every field it
passes.

Where the time goes after gate9 (2026-11-28, olimpo, callgrind and
counters patched into the emitted C under /tmp/bb-sp/dbg): ana's
`tests/SimDrive.bend` spends it on one def, `sdf.part`, a match on two
string columns that flattens to 3.5M term nodes (upstream builds the same
term; Sim.bend and chain.bend import it and pay it again). A cut of it
(`/tmp/bb-sp/sp/p3.bend`, 245,621 nodes, 1.30 s against upstream's 1.03
s): parsing is 6.3M term_higher steps (26 a node of output), 2.5M
`tm.has` steps and 2.8M `em.set` steps (the live Subs); checking is
119,326 check-ctr steps at about 13k cycles each (the datatype's entry by
name, the constructor by name, its telescope filled, then 240,905 JTele
steps) and the `K` binds' closures. span_fade alone is 26.7M calls there,
the biggest single sources `em.get`'s walk (4.7M) and `String.eq` (5.1M:
names compared a character a time, each one a shared cell): R1 and R4.
`Box/Act.bend`: `Clo_apply` 11.8% and `Lex.P.bind` 7.6% of instructions
(the parser's monad, R2).

Each of R1 to R3 touches most modules (Check.bend alone is 2,087 lines)
and is a session's work or more; the gates (1,880 + 28 + 253, byte for
byte) run after each, and the speed table above gets a row each time.

Fixed so far, each the `Bool.pick` kind of trap (both arms run, so a
recursive arm walks to the end): `Show.chain` and `Show.arr.of` walked a
whole term at every node they printed (the 3,000-deep error page took
minutes), five of Valid's list walks were 2^n (the verdict's own defs),
the parser measured the rest of the file at each string literal and each
block line (`T.len` of the cursor: quadratic), and (daa5541) the parser's
scope lookup, constructor lists, Base table reads, infer-ref's read of its
own def and a share cell's root walked on after the answer.

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

The BendTT port is `src/BendTT.bend`, started: bendtt.lean's Quan, Term
(constructors prefixed K, as Base has a constructor `App`), Ren,
Term.ren, Term.spine and Term.unspine, and its first two lemmas,
`up_ren` and `ren_ren`, with `unspine_spine` (bendtt.lean's 18th, taken
early as it needs no substitution): 7 laws with their helpers,
passing `bend src/BendTT.bend --verdict`. One change of form: bendtt.lean's
Ren is a function, and a Bend function can't be duplicated (a + binder
needs Data, which holds no lambda), nor can a pointwise hypothesis be
shared by a term's two halves (a rewrite uses its proof live). So a
renaming is Data (the identity, Nat.succ, Ren.up, Ren.pick and
composition, read by `ren.at`), a lemma stated with funext is stated at
every index, and `ren_ren` is proven under n binders at once (`ren.ups`),
which needs no extensionality. Next in bendtt.lean's order is `subk_sub`,
where a substitution (Nat -> Term) is composed with `sub` itself
(`sub τ ∘ σ`): as Data, reading it calls `sub`, which reads it, and
BendTT (so `--verdict`) lets a def call only itself and earlier defs, so
that representation is the open design question.

**The devShell (the user, 2026-11-21: "Install in the devshell").**
`flake.nix`: `nix develop` gives `bend` (upstream at the commit bendbis is
gated against, 0e2f38f7, from its sources under bun) with `$BENDTT` set to
BendTT built from that commit's `bend2/bendtt.lean` as safe.ts's
`kernel_bin` builds it, and Lean v4.34.0 (`nix/lean4.nix`, from ana, on
ana's nixpkgs, so it is the store path ana's devShell built). Nothing goes
in `~/.elan` or `~/.bend/bendtt`. On 60 of upstream's tests its
`--check-only` output is bend-head's, byte for byte (bun 1.3.13 there,
1.4.2 in bend-head).

## No proof of False: what is proven, and about what

The user (2026-11-21): "make sure that there is a proof that bendbis cannot
demonstrate Falsely-hood."

**The Lean proof holds.** `gate/axioms.sh`, inside `nix develop` (Lean
v4.34.0), has Lean check upstream's `bend2/bendtt.lean` at 0e2f38f7 (3,861
lines, sha256 3e9b678d...) and print the axioms of its three theorems:

    'halts' depends on axioms: [propext, Classical.choice, Quot.sound]
    'consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
    'adequate' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Book.check' depends on axioms: [propext, Classical.choice, Quot.sound]

(delfos, 2026-11-21, 21 s, no error, warning or `sorry`). Those three are
Lean's standard axioms: no `sorryAx`, no axiom of the file's own (it
declares none), no `native_decide` (which would add `Lean.ofReduceBool`),
no `implemented_by` or `extern`.

**What it says.** `Claim.consistent`: for every book `bk` and every def
`d` of it, if `Book.check bk` answers ok, then `d`'s type does not convert
to `Empty` (`<>`). `Book.check` is exactly what the kernel's command line
runs on the book it reads, and what upstream's `--verdict` runs. So no def
of a book the kernel accepts proves False, not even up to conversion. The
proof goes through `halts` (closed live code terminates, by a measure
that ignores types), progress and subject reduction, and `Claim.empty` (no
value has type `<>`). BendTT has `Type : Type`, so its types (the dead
part) may be inconsistent as a logic; consistency comes from the live
part, which is affine and calls only earlier defs or itself on smaller
arguments. `adequate`: a closed live proof of `{a == b}` makes `a` and `b`
convert (opaque defs unfolded to the models the kernel checked).

**What it covers for bendbis today.** bendbis has no `--verdict` yet.
`bendbis FILE --check-only` is a port of upstream's checker (bend.ts),
which upstream does not claim sound ("Use --verdict for mathematical
validity"); it is exact against upstream on the gated files, nothing more.
bendbis's own laws (`src/LAWS.bend`, 34; `src/BendTT.bend`, 7) pass
upstream's `bend --verdict`: bend2's check, then safe.ts's translation to
BendTT, then the kernel. For them, the kernel accepted their translation,
and by `consistent` nothing it accepts proves False.

**What is trusted, not proven:** safe.ts's translation (a wrong one would
have the kernel check another statement: the kernel's acceptance is
proven safe, not the meaning given to it); the kernel's text parser
(`Book.parse`, a `partial def`, outside the claims); Lean's compiler
(`lean -c`, `leanc`), which makes the binary from the proven definitions;
Lean's kernel and its three axioms.

**The limit.** By Gödel's second incompleteness theorem, BendTT, if it is
consistent and can express its own `Book.check` (it has Nat and recursion
over data), cannot prove its own consistency. So porting `consistent` to
Bend and checking it with `--verdict` cannot succeed, and is not tried.
`halts` also rests on a Dershowitz-Manna multiset order (`dm_wf`), not on
the structural descent BendTT's live check accepts. Two results in Bend
that are possible (proposals, not built; both would extend
`src/BendTT.bend`, whose porting waits on the user's answer):

1. `Claim.empty`: no value has type `<>`, by structural induction over
   the typing rules restricted to values. It is an inversion lemma, not a
   consistency proof, so Gödel's theorem does not stand in the way.
2. The consistency of a weaker fragment: books whose live code has no
   self-calls (each def calls only earlier ones). Their evaluation ends
   by a plain Nat measure (the calls left to unfold), so the fragment is a
   weaker system than BendTT, whose consistency BendTT can state and prove,
   as Peano arithmetic proves that of weaker systems.

## `--verdict` in bendbis (milestone V, planned, not started)

Upstream's `--verdict` (main.ts `cli_verdict`): book_promises (bendbis has
it: `--check-only` prints it), then `Safe.safe_check`: safe.ts (1,733
lines, about 1,280 of code) translates the checked book to BendTT text
(`safe_book`); if no def is out of scope, the text is written to a fresh
directory and `$BENDTT` checks it (`kernel_check`): exit 0 with exactly
`ALL PROOFS CHECK` passes, else the lines after `SOME PROOFS FAIL` are the
reason. `bend FILE -o X.bendtt` writes the same text.

What bendbis needs for it:

1. The elaborated term. bend.ts's def_check answers an LTerm whose every
   node is wrapped in its type (`Def.e`), and safe.ts reads it for every
   def; bendbis's checker keeps only its names ("The elaborated term",
   below). Its rules would build the whole term, only when `--verdict`
   asks, so `--check-only` pays nothing.
2. safe.ts in Bend: the items (roots; instances, one per tuple of finite
   `~` values; groups, found by regrouping and repeated passes), the model
   search under its fuel (2^22 steps, counted as safe.ts counts them), the
   lowering of λ-matches to case trees with convoys, η-long arguments
   where `eta_finite` holds, the undo trail, and the printer. Its WeakMap
   and Map memos keyed by object identity change the output where the
   memoized call has effects (`col` in `root_emit` runs `term` once per
   object), so the port has to track which values are the same object.
3. The kernel call: Base's `Process.run` (an argv run, no shell) on
   `$BENDTT`, the text through a file in a fresh directory, as
   `kernel_check` does.

The gates: first `bendbis FILE -o X.bendtt` byte for byte against
upstream's on every file upstream's own `--verdict` gate reads (gates/safe.ts:
every test), ana's files with laws, `src/LAWS.bend` and `src/BendTT.bend`;
then `bendbis FILE --verdict`, output and exit code. The same text given
to the same kernel gives the same answer, so the first gate is the work.
Its size is that of milestone 2's checker (Check.bend, 2,087 lines): more
than one session.

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
- **U32 natives** (Wnf.bend, "U32 natives"; the user, 11-27: "correctness
  and more speed than regular bend"). bend.ts evaluates Base's U32
  operations as Base defines them, through Word's constructors: one
  `U32.add` on two literals turns both into 32 `WCon` cells and runs
  Word.add's ripple carry over them, hundreds of machine steps. bendbis
  answers Base's U32.add, sub, mul, div, mod, and, or, xor, min, max, cmp,
  not, inc, to_nat, shl, shr and from_nat on literals in one step, with
  comp.ts's natives (the values the compiled program computes); the rest
  of Base's U32 ops (is_eq and the other comparisons, is_zero, is_even,
  shln, shrn, ...) are made of these and reach them by Base's own
  unfolding. Only defs whose Base body matches its arguments first are
  natives, and a native reads them as that match does: the first to its
  whnf, the second only when the first is a literal. A literal answers the
  value. A whnf the match is stuck on answers the call stuck, the
  arguments read so far in their whnfs, as Base's def does (its first
  match stuck rebuilds the call); the argument is not read twice, since a
  stuck call read again runs again (in bend.ts too): an earlier version
  that ran Base's def after a failed native read doubled the work at each
  level of a chain of natives, and four of upstream's tests
  (`conversion_shared_cells_*`, `shift_*_mask`) timed out. Anything else
  (a constructor) runs Base's def on that whnf. So every verdict and every
  printed term is Base's; a whnf differs from Base's only inside its
  arguments (stuck on b after matching a literal a, Base's def rebuilds a
  as `U32{w}`, here a stays the literal). `gate/u32n.sh` holds it to that:
  1,392 laws at edge and pseudo-random literals, their right sides
  computed by the compiled program, which upstream proves through Base's
  bit-level defs (ALL PROOFS CHECK, so Base's def and the native agree at
  each input) and bendbis checks with the same output; 12 wrong laws, one
  per op, and 12 wrong laws over a variable whose reports print stuck
  calls, all byte for byte upstream's; and the adjunction's gates
  (gate7: 1,880 + 28 + 253 files the same). Measured on olimpo (Ryzen 7
  3700X, nothing else running, two runs each), before / now / upstream:
  summing 8,000 U32s in a law, 14.0 / 0.30 / 4.7 s; the 1,392 laws, 4.5 /
  0.48 / 1.4 s; ana's `CorpusV2/ExlawText.bend`, 7.9 / 1.6 / 2.7 s; ana's
  `Walk.bend`, 8.7 / 2.4 / 2.4 s; ana's `Everything.bend` (mostly
  parsing), 3.4 / 3.0 / 1.3 s. ana's 253 files in the gate (12 at a
  time): 1.14 of upstream's time before, 0.99 now.
- **Dead Subs** (Flat.bend, `sub.live`; Core.bend, `tm.has`). Match
  flattening puts a Sub on a row's body for each variable a split binds,
  and a catch-all row goes into every split's both sides, so its body
  collects two Subs a split, and the copies share their tails: a
  16-case match on string literals made 36,820 Subs, and term_higher
  walked 2,255,658 Sub steps (a chain per leaf), each an `em.set`: an
  EmBin path of about 13 nodes, built and later freed (`term_drop` was
  56% of the parse). bend.ts's list_set is one cell, so the same walk
  costs it little. term_higher reads a Sub's entry only at a Var, a Var
  Ref or a pattern var of the Sub's index under it, so bendbis makes no
  Sub over a term its index occurs nowhere in (`tm.has`: any Var, Var
  Ref, Sub index or Sub pattern var of that index; out of fuel, yes):
  term_higher's answer is the same term. Laws: `tm.has.u32`,
  `sub.live.u32`, `tms.has.out` (LAWS.bend, --verdict); the gates: gate8,
  1,880 + 28 + 253 files, eta and G, all the same. Measured on olimpo,
  before / now / upstream, `--check-only`: the 16-case match, 1.72 / 0.40
  / 0.50 s; ana's `Box/OnBox.bend`, 2.91 / 1.32 / 0.86 s;
  `Box/Act.bend`, 4.03 / 1.70 / 1.05 s. ana's 253 files in the gate: 0.99
  of upstream's time before, 0.89 now; upstream's tests and base.bend:
  0.54 before, 0.48 now.
- **Error arms built only when taken** (Check.bend). `K.if(A, z, a, b)`
  takes both arms as values, so an arm written `K.err(.., ExS{x ++ y},
  ..)` built its message on every check that passed and then freed it:
  check-ctr spelled `S.name.key(k) ++ " with " ++ U32.show(..)` and a
  datatype's whole constructor list (`cr.names(cs)`) for every
  constructor it checked. Such an arm is now `st => K.err(..)(st)`, built
  when run: iret, uses_close, infer-adt, check-ctr (three arms) and
  check-mat (two). The messages are the same strings, built at the same
  point of the run that prints them. gate9: 1,880 + 28 + 253 the same,
  eta and G too; ana's 253 files 0.89 -> 0.76 of upstream's time,
  upstream's tests 0.48 -> 0.44 (CorpusV2.bend 82 -> 66 s, upstream 73
  s); ana's `tests/SimDrive.bend` alone 23.3 -> 19.3 s.
- **A def body's normal form in one walk** (High.bend's `nf`, PHelp's
  `P.norm.by`). `term_lower(term_higher(t))` made every node twice: a
  higher node and, a binder, a closure, which term_lower then opened. Its
  one error is a bare operator's, so on a body that names none
  (`body.ops`, a walk of the parsed body before flattening, which adds
  no Ref) the machine answers a term, and `nf` reads each node's normal
  form at once in the machine's own environment, its entries made by the
  same `em.set` calls: a Var at its entry, a Lam's or an All's body under
  Var(k, d) at d + 1, a Let's body under its bindings' Vars at d + n, a
  Sub's body under its pattern. An App whose head may become a Lam (the
  beta step, the one place term_higher puts a term for a variable) is
  the machine's, whole, at the same environment and depth; a body with
  an operator is the machine's, whole, so its error is the one in its
  order. Laws (LAWS.bend, `--verdict`): `nf.u32`, `nf.free`, `nf.lam`,
  `nf.sub`, `nf.let`, `nf.beta`, instances, one a kind of step, where
  both sides compute and meet; a wrong one (the occurrence's name for the
  binder's) fails. gate10: 1,880 + 28 + 253 the same, eta and G too.
  SimDrive's parse 9.07 -> 7.92 s; the rest of a normal form's cost is
  the environment's trie (an `em.set` copies a path of about ten nodes,
  freed again after the subtree; an `em.get` walks one, every node
  shared).
- **check-ctr's success path in one read** (Check.bend's `ctr.find`;
  `K.w`, `khead` and `kfill` pass the state by hand, no bind). check-ctr
  read the book three times through the monad, rebuilt the datatype's
  constructor list without the refined-away names (`cr.drop`) and walked
  it twice (`cr.has`, `cr.get`), for every constructor it checked (a U32
  literal in a pattern is 32 `WCon`s and 32 Bools). `ctr.find` reads the
  type's whnf, the datatype's entry and the constructor in one pure walk:
  the first constructor of that name, not in r, which is the entry
  `cr.get` finds in `cr.drop`'s list (it keeps the order and drops only
  names in r). When a read fails, the rule's own reads run again and make
  its error. gate11: 1,880 + 28 + 253 the same, eta and G too; ana's 253
  files 0.76 -> 0.70 of upstream's time, upstream's tests 0.44 -> 0.42;
  SimDrive 19.7 -> 15.2 s (upstream 9.4), its 245,621-node cut 1.31 ->
  1.05 s (upstream 1.03).
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

# bendbis

Bend implemented in Bend: a port of upstream Bend's `bend2/bend.ts` (and,
later, `bend2/comp.ts` and `bend2/main.ts`) from TypeScript to Bend, checked
against upstream `bend` as the oracle, and built to be a good fit for ana.
`DESIGN.md` has the architecture, the milestones, their gates and what ana
needs.

bendbis is a derivative work of Bend (bendlang/bend, Copyright 2026
HigherOrderCO), under the Apache License 2.0: see `LICENSE` and `NOTICE`.

## Now: milestone 2, the checker

    bend src/Main.bend -o bendbis      # upstream bend builds it (clang 14+)
    ./bendbis FILE --check-only        # bend FILE --check-only: upstream's
                                       # verdict and messages, its exit code
    ./bendbis gate2 UPDIR OUTDIR FILE..  # milestone 2's gate, one process
    ./bendbis parse FILE..             # read FILE as bend does: upstream's
                                       # error, or what was read
    ./bendbis gate1 UPDIR OUTDIR FILE..  # milestone 1's gate (gate/)

`BENDBIS_BASE` names the `base.bend` to read (default
`$HOME/src/bend2-upstream/bend2/base.bend`); `BEND_LIB` is read as bend
reads it. Milestone 1's gate driver is `gate/m1.sh`; milestone 2's runs
`gate/m2file.sh` on each file.

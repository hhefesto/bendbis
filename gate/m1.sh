#!/usr/bin/env bash
# m1.sh: milestone 1's gate (DESIGN.md). W: a fresh scratch directory;
# UPSTREAM: bendlang/bend's checkout (HEAD for its own files); BEND039:
# bend 2.0.39 (ana's pin, for ana's files); ANA: ana's tree. Builds bendbis
# with upstream's bend, saves upstream's outputs, runs the gate on upstream's
# base.bend and tests, the guide's examples and ana's bend/, and prints the
# summaries. Nothing here decides a verdict: bendbis gate1 does.
set -eu
W=${W:?a scratch directory}; UPSTREAM=${UPSTREAM:-$HOME/src/bend2-upstream}
ANA=${ANA:?ana\'s tree}; BEND=${BEND:?upstream bend at HEAD}; BEND039=${BEND039:?bend 2.0.39}
G=$(cd "$(dirname "$0")" && pwd); mkdir -p "$W/up" "$W/up039" "$W/guide" "$W/out"
(cd "$G/../src" && "$BEND" Main.bend -o "$W/bendbis")
for md in "$UPSTREAM"/guide/*.md; do "$W/bendbis" blocks "$md" "$W/guide/$(basename "$md" .md)"; done
cp "$W/guide/GUIDE_15.bend" "$W/guide/math.bend"   # the guide's "# math.bend", which GUIDE_16 imports
(cd "$UPSTREAM" && { find tests -name '*.bend' | sort; echo bend2/base.bend; } > "$W/upstream.txt")
ls "$W"/guide/*.bend > "$W/guide.txt"; (cd "$ANA" && find bend -name '*.bend' | sort > "$W/ana.txt")
(cd "$UPSTREAM" && xargs -P 6 -I{} "$G/up1.sh" "$BEND" 300 {} "$W/up" < "$W/upstream.txt")
(cd "$W/guide" && xargs -P 6 -I{} "$G/up1.sh" "$BEND" 300 {} "$W/up" < "$W/guide.txt")
(cd "$ANA" && xargs -P 6 -I{} "$G/up1.sh" "$BEND039" 900 {} "$W/up039" < "$W/ana.txt")
(cd "$UPSTREAM" && "$G/gate1.sh" "$W/bendbis" "$W/upstream.txt" "$W/up" "$W/out" upstream)
(cd "$W/guide" && "$G/gate1.sh" "$W/bendbis" "$W/guide.txt" "$W/up" "$W/out" guide)
(cd "$ANA" && "$G/gate1.sh" "$W/bendbis" "$W/ana.txt" "$W/up039" "$W/out" ana)
grep -h '^gate1' "$W"/out/{upstream,guide,ana}.txt

#!/usr/bin/env bash
# adj.sh: the adjunction's gates on one machine (DESIGN.md, "bend and
# bendbis: the adjunction"). W: a new scratch directory; UPSTREAM:
# bendlang/bend's checkout at bendbis's pin (its tests, guide and
# bend2/base.bend); ANA: ana's tree; BEND: upstream bend at the pin.
# Builds bendbis, then:
#
# 1. F, the checker: milestone 2's gate again (bendbis FILE --check-only
#    byte for byte against upstream's, upstream's tests and base.bend, the
#    guide's examples, ana's bend/), upstream at HEAD for every set;
# 2. eta, G the identity on upstream's programs: `bendbis lower FILE` is
#    FILE, byte for byte, on all of those files;
# 3. G on bendbis's own programs (lib/tests/native/*.bend): G(Q) has no
#    bare import left and G(G(Q)) = G(Q); bendbis Q --check-only against
#    upstream G(Q) --check-only, byte for byte, exit codes too (Q copied to
#    W/q, G(Q) written to W/g, the same depth, so both import F64.bend by
#    the same relative path); and upstream refuses Q itself.
#
# Nothing here decides a verdict but cmp; nothing is deleted or
# overwritten (W must be new). P: files at a time (default 8).
set -u
W=${W:?a new scratch directory}; UPSTREAM=${UPSTREAM:?bend at the pin}
ANA=${ANA:?ana\'s tree}; BEND=${BEND:?upstream bend at the pin}
[ -e "$W" ] && { echo "adj.sh: $W exists: name a new W" >&2; exit 2; }
G=$(cd "$(dirname "$0")" && pwd); R=$(cd "$G/.." && pwd)
export BENDBIS_BASE=${BENDBIS_BASE:-$UPSTREAM/bend2/base.bend} BENDBIS_LIB=${BENDBIS_LIB:-$R/lib}
mkdir -p "$W/up" "$W/guide" "$W/q" "$W/g" "$W/gq"
(cd "$R/src" && "$BEND" Main.bend -o "$W/bendbis") || exit 1
B=$W/bendbis
for md in "$UPSTREAM"/guide/*.md; do "$B" blocks "$md" "$W/guide/$(basename "$md" .md)"; done
cp "$W/guide/GUIDE_15.bend" "$W/guide/math.bend"
(cd "$UPSTREAM" && { find tests -name '*.bend' | sort; echo bend2/base.bend; } > "$W/upstream.txt")
(cd "$W/guide" && ls *.bend > "$W/guide.txt")
(cd "$ANA" && find bend -name '*.bend' | sort > "$W/ana.txt")

# 1. F: upstream's outputs, then bendbis's against them
(cd "$UPSTREAM" && xargs -P "${P:-8}" -I{} "$G/up1.sh" "$BEND" 300 {} "$W/up" < "$W/upstream.txt")
(cd "$W/guide" && xargs -P "${P:-8}" -I{} "$G/up1.sh" "$BEND" 300 {} "$W/up" < "$W/guide.txt")
(cd "$ANA" && xargs -P "${P:-8}" -I{} "$G/up1.sh" "$BEND" 900 {} "$W/up" < "$W/ana.txt")
(cd "$UPSTREAM" && "$G/m2.sh" "$B" 60 "$W/upstream.txt" "$W/up" "$W/m2-upstream") > "$W/m2-upstream.tally"
(cd "$W/guide" && "$G/m2.sh" "$B" 60 "$W/guide.txt" "$W/up" "$W/m2-guide") > "$W/m2-guide.tally"
(cd "$ANA" && "$G/m2.sh" "$B" 300 "$W/ana.txt" "$W/up" "$W/m2-ana") > "$W/m2-ana.tally"

# 2. eta: G is the identity on every one of them
eta() { while read -r f; do "$B" lower "$f" | cmp -s - "$f" && echo "same	$f" || echo "DIFF	$f"; done; }
(cd "$UPSTREAM" && eta < "$W/upstream.txt") > "$W/eta-upstream.txt"
(cd "$W/guide" && eta < "$W/guide.txt") > "$W/eta-guide.txt"
(cd "$ANA" && eta < "$W/ana.txt") > "$W/eta-ana.txt"

# 3. G on bendbis's own programs
for q in "$R"/lib/tests/native/*.bend; do
  n=$(basename "$q"); cp "$q" "$W/q/$n"
  (cd "$W/q" && "$B" lower "$n") > "$W/g/$n"
  (cd "$W/g" && "$B" lower "$n") > "$W/gq/$n"
  if grep -Eq '^[[:space:]]*import[[:space:]]+F64([[:space:]]|$)' "$W/g/$n"; then bare=BARE; else bare=nobare; fi
  cmp -s "$W/g/$n" "$W/gq/$n" && idem=idem || idem=NOTIDEM
  (cd "$W/q" && "$B" "$n" --check-only > "$W/q/$n.bb" 2>&1; echo $? > "$W/q/$n.rc")
  (cd "$W/g" && "$BEND" "$n" --check-only > "$W/g/$n.up" 2>&1; echo $? > "$W/g/$n.rc")
  (cd "$W/q" && "$BEND" "$n" --check-only > "$W/q/$n.up" 2>&1)
  cmp -s "$W/q/$n.bb" "$W/g/$n.up" && cmp -s "$W/q/$n.rc" "$W/g/$n.rc" && same=same || same=DIFF
  head -1 "$W/q/$n.up" | grep -q 'SOME PROOFS FAIL' && refused=refused || refused=ACCEPTED
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$same" "$bare" "$idem" "$refused" "$(head -1 "$W/q/$n.bb")" "$n"
done > "$W/native.txt"

for s in upstream guide ana; do echo "F $s: $(tr '\n' ' ' < "$W/m2-$s.tally")"; done
for s in upstream guide ana; do echo "eta $s: $(cut -f1 "$W/eta-$s.txt" | sort | uniq -c | tr '\n' ' ')"; done
echo "G native: $(cut -f1-4 "$W/native.txt" | sort | uniq -c | tr '\n' ' ')"

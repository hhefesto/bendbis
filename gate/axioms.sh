#!/usr/bin/env bash
# axioms.sh LEAN OUTDIR: has Lean check upstream's bend2/bendtt.lean (the
# file at LEAN, e.g. ~/src/bend2-upstream/bend2/bendtt.lean) and print the
# axioms its three theorems (halts, consistent, adequate) and Book.check
# rest on. Run inside `nix develop` (Lean v4.34.0). The copy, with the
# #print lines after it, goes in OUTDIR (it must be new), with Lean's
# output in OUTDIR/lean.out; the upstream file is only read.
set -u
src=$1; out=$2
[ -e "$out" ] && { echo "axioms.sh: $out exists: name a new OUTDIR" >&2; exit 2; }
mkdir -p "$out"
cp "$src" "$out/ax.lean"
printf '\n#print axioms halts\n#print axioms consistent\n#print axioms adequate\n#print axioms Book.check\n' >> "$out/ax.lean"
sha256sum "$src" | cut -c1-64 > "$out/sha256"
lean --version > "$out/lean.version"
cd "$out" && lean ax.lean > lean.out 2>&1
rc=$?
cat lean.out
grep -q sorryAx lean.out && { echo "axioms.sh: sorryAx appears" >&2; exit 1; }
exit $rc

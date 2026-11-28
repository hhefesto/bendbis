#!/usr/bin/env bash
# u32n.sh: the U32 natives' differential gate (Wnf.bend, "U32 natives").
# W: a new scratch directory; BEND: upstream bend at the pin; B: a bendbis
# binary (built from src/ when unset). gen.bend writes laws.bend, a law
# for each native op at 48 rounds of edge and pseudo-random literals, and
# one wrong law per op (mut.*.bend), and wrong laws over a variable whose
# reports print stuck calls (stuck.*.bend). Upstream checks them through Base's
# defs bit by bit; bendbis through its natives. Passes when upstream says
# ALL PROOFS CHECK on laws.bend, and bendbis's output and exit code equal
# upstream's on every file, byte for byte. Nothing is deleted.
set -u
W=${W:?a new scratch directory}; BEND=${BEND:?upstream bend at the pin}
export BENDBIS_BASE=${BENDBIS_BASE:?bend2/base.bend at the pin}
[ -e "$W" ] && { echo "u32n.sh: $W exists: name a new W" >&2; exit 2; }
G=$(cd "$(dirname "$0")" && pwd); R=$(cd "$G/.." && pwd)
mkdir -p "$W/f" "$W/up" "$W/bb"
[ -n "${B:-}" ] || { (cd "$R/src" && "$BEND" Main.bend -o "$W/bendbis") || exit 1; B=$W/bendbis; }
(cd "$G/u32n" && "$BEND" gen.bend -o "$W/gen") || exit 1
"$W/gen" | awk -v d="$W/f" '/^=== /{f=d "/" $2; next} {print > f}'
ok=0; bad=0
for f in "$W"/f/*.bend; do
  n=$(basename "$f")
  (cd "$W/f" && "$BEND" "$n" --check-only > "$W/up/$n.out" 2>&1; echo $? > "$W/up/$n.rc")
  (cd "$W/f" && "$B" "$n" --check-only > "$W/bb/$n.out" 2>&1; echo $? > "$W/bb/$n.rc")
  if cmp -s "$W/up/$n.out" "$W/bb/$n.out" && cmp -s "$W/up/$n.rc" "$W/bb/$n.rc"; then
    ok=$((ok + 1))
  else
    bad=$((bad + 1)); echo "DIFF $n"
  fi
done
head -1 "$W/up/laws.bend.out" | grep -qx 'ALL PROOFS CHECK' || { echo "upstream: laws.bend does not check"; bad=$((bad + 1)); }
for m in "$W"/up/mut.*.rc "$W"/up/stuck.*.rc; do [ "$(cat "$m")" = 0 ] && { echo "wrong law passed: $m"; bad=$((bad + 1)); }; done
echo "u32n: $(grep -c '^law' "$W/f/laws.bend") laws, $(ls "$W"/f/mut.*.bend | wc -l) mutants, $(ls "$W"/f/stuck.*.bend | wc -l) stuck; same $ok, differ $bad"
[ "$bad" = 0 ]

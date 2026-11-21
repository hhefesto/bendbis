#!/usr/bin/env bash
# m2file.sh SECS UPDIR OUTDIR FILE: milestone 2's gate on one file (BENDBIS: the binary). bendbis FILE --check-only under a
# timeout into OUTDIR/<FILE, / as _>.bb (kept), against upstream's output
# and exit code saved in UPDIR. Deletes nothing.
set -u
secs=$1; up=$2; out=$3; f=$4
n=$(printf '%s' "$f" | tr / _)
s=$(date +%s%N)
timeout "$secs" ${BENDBIS:?the bendbis binary} +RTS --threads 1 -RTS "$f" --check-only > "$out/$n.bb" 2>&1
rc=$?
ms=$(( ($(date +%s%N) - s) / 1000000 ))
urc=$(cut -f2 "$up/$n.t" 2>/dev/null)
if [ "$rc" = 124 ]; then echo "TIMEOUT	$f	$ms"
elif cmp -s "$out/$n.bb" "$up/$n.out" && [ "$rc" = "$urc" ]; then echo "same	$f	$ms"
else echo "DIFF	$f	$ms	rc $rc/$urc"; fi

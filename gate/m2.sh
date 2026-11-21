#!/usr/bin/env bash
# m2.sh BIN SECS LIST UPDIR OUTDIR: milestone 2's gate over the files in LIST
# (paths from the current directory), P at a time (default 8), each by m2file.sh under
# SECS: one line a file in OUTDIR/gate.txt (same, DIFF or TIMEOUT, file,
# ms), bendbis's outputs beside it, then the tally. OUTDIR must be new: the
# gate deletes nothing and overwrites nothing.
set -u
bin=$1; secs=$2; list=$3; up=$4; out=$5
[ -e "$out" ] && { echo "m2.sh: $out exists: name a new OUTDIR" >&2; exit 2; }
mkdir -p "$out"
here=$(cd "$(dirname "$0")" && pwd)
BENDBIS=$bin xargs -P "${P:-8}" -I{} "$here/m2file.sh" "$secs" "$up" "$out" {} < "$list" > "$out/gate.txt"
cut -f1 "$out/gate.txt" | sort | uniq -c

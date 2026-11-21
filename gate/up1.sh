#!/usr/bin/env bash
# up1.sh BEND SECS FILE OUTDIR: upstream's `BEND FILE --check-only` under a
# SECS timeout, stdout and stderr together into OUTDIR/<FILE, / as _>.out;
# FILE, the exit code and the milliseconds into .t
set -u
b=$1; secs=$2; f=$3; o=$4
n=$(printf '%s' "$f" | tr / _)
s=$(date +%s%N)
timeout "$secs" "$b" "$f" --check-only > "$o/$n.out" 2>&1
rc=$?
e=$(date +%s%N)
printf '%s\t%d\t%d\n' "$f" "$rc" "$(( (e - s) / 1000000 ))" > "$o/$n.t"

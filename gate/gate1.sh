#!/usr/bin/env bash
# gate1.sh BENDBIS LIST UPDIR OUTDIR NAME: `BENDBIS gate1` over the files in
# LIST (paths from the current directory) in 8 processes, one thread each;
# their lines, then their summaries, into OUTDIR/NAME.txt
set -u
bb=$1; list=$2; up=$3; out=$4; name=$5
mkdir -p "$out/$name.parts"
split -n l/8 -d "$list" "$out/$name.parts/l"
for p in "$out/$name.parts"/l[0-9][0-9]; do
  "$bb" +RTS --threads 1 -RTS gate1 "$up" "$out" $(cat "$p") > "$p.txt" 2>&1 &
done
wait
cat "$out/$name.parts"/l[0-9][0-9].txt > "$out/$name.txt"

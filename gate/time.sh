#!/usr/bin/env bash
# time.sh P SECS LIST BIN..: Wall time of `BIN.. FILE --check-only`
# over every FILE of LIST (from the current directory), P at a time, each
# under SECS; prints the total seconds and the count of timeouts
set -u
p=$1; secs=$2; list=$3; shift 3
s=$(date +%s%N)
n=$(xargs -P "$p" -I{} sh -c 'timeout '"$secs"' "$@" {} --check-only > /dev/null 2>&1; [ $? = 124 ] && echo T' _ "$@" < "$list" | grep -c T)
e=$(date +%s%N)
echo "$(( (e - s) / 1000000 )) ms, $n timeouts"

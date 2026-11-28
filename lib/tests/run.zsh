#!/usr/bin/env zsh
# lib/tests/run.zsh BEND N OUT: F64.bend against the machine's double.
# Builds vec.bend with BEND (upstream bend), Oracle.hs with nixpkgs's GHC,
# runs vec N (N random cases a section, 3 sections, about 28 lines a case,
# plus the specials' table) into OUT/vec.txt and holds every line against
# the double; prints "LINES lines, D differ", exit 1 if any differs. OUT
# must be new: the gate overwrites nothing.
set -eu
bend=$1; n=$2; out=$3
[[ -e $out ]] && { print -u2 "run.zsh: $out exists: name a new OUT"; exit 2 }
here=${0:A:h}
mkdir -p $out/o
(cd $here && $bend vec.bend -o $out/vec)
nix shell nixpkgs#ghc -c ghc -O1 -v0 -o $out/oracle -outputdir $out/o $here/Oracle.hs
$out/vec $n > $out/vec.txt
$out/oracle < $out/vec.txt

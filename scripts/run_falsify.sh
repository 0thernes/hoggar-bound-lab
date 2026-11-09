#!/usr/bin/env bash
# Falsification suite: every assignment the engine can produce is compared with the proved lower bound.
# A single assignment below the bound makes this script exit non-zero.
# Randomness: Tsotchke quantum_rng (classical mixer), seeded; every count is recomputed from scratch.
set -u
cd "$(dirname "$0")/.."
H=./build/hoggar; [ -f build/hoggar.exe ] && H=./build/hoggar.exe
out=results/falsify.log
: > "$out"
status=0
run() { echo "\$ hoggar $*" >> "$out"; $H "$@" >> "$out" 2>/dev/null; rc=$?; if [ $rc -ne 0 ]; then status=1; echo "  -> exit $rc" >> "$out"; fi; }
run exhaust2
for t in f h; do run falsify 2 $t 11 20000 0; done
for t in f h e; do run falsify 3 $t 13 20000 0; run falsify 3 $t 14 1500 20000; done
for t in f h e; do run falsify 4 $t 17 5000 0; run falsify 4 $t 18 200 300000; done
for t in f h e; do run falsify 5 $t 19 500 0; run falsify 5 $t 20 12 4000000; done
for f in data/witness/*.txt; do
  read -r N t v < "$f"
  run verify "$N" "$t" "$f"
done
# negative control: the harness must be able to say "refuted"
echo "\$ negative control: false claim d(W(5,2)) >= 64 against the Hoggar witness" >> "$out"
$H verify 3 f data/witness/n3_f_hoggar_moonlab.txt 64 >> "$out" 2>/dev/null
if [ $? -eq 3 ]; then echo "  -> correctly refuted (exit 3)" >> "$out"; else echo "  -> NEGATIVE CONTROL FAILED" >> "$out"; status=1; fi
echo "FALSIFICATION SUITE STATUS: $status (0 = no counterexample found)" >> "$out"
exit $status

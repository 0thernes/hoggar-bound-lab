#!/usr/bin/env bash
# run_family7.sh - the exhaustive seven-qubit search (paper, Theorem 13) and its orbit analysis.
#
#   bash scripts/run_family7.sh [jobs]        (default 16 parallel slices; about 8 core-hours in total)
#
# Writes results/family7.log.  The list of 13 271 040 solutions (106 MB) stays in build/ and is not kept.
# This is not part of scripts/run_all.sh: it is the long computation behind one statement, kept separate
# so that the everyday test run stays short.  The random census of the other types of B is run at the end.
set -euo pipefail
cd "$(dirname "$0")/.."
JOBS="${1:-16}"
mkdir -p build/f7 results
for f in family7 orbits7 sample7; do
  gcc -O2 -std=gnu11 -Wall -Wextra "src/$f.c" -o "build/$f"
done
LOG=results/family7.log
: > "$LOG"
echo "# family7: all third-level forms on seven qubits with B alternating of rank 6" >> "$LOG"
echo "# started $(date -u +%Y-%m-%dT%H:%M:%SZ), $JOBS slices" >> "$LOG"
STEP=$(( 32768 / JOBS ))
pids=()
for i in $(seq 0 $(( JOBS - 1 ))); do
  first=$(( i * STEP ))
  count=$STEP
  if [ "$i" -eq $(( JOBS - 1 )) ]; then count=$(( 32768 - first )); fi
  ./build/family7 "$first" "$count" "build/f7/slice_$i.bin" > "build/f7/slice_$i.log" &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
cat build/f7/slice_*.log >> "$LOG"
cat build/f7/slice_*.bin > build/f7/solutions.bin
echo "# solutions file: $(wc -c < build/f7/solutions.bin) bytes" >> "$LOG"
./build/orbits7 build/f7/solutions.bin | tee -a "$LOG"
echo "# random census of the other types of B (3e8 forms each)" >> "$LOG"
pids=()
for m in 0 1 2; do ./build/sample7 0 "$m" 300000000 $(( 1000 + m )) > "build/f7/sample_cs_$m.log" & pids+=($!); done
for k in 1 2 3 4 5 6; do ./build/sample7 "$k" 0 300000000 $(( 2000 + k )) > "build/f7/sample_t_$k.log" & pids+=($!); done
./build/sample7 0 3 2000000 12345 > build/f7/sample_cs_3.log & pids+=($!)
for p in "${pids[@]}"; do wait "$p"; done
cat build/f7/sample_*.log >> "$LOG"
echo "# finished $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$LOG"
tail -14 "$LOG"

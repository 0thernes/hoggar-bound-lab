#!/usr/bin/env bash
# Runs every executable check of the lab and prints one line per stage.
# Exit status is non-zero if any stage fails.
set -u
cd "$(dirname "$0")/.."
EXE=""; [ -f build/hoggar.exe ] && EXE=".exe"
[ -f "build/hoggar$EXE" ] || bash scripts/build.sh
mkdir -p results
fail=0
stage() { # name, command...
  local name="$1"; shift
  if "$@" > "results/.stage.log" 2>&1; then echo "PASS  $name"; else echo "FAIL  $name (see results/.stage.log)"; cat results/.stage.log | tail -5; fail=1; fi
}
stage "exhaustive two-qubit enumeration"        ./build/hoggar$EXE exhaust2
stage "exact integer bound table (N <= 6)"      ./build/hoggar$EXE table 6
stage "falsification suite + negative control"  bash scripts/run_falsify.sh
stage "Moonlab experiment (E0-E4)"              node src/moonlab_experiment.mjs
stage "QGTL kernels on the Hoggar state"        ./build/qgt_hoggar$EXE
if command -v eshkol-run >/dev/null 2>&1; then
  stage "Eshkol replication + autodiff"         bash -c 'eshkol-run -r src/eshkol/hoggar.esk | tee results/eshkol.log | grep -q ESHKOL-PASS'
else
  echo "SKIP  Eshkol (eshkol-run not on PATH)"
fi
stage "NumPy analysis (structure, spectra)"     python scripts/analysis.py
stage "averaging between families"              python scripts/ladder.py
rm -f results/.stage.log
[ $fail -eq 0 ] && echo "ALL STAGES PASSED" || echo "SOME STAGES FAILED"
exit $fail

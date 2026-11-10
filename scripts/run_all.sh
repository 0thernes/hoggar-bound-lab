#!/usr/bin/env bash
# Runs every executable check of the lab and prints one line per stage.
# Exit status is non-zero if any stage fails.
# (The seven-qubit enumeration, scripts/run_family7.sh, takes about eight core-hours and is run separately.)
set -u
cd "$(dirname "$0")/.."
EXE=""; [ -f build/hoggar.exe ] && EXE=".exe"
[ -f "build/hoggar$EXE" ] && [ -f "build/third_level$EXE" ] && [ -f "build/qgt_flat$EXE" ] || bash scripts/build.sh
mkdir -p results
fail=0
stage() { # name, command...
  local name="$1"; shift
  if "$@" > "results/.stage.log" 2>&1; then echo "PASS  $name"; else echo "FAIL  $name (see results/.stage.log)"; cat results/.stage.log | tail -5; fail=1; fi
}
ESHKOL=""
if command -v eshkol-run >/dev/null 2>&1; then ESHKOL="eshkol-run"; fi
stage "exhaustive two-qubit enumeration"        ./build/hoggar$EXE exhaust2
stage "exact integer bound table (N <= 6)"      ./build/hoggar$EXE table 6
stage "falsification suite + negative control"  bash scripts/run_falsify.sh
stage "Moonlab experiment (E0-E4)"              node src/moonlab_experiment.mjs
stage "QGTL kernels on the Hoggar state"        ./build/qgt_hoggar$EXE
if [ -n "$ESHKOL" ]; then
  stage "Eshkol replication + autodiff"         bash -c "$ESHKOL -r src/eshkol/hoggar.esk | tee results/eshkol.log | grep -q ESHKOL-PASS"
else
  echo "SKIP  Eshkol (eshkol-run not on PATH)"
fi
stage "NumPy analysis (structure, spectra)"     python scripts/analysis.py
stage "averaging between families"              python scripts/ladder.py
# ---- configurations that attain the floor (paper, Section 5)
stage "flat states, exact arithmetic (68 checks)"      bash -c 'python scripts/flat_states.py | tee results/flat_states.log | tail -1 | grep -q "68 of 68"'
stage "census of third-level phase states (N <= 5)"    bash -c "./build/third_level$EXE | tee results/third_level.log | grep -q THIRD-LEVEL-PASS"
stage "phase states, exact arithmetic (81 checks)"     bash -c 'python scripts/phase_states.py | tee results/phase_states.log | tail -1 | grep -q "81 of 81"'
stage "Moonlab: eight flat states, two circuits (S1-S3)" bash -c 'node src/moonlab_saturated.mjs | tee results/moonlab_saturated.log | grep -q MOONLAB-SATURATED-PASS'
stage "QGTL kernels on the eight flat states"          bash -c "./build/qgt_flat$EXE | tee results/qgt_flat.log | grep -q QGT-FLAT-PASS"
if [ -n "$ESHKOL" ]; then
  stage "Eshkol: the pivot configuration + autodiff"   bash -c "$ESHKOL -r src/eshkol/saturated.esk | tee results/eshkol_saturated.log | grep -q ESHKOL-SATURATED-PASS"
fi
# ---- the cospectral pair (combined paper, Section 8) and the completion minima (publication/ADDENDUM-completion-optima.md)
stage "cospectral pair, exact arithmetic (30 checks)"  bash -c 'python scripts/cospectral_pair.py | tee results/cospectral_pair.log | tail -1 | grep -q "30 of 30"'
# ---- case C3 for every number of qubits (publication/ADDENDUM-c3-all-qubits.md)
stage "C3 family, full configurations N = 3..6 (43 checks)" bash -c 'python scripts/cospectral_family.py --six | tee results/cospectral_family.log | tail -1 | grep -q "43 of 43"'
stage "C3 family, second route by tensor products (18 checks)" bash -c 'python scripts/cospectral_family_tensor_check.py | tee results/cospectral_family_tensor.log | tail -1 | grep -q "18 of 18"'
stage "C11: cone lifts of the C3 family, 4 to 6 qubits (21 checks)" bash -c 'python scripts/cospectral_family_cone_lift.py | tee results/cospectral_family_cone_lift.log | tail -1 | grep -q "21 of 21"'
stage "C3: exhaustive search near the all-plus carrier, four qubits" bash -c 'python scripts/c3_sparse_search.py 3 3 | grep -v "^time:" | tee results/c3_sparse_search_four.log | grep -q "different block spectra: 4; of these with different r_D (different completion cubic traces): 3"'
rm -f results/.stage.log
[ $fail -eq 0 ] && echo "ALL STAGES PASSED" || echo "SOME STAGES FAILED"
exit $fail

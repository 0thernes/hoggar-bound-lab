#!/usr/bin/env bash
# Developer task runner for hoggar-bound-lab (Python, C11, Node.js, Lean 4.35.0).
# Usage: scripts/dev.sh <detect|setup|build|test|lint|sanitizers|clean>
# Missing optional toolchains are skipped with a notice, never fabricated.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

ACTION="${1:-help}"; shift || true
STATUS=0

has() { command -v "$1" >/dev/null 2>&1; }
note() { printf '[dev] %s\n' "$*"; }
skip() { note "skip $1: $2"; }
run() { note "\$ $*"; "$@" || { note "failed ($?): $*"; STATUS=1; }; }
py() { if has python3; then python3 "$@"; else python "$@"; fi; }

do_detect() {
  echo "python=true"
  echo "node=true"
  echo "c-cpp=true"
  echo "lean=true"
}

do_setup() {
  if has python3 || has python; then
    run py -m pip install --quiet -r requirements.txt
  else
    skip python "python not installed"
  fi
  if has lake; then
    (cd lean && run lake exe cache get Mathlib.Analysis.Matrix.Spectrum Mathlib.Algebra.Order.Chebyshev Mathlib.Data.ZMod.Basic Mathlib.Tactic Mathlib.LinearAlgebra.Matrix.Charpoly.Basic Mathlib.LinearAlgebra.Matrix.Kronecker Mathlib.LinearAlgebra.Matrix.Trace Mathlib.LinearAlgebra.Matrix.Block Mathlib.FieldTheory.Finite.GaloisField Mathlib.FieldTheory.Finite.Trace)
  else
    skip lean "lake not installed"
  fi
}

do_build() {
  mkdir -p build/bin
  local cc=""
  if has gcc; then cc=gcc; elif has clang; then cc=clang; fi
  if [ -n "$cc" ]; then
    run "$cc" -O2 -std=c11 -Wall -Wextra -o build/bin/w52_census_verify src/w52_census_verify.c
    run "$cc" -O2 -std=c11 -Wall -Wextra -o build/bin/n9_rank8_search src/n9_rank8_search.c
    run "$cc" -O2 -std=c11 -Wall -Wextra -o build/bin/hoggar src/hoggar.c -lm
    run "$cc" -O2 -std=c11 -Wall -Wextra -o build/bin/third_level src/third_level.c -lm
  else
    skip c-cpp "gcc/clang not installed"
  fi
  if has lake; then
    (cd lean && run lake build HoggarBound.Kramers HoggarBound.SaturationTheory HoggarBound.ConjectureE HoggarBound.ConjectureEExtras HoggarBound.AuditUpgrades HoggarBound.C3ExactOptima HoggarBound.SaturatedPhaseSix HoggarBound.NormPhaseFamily HoggarBound.ExactDegreesN4N5 HoggarBound.NonVacuity HoggarBound.Challenge HoggarBound.Solution)
  else
    skip lean "lake not installed"
  fi
}

do_sanitizers() {
  mkdir -p build/san
  local cc=""
  if has clang; then cc=clang; elif has gcc; then cc=gcc; fi
  if [ -z "$cc" ]; then skip sanitizers "gcc/clang not installed"; return; fi
  run "$cc" -O1 -g -std=c11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer -o build/san/hoggar src/hoggar.c -lm
  run "$cc" -O1 -g -std=c11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer -o build/san/w52_census_verify src/w52_census_verify.c
  run "$cc" -O1 -g -std=c11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer -o build/san/n9_rank8_search src/n9_rank8_search.c
  run ./build/san/hoggar
}

do_test() {
  if has python3 || has python; then
    run py scripts/c3_sdp_dual_check.py
    run py scripts/c3_exact_optima_check.py
    run py scripts/norm_phase_family.py
    run py scripts/exact_degrees_n4_n5.py
    run py scripts/check_readme_axioms.py
    run py scripts/arithmetic_audit.py
    run py scripts/build_blueprint.py
    run py scripts/publication_release_audit.py
    run py scripts/unified_publication_audit.py
    if py -c "import pytest" 2>/dev/null; then
      run py -m pytest -q tests/test_properties.py tests/test_mutation_and_fuzz.py
    else
      run py -m unittest discover -s tests -p "test_*.py" -v
    fi
  else
    skip python "python not installed"
  fi
  if has node; then
    run node tests/frontier_c3_browser_test.cjs
    run node tests/independent_demo_test.cjs
  else
    skip node "node not installed"
  fi
}

do_lint() {
  if has ruff; then
    run ruff check scripts/c3_exact_optima_check.py scripts/norm_phase_family.py scripts/exact_degrees_n4_n5.py scripts/check_readme_axioms.py scripts/arithmetic_audit.py scripts/build_blueprint.py scripts/check_citations.py tests/test_properties.py tests/test_mutation_and_fuzz.py
  else
    skip python "ruff not installed"
  fi
  if has mypy; then
    run mypy --ignore-missing-imports scripts/check_readme_axioms.py scripts/arithmetic_audit.py scripts/build_blueprint.py scripts/check_citations.py
  else
    skip python "mypy not installed"
  fi
  if has cppcheck; then
    run cppcheck --enable=warning,style --std=c11 src/w52_census_verify.c src/n9_rank8_search.c src/hoggar.c
  else
    skip c-cpp "cppcheck not installed"
  fi
  if has lake; then
    (cd lean && run lake exe runLinter HoggarBound.Kramers HoggarBound.SaturationTheory HoggarBound.ConjectureECore HoggarBound.ConjectureECones HoggarBound.ConjectureE HoggarBound.ConjectureEExtras HoggarBound.AuditUpgrades HoggarBound.C3ExactOptimaData HoggarBound.C3ExactOptima HoggarBound.SaturatedPhaseSix HoggarBound.NormPhaseFamily HoggarBound.ExactDegreesN4N5 HoggarBound.NonVacuity HoggarBound.Solution)
  else
    skip lean "lake not installed"
  fi
}

do_clean() {
  run rm -rf build/bin build/san build/audit.json .pytest_cache .mypy_cache .ruff_cache
}

case "$ACTION" in
  detect) do_detect ;;
  setup) do_setup ;;
  build) do_build ;;
  test) do_test ;;
  lint) do_lint ;;
  sanitizers) do_sanitizers ;;
  clean) do_clean ;;
  *) sed -n '2,4p' "$0"; exit 0 ;;
esac
exit $STATUS

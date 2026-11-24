# Task runner (https://just.systems). Run `just` to list recipes.
# Every recipe delegates to plain scripts (`scripts/dev.sh` or direct verifiers), so `just` is never required.
# No recipe installs git hooks or gates a commit or push (Build Standard R1).

set shell := ["bash", "-euo", "pipefail", "-c"]
set windows-shell := ["bash", "-euo", "pipefail", "-c"]

# List recipes
default:
    @just --list

# Install pinned Python dependencies and fetch pinned Lean/Mathlib cache
setup:
    bash scripts/dev.sh setup

# Build Lean 4.35.0 modules and C11 verifiers (-Wall -Wextra)
build:
    bash scripts/dev.sh build

# Run all exact verifiers, property/negative/regression/mutation tests, and Node tests
test:
    bash scripts/dev.sh test

# Static analysis, type checks, and Lean Batteries linter (report-only)
lint:
    bash scripts/dev.sh lint

# Build and run C11 verifiers under AddressSanitizer + UndefinedBehaviorSanitizer (B16)
sanitizers:
    bash scripts/dev.sh sanitizers

# Build all v1.5.0-v1.9.0 Lean modules, verify 110 axioms, and run 6-kernel lake comparator --paranoid
verify-lean:
    cd lean && lake build HoggarBound.Kramers HoggarBound.SaturationTheory HoggarBound.ConjectureE HoggarBound.ConjectureEExtras HoggarBound.AuditUpgrades HoggarBound.C3ExactOptima HoggarBound.SaturatedPhaseSix HoggarBound.NormPhaseFamily HoggarBound.ExactDegreesN4N5 HoggarBound.NonVacuity HoggarBound.Challenge HoggarBound.Solution
    cd lean && lake env lean VerifyNewFormalizations.lean
    cd lean && lake comparator --config comparator.json --paranoid

# Check Lean Blueprint declarations and rebuild interactive dependency DAG
blueprint:
    python3 scripts/build_blueprint.py

# Clean clone to headline results: verify exact checks, continuity audits, README axioms, blueprint, and site
reproduce:
    python3 scripts/conjecture_e_trace_formula.py
    python3 scripts/conjecture_e_trace_formula.py 6
    python3 scripts/c3_sdp_dual_check.py
    python3 scripts/c3_exact_optima_check.py
    python3 scripts/norm_phase_family.py
    python3 scripts/exact_degrees_n4_n5.py
    python3 scripts/check_readme_axioms.py
    python3 scripts/arithmetic_audit.py
    python3 scripts/build_blueprint.py
    python3 scripts/publication_release_audit.py
    python3 scripts/unified_publication_audit.py
    node tests/frontier_c3_browser_test.cjs
    python3 scripts/independent_site.py

# Score this repository against Build Standard v1.1.0 (report-only; writes build/audit.json)
audit *ARGS:
    mkdir -p build
    bash scripts/audit-repo.sh --json build/audit.json {{ARGS}}

# Verify data/MANIFEST.sha256 checksums (B39)
check-data:
    cd data && sha256sum -c MANIFEST.sha256

# Show detected stacks
detect:
    bash scripts/dev.sh detect

# Push an offsite mirror (configure remote `backup` first; see docs/operations.md)
mirror:
    git push backup --mirror

# Remove temporary build output
clean:
    bash scripts/dev.sh clean

# Replication Protocol (`hoggar-bound-lab`)

This file specifies how any independent verifier can reproduce every headline Lean 4 theorem, exact integer certificate, C11 census, Blueprint dependency check, and compiled publication artifact from a clean clone (Build Standard B43 & B44).

## 1. Prerequisites

- **Git** (`>= 2.35`)
- **Python** `3.12` (exact dependencies pinned in [requirements.txt](requirements.txt): `numpy==2.0.2`, `sympy==1.14.0`, `hypothesis==6.124.0`, `pytest==8.3.4`)
- **Node.js** `24.x` (for interactive demo tests `tests/frontier_c3_browser_test.cjs` & `tests/independent_demo_test.cjs`)
- **C11 compiler** (`gcc` or `clang`, for `src/*.c` and ASan/UBSan sanitizer verification)
- **Lean 4.35.0** via `elan` (pinned automatically by [lean/lean-toolchain](lean/lean-toolchain) and [lean/lake-manifest.json](lean/lake-manifest.json))
- **Bubblewrap** (`bwrap`, Linux only, for sandboxed `lake comparator --paranoid`)

## 2. Clean-Clone Exact Verification (Fast Path, ~2–7 Minutes)

```bash
git clone https://github.com/0thernes/hoggar-bound-lab.git
cd hoggar-bound-lab

# 1. Verify pinned data checksums (B39)
(cd data && sha256sum -c MANIFEST.sha256)

# 2. Install pinned Python dependencies
python3 -m pip install -r requirements.txt

# 3. Run all 202 exact integer/symbolic checks + property/mutation/fuzz tests
python3 scripts/conjecture_e_trace_formula.py        # 97/97 checks (N=3..5)
python3 scripts/conjecture_e_trace_formula.py 6      # 39/39 checks (N=6)
python3 scripts/c3_sdp_dual_check.py                 # 15/15 checks (Prop 16')
python3 scripts/c3_exact_optima_check.py             # 10/10 checks (Thm 16'', 368/344)
python3 scripts/norm_phase_family.py                 # 32/32 checks (Thm 13b)
python3 scripts/exact_degrees_n4_n5.py               #  9/9 checks (N=4..5 42-orbit certs)
python3 -m pytest -q tests/test_properties.py tests/test_mutation_and_fuzz.py
node tests/frontier_c3_browser_test.cjs
node tests/independent_demo_test.cjs

# 4. Run continuity, README axiom sync, arithmetic, Blueprint, and Build Standard audits
python3 scripts/check_readme_axioms.py
python3 scripts/arithmetic_audit.py
python3 scripts/build_blueprint.py
python3 scripts/publication_release_audit.py
python3 scripts/unified_publication_audit.py
python3 scripts/independent_site.py
bash scripts/audit-repo.sh
```

## 3. Clean-Clone Lean 4.35.0 Multi-Kernel Verification (~6–10 Minutes)

```bash
cd lean

# 1. Fetch pinned Mathlib v4.35.0 cache (never modifies lean-toolchain or lake-manifest.json)
lake exe cache get Mathlib.Analysis.Matrix.Spectrum \
  Mathlib.Algebra.Order.Chebyshev Mathlib.Data.ZMod.Basic Mathlib.Tactic \
  Mathlib.LinearAlgebra.Matrix.Charpoly.Basic Mathlib.LinearAlgebra.Matrix.Kronecker \
  Mathlib.LinearAlgebra.Matrix.Trace Mathlib.LinearAlgebra.Matrix.Block \
  Mathlib.FieldTheory.Finite.GaloisField Mathlib.FieldTheory.Finite.Trace

# 2. Build all v1.5.0–v1.9.0 modules (zero sorry in every proof module)
lake build HoggarBound.Kramers HoggarBound.SaturationTheory \
  HoggarBound.ConjectureE HoggarBound.ConjectureEExtras HoggarBound.AuditUpgrades \
  HoggarBound.C3ExactOptima HoggarBound.SaturatedPhaseSix HoggarBound.NormPhaseFamily \
  HoggarBound.ExactDegreesN4N5 HoggarBound.NonVacuity HoggarBound.Challenge HoggarBound.Solution

# 3. Audit all 110 declarations strictly within [propext, Classical.choice, Quot.sound]
lake env lean VerifyNewFormalizations.lean

# 4. Run Batteries linter across all 14 new modules
lake exe runLinter HoggarBound.Kramers HoggarBound.SaturationTheory \
  HoggarBound.ConjectureECore HoggarBound.ConjectureECones HoggarBound.ConjectureE \
  HoggarBound.ConjectureEExtras HoggarBound.AuditUpgrades HoggarBound.C3ExactOptimaData \
  HoggarBound.C3ExactOptima HoggarBound.SaturatedPhaseSix HoggarBound.NormPhaseFamily \
  HoggarBound.ExactDegreesN4N5 HoggarBound.NonVacuity HoggarBound.Solution

# 5. Isolated Challenge vs Solution replay across all SIX bundled Lean 4.35.0 kernels
#    (official C++, leanchecker-paranoid, lean4lean, nanoda 0.4.19, con-leche, con-ron)
lake comparator --config comparator.json --paranoid
```

## 4. Clean-Clone C11 Sanitizers & Independent Orbit/Rank Censuses

```bash
# AddressSanitizer + UndefinedBehaviorSanitizer check (B16)
gcc -O1 -g -std=c11 -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer -o build/san/hoggar src/hoggar.c -lm && ./build/san/hoggar
gcc -O2 -std=c11 -Wall -Wextra -o build/bin/w52_census_verify src/w52_census_verify.c && ./build/bin/w52_census_verify
gcc -O2 -std=c11 -Wall -Wextra -o build/bin/n9_rank8_search src/n9_rank8_search.c && ./build/bin/n9_rank8_search
```

## 5. Recorded Replication Log (B44)

All rows below are **real observed runs** (author-triggered local + public GitHub Actions runners). External third-party human replication is welcomed via an issue tagged `replication` — none is falsely claimed below.

| Date (UTC) | Verifier / Environment | Commit / Tag | Scope Replicated | Result | Evidence |
| --- | --- | --- | --- | --- | --- |
| 2026-11-10 | GitHub Actions `ubuntu-24.04` (public runner) | `87f08a0` (`v1.2.0`) | Full Lean baseline (22), C3 (42), stability (6), saturation (14) + C/Node/Python | PASS | [Run 42741638647](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42741638647), [Run 42741638912](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42741638912) |
| 2026-11-10 | GitHub Actions `ubuntu-24.04` (public runner) | `b7b0273` (`v1.3.0`) | Seven-qubit `phase7_degree` (13 decls) + C3 all qubits (74 decls) | PASS | [Run 42808984960](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42808984960) |
| 2026-11-21 | GitHub Actions `ubuntu-24.04` (public runner) | `eb2d83e` (`v1.8.0`) | 100 Lean 4.35.0 declarations + 202 exact Python checks + publication audits | PASS | [Run 44959312365](https://github.com/0thernes/hoggar-bound-lab/actions/runs/44959312365), [Run 44959313235](https://github.com/0thernes/hoggar-bound-lab/actions/runs/44959313235) |
| 2026-11-22 | Independent read-only audit (`DEFENSIBLE_INDEPENDENT_AI_RESEARCH_PLAYBOOK.md`) | `7b5cbaf` (`v1.8.0`) | Static Lean token audit (`0 sorry`, `0 native_decide`, ~21k lines across 42 files), metadata & policy review | PASS (static) + findings logged | `docs/reviews/2026-11-24-ten-pass-playbook-audit.md` |
| 2026-11-24 | Windows 11 + GitHub Actions `ubuntu-24.04` / `macos-latest` / `windows-latest` | `v1.9.0` (pending final SHA in `docs/run-log.md`) | 110 Lean declarations, Batteries `runLinter`, 6-kernel `lake comparator --paranoid`, ASan/UBSan C11, Blueprint `checkdecls`, Build Standard v1.1.0 | Recorded in `docs/run-log.md` after CI completion | [docs/run-log.md](docs/run-log.md) |

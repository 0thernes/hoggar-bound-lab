# Environment and Configuration (`hoggar-bound-lab`)

This repository requires **zero API keys, zero cloud credentials, and zero `.env` secrets** to build, test, or verify every mathematical result (Build Standard A33).

## Pinned Toolchains & Dependencies

| Component | Pin File | Exact Version | Notes |
| --- | --- | --- | --- |
| Lean 4 & Lake | [lean/lean-toolchain](lean/lean-toolchain) | `leanprover/lean4:v4.35.0` | Includes `leanchecker-paranoid`, `lean4lean`, `nanoda` 0.4.19, `con-leche`, `con-ron`, `lake comparator`. |
| Mathlib & Batteries | [lean/lake-manifest.json](lean/lake-manifest.json) | `v4.35.0` | Fetched via `lake exe cache get` (read-only). |
| Python runtime & packages | [requirements.txt](requirements.txt) | Python `3.12`, `numpy==2.0.2`, `sympy==1.14.0`, `hypothesis==6.124.0`, `pytest==8.3.4` | All exact verifiers run purely on stdlib + NumPy + SymPy. |
| Node.js | `.github/workflows/*.yml` | Node `24.x` | Used for `tests/frontier_c3_browser_test.cjs` and `tests/independent_demo_test.cjs`. |
| C11 compiler | `scripts/dev.sh` | `gcc` or `clang` (`-std=c11 -Wall -Wextra`) | Sanitizers use `-fsanitize=address,undefined -fno-omit-frame-pointer`. |
| Paper build (optional) | `scripts/build_unified_paper.py` | XeLaTeX / TeX Live + Pandoc | Only needed when regenerating PDFs from `paper/unified-contextuality.md`. |

## Optional Environment Variables

| Variable | Default | Effect |
| --- | --- | --- |
| `COMPARATOR_BWRAP` | `bwrap` (on `PATH`) | Path to Linux `bubblewrap` executable used by sandboxed `lake comparator --paranoid`. |
| `HYPOTHESIS_PROFILE` | `default` | Standard Hypothesis profile selector when running `tests/test_properties.py`. |
| `LEAN_PATH` | Managed by `lake env` | Automatically configured by `lake`; never set manually. |

## Windows PowerShell Note

When working inside paths containing square brackets (e.g. `Z:\[Vibe Coded (AI)]\...`), pass `-LiteralPath` to PowerShell file cmdlets (`Test-Path -LiteralPath`, `Set-Location -LiteralPath`, `Get-Content -LiteralPath`) so `[...]` is not treated as a wildcard pattern.

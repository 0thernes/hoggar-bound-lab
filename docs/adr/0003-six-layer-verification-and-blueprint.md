# ADR 0003: Six-Kernel Comparator, Non-Vacuity Witnesses & Single-Site Blueprint

- **Date:** 2026-11-24
- **Status:** Accepted

## Context

Following Lean kernel soundness bug `#14576` (July 2026) and the November 2026 independent verification playbook audit (`DEFENSIBLE_INDEPENDENT_AI_RESEARCH_PLAYBOOK.md`), compiling under a single kernel is insufficient defense against metaprogramming hacks, silent definition drift, or vacuous hypotheses. In addition, running `leanblueprint new` naively would create a second GitHub Pages workflow colliding with `.github/workflows/independent-pages.yml` (Finding #15).

## Decision

1. Isolate headline target statements in `lean/HoggarBound/Challenge.lean`, match them in sorry-free `lean/HoggarBound/Solution.lean`, and verify them via `lake comparator --config comparator.json --paranoid` (all 6 bundled Lean 4.35.0 kernels: official C++, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
2. Add `lean/HoggarBound/NonVacuity.lean` with 10 explicit existential witness theorems proving every headline hypothesis bundle is non-vacuously inhabited, and lint all 14 new modules cleanly with Batteries `lake exe runLinter`.
3. Generate the declaration-checked Lean Blueprint (`blueprint/src/content.tex` + `scripts/build_blueprint.py`) directly into `build/independent-site/blueprint/` inside `scripts/independent_site.py`, preserving the single GitHub Pages deployment workflow.

## Consequences

- **Positive:** Eliminates single-kernel trust, statement-drift risk, vacuous-definition risk, and Pages workflow conflicts in one cohesive CI pipeline, while leaving all frozen files untouched.
- **Trade-off:** `Challenge.lean` intentionally holds `sorry` stubs (required by `lake comparator`), so forbidden-token CI scripts explicitly audit `Solution.lean` and all proof modules for zero `sorry` while exempting `Challenge.lean`.

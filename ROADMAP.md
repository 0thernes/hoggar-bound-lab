# Roadmap (`hoggar-bound-lab`)

## Completed Milestones (`v0.1.0` – `v1.9.0`)

- **v0.1.0 – v1.4.0:** Lean 4 spectral floor, saturated configurations (`75`, `480`, `729344`), 4-qubit C3 counterexample (`42` decls), all-qubit C3 family (`74` decls), unified paper and self-contained Conjecture E proof.
- **v1.5.0 – v1.7.0:** Lean 4 formalizations of Theorem 2 (Kramers), Theorems 3–4 (5-way saturation TFAE), Lemmas 20–21, Theorem 22, eigenvalue-multiset Theorem 19 across all 9 vertex cases (`N ≥ 4`), Clifford transport, Propositions 3/8/10, Corollary A asymptotics, and Proposition 16' QUBO SDP dual (`330`).
- **v1.8.0:** Theorem 16'' exact C3 binary optima (`368` and `344`, exact gap `24`), Theorem 13b infinite pure-CCZ determinant family `|Ψ_{3m}⟩` (`m ≥ 1`) + `N=6` degree `2,016` + 540.3M-form `N=9` cyclic census, classical `N=4..5` ladders/CSS witnesses/unconditional bounds (`1455`, `6444`) + independent 42-orbit C/Python verification (`100` newly audited Lean declarations).
- **v1.9.0 (current):** Six-layer Independent Scientist Verification Playbook & Build Standard v1.1.0 upgrade — `NonVacuity.lean` (`110` audited Lean declarations), isolated `Challenge.lean`/`Solution.lean` + `comparator.json` (`lake comparator --paranoid` across 6 kernels), Batteries `runLinter` clean, verbatim README 5-second `#print axioms` proof, Statement Fidelity Table, interactive Lean Blueprint (`/blueprint/`), ASan/UBSan C11 sanitizers, property/mutation/fuzz tests, citation & arithmetic audits, cross-platform CI, and SLSA `attest-build-provenance` release workflow.

## Open Scientific Frontiers

1. **In-kernel `d(Q⁻(7,2)) ≥ 315`:** Port the 42-orbit `W(5,2)` orbit classification and 42 pure-integer certificates (`src/w52_census_verify.c`, `data/q7minus_42_certs.json`) into Lean 4 so `exact_degrees_n4_n5_of_q7minus_315` becomes unconditional inside the kernel.
2. **Non-cyclic nine-qubit rank-8 trilinear forms:** Determine whether any non-cyclic alternating trilinear form on $\mathbb{F}_2^9$ has constant contraction rank 8.
3. **Full group-transitivity classification in Lean:** Formalize Jonah `[J3, Theorem B4]`'s single-orbit symplectic transitivity across hyperplane classes so Theorem 19 has zero remaining preprint citation dependencies.

## Open Governance, Legal & Publication Milestones (Owner-Controlled)

4. **Legal entity & licensing decision:** Resolve `0thernes LLC` formation vs. individual researcher attribution across `LICENSE`, `CITATION.cff`, and ORCID, and evaluate re-licensing code to `Apache-2.0` and text to `CC-BY-4.0` (unlocking Mathlib helper-lemma PRs and JOSS eligibility).
5. **External registration & review (release order):**
   1. Evaluate Zenodo AI-depositor eligibility (or use OSF/HAL identifier) and update ORCID by external identifier.
   2. Submit `Challenge.lean` / `Solution.lean` / `comparator.json` / `formalization.yaml` to Palomar Registry (requires `module` headers on submitted files).
   3. Engage Lean Zulip (`#new members`, `#maths`) with human-written questions and small Apache-2.0 helper lemmas for Mathlib.
   4. Obtain a personal `quant-ph` endorser and submit to arXiv / *Journal of Physics A* or *Quantum*.
   5. Optional final discoverability mirror on `ai.viXra.org` only after DOI/ORCID/blueprint are live.

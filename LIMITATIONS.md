# Limitations, Boundaries, and Real-vs-Metaphor

This repository separates **what is machine-checked inside Lean 4's kernel**, **what is verified by exact integer/symbolic computation**, **what is floating-point numerical exploration**, and **what remains open or requires human/legal action** (Build Standard B41).

## 1. Peer Review & External Scrutiny Status

- **Not externally peer reviewed.** No theorem, manuscript, or software module in this repository has undergone journal peer review, refereeing, or formal approval by arXiv, Zenodo, Palomar Registry, or any academic institution.
- **No external human line-by-line audit of v1.5.0–v1.9.0.** Lean 4.35.0 kernel checking (and multi-kernel `lake comparator --paranoid` replay) guarantees logical validity *of the formalized Lean statements* under `[propext, Classical.choice, Quot.sound]`, but does **not** automatically guarantee that every informal English sentence in the manuscript matches its Lean definition or literature anchor. See [docs/statement-fidelity.md](docs/statement-fidelity.md) for the explicit Lean-to-literature mapping.
- **Prior work includes non-peer-reviewed preprints.** B. W. Jonah's notes (`doi:10.5281/zenodo.23524332`, `doi:10.5281/zenodo.23538829`, and `[J1]`) are Zenodo preprints rather than peer-reviewed journal articles, and Cieśliński (`arXiv:2610.07172`) is an arXiv preprint. They are labeled as such throughout the paper.

## 2. Formalization & Computational Boundaries

| Area | Inside Lean 4 Kernel | Outside Lean 4 Kernel |
| --- | --- | --- |
| Spectral floor, Kramers floor, saturation TFAE, Props 3/8/10, asymptotics | Proved for all $N \ge 1$ / $N \ge 2$ (`Bound`, `Kramers`, `SaturationTheory`, `AuditUpgrades`) | State-to-mask identifications of finite Table 1 rows other than `|Ψ_{3m}⟩` (`flat_states.py`, `phase_states.py`); Propositions 4, 6, 9, 11; exhaustive enumerations of Theorems 12–13. |
| Infinite non-closed family `|Ψ_{3m}⟩` & $N=9$ search | Proved directly from the state vector for all $m \ge 1$ (`NormPhaseFamily.lean`) + concrete $N=6$ degree `2,016` (`SaturatedPhaseSix.lean`) | Exhaustive 540,299,769-form $N=9$ cyclic-symmetry rank-8 search (`src/n9_rank8_search.c`); **non-cyclic** nine-qubit rank-8 trilinear forms remain **open**. |
| Classical $N=4, 5$ exact degrees `(315, 1575, 6975)` | Transvection invariance, CSS witnesses (`315`, `1575`, `6975`), ladders, unconditional bounds `d(W(7,2)) >= 1455` and `d(Q^+(9,2)) >= 6444`, Lemmas L1 & L4, and master reduction (`ExactDegreesN4N5.lean`) | The from-scratch 42-orbit $W(5,2)$ census (`src/w52_census_verify.c`) and 42 pure-integer dual certificates (`scripts/exact_degrees_n4_n5.py`) independently reproducing Jonah `[J1]`'s $d(Q^-(7,2)) \ge 315$. |
| Four-qubit C3 & Conjecture E (all 9 cases, $N \ge 4$) | Exact binary optima `368` & `344` (`C3ExactOptima.lean`), all 9 vertex cases at eigenvalue-multiset level (`ConjectureE.lean`, `AuditUpgrades.lean`), cone lift (`ConjectureEExtras.lean`), Clifford transport (`AuditUpgrades.lean`) | Printed polynomial factorizations & continuous relaxation gap `32` (`frontier_c3_verify.py`); single-orbit group-transitivity classification of Jonah `[J3, Theorem B4]`. |
| Floating-point scripts | None (Lean uses exact `ℤ`/`ℚ`/`ℝ` algebra and kernel `decide`) | Scripts flagged `numerical_approximation` in [results/arithmetic-audit.json](results/arithmetic-audit.json) (e.g. `flat_states.py` using `1e-12` tolerance for state discovery or figure generation). No headline claim relies solely on float64. |

## 3. Real vs. Metaphor (No Quantum-Hardware Claims)

- All quantum-state simulations (`Moonlab`, `quantum_geometric_tensor`, `quantum_rng`, `Eshkol`, `c3-lab/`, `independent-review/`) execute on **classical CPUs/browsers**.
- Nothing in this repository is a quantum-hardware experiment, a Bell/KS loophole-free laboratory test, a demonstration of quantum computational advantage, or certified physical quantum randomness.

## 4. Known Governance, Legal & Provenance Findings (Classified per Build Standard R7)

The independent audit playbook (`DEFENSIBLE_INDEPENDENT_AI_RESEARCH_PLAYBOOK.md`, Nov 22–24, 2026) identified the following non-code findings that require explicit owner decisions rather than unilateral agent edits:

1. **`[problem]` Entity name `0thernes LLC`:** Earlier commits, `LICENSE`, `CITATION.cff`, `publication/c3-metadata-draft.json`, and the author's ORCID bio display `0thernes LLC` while legal entity formation remained pending as of Nov 19, 2026. Because `scripts/publication_release_audit.py` hash-locks `LICENSE` and `NOTICE` against frozen commit `d3811e3`, those files have not been unilaterally rewritten; resolving the corporate/individual affiliation is an owner legal action (`formalization.yaml` explicitly records this).
2. **`[issue]` Verification-only `LICENSE`:** The current `LICENSE` grants permission to build, run, study, and reproduce, but reserves commercial and modification redistribution rights. Re-licensing code to `Apache-2.0` and prose to `CC-BY-4.0` is an owner legal prerequisite for Mathlib upstreaming and JOSS submission.
3. **`[issue]` Unsigned commits and tags:** Historical commits and tags were pushed unsigned (`git %G? = N`). Build Standard R1 forbids commit/push gates; configuring local SSH/GPG signing keys (`git config gpg.format ssh`) is an optional owner action.
4. **`[conflict]` AI-assisted origin vs. external venue policies:** Full multi-agent AI involvement (`Claude/Anthropic`, `OpenAI Codex`, `Google Gemini / Antigravity`) is disclosed in `formalization.yaml` and `publication/AUTHOR-DECLARATIONS.md`. Zenodo's April 27, 2026 generative-AI policy, arXiv's `quant-ph` personal endorsement requirement, IOP ScholarOne authorship attestation, and Lean Zulip's human-written comment rule all require direct human evaluation and execution.
5. **`[issue]` Palomar `module` headers:** Lean 4.35.0 emits informational warnings on legacy non-`module` files importing Mathlib. Frozen Lean files (`d3811e3`, `87f08a0`, `5dcea35`) cannot be edited without breaking continuity audits; all new files stay well under Palomar's 10,000-line ceiling (longest file: 2,522 lines).

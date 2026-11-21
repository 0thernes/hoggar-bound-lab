# Index: where each claim is proved, tested and recorded

Repository version 1.8.0. For the terms see [GLOSSARY.md](GLOSSARY.md); for a non-technical overview see
[SUMMARY.md](SUMMARY.md); for the full text see the [unified paper](paper/unified-contextuality.md).

## Documents

| document | what it is |
|---|---|
| [README.md](README.md) | the front page: statement, attribution, layout, how to reproduce |
| [paper/unified-contextuality.md](paper/unified-contextuality.md) | the combined canonical paper, with [PDF](paper/unified-contextuality.pdf) and [HTML](paper/unified-contextuality.html) |
| [publication/unified-contextuality/](publication/unified-contextuality/) | combined LaTeX, arXiv source archive and Journal of Physics A manuscript/supplement |
| [publication/PAPER-MAP.md](publication/PAPER-MAP.md) | relation between the combined paper and preserved source studies |
| [publication/DISTRIBUTION-PLAN.md](publication/DISTRIBUTION-PLAN.md) | eight requested publication, indexing and preservation destinations |
| [paper/spectral-floor.md](paper/spectral-floor.md) | preserved spectral-floor source study, with [PDF](paper/spectral-floor.pdf) and [web page](https://0thernes.github.io/hoggar-bound-lab/paper/spectral-floor.html) |
| [publication/spectral-floor/](publication/spectral-floor/) | LaTeX source, typeset PDF, arXiv archive and submission sheets |
| [SUMMARY.md](SUMMARY.md) | plain-language summary |
| [GLOSSARY.md](GLOSSARY.md) | terms |
| [CHANGELOG.md](CHANGELOG.md), [VERSION](VERSION) | versions |
| [LEGAL.md](LEGAL.md), [LICENSE](LICENSE), [NOTICE](NOTICE) | licence, third-party notices, authorship and AI disclosure |
| [CITATION.cff](CITATION.cff) | how to cite |
| [lean/README.md](lean/README.md) | the Lean 4 development: modules, theorems, how to build and audit |
| [INDEPENDENT-REVIEW.md](INDEPENDENT-REVIEW.md) | the independent companion review (separate agent sessions) |
| [paper/c3-spectral-counterexample.md](paper/c3-spectral-counterexample.md) | the companion note on a four-qubit C3 instance (separate work, same repository) |

## C3 research and publication guide

- [C3 summary](docs/RESEARCH-SUMMARY.md): the explicit four-qubit pair and what it establishes.
- [Claim register](docs/CLAIMS.md): named C3 theorems, the 42-declaration audit, six stability declarations, the separately scoped 14 saturation declarations, for version 1.3.0 the 13 seven-qubit and 74 `CarrierFamily.lean` declarations, for version 1.4.0 the lemma checks of Theorem 19, and for versions 1.5.0–1.8.0 the **100** audited declarations of `VerifyNewFormalizations.lean` (Kramers, saturation, Propositions 3/8/10, asymptotics, Clifford transport, Lemmas 20–21, Theorem 22, eigenvalue-multiset Theorem 19 in all nine cases, Corollary 18, exact four-qubit C3 binary optima 368/344, Theorem 13b infinite determinant family + N=6 degree 2016, and N=4–5 CSS witnesses/ladders/unconditional bounds).
- [Verification guide](VERIFICATION.md): original-model connection, exact commands, evidence and measured proof-checking costs.
- [Affiliation records](publication/AFFILIATIONS.md): 0thernes LLC across prepared records and the observed state of each live service.
- [Publication status](publication/STATUS.md): public releases versus pending archive/journal steps.

## Claims and their evidence

"Lean" means the statement is a theorem checked by the Lean kernel; the file is under
`lean/HoggarBound/`. "Exact" means a program counts in integer arithmetic. Logs are under `results/`.

### The bound

| claim | Lean theorem | other checks | record |
|---|---|---|---|
| For every N ≥ 1, every set S of non-identity Pauli observables and every assignment: 6·(D−1)·β ≤ (D−2)·\|S\|·√((D−1)\|S\|) | `hoggar_bound` (`Bound.lean`) | trace identities on random data (`scripts/analysis.py`); 20-run falsification suite with a negative control (`scripts/run_falsify.sh`) | `lean-axioms.log`, `lean-audit.md`, `falsify.log`, `analysis.json` |
| Full N-qubit space: violated fraction ≥ 1/2 − √(D+1)/(D+2) and formal limit → 1/2 as N → ∞ | `full_space_fraction` (`Corollaries.lean`), `full_space_fraction_tendsto_half`, `hyperbolic_fraction_tendsto_half`, `full_space_violated_fraction_eventually_gt`, `elliptic_violated_fraction_eventually_gt` (`AuditUpgrades.lean`) | integer bound table (`build/hoggar table 6`) | `new-formalizations-lean-axioms.log`, `table.txt` |
| Three qubits: at least 63 of 315; four: at least 1451 of 5355; five: at least 28786 of 86955 | `three_qubit_contexts`, `four_qubit_contexts`, `five_qubit_contexts` | best assignments recounted from `data/witness/` | `falsify.log` |
| Four-qubit hyperbolic quadric: at least 315 of 1575; five-qubit: at least 6426 of 23715; unconditional Kramers-lifted ladders: W(7,2) ≥ 1455, Q⁺(9,2) ≥ 6444; CSS witnesses 315/1575/6975 & master reduction | `four_qubit_hyperbolic_contexts`, `five_qubit_hyperbolic_contexts` (`Quadric.lean`); `w72_ge_1455`, `q9plus_ge_6444`, `q7minus_css_witness`, `w72_css_witness`, `q9plus_css_witness`, `exact_degrees_n4_n5_of_q7minus_315` (`ExactDegreesN4N5.lean`) | `src/w52_census_verify.c` (42 orbits, 17,652,160 classes) + `scripts/exact_degrees_n4_n5.py` (9 pure-integer checks reproducing Jonah [J1]) | `new-formalizations-lean-axioms.log`, `exact_degrees_n4_n5.json` |
| Quaternionic / Kramers spectral floor & elliptic quadrics Q^-(2N-1,2) (Theorem 2): violated fraction >= 1/2 - sqrt(D+1)/(D+2); finite bounds 9, 291, 6501 | `hoggar_bound_quaternionic`, `elliptic_fraction`, `three_qubit_elliptic_contexts`, `four_qubit_elliptic_contexts`, `five_qubit_elliptic_contexts` (`Kramers.lean`) | integer bound table (`build/hoggar table 6`) | `new-formalizations-lean-axioms.log`, `table.txt` |

### Exact degrees (paper, Section 5)

| configuration | observables / contexts / degree | Lean theorem | other checks | record |
|---|---|---|---|---|
| four qubits, pivot configuration | 135 / 1095 / **75** | `pivot_degree`, `pivot_contexts` (`Saturated.lean`) | `scripts/flat_states.py` (exact); Moonlab S1–S3; QGTL; Eshkol | `lean-saturated-axioms.log`, `flat_states.json`, `moonlab_saturated.json` |
| five qubits, support of Cieśliński's state | 496 / 10880 / **480** | `cieslinski5_degree`, `cieslinski5_contexts` (`Saturated.lean`, counts in `SaturatedFive.lean`) | the same | the same |
| five qubits, support of the circuit state Φ5 | 496 / 10880 / **480** | `phase5_degree`, `phase5_contexts` (`SaturatedPhaseFive.lean`) | `scripts/phase_states.py` (exact); Moonlab (as a circuit); QGTL | `phase_states.json` |
| six qubits, pure-CCZ determinant state Ψ6 (`m = 2`, Theorem 13b) | 1008 / 45696 / **2016** | `det6_degree`, `det6_contexts` (`SaturatedPhaseSix.lean`), `infinite_nonclosed_saturated_family` (`NormPhaseFamily.lean`) | `scripts/norm_phase_family.py` (32 checks, `m = 1..4`) | `new-formalizations-lean-axioms.log`, `norm_phase_family.json` |
| infinite family of non-closed contextual pure-CCZ determinant states `Ψ_{3m}` (all `m ≥ 1`, Theorem 13b) | `(q³-1)q²` / `(q³-1)q⁴(q²+q-3)/6` / **`(q³-1)q³(q-1)(q-2)/12`** (`q = 2^m`) | `detPhase_isFlatState`, `detSupport_not_closed`, `infinite_nonclosed_saturated_family`, `infinite_nonclosed_family_contextual` (`NormPhaseFamily.lean`) | `scripts/norm_phase_family.py` (32 checks including full N=9 WHT: 32,704 pts, 24,070,144 ctx, d=915,712) | `new-formalizations-lean-axioms.log`, `norm_phase_family.json` |
| seven qubits, support of the circuit state Φ7 | 8128 / 2824192 / **729344** | `phase7_degree`, `phase7_contexts` (`SaturatedPhaseSeven.lean`, rows by `MaskRows.lean`); counts evaluated by the kernel | three programs without shared code: `scripts/phase_states.py` (Python, exact), `src/qgt_flat.c` (C), `src/moonlab_saturated.mjs` (JavaScript, from Moonlab's numbers) | `phase_states.json`, `moonlab_saturated_full7.log` |
| four-qubit hyperbolic quadric | 135 / 1575 / 315 | `quadric_degree` | `scripts/flat_states.py` | `flat_states.json` |
| three qubits, all observables | 63 / 315 / 63 | `hoggar_degree`; also `IndependentWitness.lean` | `scripts/flat_states.py` | the same |
| three qubits (CCZ state), two qubits (LLY state) | 28 / 56 / 0 and 12 / 8 / 0 | `ccz_degree`, `lly_degree` | `scripts/flat_states.py` | the same |

### Completion spectra and Conjecture E (paper, Section 8)

| claim | Lean theorem | other checks | record |
|---|---|---|---|
| Four-qubit C3 pair: equal carrier spectra, completion cubic traces 14976 and 15360 (Theorem 14) | `four_qubit_C3_spectral_counterexample` and 41 more (`C3Spectra.lean` and companions) | `scripts/frontier_c3_verify.py`, `scripts/frontier_c3_context_verify.py`, `scripts/cospectral_pair.py` | `frontier-c3-lean-audit.md`, `cospectral_pair.json` |
| Exact global binary completion minima of that pair: **368** and **344**, exact gap **24** (Corollary 16, Proposition 16', Theorem 16'') | `corollary16_sigmaA_exact_lower`, `corollary16_sigmaB_exact_lower`, `corollary16_exact_binary_optima` (`C3ExactOptima.lean`); plus `ConjectureEExtras.lean` & `AuditUpgrades.lean` | `scripts/c3_exact_optima_check.py` (10 pure-integer checks), `scripts/c3_sdp_dual_check.py` (15), `scripts/cospectral_pair.py` (30) | `new-formalizations-lean-axioms.log`, `c3_exact_optima_check.json`, `c3_sdp_dual_check.json`, `cospectral_pair.json` |
| Case C3 for every N >= 4: cospectral carriers, cubic traces differ by 3/2 8^(N-1) (Theorem 17) | `c3_strict_law_fails_general` (`CarrierFamily.lean`, 74 audited declarations) and `c3_strict_law_fails` (`ConjectureE.lean`, N >= 3) | `scripts/cospectral_family.py --six` (43), `scripts/cospectral_family_tensor_check.py` (18), `scripts/c3_sparse_search.py` | `lean-c3-all-qubits-axioms.log`, `new-formalizations-lean-axioms.log`, `cospectral_family.json`, `c3_sparse_search.json` |
| General cone lift ([J3, Lemma D (D2)]), case C11 for every N >= 4 (Corollary 18), and signed-Clifford orbit transport | `cone_lift_carrier_charpoly`, `cone_lift_completion_charpoly`, `cone_lift_completion_trace_cube`, `cone_lift_strict_law_fails`, `corollary18_c11_from_c3` (`ConjectureEExtras.lean`); `clifford_transport_strict_law_fails` (`AuditUpgrades.lean`) | `scripts/cospectral_family_cone_lift.py` (21) | `new-formalizations-lean-axioms.log`, `cospectral_family_cone_lift.json` |
| Conjecture E: all nine vertex cases, every N >= 4 (and N >= 3 for C1, C3, C6, C11), including canonical Hermitian eigenvalue multisets (Theorem 19) | `jonah_conjecture_e_all_nine_cases`, `c1_strict_law_fails`..`c15_strict_law_fails` (`ConjectureE.lean`, `ConjectureECones.lean`); `jonah_conjecture_e_all_nine_cases_spectra` (`AuditUpgrades.lean`) | `scripts/conjecture_e.py` (81, N = 3 to 5; argument `6`: 36 more, N = 6) | `new-formalizations-lean-axioms.log`, `conjecture_e.json`, `conjecture_e_n6.json` |
| Lemmas 20 and 21, Theorem 22 (universal cubic-trace identity) and Table 8 outside character sums | `lemma20_jordan_action`, `trace_completion_cube_universal`, `lemma21_trace_cube_sylvester`, `lemma21_trace_cube_symm`, `charSumOut_C1`..`charSumOut_C12_C15` (`ConjectureECore.lean`, `ConjectureECones.lean`) | `scripts/conjecture_e_lemmas.py` (115 + 46 at N = 6), `scripts/conjecture_e_trace_formula.py` (97 + 39 at N = 6 = 136) | `new-formalizations-lean-axioms.log`, `conjecture_e_lemmas.json`, `conjecture_e_lemmas_n6.json`, `conjecture_e_trace_formula.json`, `conjecture_e_trace_formula_n6.json` |

### Structure and classification (paper, Section 5.3)

| claim | how it is established | record |
|---|---|---|
| For a nonempty support, the floor is attained exactly when a flat state exists; combinatorial criterion and `(2^N - 1)|S| = square` (Theorems 3, 4) | Lean (`SaturationTheory.lean`: `opA_sq_eq`, `saturation_tfae`, `saturation_mul_isSquare`); condition (d) checked at every point of eleven states | `new-formalizations-lean-axioms.log`, `flat_states.json`, `phase_states.json` |
| Quantum metric and Berry curvature criteria for violated contexts and flat states (Propositions 3, 8) | Lean (`AuditUpgrades.lean`: `proposition3_violated_iff`, `proposition3_satisfied_iff`, `proposition8_flat_state_qgt`); QGTL numerical checks | `new-formalizations-lean-axioms.log`, `qgt_hoggar.log`, `run_all.log` |
| The support of a flat state is a two-character set with exact hyperplane intersection sizes (Proposition 10) | Lean (`AuditUpgrades.lean`: `pure_state_pauli_sq_transform`, `proposition10_two_character_sum`, `proposition10_hyperplane_card`); checked for eleven states | `new-formalizations-lean-axioms.log`, `phase_states.json` |
| Phase states of the third level are flat exactly when a trilinear form has constant rank (Proposition 11) | proof in the paper; support structure checked for five states | `phase_states.json` |
| All such states with nonzero associated trilinear form on up to five qubits (Theorem 12): none on four, one class on five | exhaustive enumeration, 33 554 431 forms for five qubits (`src/third_level.c`); second implementation for N ≤ 4 (`scripts/phase_states.py`) | `run_all.log` |
| The support of Φ5 is Clifford-equivalent to the support of Cieśliński's state | explicit symplectic map, verified on all 1023 points | `phase_states.json` |
| Seven qubits: one class in the family with B alternating of rank 6, stabilizer of order 7 (Theorem 13) | exhaustive enumeration of 1.46 × 10^10 forms (`src/family7.c`), orbit computation (`src/orbits7.c`); count agrees with orbit size | `family7.log` |
| Seven qubits, other types of B: none found | random census, 3 × 10^8 forms per type (`src/sample7.c`). Evidence, not proof | `family7.log` |

### The demonstration on the Tsotchke stack (combined paper, Section 10)

| what | program | record |
|---|---|---|
| State-independent contextuality test for two, three and four qubits, with noise | `src/moonlab_experiment.mjs` | `moonlab_experiment.json` |
| Eight flat states; Φ5 and Φ7 prepared as circuits; every context of the four- and five-qubit configurations measured; noise against exact ceilings | `src/moonlab_saturated.mjs` | `moonlab_saturated.json` |
| All 2 824 192 contexts of the seven-qubit configuration measured once | `src/moonlab_saturated.mjs --full7` | `moonlab_saturated_full7.log` |
| Quantum metric and Berry curvature of the flat states; violated contexts read off the metric | `src/qgt_hoggar.c`, `src/qgt_flat.c` | `qgt_hoggar.log`, `run_all.log` |
| Independent re-implementation and automatic differentiation | `src/eshkol/hoggar.esk`, `src/eshkol/saturated.esk` | `eshkol.log` |

## Continuous integration

| workflow | what it runs |
|---|---|
| [Saturated configurations](.github/workflows/saturated-configurations.yml) | the exact checks of Section 5 and the Lean build of the exact degrees, with an axiom allowlist |
| [Independent verification](.github/workflows/independent-verification.yml) | the independent companion checks, the core Lean proof and the companion Lean certificates |
| [Case C3 for every number of qubits](.github/workflows/c3-all-qubits.yml) | `CarrierFamily.lean` with an axiom allowlist, and the exact checks of the carrier families, of Conjecture E and of Lemmas 20 and 21 (paper, Section 11.3) |
| [Conjecture E (all 9 cases), Kramers floor & saturation Lean 4 audit](.github/workflows/conjecture-e-all-cases.yml) | All 12 v1.5.0–v1.8.0 Lean modules with **100-declaration** axiom allowlist (`VerifyNewFormalizations.lean`), plus `scripts/conjecture_e_trace_formula.py` (136 checks), `scripts/c3_sdp_dual_check.py` (15 checks), `scripts/c3_exact_optima_check.py` (10 checks), `scripts/norm_phase_family.py` (32 checks), and `scripts/exact_degrees_n4_n5.py` (9 checks) |

## What is not proved

Listed in the combined paper, Sections 9 ("Formal verification and its boundary") and 12, and in the README under "What is and
is not claimed". In short: nothing is peer reviewed; state-to-mask identifications of Table 1, Propositions 4, 6, 9 and 11,
and the single-orbit group-transitivity classification of Jonah [J3, Theorem B4] remain outside Lean; the enumerations of
Theorems 12 and 13 are exact computations; and novelty rests on a bounded search.

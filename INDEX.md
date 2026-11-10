# Index: where each claim is proved, tested and recorded

Version 1.1.1. For the terms see [GLOSSARY.md](GLOSSARY.md); for a non-technical overview see
[SUMMARY.md](SUMMARY.md); for the full text see the [paper](paper/spectral-floor.md).

## Documents

| document | what it is |
|---|---|
| [README.md](README.md) | the front page: statement, attribution, layout, how to reproduce |
| [paper/spectral-floor.md](paper/spectral-floor.md) | the paper (canonical source), with [PDF](paper/spectral-floor.pdf) and [web page](https://0thernes.github.io/hoggar-bound-lab/) |
| [publication/spectral-floor/](publication/spectral-floor/) | LaTeX source, typeset PDF, arXiv archive and submission sheets |
| [SUMMARY.md](SUMMARY.md) | plain-language summary |
| [GLOSSARY.md](GLOSSARY.md) | terms |
| [CHANGELOG.md](CHANGELOG.md), [VERSION](VERSION) | versions |
| [LEGAL.md](LEGAL.md), [LICENSE](LICENSE), [NOTICE](NOTICE) | licence, third-party notices, authorship and AI disclosure |
| [CITATION.cff](CITATION.cff) | how to cite |
| [lean/README.md](lean/README.md) | the Lean 4 development: modules, theorems, how to build and audit |
| [INDEPENDENT-REVIEW.md](INDEPENDENT-REVIEW.md) | the independent companion review (separate agent sessions) |
| [paper/c3-spectral-counterexample.md](paper/c3-spectral-counterexample.md) | the companion note on a four-qubit C3 instance (separate work, same repository) |

## Claims and their evidence

"Lean" means the statement is a theorem checked by the Lean kernel; the file is under
`lean/HoggarBound/`. "Exact" means a program counts in integer arithmetic. Logs are under `results/`.

### The bound

| claim | Lean theorem | other checks | record |
|---|---|---|---|
| For every N ≥ 1, every set S of non-identity Pauli observables and every assignment: 6·(D−1)·β ≤ (D−2)·\|S\|·√((D−1)\|S\|) | `hoggar_bound` (`Bound.lean`) | trace identities on random data (`scripts/analysis.py`); 20-run falsification suite with a negative control (`scripts/run_falsify.sh`) | `lean-axioms.log`, `lean-audit.md`, `falsify.log`, `analysis.json` |
| Full N-qubit space: violated fraction ≥ 1/2 − √(D+1)/(D+2), every N | `full_space_fraction` (`Corollaries.lean`) | integer bound table (`build/hoggar table 6`) | `table.txt` |
| Three qubits: at least 63 of 315; four: at least 1451 of 5355; five: at least 28786 of 86955 | `three_qubit_contexts`, `four_qubit_contexts`, `five_qubit_contexts` | best assignments recounted from `data/witness/` | `falsify.log` |
| Four-qubit hyperbolic quadric: at least 315 of 1575; five-qubit: at least 6426 of 23715 | `four_qubit_hyperbolic_contexts`, `five_qubit_hyperbolic_contexts` (`Quadric.lean`) | the same | `falsify.log` |

### Exact degrees (paper, Section 5)

| configuration | observables / contexts / degree | Lean theorem | other checks | record |
|---|---|---|---|---|
| four qubits, pivot configuration | 135 / 1095 / **75** | `pivot_degree`, `pivot_contexts` (`Saturated.lean`) | `scripts/flat_states.py` (exact); Moonlab S1–S3; QGTL; Eshkol | `lean-saturated-axioms.log`, `flat_states.json`, `moonlab_saturated.json` |
| five qubits, support of Cieśliński's state | 496 / 10880 / **480** | `cieslinski5_degree`, `cieslinski5_contexts` (`Saturated.lean`, counts in `SaturatedFive.lean`) | the same | the same |
| five qubits, support of the circuit state Φ5 | 496 / 10880 / **480** | `phase5_degree`, `phase5_contexts` (`SaturatedPhaseFive.lean`) | `scripts/phase_states.py` (exact); Moonlab (as a circuit); QGTL | `phase_states.json` |
| seven qubits, support of the circuit state Φ7 | 8128 / 2824192 / **729344** | lower bound: `hoggar_bound` with \|S\| = 8128. The counts of contexts and violated contexts are **not** kernel-checked | three programs without shared code: `scripts/phase_states.py` (Python, exact), `src/qgt_flat.c` (C), `src/moonlab_saturated.mjs` (JavaScript, from Moonlab's numbers) | `phase_states.json`, `moonlab_saturated_full7.log` |
| four-qubit hyperbolic quadric | 135 / 1575 / 315 | `quadric_degree` | `scripts/flat_states.py` | `flat_states.json` |
| three qubits, all observables | 63 / 315 / 63 | `hoggar_degree`; also `IndependentWitness.lean` | `scripts/flat_states.py` | the same |
| three qubits (CCZ state), two qubits (LLY state) | 28 / 56 / 0 and 12 / 8 / 0 | `ccz_degree`, `lly_degree` | `scripts/flat_states.py` | the same |

### Structure and classification (paper, Section 5.3)

| claim | how it is established | record |
|---|---|---|
| The floor is attained exactly when a flat state exists; combinatorial criterion (Theorems 3, 4) | proof in the paper; condition (d) checked at every point of eleven states | `flat_states.json`, `phase_states.json` |
| The support of a flat state is a two-character set (Proposition 10) | proof in the paper; checked for eleven states | `phase_states.json` |
| Phase states of the third level are flat exactly when a trilinear form has constant rank (Proposition 11) | proof in the paper; support structure checked for five states | `phase_states.json` |
| All such states on up to five qubits (Theorem 12): none on four, one class on five | exhaustive enumeration, 33 554 431 forms for five qubits (`src/third_level.c`); second implementation for N ≤ 4 (`scripts/phase_states.py`) | `run_all.log` |
| The support of Φ5 is Clifford-equivalent to the support of Cieśliński's state | explicit symplectic map, verified on all 1023 points | `phase_states.json` |
| Seven qubits: one class in the family with B alternating of rank 6, stabilizer of order 7 (Theorem 13) | exhaustive enumeration of 1.46 × 10^10 forms (`src/family7.c`), orbit computation (`src/orbits7.c`); count agrees with orbit size | `family7.log` |
| Seven qubits, other types of B: none found | random census, 3 × 10^8 forms per type (`src/sample7.c`). Evidence, not proof | `family7.log` |

### The demonstration on the Tsotchke stack (paper, Section 9)

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

## What is not proved

Listed in the paper, Sections 8 ("What is not formalized") and 11, and in the README under "What is and
is not claimed". In short: nothing is peer reviewed; the quaternionic refinement, the equivalences of
Theorems 3 and 4 and the propositions about states are proved on paper only; the enumerations are
computations; the seven-qubit counts are not kernel-checked; novelty rests on a bounded search.

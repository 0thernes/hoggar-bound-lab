# Hoggar Bound Lab

One combined study of spectral bounds and their limits in Pauli contextuality: a Lean-checked
general bound, configurations that attain it, and explicit sign carriers showing that equal carrier
spectra need not determine equal completion spectra, in every vertex case of Jonah's classification
and for every number of qubits from four on, which proves Jonah's Conjecture E. Reproducible
experiments use Moonlab, quantum_geometric_tensor, quantum_rng and Eshkol.

[![Saturated configurations](https://github.com/0thernes/hoggar-bound-lab/actions/workflows/saturated-configurations.yml/badge.svg)](https://github.com/0thernes/hoggar-bound-lab/actions/workflows/saturated-configurations.yml)
[![Independent verification](https://github.com/0thernes/hoggar-bound-lab/actions/workflows/independent-verification.yml/badge.svg)](https://github.com/0thernes/hoggar-bound-lab/actions/workflows/independent-verification.yml)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0-blue)](lean/README.md)
[![Case C3 for every number of qubits](https://github.com/0thernes/hoggar-bound-lab/actions/workflows/c3-all-qubits.yml/badge.svg)](https://github.com/0thernes/hoggar-bound-lab/actions/workflows/c3-all-qubits.yml)
[![Version 1.3.0](https://img.shields.io/badge/version-1.3.0-informational)](CHANGELOG.md)

**Unified paper:** [Spectral bounds and their limits in Pauli contextuality](paper/unified-contextuality.md) ([PDF](paper/unified-contextuality.pdf), [HTML](https://0thernes.github.io/hoggar-bound-lab/paper/unified-contextuality.html)).
&nbsp;·&nbsp; **Proofs:** [lean/README.md](lean/README.md)
&nbsp;·&nbsp; **Independent review:** [INDEPENDENT-REVIEW.md](INDEPENDENT-REVIEW.md)

**Start here:** [SUMMARY.md](SUMMARY.md) (plain language) · [INDEX.md](INDEX.md) (every claim, with its proof, test and log) ·
[GLOSSARY.md](GLOSSARY.md) · [CHANGELOG.md](CHANGELOG.md) · [LEGAL.md](LEGAL.md) · [CITATION.cff](CITATION.cff)

Status: research preprint, repository version 1.3.0, 10 November 2026. Not peer reviewed. AI-generated under human
direction. Author: Alexander S. Donahue, 0thernes LLC ([ORCID 0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648)).

**New in 1.3.0** (paper Sections 8.5 to 8.8 and 9.3; first recorded in the addenda under
[publication/](publication/)):

* **Conjecture E is true** (Theorem 19). In all nine vertex cases of
  [Jonah's note](https://doi.org/10.5281/zenodo.23524332) and for every $N \ge 4$ there are two sign
  carriers with the same carrier spectrum and different completion spectra. The carriers come from graphs
  with one edge for each nonzero difference, over the real, complex and quaternionic numbers, and from a
  pair swap for cones. Outside case C3 the proof is on paper, uses Theorems A and B3 of the note, and is
  checked by exact computation for three to six qubits (`python scripts/conjecture_e.py`, 81 checks, and
  `python scripts/conjecture_e.py 6`, 36 checks).
* **Case C3 for every number of qubits, in Lean** (Theorem 17): `c3_strict_law_fails_general` in
  [lean/HoggarBound/CarrierFamily.lean](lean/HoggarBound/CarrierFamily.lean), about the library's own
  Pauli matrices, real quadric and context signs; 74 audited declarations, standard axioms only. Case
  C11 follows by the note's cone lift (Corollary 18).
* **The binary completion minima of the four-qubit pair differ** (Corollary 16): at least 347 against at
  most 344 violated outside contexts.
* **The seven-qubit degree 729344 is a Lean theorem** (`phase7_degree`), with kernel-evaluated counts.

**Research website:** [Hoggar Bound Lab](https://0thernes.github.io/hoggar-bound-lab/).
The [C3 research summary](docs/RESEARCH-SUMMARY.md), [verification guide](VERIFICATION.md),
and [claim register](docs/CLAIMS.md) connect the four-qubit spectral result to exact data and Lean theorem names.
The combined manuscript editions `v1.2.0` and `v1.3.0` preserve the C3 scientific paper and proof artifacts in
[v0.2.0-c3-certificate](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v0.2.0-c3-certificate).
See the [source-paper map](publication/PAPER-MAP.md) and [eight-destination distribution plan](publication/DISTRIBUTION-PLAN.md).
See [affiliation records](publication/AFFILIATIONS.md) for confirmed platform updates and remaining account steps.

**C3 component and preserved source paper:** [Cospectral Pauli carriers with different completion spectra](paper/c3-spectral-counterexample.md)
([PDF](paper/c3-spectral-counterexample.pdf), [working exact-certificate demo](https://0thernes.github.io/hoggar-bound-lab/c3-lab/)).
Two explicit four-qubit sign carriers have the same characteristic polynomial, while their completion
cubic traces are 14976 and 15360. This establishes the four-qubit C3 instance left open in
[Jonah's Conjecture E, v0.5](https://zenodo.org/records/23524332).
The [Lean spectral theorem](lean/HoggarBound/C3Spectra.lean) and [42-declaration axiom audit](results/frontier-c3-lean-audit.md)
verify the Pauli-model connection, carrier cospectrality and completion noncospectrality. Independent integer
checks and an Eshkol execution record accompany the paper. This finite result is separate from the previously known spectral floor below,
and does not establish historical priority; the combined paper extends it to every dimension and every vertex case (see above).

**Configurations that attain the floor** ([unified paper](paper/unified-contextuality.md), Section 5). The bound
below holds for arbitrary sets of observables. For a nonempty set, saturation is equivalent to a pure
state having Pauli expectation values of one nonzero modulus on the set and zero elsewhere. Three such configurations outside the
classical families, with their exact contextuality degrees:

| qubits | state | observables | contexts | contextuality degree | how the degree is proved |
|---|---|---|---|---|---|
| 4 | equal superposition of the basis states 0011, 0111, 1011, 1100, 1101 and $i$ times 1110 | 135 | 1095 | **75** | Lean (`pivot_degree`) |
| 5 | CS(0,1) CS(1,3) CS(2,4) CCZ(0,1,4) CCZ(0,2,3) applied to the all-plus state | 496 | 10880 | **480** | Lean (`phase5_degree`, `cieslinski5_degree`) |
| 7 | three CS and eight CCZ gates applied to the all-plus state (Theorem 13) | 8128 | 2824192 | **729344** | Lean (`phase7_degree`) |

The five-qubit configuration is, up to a Clifford operation, the Pauli support of a state found
numerically by Cieśliński (arXiv:2610.07172). Its circuit description, the classification of all such
circuit states with nonzero associated trilinear form on up to five qubits (none on four, one class on five) and the seven-qubit state are new
to our knowledge, which rests on a bounded literature search. Nothing here has been peer reviewed.

## The statement

Take $N$ qubits, $D = 2^N$. Give every Pauli observable in a set $S$ a value $+1$ or $-1$. A *context*
is three mutually commuting observables of $S$ whose product is $\pm I$; quantum mechanics fixes the
sign of the product of their values. Then, for every $S$ and every assignment,

```math
\#\text{satisfied} - \#\text{violated} \;\le\; \frac{(D-2)\,|S|^{3/2}}{6\sqrt{D-1}} .
```

For $N \ge 2$, using all $4^N - 1$ observables means at least the fraction $\tfrac12 - \sqrt{D+1}/(D+2)$ of the
contexts is violated: 63 of 315 for three qubits (exact), at least 1451 of 5355 for four, at least
28786 of 86955 for five, and the fraction tends to one half.

## Whose result this is

The inequality was first posted by **B. W. Jonah** on 21 October 2026 as the *spectral floor*
([doi:10.5281/zenodo.23538829](https://doi.org/10.5281/zenodo.23538829)); the exact four- and
five-qubit values 315, 1575 and 6975 are his computer-assisted results
([doi:10.5281/zenodo.23510634](https://doi.org/10.5281/zenodo.23510634)); the value 315 for the
four-qubit hyperbolic quadric is due to Li, Gupta and Ganesh (arXiv:2610.26465); the scalar inequality
is Okumura's lemma (1974). We found the bound independently on 9 November 2026 and learned of the
earlier notes during our own literature audit the same day.

What this repository adds:

* a complete **Lean 4 proof** for every $N \ge 1$ and arbitrary sets of observables, about the explicit
  complex Pauli matrices, with no axioms beyond `propext`, `Classical.choice`, `Quot.sound`;
* **formally verified corollaries**, including the first kernel-checked proof we know of that the
  five-qubit hyperbolic quadric has degree greater than 4743 (at least 6426);
* an **independent reproduction** of the best known assignments for two to five qubits, of the
  geometry of their violated contexts, and of the three cases where the bound is attained;
* the **state-independent contextuality experiment** run end to end on a simulator;
* **exact contextuality degrees outside the classical families**: 75 (four qubits, 1095 contexts) and 480
  (five qubits, 10880 contexts) proved in Lean, lower bound and witness, and 729344 (seven qubits,
  2824192 contexts) from the Lean inequality and exact counts;
* a **criterion and a classification**: which states built from T, controlled-S and CCZ gates on the
  all-plus state have a single non-zero Pauli modulus, exhaustively for up to five qubits; and the fact
  that the Pauli support of any such state is a two-character set (the support of a bent function in the
  three-, five- and seven-qubit cases).

## Layout

| path | what |
|---|---|
| `lean/HoggarBound/` | the Lean 4 development (`Moment`, `Pauli`, `Bound`, `Counting`, `Corollaries`, `Quadric`; the exact degrees `MaskConfig`, `Saturated`, `SaturatedFive`, `SaturatedPhaseFive` with generated data `FlatData`, `PhaseData`; plus the independently written `IndependentContexts`, `IndependentWitness`) |
| `src/hoggar.c` | engine: geometry, exact integer bounds, verification, annealing search, falsification harness |
| `src/moonlab_experiment.mjs` | the experiment on Moonlab (WebAssembly) |
| `src/qgt_hoggar.c` | quantum geometric tensor of the Hoggar state with the QGTL kernels |
| `src/eshkol/hoggar.esk`, `src/eshkol/saturated.esk` | independent re-implementations and automatic-differentiation checks in Eshkol |
| `scripts/flat_states.py`, `scripts/phase_states.py` | exact integer verification of the eleven flat states of the paper (68 + 81 checks); they generate the Lean data |
| `src/third_level.c` | exhaustive census of flat third-level phase states on up to five qubits (seven seconds) |
| `src/moonlab_saturated.mjs`, `src/qgt_flat.c` | the flat states on Moonlab (two of them as circuits) and under the QGTL kernels |
| `src/family7.c`, `src/orbits7.c`, `src/sample7.c`, `scripts/run_family7.sh` | the seven-qubit enumeration (about eight core-hours) and its orbit analysis |
| `scripts/` | `build.sh`, `run_all.sh`, `analysis.py`, `ladder.py`, `run_falsify.sh`, `build_paper.py`, `check_github_math.py`, `fix_github_math.py` |
| `data/witness/`, `data/flat/` | assignments (hex masks) for every classical configuration up to five qubits; supports and optimal signs of the flat states |
| `results/` | logs and JSON written by the runs |
| `third_party/` | vendored Moonlab engine, quantum_rng and one QGTL source file, with licences and provenance |
| `independent-review/`, `tests/`, `results/*audit*` | the independent companion review |

## Reproduce

```bash
bash scripts/build.sh
```

```bash
bash scripts/run_all.sh
```

```bash
cd lean && lake exe cache get && lake build
```

The exact degrees of Section 5 are separate Lean targets (kernel evaluations; about a quarter of an hour
for each of the two five-qubit configurations):

```bash
cd lean && lake build HoggarBound.Saturated HoggarBound.SaturatedPhaseFive && lake env lean SaturatedVerification.lean
```

`run_all.sh` needs gcc, Python 3 with NumPy and Matplotlib, and Node; Eshkol is optional. It prints one
line per stage and ends with `ALL STAGES PASSED`; the last complete run is kept in
[results/run_all.log](results/run_all.log) and [results/falsify.log](results/falsify.log). The Lean
build needs [elan](https://github.com/leanprover/elan); it downloads Lean 4.35.0 and the Mathlib cache.

## What is and is not claimed

* The Lean theorems are exactly what their statements say; comments are not theorems.
* Lower bounds are proved. Upper bounds are explicit assignments that anyone can recount.
  Optimality of the four- and five-qubit assignments of the classical families is not proved here,
  except for the four-qubit hyperbolic quadric.
* For the configurations of Section 5 both bounds are proved in Lean up to five qubits. The seven-qubit
  degree uses the Lean inequality with counts made by three independent programs, not by the kernel. The
  uniqueness statement for seven qubits is proved by enumeration inside one family of forms only.
* Novelty of the Section 5 results is claimed to the extent of a bounded literature search.
* The quaternionic refinement for elliptic quadrics is proved on paper and tested numerically only.
* Moonlab is a classical simulator; quantum_rng is a classical "quantum-inspired" generator; only the
  `diffgeo_*` kernels of QGTL are used. Nothing here is a measurement on quantum hardware.
* No priority is claimed for the bound, for its saturation by Hoggar states, or for the exact values.

## Corrections

If you find an error in a statement, a proof or a count, please open an issue on this repository or
write to 0_0@0thernes.art. A pointer to earlier work that already contains one of the results of
Section 5 is especially welcome.

## Licence

Copyright © 2026 0thernes LLC. See [LICENSE](LICENSE) and [LEGAL.md](LEGAL.md). Third-party components
keep their MIT licences ([NOTICE](NOTICE)).

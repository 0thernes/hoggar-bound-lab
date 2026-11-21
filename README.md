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
[![Conjecture E all 9 cases Lean 4 audit](https://github.com/0thernes/hoggar-bound-lab/actions/workflows/conjecture-e-all-cases.yml/badge.svg)](https://github.com/0thernes/hoggar-bound-lab/actions/workflows/conjecture-e-all-cases.yml)
[![Version 1.8.0](https://img.shields.io/badge/version-1.8.0-informational)](CHANGELOG.md)

**Unified paper:** [Spectral bounds and their limits in Pauli contextuality](paper/unified-contextuality.md) ([PDF](paper/unified-contextuality.pdf), [HTML](https://0thernes.github.io/hoggar-bound-lab/paper/unified-contextuality.html)).
&nbsp;·&nbsp; **Proofs:** [lean/README.md](lean/README.md)
&nbsp;·&nbsp; **Independent review:** [INDEPENDENT-REVIEW.md](INDEPENDENT-REVIEW.md)

**Start here:** [SUMMARY.md](SUMMARY.md) (plain language) · [INDEX.md](INDEX.md) (every claim, with its proof, test and log) ·
[GLOSSARY.md](GLOSSARY.md) · [CHANGELOG.md](CHANGELOG.md) · [LEGAL.md](LEGAL.md) · [CITATION.cff](CITATION.cff)

Status: research preprint, repository version 1.8.0, 21 November 2026. Not peer reviewed. AI-generated under human
direction. Author: Alexander S. Donahue, 0thernes LLC ([ORCID 0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648)).

**New in 1.8.0** (paper Sections 5.1, 5.3, 6, 7, 8.5, 9.4, 11.3, 12; `VerifyNewFormalizations.lean` expanded to **100** audited declarations strictly within `[propext, Classical.choice, Quot.sound]`):

* **Theorem 16'' — Exact global binary completion optima of four-qubit C3 (`368` and `344`, exact gap `24`).** `C3ExactOptimaData.lean` and `C3ExactOptima.lean` close BOTH remaining gaps (`[347, 368]` and `[330, 344]`) to zero inside Lean 4's kernel via pure-integer MET-SDP frustrated-triangle dual certificates (421 and 442 cuts, lower-triangular integer Cholesky + Gershgorin diagonal dominance, zero floating point): `corollary16_exact_binary_optima` proves $\min_y F(\sigma_0,y)=368$ and $\min_y F(\sigma_1,y)=344$. Independently verified by `python scripts/c3_exact_optima_check.py` (10 of 10 checks including 4 negative controls; [results/c3_exact_optima_check.json](results/c3_exact_optima_check.json)).
* **Theorem 13b — Infinite non-closed contextual floor-saturating family (`NormPhaseFamily.lean`, `SaturatedPhaseSix.lean`).** Settles the open problem of building an infinite family of non-closed contextual configurations attaining the spectral floor: for every $m\ge1$ ($N=3m$, $q=2^m$), the pure-CCZ determinant phase state $`|\Psi_{3m}\rangle`$ of $`\operatorname{Tr}_{\mathbb F_q/\mathbb F_2}(x_1x_2x_3)`$ is proved directly in Lean 4 to be flat on a strictly non-closed support of size $(q^3-1)q^2$ with exact degree $\tfrac1{12}(q^3-1)q^3(q-1)(q-2)$ (strictly positive for every $m\ge2$), alongside the kernel-checked six-qubit ($m=2$, 6 CCZ) certificate (`det6_degree`: 1,008 observables, 45,696 contexts, exact degree **2,016**) and exact checks through $m=4$ (`python scripts/norm_phase_family.py`, 32 of 32 checks). An exhaustive C census (`src/n9_rank8_search.c`, `results/n9_rank8_search.tsv`) rules out constant rank 8 on nine qubits across all 25 cyclic-invariant subspaces of $GL(9,2)$ (540,299,769 forms, 0 hits).
* **Classical $N=4, 5$ exact ladders, CSS witnesses, unconditional Lean bounds & independent 42-orbit verification (`ExactDegreesN4N5.lean`, `src/w52_census_verify.c`, `scripts/exact_degrees_n4_n5.py`).** Lean 4 proves symplectic transvection invariance (`transv_violatedLines_eq`), exact CSS witnesses (315, 1575, 6975), double-counting ladders ($`Q^-(7,2)\to W(7,2)\to Q^+(9,2)`$), **unconditional Kramers-lifted bounds $d(W(7,2))\ge1455$ and $d(Q^+(9,2))\ge6444$**, pigeonhole Lemmas L1 & L4, and the exact master reduction to $d(Q^-(7,2))\ge315$, paired with a clean from-scratch C census (42 orbits, 17,652,160 classes) and pure-integer 42-orbit dual certification (9 of 9 checks, zero floating point) reproducing Jonah's [J1] exact triple $(315, 1575, 6975)$.
* **Refreshed v1.8.0 submission packets (`publication/`).** All prepared submission packets, cover texts, arXiv source archive, 1,897-char plain abstract, BibTeX, and metadata synchronized to v1.8.0 with full AI disclosure and explicit verification boundaries.

**New in 1.7.0** (paper Sections 4, 5, 6, 8.5, 8.7, 9.4, 11.3):

* **Proposition 16' — Tightened QUBO SDP-dual lower bound for four-qubit C3 (`315 -> 330`).** Using the exact zero-sum geometric shift $`d_{16}(p\bmod4)\in\{-40,+8,+8,+24\}`$ on the four 16-point orbits of $`\Lambda_{\sigma_1}`$, `AuditUpgrades.lean` proves **`330 <= min_y F(sigma_1, y) <= 344`** (halving the uncertainty interval from 29 to 14 integers and hitting the exact ceiling of the full 64-variable elliptope SDP dual $329.8560\ldots$) alongside **`347 <= min_y F(sigma_0, y) <= 368`** (where $d=0$ is already optimal). Independently checked by `python scripts/c3_sdp_dual_check.py` (15 of 15 exact integer/SymPy checks; [results/c3_sdp_dual_check.json](results/c3_sdp_dual_check.json)).
* **Six additional formalization gaps closed in Lean 4.35.0 (`lean/HoggarBound/AuditUpgrades.lean`, 2,042 lines; `VerifyNewFormalizations.lean` expanded to 77 audited declarations):**
  - Asymptotic `Filter.Tendsto` limit theorems for Corollary A ($d/L\to1/2$ for full space, hyperbolic, and elliptic quadrics);
  - Quantum-metric and Berry-curvature criteria (Propositions 3 and 8) and the two-character hyperplane-intersection theorem (Proposition 10);
  - Signed-Clifford / symplectic orbit transport of carrier and completion characteristic polynomials (`clifford_transport_strict_law_fails`);
  - Full canonical Hermitian eigenvalue-multiset upgrade of Theorem 19 across all nine vertex cases (`jonah_conjecture_e_all_nine_cases_spectra`).
* **Six-qubit Theorem 22 verification & software/typesetting audit.** `python scripts/conjecture_e_trace_formula.py 6` verifies Theorem 22 and Table 8 across all nine vertex cases at 6 qubits (**39 of 39 checks**, 136 total across $N=3\text{–}6$; [results/conjecture_e_trace_formula_n6.json](results/conjecture_e_trace_formula_n6.json)); repaired Python script warnings/dependencies (`check_github_math.py`, `fix_github_math.py`, `analysis.py`, `ladder.py`) and TeX equation/URL overflows.

**New in 1.5.0 and 1.6.0** (paper Sections 3, 4, 5.1, 8.5–8.7, and 9.4):

* **Complete Lean 4.35.0 formalization of Conjecture E (all 9 vertex cases), Kramers floor, saturation equivalences, and Corollaries 16 & 18.** Together with `AuditUpgrades.lean`, seven sorry-free Lean modules (9,728 lines total; 77 audited declarations in [lean/VerifyNewFormalizations.lean](lean/VerifyNewFormalizations.lean), strictly within `[propext, Classical.choice, Quot.sound]`, zero `native_decide` or custom axioms) prove:
  - **Theorem 2** (`Kramers.lean`): quaternionic / Kramers spectral floor (`hoggar_bound_quaternionic`) and elliptic quadrics $Q^-(2N-1,2)$ (`elliptic_fraction`, plus finite bounds 9, 291, 6501).
  - **Theorems 3 & 4** (`SaturationTheory.lean`): exact Pauli expansion of $A^2$, five-way saturation equivalence (`saturation_tfae`), and $(2^N-1)|S|=\square$ (`saturation_mul_isSquare`).
  - **Lemmas 20 & 21 and Theorem 22** (`ConjectureECore.lean`): Jordan restriction (`lemma20_jordan_action`), Sylvester/symmetric cubic-trace identities, and the eigenvalue-free universal cubic-trace identity (`trace_completion_cube_universal`).
  - **Theorem 19 (all nine vertex cases)** (`ConjectureECones.lean`, `ConjectureE.lean`, `AuditUpgrades.lean`): closed-form outside character sums (Table 8), `jonah_conjecture_e_all_nine_cases`, and `jonah_conjecture_e_all_nine_cases_spectra` across C1, C3, C5, C6, C8, C11, C12, C14, C15 for every $N\ge4$ (and $N\ge3$ for C1, C3, C6, C11).
  - **Corollaries 16 & 18 & Proposition 16'** (`ConjectureEExtras.lean`, `AuditUpgrades.lean`): Jonah's general cone lift (`cone_lift_strict_law_fails`, `corollary18_c11_from_c3`) and the four-qubit C3 binary completion enclosures (`corollary16_binary_minima_tightened`: $330\le\min_y F(\sigma_1,y)\le344\lt347\le\min_y F(\sigma_0,y)\le368$) via pure-integer fraction-free $LDL^{\mathsf T}$ certificates.
* **Theorem 22 & exact trace-formula / SDP-dual verifiers.** `python scripts/conjecture_e_trace_formula.py` (97 checks for $N=3\text{–}5$ + 39 checks at $N=6$ = 136 exact checks) and `python scripts/c3_sdp_dual_check.py` (15 checks) run in CI alongside the 77-declaration Lean audit (`.github/workflows/conjecture-e-all-cases.yml`).

**New in 1.4.0** (paper Sections 8.6 and 8.7):

* **The proof of Conjecture E is self-contained.** Theorem 19 no longer only cites two structure
  theorems of Jonah's preprint: Lemmas 20 and 21 write out his Theorem A and the linear algebra of his
  proof of Theorem B3, each case paragraph verifies their hypotheses, the proof of his cone lift is
  repeated for Corollary 18, and a short transport argument carries each construction to every
  hyperplane class of its case. The proof now uses the preprint only through its definitions and case
  list. `python scripts/conjecture_e_lemmas.py` (115 checks; with the argument `6`, 46 more at six
  qubits) checks the lemmas, their hypotheses and the predicted traces in exact arithmetic, with four
  negative controls. No theorem statement changes.

**New in 1.3.0** (paper Sections 8.5 to 8.8 and 9.3; first recorded in the addenda under
[publication/](publication/)):

* **Conjecture E is true** (Theorem 19). In all nine vertex cases of
  [Jonah's note](https://doi.org/10.5281/zenodo.23524332) and for every $N \ge 4$ there are two sign
  carriers with the same carrier spectrum and different completion spectra. The carriers come from graphs
  with one edge for each nonzero difference, over the real, complex and quaternionic numbers, and from a
  pair swap for cones. Outside case C3 the proof is on paper (in version 1.3.0 it used Theorems A and B3
  of the note; see 1.4.0 above) and is checked by exact computation for three to six qubits (`python scripts/conjecture_e.py`, 81 checks, and
  `python scripts/conjecture_e.py 6`, 36 checks).
* **Case C3 for every number of qubits from four on, in Lean** (Theorem 17): `c3_strict_law_fails_general` in
  [lean/HoggarBound/CarrierFamily.lean](lean/HoggarBound/CarrierFamily.lean), about the library's own
  Pauli matrices, real quadric and context signs; 74 audited declarations, standard axioms only. Case
  C11 follows by the note's cone lift, whose proof the paper repeats (Corollary 18).
* **The binary completion minima of the four-qubit pair differ** (Corollary 16): at least 347 against at
  most 344 violated outside contexts.
* **The seven-qubit degree 729344 is a Lean theorem** (`phase7_degree`), with kernel-evaluated counts.

**Research website:** [Hoggar Bound Lab](https://0thernes.github.io/hoggar-bound-lab/).
The [C3 research summary](docs/RESEARCH-SUMMARY.md), [verification guide](VERIFICATION.md),
and [claim register](docs/CLAIMS.md) connect the four-qubit spectral result to exact data and Lean theorem names.
The combined manuscript editions `v1.2.0`–`v1.4.0` and `v1.6.0`–`v1.7.0` (and Lean formalization release `v1.5.0`) preserve the C3 scientific paper and proof artifacts in
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
| 6 | six CCZ gates applied to the all-plus state ($m=2$ member of Theorem 13b) | 1008 | 45696 | **2016** | Lean (`det6_degree`, `infinite_nonclosed_saturated_family`) |
| 7 | three CS and eight CCZ gates applied to the all-plus state (Theorem 13) | 8128 | 2824192 | **729344** | Lean (`phase7_degree`) |
| $3m$ | pure-CCZ determinant phase state of $`\operatorname{Tr}_{\mathbb F_{2^m}/\mathbb F_2}(x_1x_2x_3)`$ ($m\ge1$, Theorem 13b) | $(q^3-1)q^2$ | $\tfrac16(q^3-1)q^4(q^2+q-3)$ | **$\tfrac1{12}(q^3-1)q^3(q-1)(q-2)$** | Lean (`NormPhaseFamily.lean`, all $m\ge1$) |

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
* **exact contextuality degrees outside the classical families**: 75 (four qubits, 1095 contexts), 480
  (five qubits, 10880 contexts) and 729344 (seven qubits, 2824192 contexts), each proved in Lean with
  lower bound, witness and kernel-evaluated counts;
* a **criterion and a classification**: which states built from T, controlled-S and CCZ gates on the
  all-plus state have a single non-zero Pauli modulus, exhaustively for up to five qubits; and the fact
  that the Pauli support of any such state is a two-character set (the support of a bent function in the
  three-, five- and seven-qubit cases).

## Layout

| path | what |
|---|---|
| `lean/HoggarBound/` | the Lean 4 development (`Moment`, `Pauli`, `Bound`, `Counting`, `Corollaries`, `Quadric`; the exact degrees `MaskConfig`, `Saturated`, `SaturatedFive`, `SaturatedPhaseFive`, `MaskRows`, `SaturatedPhaseSix`, `SaturatedPhaseSeven` with generated data `FlatData`, `PhaseData`; case C3 for every N >= 4, `CarrierFamily`; v1.5.0–v1.8.0 formalizations `Kramers`, `SaturationTheory`, `ConjectureECore`, `ConjectureECones`, `ConjectureE`, `ConjectureEExtras`, `AuditUpgrades`, `C3ExactOptimaData`, `C3ExactOptima`, `NormPhaseFamily`, `ExactDegreesN4N5`; plus `IndependentContexts`, `IndependentWitness`, `C3*`, `Stability`) |
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

The seven-qubit degree (about 1.5 minutes and 6.4 GB of memory in CI) and case C3 for every number of
qubits from four on:

```bash
cd lean && lake build HoggarBound.MaskRows HoggarBound.SaturatedPhaseSeven && lake env lean SaturatedSevenVerification.lean
```

```bash
cd lean && lake build HoggarBound.Bound HoggarBound.Quadric && lake env lean HoggarBound/CarrierFamily.lean
```

Theorem 2 (Kramers/elliptic), Theorems 3–4 (saturation), Propositions 3/8/10, asymptotics, Clifford transport, Lemmas 20–21, Theorem 22, eigenvalue-multiset Theorem 19 (all nine vertex cases), Corollaries 16 & 18, and Proposition 16' SDP dual (77 audited declarations):

```bash
cd lean && lake build HoggarBound.Kramers HoggarBound.SaturationTheory HoggarBound.ConjectureE HoggarBound.ConjectureEExtras HoggarBound.AuditUpgrades && lake env lean VerifyNewFormalizations.lean
```

`run_all.sh` needs gcc, Python 3 with NumPy and Matplotlib, and Node; Eshkol is optional. It prints one
line per stage and ends with `ALL STAGES PASSED`; the last complete run (all 22 stages, on 10 November
2026, in a fresh clone of commit `28dc811`, about 15 minutes on a Windows 11 desktop computer) is kept in
[results/run_all.log](results/run_all.log) and [results/falsify.log](results/falsify.log); apart from
elapsed seconds in one log, it reproduced every committed record. The Lean
build needs [elan](https://github.com/leanprover/elan); it downloads Lean 4.35.0 and the Mathlib cache.

## What is and is not claimed

* The Lean theorems are exactly what their statements say; comments are not theorems.
* Lower bounds are proved. Upper bounds are explicit assignments that anyone can recount.
  Optimality of the four- and five-qubit assignments of the classical families is not proved here,
  except for the four-qubit hyperbolic quadric.
* For the configurations of Section 5 both bounds are proved in Lean, for seven qubits as well
  (`phase7_degree`, `phase7_contexts`, counts evaluated by the kernel); that the masks are the supports
  of the named states is checked by programs, outside Lean. The uniqueness statement for seven qubits
  is proved by enumeration inside one family of forms only.
* Conjecture E (Theorem 19 across all nine vertex cases for every $N \ge 4$ at the canonical Hermitian
  eigenvalue-multiset level), signed-Clifford orbit transport, Corollaries 16 and 18, Proposition 16'
  ($330 \le \min_y F(\sigma_1,y) \le 344 \lt 347 \le \min_y F(\sigma_0,y) \le 368$), Lemmas 20 and 21,
  Theorem 22, the quaternionic refinement (Theorem 2), the saturation equivalences (Theorems 3 and 4),
  Propositions 3, 8 and 10, and the asymptotic $1/2$ limit (Corollary A) are all proved in Lean 4 (77
  audited declarations in `VerifyNewFormalizations.lean`, strictly standard axioms) and checked by exact
  computation through six qubits. Only the single-orbit group transitivity classification of Jonah
  [J3, Theorem B4] remains a cited paper input. No external referee has reviewed the proofs.
* Novelty of the Section 5 results is claimed to the extent of a bounded literature search.
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

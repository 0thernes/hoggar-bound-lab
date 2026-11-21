# The Lean 4 development

Lean 4.35.0 with Mathlib v4.35.0 (pinned in `lean-toolchain` and `lake-manifest.json`). Every theorem
listed here depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. There is no
`sorry`, no `native_decide` and no added axiom anywhere in these modules.

## What is proved

All statements are about explicit complex matrices: `pauli u` is the `2^N × 2^N` matrix
`i^{|a∧c|} X^a Z^c` for `u = (a, c)`, defined entry by entry; its product rule, its commutation rule and
the sign of a context are theorems, not definitions.

### The bound, for every number of qubits

```lean
theorem hoggar_bound (hN : 1 ≤ N) (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S) (f : Pt N → ℝ)
    (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ N - 1) * beta6 S f
      ≤ ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card)
```

`beta6 S f` is six times (satisfied − violated contexts): a sum over ordered commuting pairs of `S` whose
product lies in `S`. `S` is an arbitrary finite set of non-identity Pauli observables.

### Corollaries for the classical families

| theorem | statement |
|---|---|
| `full_space_fraction` | for every N ≥ 1, the violated fraction of the full N-qubit configuration is at least 1/2 − √(2^N+1)/(2^N+2) |
| `three_qubit_contexts` | every assignment of the 63 three-qubit observables violates at least 63 contexts |
| `four_qubit_contexts` | every assignment of the 255 four-qubit observables violates at least 1451 contexts |
| `five_qubit_contexts` | every assignment of the 1023 five-qubit observables violates at least 28786 contexts |
| `four_qubit_hyperbolic_contexts` | at least 315 contexts for the 135 real four-qubit observables |
| `five_qubit_hyperbolic_contexts` | at least 6426 contexts for the 527 real five-qubit observables |

### Exact contextuality degrees

Each of these is a two-sided statement: every assignment violates at least `d` contexts, **and** some
assignment violates exactly `d`.

| theorem | configuration (given by a bit mask) | observables | contexts | degree |
|---|---|---|---|---|
| `pivot_degree`, `pivot_contexts` | four qubits, the pivot configuration | 135 | 1095 | 75 |
| `cieslinski5_degree`, `cieslinski5_contexts` | five qubits, support of the state of arXiv:2610.07172 | 496 | 10880 | 480 |
| `phase5_degree`, `phase5_contexts` | five qubits, support of `CCZ(0,1,4) CCZ(0,2,3) CS(0,1) CS(1,3) CS(2,4) \|+++++⟩` | 496 | 10880 | 480 |
| `phase7_degree`, `phase7_contexts` | seven qubits, support of the circuit state Φ7 (three CS and eight CCZ gates on `\|+⟩^⊗7`) | 8128 | 2824192 | 729344 |
| `quadric_degree` | four qubits, the hyperbolic quadric | 135 | 1575 | 315 |
| `hoggar_degree` | three qubits, all observables | 63 | 315 | 63 |
| `ccz_degree`, `lly_degree` | three and two qubits | 28, 12 | 56, 8 | 0 |

The seven-qubit counts are double sums with 2^28 terms. `MaskRows.lean` evaluates one row of either
sum on packed sets of codes and proves, for every N, that the result is the row; the kernel evaluates
the 2^14 rows in 16 blocks (`SaturatedPhaseSeven.lean`; in CI the whole build took about 1.5 minutes
and at most 6.4 GB of memory, one block of 1024 rows about 2.5 GB in a local test).

### Case C3 for every number of qubits from four on

`HoggarBound/CarrierFamily.lean` (a separate build target, not imported by `HoggarBound.lean`) proves
that the strict law fails for sign carriers in case C3 of Jonah's classification for every N ≥ 4:

```lean
theorem c3_strict_law_fails_general (hm : 3 ≤ m) :
    ∃ σ τ : Pt (m + 1) → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionPts m) σ).charpoly = (opA (sectionPts m) τ).charpoly ∧
      (completionMatrix m σ).charpoly ≠ (completionMatrix m τ).charpoly
```

`sectionPts` and `outsidePts` are the real points that commute and anticommute with Z on qubit 0, and
`completionMatrix` has the entry `lineSign (p + q) q * σ (p + q)` for commuting distinct outside points
`p`, `q`. The 74 audited declarations use only the standard axioms (`results/lean-c3-all-qubits-axioms.log`).
See Section 9.3 of the combined paper for what the statement leaves to the reader.

### Kramers floor, saturation theory, Conjecture E across all nine vertex cases, exact C3 binary optima, infinite determinant family, and N=4–5 ladders (`v1.5.0`–`v1.8.0`)

Twelve additional sorry-free modules (13,910 lines total) audited by `VerifyNewFormalizations.lean` (**100** declarations strictly within `[propext, Classical.choice, Quot.sound]`, log in `../results/new-formalizations-lean-axioms.log`) prove:

- **Theorem 2 (`HoggarBound/Kramers.lean`):** `kramers_even_mult`, `hoggar_bound_quaternionic`, `card_ellipticPoints`, `card_flags_elliptic`, `elliptic_fraction`, and finite elliptic-quadric bounds `three_qubit_elliptic_contexts` (9), `four_qubit_elliptic_contexts` (291), `five_qubit_elliptic_contexts` (6501).
- **Theorems 3 and 4 (`HoggarBound/SaturationTheory.lean`):** `opA_sq_eq`, `saturation_tfae` (full five-way saturation equivalence for nonempty supports), and `saturation_mul_isSquare` (`(2^N - 1)|S| = □` for `N ≥ 2`).
- **Lemmas 20 and 21 and Theorem 22 (`HoggarBound/ConjectureECore.lean`):** `lemma20_jordan_action`, `trace_completion_pow_eq`, `trace_completion_cube_universal` (universal cubic-trace identity), `lemma21_trace_cube_sylvester`, `lemma21_trace_cube_symm`.
- **Theorem 19 across all nine vertex cases (`HoggarBound/ConjectureECones.lean`, `HoggarBound/ConjectureE.lean`):** Table 8 closed-form outside character sums (`charSumOut_C1`..`charSumOut_C12_C15`) and `jonah_conjecture_e_all_nine_cases` for every `N ≥ 4` (plus `N ≥ 3` for C1, C3, C6, C11).
- **Corollaries 16 and 18 (`HoggarBound/ConjectureEExtras.lean`):** Jonah's general cone lift (`cone_lift_carrier_charpoly`, `cone_lift_completion_charpoly`, `cone_lift_completion_trace_cube`, `cone_lift_strict_law_fails`, `corollary18_c11_from_c3`) and the four-qubit C3 binary completion minima separation (`c3_quadForm_eq`, `corollary16_sigmaA_lower`, `corollary16_sigmaB_lower`, `corollary16_sigmaB_witness`, `corollary16_binary_minima_differ`: `≤ 344 < 347`).
- **Version 1.7.0 audit upgrades & Proposition 16' (`HoggarBound/AuditUpgrades.lean`, 2,042 lines):**
  - Asymptotic `Filter.Tendsto` limit theorems (`floor_deficit_tendsto_zero`, `full_space_fraction_tendsto_half`, `hyperbolic_fraction_tendsto_half`, `full_space_violated_fraction_eventually_gt`, `elliptic_violated_fraction_eventually_gt`);
  - Propositions 3 and 8 (`proposition3_commuting_qgt`, `anticommuting_qgt`, `proposition3_violated_iff`, `proposition3_satisfied_iff`, `proposition8_flat_state_qgt`) and Proposition 10 (`pure_state_pauli_sq_transform`, `proposition10_two_character_sum`, `proposition10_hyperplane_card`);
  - Signed-Clifford orbit transport (`clifford_preserves_symp`, `clifford_transport_comm_product`, `clifford_transport_opA`, `clifford_transport_carrier_charpoly`, `clifford_transport_completion_charpoly`, `clifford_transport_strict_law_fails`);
  - Canonical Hermitian eigenvalue-multiset Conjecture E across all nine vertex cases (`completionMat_isHermitian`, `real_hermitian_charpoly_eq_iff_roots_eq`, `strict_law_fails_to_spectra`, `jonah_conjecture_e_all_nine_cases_spectra`);
  - Proposition 16' QUBO SDP-dual tightened Corollary 16 (`c3SdpBlock_pos_def`, `c3_shift_quad_zero`, `corollary16_sigmaB_sdp_lower`, `corollary16_sigmaA_witness`, `corollary16_binary_minima_tightened`: `330 ≤ min_y F(σ₁, y) ≤ 344 < 347 ≤ min_y F(σ₀, y) ≤ 368`).
- **Version 1.8.0 frontier resolutions:**
  - **Theorem 16'' (`HoggarBound/C3ExactOptimaData.lean`, `HoggarBound/C3ExactOptima.lean`, 1,374 lines):** Exact global binary completion optima of four-qubit C3 (`corollary16_sigmaA_exact_lower`: `≥ 368`, `corollary16_sigmaB_exact_lower`: `≥ 344`, `corollary16_exact_binary_optima`: exact minima `368` and `344`, exact gap `24`), via pure-integer MET-SDP frustrated-triangle duals and strictly diagonally dominant integer Cholesky certificates.
  - **Theorem 13b (`HoggarBound/NormPhaseFamily.lean`, `HoggarBound/SaturatedPhaseSix.lean`, 1,519 lines):** Infinite non-closed contextual floor-saturating pure-CCZ determinant family `|Ψ_{3m}⟩` for every `m ≥ 1` (`detPhase_isFlatState`, `detSupport_card`, `detSupport_not_closed`, `detSupport_flags_card`, `infinite_nonclosed_saturated_family`, `infinite_nonclosed_family_contextual`) plus kernel-checked `m = 2` six-qubit mask (`det6_card`: `1,008`, `det6_contexts`: `45,696`, `det6_degree`: `2,016`).
  - **Classical `N = 4, 5` exact ladders & unconditional bounds (`HoggarBound/ExactDegreesN4N5.lean`, 1,289 lines):** Symplectic transvection invariance (`transv_violatedLines_eq`), CSS witnesses (`q7minus_css_witness`: `315`, `w72_css_witness`: `1575`, `q9plus_css_witness`: `6975`), exact double-counting ladders (`d_W72_of_Q7minus`, `d_Q9plus_of_W72`), unconditional Kramers-lifted bounds (`w72_ge_1455`, `q9plus_ge_6444`), Lemmas L1 & L4 (`lemma_L1_q7minus_section_le_92`, `lemma_L4_w52_hyperplane_le_21`), and master reduction (`exact_degrees_n4_n5_of_q7minus_315`).

## Modules

| module | content |
|---|---|
| `HoggarBound/Moment.lean` | the scalar inequality `sum_cube_le`; traces of powers of a Hermitian matrix as power sums of eigenvalues |
| `HoggarBound/Pauli.lean` | points, Pauli matrices, their products, traces and commutation |
| `HoggarBound/Bound.lean` | contexts as flags, the operator `A = Σ f(v) P_v`, `tr A³`, **`hoggar_bound`** |
| `HoggarBound/Counting.lean` | violated flags and contexts; the flag count of the full space for every N |
| `HoggarBound/Corollaries.lean` | the full-space corollaries |
| `HoggarBound/Quadric.lean` | the real quadric and its counts for every N, by character sums |
| `HoggarBound/MaskConfig.lean` | configurations and assignments as bit masks; `card_flags_cfg`, `card_violated_cfg`; `degree_of_certificate` |
| `HoggarBound/FlatData.lean`, `PhaseData.lean` | generated: the masks |
| `HoggarBound/SaturatedFive.lean`, `SaturatedPhaseFive.lean` | generated: the five-qubit counts, 16 kernel-evaluated blocks per sum |
| `HoggarBound/Saturated.lean` | the two-, three- and four-qubit counts and the exact-degree theorems |
| `HoggarBound/MaskRows.lean`, `SaturatedPhaseSeven.lean` | rows of the counts on packed sets of codes; the seven-qubit counts and **`phase7_degree`** |
| `HoggarBound/CarrierFamily.lean` | case C3 for every number of qubits from four on: **`c3_strict_law_fails_general`** |
| `HoggarBound/Kramers.lean` | Theorem 2: quaternionic/Kramers spectral floor and elliptic quadrics `Q⁻(2N-1,2)` |
| `HoggarBound/SaturationTheory.lean` | Theorems 3 & 4: Pauli expansion of `A²`, five-way saturation equivalence, `(2^N - 1)|S| = □` |
| `HoggarBound/ConjectureECore.lean` | Lemmas 20 & 21 and Theorem 22 (universal cubic-trace identity) |
| `HoggarBound/ConjectureECones.lean`, `ConjectureE.lean` | Table 8 outside character sums and Theorem 19 across all nine vertex cases (`jonah_conjecture_e_all_nine_cases`) |
| `HoggarBound/ConjectureEExtras.lean` | Corollary 18 (general cone lift, C11 from C3) and Corollary 16 (four-qubit C3 binary completion minima separation `≤ 344 < 347`) |
| `HoggarBound/AuditUpgrades.lean` | Version 1.7.0 audit upgrades: asymptotics, Propositions 3/8/10, Clifford orbit transport, eigenvalue-multiset Conjecture E across all 9 cases, and Proposition 16' QUBO SDP-dual tightened Corollary 16 (`330 ≤ F(σ₁) ≤ 344`, `347 ≤ F(σ₀) ≤ 368`) |
| `HoggarBound/C3ExactOptimaData.lean`, `C3ExactOptima.lean` | Theorem 16'': exact global binary completion optima of four-qubit C3 (`min F(σ₀) = 368`, `min F(σ₁) = 344`, exact gap `24`) |
| `HoggarBound/SaturatedPhaseSix.lean`, `NormPhaseFamily.lean` | Theorem 13b: infinite non-closed contextual pure-CCZ determinant family `|Ψ_{3m}⟩` for every `m ≥ 1` + six-qubit exact degree `2,016` |
| `HoggarBound/ExactDegreesN4N5.lean` | Transvection invariance, CSS witnesses (`315 / 1575 / 6975`), double-counting ladders, unconditional `d(W(7,2)) ≥ 1455` & `d(Q⁺(9,2)) ≥ 6444`, Lemmas L1/L4, master reduction |
| `HoggarBound/IndependentContexts.lean`, `IndependentWitness.lean` | written by the independent companion review |
| `HoggarBound/C3*.lean`, `Stability.lean` | the companion C3 note (separate work) |

The root module `HoggarBound.lean` imports the first six. The other modules are separate build targets,
so that the default build stays short.

## Build and audit

```bash
lake exe cache get
```

```bash
lake build
```

```bash
lake build HoggarBound.Saturated HoggarBound.SaturatedPhaseFive
```

```bash
lake env lean SaturatedVerification.lean
```

```bash
lake build HoggarBound.MaskRows HoggarBound.SaturatedPhaseSeven
```

```bash
lake env lean SaturatedSevenVerification.lean
```

```bash
lake build HoggarBound.Bound HoggarBound.Quadric
```

```bash
lake env lean HoggarBound/CarrierFamily.lean
```

```bash
lake build HoggarBound.Kramers HoggarBound.SaturationTheory HoggarBound.ConjectureE HoggarBound.ConjectureEExtras HoggarBound.AuditUpgrades HoggarBound.C3ExactOptima HoggarBound.SaturatedPhaseSix HoggarBound.NormPhaseFamily HoggarBound.ExactDegreesN4N5
```

```bash
lake env lean VerifyNewFormalizations.lean
```

`SaturatedVerification.lean` prints the axioms of the fourteen declarations of the two- to five-qubit
exact-degree modules (expected output `../results/lean-saturated-axioms.log`),
`SaturatedSevenVerification.lean` those of the thirteen seven-qubit declarations
(`../results/lean-saturated-seven-axioms.log`), `CarrierFamily.lean` those of its 74 declarations
(`../results/lean-c3-all-qubits-axioms.log`), and `VerifyNewFormalizations.lean` those of the **100**
declarations across the twelve `v1.5.0`–`v1.8.0` modules (`../results/new-formalizations-lean-axioms.log`). `IndependentVerification.lean` does the
same for the core modules (expected output: `../results/lean-axioms.log`).

Resources: the default build takes a few minutes after the Mathlib cache is fetched. In the successful
[Ubuntu run 42741638912](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42741638912), the two
five-qubit modules took 6:48.05 and 6:49.55, with maximum resident memory of 6,350,756 and 6,490,260 KiB.
`Saturated.lean` took 53.31 seconds with 6,047,364 KiB maximum resident memory. These are measurements
from that runner, not hardware-independent guarantees. Run the substantial builds sequentially; the
separate C3 certificate has a larger memory and runtime budget described in [VERIFICATION.md](../VERIFICATION.md).

## How the finite counts are checked

A configuration on N qubits is a number `mask < 2^(4^N)`: bit `a + 2^N c` says whether the observable
`(a, c)` belongs to it. `MaskConfig.lean` proves, for every N and every mask, that the number of flags of
the configuration, and the number of flags violated by an assignment that is itself given by a mask,
equal double sums over codes of Boolean expressions made of bit tests, exclusive or and addition. Those
sums are closed terms of type `ℕ`, and `decide +kernel` has the Lean kernel evaluate them. For five
qubits each sum has 2^20 terms; it is split into 16 blocks of 64 rows, one theorem per block, and the
blocks are added by `loop_blocks`. `degree_of_certificate` turns three evaluated numbers (observables,
flags, flags violated by the witness) and `hoggar_bound` into the two-sided statement.

The masks are generated by `scripts/flat_states.py --lean` and `scripts/phase_states.py --lean`, which
also verify in exact arithmetic that they are the supports and sign patterns of the states named in the
paper. That link is not part of the Lean statements, and the statements do not need it.

## Continuous integration

`.github/workflows/saturated-configurations.yml` builds the exact-degree modules, prints the axioms and
fails if any declaration uses an axiom outside the allowlist or if a source file contains `sorry`,
`native_decide` or an `axiom` declaration. `.github/workflows/independent-verification.yml` does the same
for the core proof and the companion modules. `.github/workflows/c3-all-qubits.yml` checks
`CarrierFamily.lean`, enforces the allowlist on its 74 declarations and fails if the file contains
`sorry`, `admit`, `native_decide`, `unsafe`, `set_option` or an `axiom` declaration.
`.github/workflows/conjecture-e-all-cases.yml` builds `Kramers`, `SaturationTheory`, `ConjectureE`, and
`ConjectureEExtras`, enforces the same allowlist and zero-forbidden-token check across all 49 declarations
of `VerifyNewFormalizations.lean`, and runs `scripts/conjecture_e_trace_formula.py` (97 checks).

## Exact four-qubit C3 certificate

The C3 development proves that two explicitly encoded section assignments give the same carrier
spectrum and different completion spectra, including the bridge to the original Pauli matrices and
signed contexts. Its 42-declaration audit is separate from the saturation audit above.

See [VERIFICATION.md](../VERIFICATION.md) for sequential build commands, source/evidence hashes,
measured runtime and memory, and the successful independent Linux run. The [claim register](../docs/CLAIMS.md)
maps theorem names to each asserted result and identifies the paper's algebraic conclusions outside Lean.
`python scripts/publication_release_audit.py`, run from the repository root, checks that a documentation
release retains the verified C3 artifacts. It is a continuity check, not a fresh Lean compilation.

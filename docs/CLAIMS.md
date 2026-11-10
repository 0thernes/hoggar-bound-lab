# Claim-to-theorem and evidence map

This map describes the frozen research result in [`v0.2.0-c3-certificate`](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v0.2.0-c3-certificate), commit `d3811e3b53048fa8f3206f08494f0a9834eed287`. It accompanies the `v1.1.2` update with unchanged proof sources. Build commands, measured costs, release provenance, and durable CI downloads are in [VERIFICATION.md](../VERIFICATION.md).

The main claim is **equal carrier spectra and unequal completion spectra for one explicit four-qubit C3 pair**. This refutes the strict carrier-spectrum-to-completion-spectrum law in that instance and establishes the corresponding instance of Conjecture E, which predicts such failure. The result does not resolve Conjecture E in every dimension or case.

## Evidence categories

- **Lean theorem:** a precise declaration in the linked source, connected through the proof dependencies and checked by the recorded source builds.
- **Exact executable evidence:** independently reconstructed finite matrices, integer calculations, symbolic polynomials, or falsification controls. These support a computational claim with their own programs and outputs.
- **Ordinary mathematical derivation:** an argument in the paper or notes that is not included in the stated Lean declaration audit.
- **Literature or scope statement:** a comparison or interpretation with its own cited source; kernel checking does not establish historical priority or peer review.

The 42 C3 names below are exactly those requested by [`C3Verification.lean`](../lean/C3Verification.lean). Each appears in the [raw local axiom log](../results/frontier-c3-lean-axioms.log), the [parsed report](../results/frontier-c3-axioms.json), and the actual successful Linux logs in the [published Lean evidence ZIP](https://github.com/0thernes/hoggar-bound-lab/releases/download/v0.2.0-c3-certificate/linux-lean-evidence.zip). Every list contains only `propext`, `Classical.choice`, and `Quot.sound`. These counts refer to audited declarations, not additional axioms.

## C3 geometry, supplied data, and the original model

All declaration names in the next two tables have namespace prefix **`HoggarBound.C3.`**.

| Claim | Audited declarations | Source |
| --- | --- | --- |
| Binary coordinates faithfully represent the original vector/point types and preserve addition. | `bits_bijective`, `codePoint_bijective`, `codePoint_add` | [C3Geometry.lean](../lean/HoggarBound/C3Geometry.lean) |
| The polar point is real; the coded section and complement are exactly the original real Pauli points with the corresponding symplectic condition. | `section_correct`, `outside_correct`, `polar_point_real`, `section_image`, `outside_image` | [C3Geometry.lean](../lean/HoggarBound/C3Geometry.lean), [C3Theorem.lean](../lean/HoggarBound/C3Theorem.lean) |
| The section has 71 points; the complement has 64; the outside labels are complete and injective. | `section_card`, `outside_card`, `outside_labels_complete`, `outside_labels_injective` | [C3Geometry.lean](../lean/HoggarBound/C3Geometry.lean) |
| For a real code, the integral matrix-entry formula agrees with the original complex Pauli operator in binary computational-basis order. | `realPauliCode_cast` | [C3Geometry.lean](../lean/HoggarBound/C3Geometry.lean), using [Pauli.lean](../lean/HoggarBound/Pauli.lean) |
| The supplied integer carrier matrices equal the signed Pauli sums for the two fixed assignments. | `carrierA_from_section`, `carrierB_from_section` | [C3Geometry.lean](../lean/HoggarBound/C3Geometry.lean) |
| The supplied integer completion matrices equal the signed commuting-context definitions on all outside labels. | `completionA_from_contexts`, `completionB_from_contexts` | [C3Geometry.lean](../lean/HoggarBound/C3Geometry.lean) |
| The actual complex Pauli carriers are Hermitian; casting and reindexing the integral carriers gives those operators, whose characteristic polynomials are equal. | `pauliCarrier_isHermitian`, `carrier_cast_reindex`, `pauli_carrier_charpoly_eq` | [C3Theorem.lean](../lean/HoggarBound/C3Theorem.lean) |
| Casting the integer completion gives the original real line-sign model; its two cubic traces are 14976 and 15360, and they are unequal. | `completion_cast`, `pauli_completionA_trace_cube`, `pauli_completionB_trace_cube`, `pauli_completion_cube_traces_ne` | [C3Theorem.lean](../lean/HoggarBound/C3Theorem.lean) |

The underlying context-sign conversion is the earlier lemma **`HoggarBound.lineSign_eq_integer`** in [IndependentWitness.lean](../lean/HoggarBound/IndependentWitness.lean). It equates the computable integer sign with the original real `lineSign`; it is a dependency of the checked model connection. The input matrices themselves are explicit definitions in [C3Data.lean](../lean/HoggarBound/C3Data.lean). Supplying those definitions does not assume their geometric or spectral properties: the declarations above prove the required connections.

The code convention is `v = a + 16c`, qubit zero least significant, and polar point 128. `signA` is negative at 48, 102, 176, 230; `signB` is negative at 87, 144, 176, 215. Their `signA_values`/`signB_values` validity lemmas occur in [C3Geometry.lean](../lean/HoggarBound/C3Geometry.lean) and are used by the final existential theorem. They are covered through that theorem's dependency audit, although they are not separate entries in the 42-name print list.

## C3 arithmetic and spectral conclusion

| Claim | Audited declarations | Source |
| --- | --- | --- |
| The literal matrices obey `A M = M B` and `M R = 46656 I`; consequently `det M ≠ 0`. | `carrier_intertwining`, `intertwiner_inverse`, `intertwiner_det_ne_zero` | [C3Certificate.lean](../lean/HoggarBound/C3Certificate.lean) |
| The integer carriers have the same characteristic polynomial. | `carrier_charpoly_eq` | [C3Certificate.lean](../lean/HoggarBound/C3Certificate.lean) |
| The integer completion cubic traces are exactly 14976 and 15360 and therefore differ. | `completionA_trace_cube`, `completionB_trace_cube`, `completion_cube_traces_ne` | [C3Certificate.lean](../lean/HoggarBound/C3Certificate.lean) |
| Two valid sign assignments exist on the section with equal actual carrier characteristic polynomials and the two stated actual completion traces. | `four_qubit_C3_counterexample` | [C3Theorem.lean](../lean/HoggarBound/C3Theorem.lean) |
| For real Hermitian matrices, power traces are eigenvalue power sums; equal characteristic polynomials imply equal power traces; equal real root multisets imply equal characteristic polynomials. | `hermitian_trace_pow`, `hermitian_trace_pow_eq_of_charpoly_eq`, `hermitian_charpoly_eq_of_roots_eq` | [C3Spectra.lean](../lean/HoggarBound/C3Spectra.lean) |
| Signed-context adjacency is Hermitian under the stated structural assumptions; the concrete completion operators satisfy them. | `signed_context_adjacency_isHermitian`, `pauliCompletion_isHermitian` | [C3Spectra.lean](../lean/HoggarBound/C3Spectra.lean) |
| The actual complex carriers have equal canonical real eigenvalue functions; the actual real completions have unequal characteristic polynomials, eigenvalue functions, and real root multisets. | `pauli_carrier_eigenvalues_eq`, `pauli_completion_charpoly_ne`, `pauli_completion_eigenvalues_ne`, `pauli_completion_eigenvalue_multisets_ne` | [C3Spectra.lean](../lean/HoggarBound/C3Spectra.lean) |
| The fixed pair simultaneously has equal carrier characteristic polynomials and unequal completion characteristic polynomials/root multisets. | `four_qubit_C3_spectral_counterexample` | [C3Spectra.lean](../lean/HoggarBound/C3Spectra.lean) |

`C3Certificate.lean` includes private intermediate matrices `completionSquareA` and `completionSquareB`. The private `completionA_square` and `completionB_square` proofs check their entries row by row before the public trace theorems use them. Those square values are verified data. The finite equalities use `decide +kernel`; they are not accepted from a floating-point calculation or a Python output file.

Only `M R = 46656 I` is used as the formal inverse-numerator identity. The independent executable certificate also checks `R M = 46656 I`; that opposite product is not presented here as a separate audited Lean theorem.

## Auxiliary scalar stability: six audited declarations

These names have namespace prefix **`HoggarBound.`** and source [Stability.lean](../lean/HoggarBound/Stability.lean). The exact entry point is [StabilityVerification.lean](../lean/StabilityVerification.lean), with [raw axiom output](../results/stability-lean-axioms.log), [parsed audit](../results/stability-axioms.json), and a [successful source-build log](../results/stability-lean-build.log).

For the final existence theorem, let `n = |ι| ≥ 2`, `Σ xⱼ = 0`, `Σ xⱼ² = n m`, `a ≥ 0`, and `a² = (n − 1)m`. Define

```text
Δ = n m (n − 2)a − (n − 1) Σ xⱼ³.
e⁽ⁱ⁾ᵢ = a;   e⁽ⁱ⁾ⱼ = −a/(n − 1) for j ≠ i.
dist²(x, e⁽ⁱ⁾) = Σ (xⱼ − e⁽ⁱ⁾ⱼ)².
```

| Claim | Audited declaration |
| --- | --- |
| Each coordinate is at most `a` under the moment and dimension hypotheses. | `moment_entry_le` |
| `Σ ((n − 1)xⱼ + a)² = n²a²`. | `shifted_square_sum` |
| `Σ (a − xⱼ)((n − 1)xⱼ + a)² = (n − 1)Δ`. | `cubic_residual_identity` |
| Any upper coordinate bound `t` gives `n²a²(a − t) ≤ (n − 1)Δ`. | `cubic_deficit_controls_top` |
| `(n − 1)dist²(x,e⁽ⁱ⁾) = 2na(a − xᵢ)`. | `spectrum_distance_identity` |
| There exists a maximum coordinate `i`, with `xᵢ ≤ a`, satisfying `na dist²(x,e⁽ⁱ⁾) ≤ 2Δ`. | `exists_near_extremal_spectrum` |

The source states each lemma's own hypotheses; some identities need fewer assumptions than the final existence theorem. The final statement is cross-multiplied and includes `a = 0`. For `a > 0`, its usual distance-bound interpretation follows by division. The six audited declarations concern real scalar spectra. Matrix/Frobenius distance, pure-state Pauli coordinates, and sign-rounding interpretations in [stability-theory.md](../results/stability-theory.md) are ordinary derivations outside these six declarations. No priority claim is made for the scalar inequality.

## Earlier spectral baseline and finite bounds

The [literature audit](../results/literature-audit.md) identifies the scalar third-moment bound as the classical Okumura inequality and identifies the same Pauli spectral floor in prior work. The three-qubit minimum 63 is also established prior work. These modules provide formalization, explicit hypotheses, and reproducible certificates. The audit documents stronger reported bounds and distinctions between published results, preprint claims, and independently checked evidence.

The following names have namespace prefix **`HoggarBound.`**. Their separate [22-declaration entry point](../lean/IndependentVerification.lean) and [recorded axiom log](../results/lean-independent-verification.log) belong to the earlier development.

| Claim proved in this repository | Declaration | Source |
| --- | --- | --- |
| For `n ≥ 2`, zero first moment, second moment `nm`, `a ≥ 0`, and `a²=(n−1)m`, `(n−1)Σx³ ≤ nm(n−2)a`; a corresponding Hermitian trace bound. | `sum_cube_le`, `trace_cube_le` | [Moment.lean](../lean/HoggarBound/Moment.lean) |
| The cubic Pauli trace identity and induced-support spectral bound, for the support/sign hypotheses in the source. | `trace_opA_cube`, `hoggar_bound` | [Bound.lean](../lean/HoggarBound/Bound.lean) |
| A full-space inequality and a finite-`N` violated-fraction bound. | `full_space_bound`, `full_space_fraction` | [Corollaries.lean](../lean/HoggarBound/Corollaries.lean) |
| Three-qubit full space: exactly 315 contexts; the minimum violated-context count is 63, attained by the supplied Hoggar assignment. | `three_qubit_total_contexts`, `hoggar_contexts_exact`, `three_qubit_exact_minimum` | [IndependentVerification.lean](../lean/IndependentVerification.lean) |
| Full-space lower bounds: at least 1451 violations for four qubits and 28786 for five. | `four_qubit_contexts`, `five_qubit_contexts` | [Counting.lean](../lean/HoggarBound/Counting.lean), [Corollaries.lean](../lean/HoggarBound/Corollaries.lean) |
| Real-quadric lower bounds: at least 315 violations for four qubits and 6426 for five. | `four_qubit_hyperbolic_contexts`, `five_qubit_hyperbolic_contexts` | [Quadric.lean](../lean/HoggarBound/Quadric.lean) |
| The five-qubit real-quadric count cannot be 4743 or any number below 6426. | `five_qubit_hyperbolic_not_one_fifth`, `five_qubit_hyperbolic_no_assignment_below_6426` | [IndependentVerification.lean](../lean/IndependentVerification.lean) |

The numerical lower bounds in this table do not by themselves assert exact minima. The separate three-qubit existence-and-lower-bound theorem does assert an exact minimum. `full_space_fraction` is a finite-dimensional inequality; a formal limit theorem as `N → ∞` is not one of the audited declarations.

## Separate v1.1.0 saturation development: 14 audited declarations

Commit [`87f08a0fb5007c8529abc13eabeec093027c0eba`](https://github.com/0thernes/hoggar-bound-lab/tree/87f08a0fb5007c8529abc13eabeec093027c0eba) adds a separate development for configurations that attain the spectral floor. Its [SaturatedVerification.lean](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/lean/SaturatedVerification.lean) requests the following **14** declarations, all in namespace `HoggarBound`. The [committed axiom log](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/results/lean-saturated-axioms.log) contains each name exactly once and uses only `propext`, `Classical.choice`, and `Quot.sound`. This is separate from the 42 C3 and six scalar stability reports.

| Claim | Audited declarations | Source |
| --- | --- | --- |
| Bit-mask flag and violated-flag counts agree with the original Pauli/context definitions. Exact finite counts and a tight spectral floor give a lower bound for every sign assignment and an explicit assignment attaining it; six flags correspond to one context. | `card_flags_cfg`, `card_violated_cfg`, `degree_of_certificate`, `contexts_of_flags` | [MaskConfig.lean](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/lean/HoggarBound/MaskConfig.lean) |
| Two-qubit 12-point mask and three-qubit 28-point mask: exact degree 0. | `lly_degree`, `ccz_degree` | [Saturated.lean](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/lean/HoggarBound/Saturated.lean) |
| Three-qubit 63-point mask: exact degree 63. Four-qubit 135-point quadric mask: exact degree 315. | `hoggar_degree`, `quadric_degree` | [Saturated.lean](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/lean/HoggarBound/Saturated.lean) |
| Four-qubit 135-point pivot mask: 1095 contexts and exact degree 75. | `pivot_degree`, `pivot_contexts` | [Saturated.lean](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/lean/HoggarBound/Saturated.lean) |
| Five-qubit 496-point Cieśliński mask: 10880 contexts and exact degree 480. | `cieslinski5_degree`, `cieslinski5_contexts` | [Saturated.lean](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/lean/HoggarBound/Saturated.lean), with counts in [SaturatedFive.lean](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/lean/HoggarBound/SaturatedFive.lean) |
| Five-qubit 496-point phase mask: 10880 contexts and exact degree 480. | `phase5_degree`, `phase5_contexts` | [SaturatedPhaseFive.lean](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/lean/HoggarBound/SaturatedPhaseFive.lean) |

These are statements about explicitly encoded finite configurations and signs. Their finite counts use `decide +kernel`; the five-qubit sums are split into checked blocks. The identification of the masks with the supports/signs of named quantum states, and the circuits that prepare those states, is checked by the [flat-state](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/scripts/flat_states.py), [phase-state](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/scripts/phase_states.py), and [Moonlab](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/src/moonlab_saturated.mjs) programs. That state/circuit identification is **outside the Lean statements**.

The seven-qubit configuration's **8128 observables, 2824192 contexts, and degree 729344** use the general Lean spectral bound together with executable finite counts; those seven-qubit counts and their specialization are **not kernel-checked in this development**. The saturation equivalence, two-character property, phase-state rank criterion, and classification/enumeration claims are also outside these 14 declarations. See the [spectral-floor paper's formalization boundary](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/paper/spectral-floor.md#8-the-lean-4-development) and [Lean guide](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/lean/README.md).

For this development, [Saturated configurations run 42741638912](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42741638912) **passed both its executable and Lean jobs** at exact commit `87f08a0fb5007c8529abc13eabeec093027c0eba`. Both job logs confirm that checkout commit. The downloaded evidence ZIPs match GitHub's SHA-256 digests, and an independent parse of the actual Lean artifact found all 14 requested axiom reports with only the three permitted axioms. This is a separate successful proof run from the frozen C3 verification. The [workflow](https://github.com/0thernes/hoggar-bound-lab/blob/87f08a0fb5007c8529abc13eabeec093027c0eba/.github/workflows/saturated-configurations.yml) rebuilds the modules and enforces that allowlist. To reproduce the saturation build in a checkout containing these sources, run from `lean/` after fetching the pinned Mathlib cache:

```bash
lake build HoggarBound.Saturated
lake build HoggarBound.SaturatedPhaseFive
lake env lean SaturatedVerification.lean
```

## Claims with evidence outside the C3 Lean boundary

| Claim or observation | Evidence and precise boundary |
| --- | --- |
| The displayed factorization of the common carrier characteristic polynomial. | The [paper](../paper/c3-spectral-counterexample.md) and [exact tensor/block verification](../results/frontier-c3-n4-verification.json). Lean proves equality of the two carrier characteristic polynomials; the displayed factorization is not an additional theorem in the 42-name audit. |
| The block/Jordan completion formulas used in the paper's ordinary proof. | The paper and [frontier_c3_verify.py](../scripts/frontier_c3_verify.py). The Lean model connection uses the original signed-context definition and checked matrices; this audit does not claim a separate Lean theorem for the displayed Jordan/Kronecker formula. |
| The largest completion eigenvalues differ by exactly **2**, and the corresponding continuous-relaxation lower bounds differ by **32**. | Ordinary algebraic arguments in the paper, supported by exact polynomial/matrix computations. The formal C3 theorem proves different spectra and different cubic traces; these two numerical gaps are outside its audited conclusions. |
| There are **1120** signed outside contexts, reconstructed independently. | [Context verification report](../results/frontier-c3-context-verification.json) and [context verifier](../scripts/frontier_c3_context_verify.py). The Lean audit checks the geometry and every completion entry. It does not print a separate public theorem stating this 1120 count. |
| Deliberate sign perturbations and invalid inputs are detected by the executable/browser checks. | [Certificate audit](../results/frontier-c3-certificate-audit.json), [browser test](../tests/frontier_c3_browser_test.cjs), and [published executable evidence](https://github.com/0thernes/hoggar-bound-lab/releases/download/v0.2.0-c3-certificate/linux-executable-evidence.zip). An interactive configuration is not automatically covered by the fixed `signA`/`signB` Lean witness. |
| Tsotchke-stack programs execute the recorded arithmetic or simulation workloads. | [Stack audit](../results/stack-independent-audit.md) and the run records cited by the paper. The Lean theorem does not certify their implementations, hardware quantum randomness, or quantum computational advantage. |
| The inspected prior preprint leaves the four-qubit C3 instance open. | The paper's primary-source comparison and [frontier prior-art report](../results/frontier-prior-art.md). This is a bounded literature finding, not a kernel theorem or an exhaustive proof of historical priority. |

The frozen result makes no claim of an exact binary completion optimum, a classification of all cospectral carriers, a resolution of every case/dimension of Conjecture E, or journal acceptance. Publication and submission status are maintained in [publication/STATUS.md](../publication/STATUS.md).

## Which run proves what

The successful complete Linux proof is [run 42728421086](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42728421086) at `85520dc263c83de55d1a3d107cd80e7068be8616`. The [published audit](https://github.com/0thernes/hoggar-bound-lab/releases/download/v0.2.0-c3-certificate/linux-verification-audit.json) records the checkout, downloaded artifact digest, raw 42/6 axiom parsing, and proof-source equivalence to frozen publication commit `d3811e3b53048fa8f3206f08494f0a9834eed287`.

[Run 42732149645](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42732149645), at `026961ef81f70aa7cc464b527d4ca30e647e6b17`, supplies the successful main executable job. Its formal job and overall workflow were cancelled after the identical proof sources had already passed. Its [executable audit](https://github.com/0thernes/hoggar-bound-lab/releases/download/v0.2.0-c3-certificate/linux-executable-audit.json) preserves that distinction. The documentation update does not convert a cancelled workflow into a proof pass or introduce new proof sources.

The documentation release's [continuity checker](../scripts/publication_release_audit.py) compares the retained research artifacts with `d3811e3`, including all 21 proof/configuration files and the paper PDF. Its result is artifact/source equivalence evidence, not a new proof run or an extension of any theorem's scope. [VERIFICATION.md](../VERIFICATION.md) gives the command and the separate full-rebuild procedure.

/- Axiom audit for the formalizations closing the gaps of the combined paper
   (Sections 1.1, 2.2, 3, 4, 5.1, 6, 8.5–8.7, 9.3–9.4, and 12):
   - Theorem 2: Quaternionic / Kramers spectral floor & elliptic quadrics Q⁻(2N-1,2) (`Kramers.lean`)
   - Theorems 3 & 4: Full 5-way saturation equivalences & (2^N-1)|S| = □ (`SaturationTheory.lean`)
   - Lemmas 20 & 21 and Theorem 22 (Universal Cubic-Trace Identity) (`ConjectureECore.lean`)
   - Theorem 19: Jonah's Conjecture E in all nine vertex cases for every N ≥ 4
     (`ConjectureECones.lean`, `ConjectureE.lean`)
   - Corollaries 16 & 18: Four-qubit C3 binary completion minima separation (≤ 344 < 347) and
     general cone lift from C3 to C11 for every N ≥ 4 (`ConjectureEExtras.lean`)
   - Audit upgrades (`AuditUpgrades.lean`): asymptotic Filter.Tendsto limits (Corollary A),
     quantum metric & Berry curvature (Propositions 3 & 8), two-character hyperplane sums
     (Proposition 10), signed-Clifford orbit transport, eigenvalue-multiset Conjecture E across
     all nine vertex cases, and tightened Corollary 16 via exact QUBO SDP dual (330 ≤ F(σ₁) ≤ 344,
     347 ≤ F(σ₀) ≤ 368).
   - Frontier resolutions (v1.8.0):
     * Exact global binary completion optima of four-qubit C3: min F(σ₀) = 368 and min F(σ₁) = 344,
       exact binary gap 24 (`C3ExactOptimaData.lean`, `C3ExactOptima.lean`).
     * Infinite family of non-closed contextual floor-saturating pure-CCZ determinant phase states
       `|Ψ_{3m}⟩` for every `m ≥ 1` (`NormPhaseFamily.lean`) plus exact kernel-checked `m = 2`
       six-qubit member: 1,008 observables, 45,696 contexts, exact degree 2,016 (`SaturatedPhaseSix.lean`).
     * Symplectic transvection invariance, exact CSS witnesses (315, 1575, 6975), double-counting
       ladders (`Q⁻(7,2) → W(7,2) → Q⁺(9,2)`), unconditional Kramers-lifted bounds `d(W(7,2)) ≥ 1455`
       and `d(Q⁺(9,2)) ≥ 6444`, pigeonhole Lemmas L1 & L4, and exact master reduction
       (`ExactDegreesN4N5.lean`).

   Every `#print axioms` line must report a subset of `[propext, Classical.choice, Quot.sound]`.

   run:
     cd lean && lake build HoggarBound.Kramers HoggarBound.SaturationTheory HoggarBound.ConjectureE HoggarBound.ConjectureEExtras HoggarBound.AuditUpgrades HoggarBound.C3ExactOptima HoggarBound.SaturatedPhaseSix HoggarBound.NormPhaseFamily HoggarBound.ExactDegreesN4N5 && lake env lean VerifyNewFormalizations.lean -/
import HoggarBound.Kramers
import HoggarBound.SaturationTheory
import HoggarBound.ConjectureE
import HoggarBound.ConjectureEExtras
import HoggarBound.AuditUpgrades
import HoggarBound.C3ExactOptima
import HoggarBound.SaturatedPhaseSix
import HoggarBound.NormPhaseFamily
import HoggarBound.ExactDegreesN4N5
import HoggarBound.NonVacuity

-- Theorem 2: Quaternionic / Kramers spectral floor and elliptic quadrics
#print axioms HoggarBound.kramers_even_mult
#print axioms HoggarBound.sum_cube_le_even_mult
#print axioms HoggarBound.trace_cube_le_kramers
#print axioms HoggarBound.hoggar_bound_quaternionic
#print axioms HoggarBound.hoggar_bound_quaternionic_violated
#print axioms HoggarBound.card_ellipticPoints
#print axioms HoggarBound.card_flags_elliptic
#print axioms HoggarBound.elliptic_fraction
#print axioms HoggarBound.three_qubit_elliptic_contexts
#print axioms HoggarBound.four_qubit_elliptic_contexts
#print axioms HoggarBound.five_qubit_elliptic_contexts

-- Theorems 3 & 4: Saturation equivalences, Pauli expansion of A², and (2^N - 1)|S| = □
#print axioms HoggarBound.sum_cube_eq_iff
#print axioms HoggarBound.matrix_eq_sum_pauli
#print axioms HoggarBound.opA_sq_eq
#print axioms HoggarBound.saturation_tfae
#print axioms HoggarBound.saturation_mul_isSquare

-- Lemmas 20 & 21 and the Universal Cubic-Trace Identity
#print axioms HoggarBound.ConjectureE.lemma20_jordan_action
#print axioms HoggarBound.ConjectureE.trace_completion_pow_eq
#print axioms HoggarBound.ConjectureE.trace_completion_cube_universal
#print axioms HoggarBound.ConjectureE.lemma21_trace_cube_sylvester
#print axioms HoggarBound.ConjectureE.lemma21_trace_cube_symm

-- Closed-form outside character sums S_O(s) across all nine vertex cases
#print axioms HoggarBound.ConjectureE.charSumOut_C1
#print axioms HoggarBound.ConjectureE.charSumOut_C3_C5
#print axioms HoggarBound.ConjectureE.charSumOut_C6
#print axioms HoggarBound.ConjectureE.charSumOut_C8
#print axioms HoggarBound.ConjectureE.charSumOut_C11_C14
#print axioms HoggarBound.ConjectureE.charSumOut_C12_C15

-- Theorem 19: Jonah's Conjecture E in all nine vertex cases
#print axioms HoggarBound.ConjectureE.c1_strict_law_fails
#print axioms HoggarBound.ConjectureE.c3_strict_law_fails
#print axioms HoggarBound.ConjectureE.c5_strict_law_fails
#print axioms HoggarBound.ConjectureE.c6_strict_law_fails
#print axioms HoggarBound.ConjectureE.c8_strict_law_fails
#print axioms HoggarBound.ConjectureE.c11_strict_law_fails
#print axioms HoggarBound.ConjectureE.c12_strict_law_fails
#print axioms HoggarBound.ConjectureE.c14_strict_law_fails
#print axioms HoggarBound.ConjectureE.c15_strict_law_fails
#print axioms HoggarBound.ConjectureE.jonah_conjecture_e_all_nine_cases

-- Corollary 18: General cone lift (Jonah [J3], Lemma D (D2)) and C11 from C3 for every N ≥ 4
#print axioms HoggarBound.ConjectureE.cone_lift_opA_reindex
#print axioms HoggarBound.ConjectureE.cone_lift_carrier_charpoly
#print axioms HoggarBound.ConjectureE.cone_lift_completion_reindex
#print axioms HoggarBound.ConjectureE.cone_lift_completion_charpoly
#print axioms HoggarBound.ConjectureE.cone_lift_completion_trace_cube
#print axioms HoggarBound.ConjectureE.cone_lift_strict_law_fails
#print axioms HoggarBound.ConjectureE.corollary18_c11_from_c3

-- Corollary 16: Four-qubit C3 binary completion minima separation (≤ 344 < 347)
#print axioms HoggarBound.ConjectureE.c3_quadForm_eq
#print axioms HoggarBound.ConjectureE.corollary16_sigmaA_lower
#print axioms HoggarBound.ConjectureE.corollary16_sigmaB_lower
#print axioms HoggarBound.ConjectureE.corollary16_sigmaB_witness
#print axioms HoggarBound.ConjectureE.corollary16_binary_minima_differ

-- AuditUpgrades (v1.7.0): Asymptotics, Propositions 3/8/10, Clifford transport,
-- eigenvalue-multiset Conjecture E across all nine cases, and SDP-dual tightened Corollary 16
#print axioms HoggarBound.AuditUpgrades.floor_deficit_tendsto_zero
#print axioms HoggarBound.AuditUpgrades.full_space_fraction_tendsto_half
#print axioms HoggarBound.AuditUpgrades.hyperbolic_fraction_tendsto_half
#print axioms HoggarBound.AuditUpgrades.full_space_violated_fraction_eventually_gt
#print axioms HoggarBound.AuditUpgrades.elliptic_violated_fraction_eventually_gt
#print axioms HoggarBound.AuditUpgrades.proposition3_commuting_qgt
#print axioms HoggarBound.AuditUpgrades.anticommuting_qgt
#print axioms HoggarBound.AuditUpgrades.proposition3_violated_iff
#print axioms HoggarBound.AuditUpgrades.proposition3_satisfied_iff
#print axioms HoggarBound.AuditUpgrades.proposition8_flat_state_qgt
#print axioms HoggarBound.AuditUpgrades.pure_state_pauli_sq_transform
#print axioms HoggarBound.AuditUpgrades.proposition10_two_character_sum
#print axioms HoggarBound.AuditUpgrades.proposition10_hyperplane_card
#print axioms HoggarBound.AuditUpgrades.clifford_preserves_symp
#print axioms HoggarBound.AuditUpgrades.clifford_transport_comm_product
#print axioms HoggarBound.AuditUpgrades.clifford_transport_opA
#print axioms HoggarBound.AuditUpgrades.clifford_transport_carrier_charpoly
#print axioms HoggarBound.AuditUpgrades.clifford_transport_completion_charpoly
#print axioms HoggarBound.AuditUpgrades.clifford_transport_strict_law_fails
#print axioms HoggarBound.AuditUpgrades.completionMat_isHermitian
#print axioms HoggarBound.AuditUpgrades.real_hermitian_charpoly_eq_iff_roots_eq
#print axioms HoggarBound.AuditUpgrades.strict_law_fails_to_spectra
#print axioms HoggarBound.AuditUpgrades.jonah_conjecture_e_all_nine_cases_spectra
#print axioms HoggarBound.AuditUpgrades.c3SdpBlock_pos_def
#print axioms HoggarBound.AuditUpgrades.c3_shift_quad_zero
#print axioms HoggarBound.AuditUpgrades.corollary16_sigmaB_sdp_lower
#print axioms HoggarBound.AuditUpgrades.corollary16_sigmaA_witness
#print axioms HoggarBound.AuditUpgrades.corollary16_binary_minima_tightened

-- C3ExactOptima (v1.8.0): Exact global binary completion optima of four-qubit C3 (368 and 344, gap 24)
#print axioms HoggarBound.C3ExactOptima.corollary16_sigmaA_exact_lower
#print axioms HoggarBound.C3ExactOptima.corollary16_sigmaB_exact_lower
#print axioms HoggarBound.C3ExactOptima.corollary16_exact_binary_optima

-- SaturatedPhaseSix & NormPhaseFamily (v1.8.0): Infinite non-closed contextual floor-saturating family |Ψ_{3m}⟩
#print axioms HoggarBound.det6_card
#print axioms HoggarBound.det6_contexts
#print axioms HoggarBound.det6_degree
#print axioms HoggarBound.NormPhaseFamily.detPhase_isFlatState
#print axioms HoggarBound.NormPhaseFamily.detSupport_card
#print axioms HoggarBound.NormPhaseFamily.detSupport_not_closed
#print axioms HoggarBound.NormPhaseFamily.detSupport_flags_card
#print axioms HoggarBound.NormPhaseFamily.infinite_nonclosed_saturated_family
#print axioms HoggarBound.NormPhaseFamily.infinite_nonclosed_family_contextual

-- ExactDegreesN4N5 (v1.8.0): Transvection invariance, CSS witnesses (315, 1575, 6975), ladders,
-- unconditional Kramers-lifted bounds (W(7,2) ≥ 1455, Q⁺(9,2) ≥ 6444), Lemmas L1 & L4, master reduction
#print axioms HoggarBound.ExactDegreesN4N5.transv_violatedLines_eq
#print axioms HoggarBound.ExactDegreesN4N5.q7minus_css_witness
#print axioms HoggarBound.ExactDegreesN4N5.w72_css_witness
#print axioms HoggarBound.ExactDegreesN4N5.q9plus_css_witness
#print axioms HoggarBound.ExactDegreesN4N5.d_W72_of_Q7minus
#print axioms HoggarBound.ExactDegreesN4N5.d_Q9plus_of_W72
#print axioms HoggarBound.ExactDegreesN4N5.w72_ge_1455
#print axioms HoggarBound.ExactDegreesN4N5.q9plus_ge_6444
#print axioms HoggarBound.ExactDegreesN4N5.lemma_L1_q7minus_section_le_92
#print axioms HoggarBound.ExactDegreesN4N5.lemma_L4_w52_hyperplane_le_21
#print axioms HoggarBound.ExactDegreesN4N5.exact_degrees_n4_n5_of_q7minus_315

-- NonVacuity (v1.9.0): Explicit non-vacuity witness lemmas for every headline theorem family
#print axioms HoggarBound.NonVacuity.spectral_floor_nonvacuous
#print axioms HoggarBound.NonVacuity.kramers_nonvacuous
#print axioms HoggarBound.NonVacuity.saturation_tfae_nonvacuous
#print axioms HoggarBound.NonVacuity.conjecture_e_nonvacuous
#print axioms HoggarBound.NonVacuity.clifford_transport_nonvacuous
#print axioms HoggarBound.NonVacuity.cone_lift_nonvacuous
#print axioms HoggarBound.NonVacuity.norm_phase_family_nonvacuous
#print axioms HoggarBound.NonVacuity.c3_exact_optima_nonvacuous
#print axioms HoggarBound.NonVacuity.exact_degrees_ladders_nonvacuous
#print axioms HoggarBound.NonVacuity.propositions_qgt_twochar_nonvacuous

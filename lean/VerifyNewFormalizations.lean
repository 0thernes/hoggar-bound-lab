/- Axiom audit for the new formalizations closing the gaps of the combined paper
   (Sections 1.1, 2.2, 3, 4, 5.1, 8.5–8.7, 9.3, and 12):
   - Theorem 2: Quaternionic / Kramers spectral floor & elliptic quadrics Q⁻(2N-1,2) (`Kramers.lean`)
   - Theorems 3 & 4: Full 5-way saturation equivalences & (2^N-1)|S| = □ (`SaturationTheory.lean`)
   - Lemmas 20 & 21 and Theorem 22 (Universal Cubic-Trace Identity) (`ConjectureECore.lean`)
   - Theorem 19: Jonah's Conjecture E in all nine vertex cases for every N ≥ 4
     (`ConjectureECones.lean`, `ConjectureE.lean`)
   - Corollaries 16 & 18: Four-qubit C3 binary completion minima separation (≤ 344 < 347) and
     general cone lift from C3 to C11 for every N ≥ 4 (`ConjectureEExtras.lean`)

   Every `#print axioms` line must report a subset of `[propext, Classical.choice, Quot.sound]`.

   run:
     cd lean && lake build HoggarBound.Kramers HoggarBound.SaturationTheory HoggarBound.ConjectureE HoggarBound.ConjectureEExtras && lake env lean VerifyNewFormalizations.lean -/
import HoggarBound.Kramers
import HoggarBound.SaturationTheory
import HoggarBound.ConjectureE
import HoggarBound.ConjectureEExtras

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

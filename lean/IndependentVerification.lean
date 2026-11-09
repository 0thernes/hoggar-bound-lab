/-
Standalone audit entry point. Run `lake env lean IndependentVerification.lean`.
The printed axiom lists are part of the audit output, not additional axioms.
-/
import HoggarBound
import HoggarBound.IndependentWitness
import HoggarBound.IndependentContexts

namespace HoggarBound

/-- The explicit Hoggar assignment is sign-valued. -/
theorem hoggar_assignment_valid :
    ∀ u ∈ allPoints 3, (hoggarSign u : ℝ) = 1 ∨ (hoggarSign u : ℝ) = -1 := by
  intro u _
  rcases hoggarSign_values u with h | h <;> simp [h]

/-- The kernel-checked finite witness violates exactly 63 unordered contexts. -/
theorem hoggar_contexts_exact :
    (violatedLines (allPoints 3) (fun u => (hoggarSign u : ℝ))).card = 63 := by
  have h0 : (0 : Pt 3) ∉ allPoints 3 := by simp [allPoints]
  have h := card_violated_eq_six (allPoints 3) h0 (fun u => (hoggarSign u : ℝ))
  rw [hoggar_violated_flags] at h
  omega

/-- The model contains exactly 315 three-qubit contexts. -/
theorem three_qubit_total_contexts : (contexts (allPoints 3)).card = 315 := by
  have h0 : (0 : Pt 3) ∉ allPoints 3 := by simp [allPoints]
  have h := card_flags_eq_six_contexts (allPoints 3) h0
  have hF := card_flags_all (N := 3)
  norm_num at hF
  omega

/-- Exact minimization statement: 63 is attained, and every assignment has at least 63.
The lower bound is analytic; the upper bound is a finite kernel-checked certificate. -/
theorem three_qubit_exact_minimum :
    (∃ f : Pt 3 → ℝ,
      (∀ u ∈ allPoints 3, f u = 1 ∨ f u = -1) ∧
      (violatedLines (allPoints 3) f).card = 63) ∧
    (∀ f : Pt 3 → ℝ,
      (∀ u ∈ allPoints 3, f u = 1 ∨ f u = -1) →
      63 ≤ (violatedLines (allPoints 3) f).card) := by
  exact ⟨⟨fun u => (hoggarSign u : ℝ), hoggar_assignment_valid, hoggar_contexts_exact⟩,
    three_qubit_contexts⟩

/-- An explicit consequence of the five-qubit real-quadric lower bound.
No assignment has exactly one fifth of the 23,715 contexts violated. -/
theorem five_qubit_hyperbolic_not_one_fifth
    (f : Pt 5 → ℝ)
    (hf : ∀ u ∈ realPoints 5, f u = 1 ∨ f u = -1) :
    (violatedLines (realPoints 5) f).card ≠ 4743 := by
  have h := five_qubit_hyperbolic_contexts f hf
  omega

/-- The stronger threshold itself, restated as impossibility of a smaller assignment. -/
theorem five_qubit_hyperbolic_no_assignment_below_6426 :
    ¬ ∃ f : Pt 5 → ℝ,
      (∀ u ∈ realPoints 5, f u = 1 ∨ f u = -1) ∧
      (violatedLines (realPoints 5) f).card < 6426 := by
  rintro ⟨f, hf, hsmall⟩
  have h := five_qubit_hyperbolic_contexts f hf
  omega

end HoggarBound

#print axioms HoggarBound.sum_cube_le
#print axioms HoggarBound.trace_cube_le
#print axioms HoggarBound.context_product
#print axioms HoggarBound.pauli_comm
#print axioms HoggarBound.trace_opA_cube
#print axioms HoggarBound.hoggar_bound
#print axioms HoggarBound.card_flags_all
#print axioms HoggarBound.full_space_bound
#print axioms HoggarBound.full_space_fraction
#print axioms HoggarBound.three_qubit_contexts
#print axioms HoggarBound.four_qubit_contexts
#print axioms HoggarBound.five_qubit_contexts
#print axioms HoggarBound.card_flags_real
#print axioms HoggarBound.four_qubit_hyperbolic_contexts
#print axioms HoggarBound.five_qubit_hyperbolic_contexts
#print axioms HoggarBound.five_qubit_hyperbolic_not_one_fifth
#print axioms HoggarBound.five_qubit_hyperbolic_no_assignment_below_6426
#print axioms HoggarBound.hoggar_flags_certificate
#print axioms HoggarBound.card_violated_eq_six
#print axioms HoggarBound.hoggar_contexts_exact
#print axioms HoggarBound.three_qubit_total_contexts
#print axioms HoggarBound.three_qubit_exact_minimum

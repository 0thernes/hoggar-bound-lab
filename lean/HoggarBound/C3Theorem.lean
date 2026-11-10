/- The exact certificate, connected to the previously formalized complex Pauli model. -/
import HoggarBound.C3Geometry
import HoggarBound.C3Certificate

open Matrix Finset

namespace HoggarBound.C3

noncomputable def basisEquiv : Fin 16 ≃ Vec 4 := Equiv.ofBijective bits bits_bijective

theorem section_image : sectionCodes.image codePoint =
    (realPoints 4).filter (fun u => symp u (codePoint 128) = 0) := by
  ext u
  obtain ⟨v, rfl⟩ := codePoint_bijective.2 u
  constructor
  · intro h
    obtain ⟨w, hw, heq⟩ := mem_image.1 h
    have hwv := codePoint_injective heq
    subst w
    exact mem_filter.2 ((section_correct v).1 hw)
  · intro h
    exact mem_image.2 ⟨v, (section_correct v).2 (mem_filter.1 h), rfl⟩

theorem outside_image : outsideCodes.image codePoint =
    (realPoints 4).filter (fun u => symp u (codePoint 128) ≠ 0) := by
  ext u
  obtain ⟨v, rfl⟩ := codePoint_bijective.2 u
  constructor
  · intro h
    obtain ⟨w, hw, heq⟩ := mem_image.1 h
    have hwv := codePoint_injective heq
    subst w
    exact mem_filter.2 ((outside_correct v).1 hw)
  · intro h
    exact mem_image.2 ⟨v, (outside_correct v).2 (mem_filter.1 h), rfl⟩

/-- The carrier is a sum of the original explicit complex Pauli operators. -/
noncomputable def pauliCarrier (f : Fin 256 → ℤ) : Matrix (Vec 4) (Vec 4) ℂ :=
  ∑ v ∈ sectionCodes, (f v : ℂ) • pauli (codePoint v)

theorem pauliCarrier_isHermitian (f : Fin 256 → ℤ) : (pauliCarrier f).IsHermitian := by
  unfold Matrix.IsHermitian pauliCarrier
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.conjTranspose_smul, (pauli_isHermitian (codePoint v)).eq]
  simp

theorem carrier_cast_reindex (f : Fin 256 → ℤ) :
    (carrierOf f).map (Int.castRingHom ℂ) =
      Matrix.reindex basisEquiv.symm basisEquiv.symm (pauliCarrier f) := by
  ext i j
  change ((carrierOf f) i j : ℂ) = pauliCarrier f (bits i) (bits j)
  simp only [carrierOf, pauliCarrier, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Int.cast_sum, Int.cast_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  have heven : bitCount4 (Nat.land (xCode v).val (zCode v).val) % 2 = 0 :=
    (mem_filter.1 (mem_filter.1 hv).1).2.2
  rw [realPauliCode_cast v heven]

/-- Exact characteristic-polynomial equality for the actual complex Pauli carriers. -/
theorem pauli_carrier_charpoly_eq :
    (pauliCarrier signA).charpoly = (pauliCarrier signB).charpoly := by
  have h : (carrierA.map (Int.castRingHom ℂ)).charpoly =
      (carrierB.map (Int.castRingHom ℂ)).charpoly := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, carrier_charpoly_eq]
  rw [← carrierA_from_section, ← carrierB_from_section,
    carrier_cast_reindex, carrier_cast_reindex,
    Matrix.charpoly_reindex, Matrix.charpoly_reindex] at h
  exact h

/-- Signed completion adjacency, directly in terms of commuting Pauli triples.
The outside labels enumerate every point of the complement exactly once. -/
noncomputable def pauliCompletion (f : Fin 256 → ℤ) : Matrix (Fin 64) (Fin 64) ℝ := fun i j =>
  let u := outsideLabel i
  let v := outsideLabel j
  let s := codeAdd u v
  if s ∈ sectionCodes ∧ symp (codePoint u) (codePoint v) = 0 then
    (f s : ℝ) * lineSign (codePoint u) (codePoint v)
  else 0

theorem completion_cast (f : Fin 256 → ℤ) :
    (completionOf f).map (Int.castRingHom ℝ) = pauliCompletion f := by
  ext i j
  change ((completionOf f i j : ℤ) : ℝ) = pauliCompletion f i j
  simp only [completionOf, pauliCompletion]
  split_ifs <;> simp [lineSign_eq_integer]

theorem pauli_completionA_trace_cube : (pauliCompletion signA ^ 3).trace = 14976 := by
  rw [← completion_cast, completionA_from_contexts, ← Matrix.map_pow,
    ← AddMonoidHom.map_trace, completionA_trace_cube]
  norm_num

theorem pauli_completionB_trace_cube : (pauliCompletion signB ^ 3).trace = 15360 := by
  rw [← completion_cast, completionB_from_contexts, ← Matrix.map_pow,
    ← AddMonoidHom.map_trace, completionB_trace_cube]
  norm_num

theorem pauli_completion_cube_traces_ne :
    (pauliCompletion signA ^ 3).trace ≠ (pauliCompletion signB ^ 3).trace := by
  rw [pauli_completionA_trace_cube, pauli_completionB_trace_cube]
  norm_num

/-- **Four-qubit C3 counterexample.** Sign carriers on the hyperbolic Pauli section have
identical carrier characteristic polynomials and different completion cubic moments. -/
theorem four_qubit_C3_counterexample :
    ∃ f g : Fin 256 → ℤ,
      (∀ v ∈ sectionCodes, f v = 1 ∨ f v = -1) ∧
      (∀ v ∈ sectionCodes, g v = 1 ∨ g v = -1) ∧
      (pauliCarrier f).charpoly = (pauliCarrier g).charpoly ∧
      (pauliCompletion f ^ 3).trace = 14976 ∧
      (pauliCompletion g ^ 3).trace = 15360 := by
  exact ⟨signA, signB, fun v _ => signA_values v, fun v _ => signB_values v,
    pauli_carrier_charpoly_eq, pauli_completionA_trace_cube, pauli_completionB_trace_cube⟩

end HoggarBound.C3

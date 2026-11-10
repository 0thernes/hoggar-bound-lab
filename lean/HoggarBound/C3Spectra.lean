/- Spectral consequences of the finite C3 certificate. -/
import Mathlib.Analysis.Matrix.Spectrum
import HoggarBound.IndependentContexts
import HoggarBound.C3Theorem

open Matrix Finset

namespace HoggarBound.C3

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of each power of a Hermitian matrix is its eigenvalue power sum. -/
theorem hermitian_trace_pow {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k := by
  conv_lhs =>
    rw [hA.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
      Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp

/-- Equal characteristic polynomials of Hermitian matrices give equal power traces. -/
theorem hermitian_trace_pow_eq_of_charpoly_eq {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) (k : ℕ) :
    (A ^ k).trace = (B ^ k).trace := by
  rw [hermitian_trace_pow hA, hermitian_trace_pow hB,
    (hA.eigenvalues_eq_eigenvalues_iff hB).2 h]

/-- The eigenvalue multiset of a Hermitian matrix determines its monic characteristic polynomial. -/
theorem hermitian_charpoly_eq_of_roots_eq {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly.roots = B.charpoly.roots) :
    A.charpoly = B.charpoly := by
  conv_lhs => rw [hA.splits_charpoly.eq_prod_roots_of_monic A.charpoly_monic]
  conv_rhs => rw [hB.splits_charpoly.eq_prod_roots_of_monic B.charpoly_monic]
  rw [h]

/-- Symmetry of signed-context adjacency is structural, not a finite matrix computation. -/
theorem signed_context_adjacency_isHermitian {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    {N : ℕ} (S : Finset κ) (point : κ → Pt N) (outside : ι → κ)
    (add : κ → κ → κ) (hadd : ∀ u v, add u v = add v u) (f : κ → ℝ) :
    Matrix.IsHermitian (Matrix.of fun (i j : ι) => if add (outside i) (outside j) ∈ S ∧
        symp (point (outside i)) (point (outside j)) = 0 then
      f (add (outside i) (outside j)) * lineSign (point (outside i)) (point (outside j))
    else 0) := by
  rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
  intro i j
  simp only [Matrix.of_apply]
  rw [hadd (outside j) (outside i), symp_comm (point (outside j)) (point (outside i))]
  split_ifs with h
  · rw [lineSign_swap h.2]
  · rfl

/-- Every real signed-context completion operator is Hermitian. -/
theorem pauliCompletion_isHermitian (f : Fin 256 → ℤ) : (pauliCompletion f).IsHermitian := by
  change Matrix.IsHermitian (Matrix.of fun (i j : Fin 64) =>
    if codeAdd (outsideLabel i) (outsideLabel j) ∈ sectionCodes ∧
        symp (codePoint (outsideLabel i)) (codePoint (outsideLabel j)) = 0 then
      (f (codeAdd (outsideLabel i) (outsideLabel j)) : ℝ) *
        lineSign (codePoint (outsideLabel i)) (codePoint (outsideLabel j))
    else 0)
  exact signed_context_adjacency_isHermitian sectionCodes codePoint outsideLabel codeAdd
      (fun u v => by
        apply Fin.ext
        change Nat.xor u.val v.val % 256 = Nat.xor v.val u.val % 256
        simpa only [Nat.xor_eq] using
          congrArg (fun w : ℕ => w % 256) (Nat.xor_comm u.val v.val)) (fun v => (f v : ℝ))

/-- The actual complex Pauli carriers have equal canonical real eigenvalue lists. -/
theorem pauli_carrier_eigenvalues_eq :
    (pauliCarrier_isHermitian signA).eigenvalues =
      (pauliCarrier_isHermitian signB).eigenvalues :=
  ((pauliCarrier_isHermitian signA).eigenvalues_eq_eigenvalues_iff
    (pauliCarrier_isHermitian signB)).2 pauli_carrier_charpoly_eq

/-- The actual C3 completion matrices have different characteristic polynomials. -/
theorem pauli_completion_charpoly_ne :
    (pauliCompletion signA).charpoly ≠ (pauliCompletion signB).charpoly := by
  intro h
  exact pauli_completion_cube_traces_ne
    (hermitian_trace_pow_eq_of_charpoly_eq (pauliCompletion_isHermitian signA)
      (pauliCompletion_isHermitian signB) h 3)

/-- The canonical eigenvalue lists differ, retaining every multiplicity. -/
theorem pauli_completion_eigenvalues_ne :
    (pauliCompletion_isHermitian signA).eigenvalues ≠
      (pauliCompletion_isHermitian signB).eigenvalues := by
  intro h
  exact pauli_completion_charpoly_ne
    (((pauliCompletion_isHermitian signA).eigenvalues_eq_eigenvalues_iff
      (pauliCompletion_isHermitian signB)).1 h)

/-- The real eigenvalue multisets differ, rather than merely their chosen indexing. -/
theorem pauli_completion_eigenvalue_multisets_ne :
    (pauliCompletion signA).charpoly.roots ≠ (pauliCompletion signB).charpoly.roots := by
  intro h
  exact pauli_completion_charpoly_ne
    (hermitian_charpoly_eq_of_roots_eq (pauliCompletion_isHermitian signA)
      (pauliCompletion_isHermitian signB) h)

/-- A fully spectral formulation of the explicit four-qubit C3 example. -/
theorem four_qubit_C3_spectral_counterexample :
    (pauliCarrier signA).charpoly = (pauliCarrier signB).charpoly ∧
    (pauliCompletion signA).charpoly ≠ (pauliCompletion signB).charpoly ∧
    (pauliCompletion signA).charpoly.roots ≠ (pauliCompletion signB).charpoly.roots :=
  ⟨pauli_carrier_charpoly_eq, pauli_completion_charpoly_ne,
    pauli_completion_eigenvalue_multisets_ne⟩

end HoggarBound.C3

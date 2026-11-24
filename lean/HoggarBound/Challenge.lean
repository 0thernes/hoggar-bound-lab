/-
Hoggar Bound Lab — Isolated Statement-Fidelity Challenge File (`lake comparator`).

This file contains ONLY the target statements of the headline theorems, importing only the
foundational geometry/operator definitions (`Bound`, `Counting`, `Quadric`, `C3Geometry`,
`ConjectureECore`, `ConjectureEExtras`) and NONE of the proof modules (`ConjectureE`,
`AuditUpgrades`, `C3ExactOptima`, `NormPhaseFamily`, `SaturatedPhaseSix`, `ExactDegreesN4N5`,
`SaturationTheory`).

NOTE: Every `sorry` in this file is intentional — `Challenge.lean` is the specification stub
checked against the sorry-free `HoggarBound.Solution` module by:

    lake comparator --config comparator.json --paranoid

which verifies definitional statement identity, enforces `[propext, Quot.sound, Classical.choice]`,
and replays the full proof export through all six bundled Lean 4.35.0 kernels
(official C++ kernel, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
-/
import HoggarBound.Bound
import HoggarBound.Counting
import HoggarBound.IndependentContexts
import HoggarBound.Quadric
import HoggarBound.C3Geometry
import HoggarBound.ConjectureECore
import HoggarBound.ConjectureEExtras

open Finset Matrix

namespace HoggarBound.ComparatorTarget

/-- Target 1 (Theorem 1): Universal spectral floor for arbitrary N-qubit Pauli subsets. -/
theorem target_spectral_floor {N : ℕ} (hN : 1 ≤ N) (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S)
    (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ N - 1) * beta6 S f ≤
      ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card) := by
  sorry

/-- Target 2 (Theorem 2): Quaternionic / Kramers spectral floor for N ≥ 2. -/
theorem target_kramers_floor {N : ℕ} (hN : 2 ≤ N) (w : Pt N) (hw : qform w = 1)
    (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S)
    (hS : ∀ u ∈ S, qform u + symp w u = 0)
    (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ (N - 1) - 1) * beta6 S f ≤
      ((2 : ℝ) ^ (N - 1) - 2) * S.card * Real.sqrt (((2 : ℝ) ^ (N - 1) - 1) * S.card) := by
  sorry

/-- Target 3 (Theorem 4): Saturation forces `(2^N - 1) * |S|` to be a perfect square. -/
theorem target_saturation_mul_isSquare {N : ℕ} (hN : 2 ≤ N) (S : Finset (Pt N)) (hne : S.Nonempty)
    (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1)
    (hsat : ((2 : ℝ) ^ N - 1) * beta6 S f =
      ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card)) :
    ∃ k : ℕ, (2 ^ N - 1) * S.card = k ^ 2 := by
  sorry

/-- Target 4 (Theorem 13b): Infinite non-closed contextual floor-saturating family for all `m ≥ 1`. -/
theorem target_infinite_nonclosed_saturated_family (m : ℕ) (hm : 1 ≤ m) :
    let q := 2 ^ m
    ∃ S : Finset (Pt (3 * m)),
      (0 : Pt (3 * m)) ∉ S ∧
      S.card = (q ^ 3 - 1) * q ^ 2 ∧
      (∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ symp u v = 0 ∧ u + v ∉ S) ∧
      6 * (contexts S).card = (q ^ 3 - 1) * q ^ 4 * (q ^ 2 + q - 3) ∧
      (∀ f : Pt (3 * m) → ℝ, (∀ u ∈ S, f u = 1 ∨ f u = -1) →
        (q ^ 3 - 1) * q ^ 3 * (q - 1) * (q - 2) ≤ 12 * (violatedLines S f).card) ∧
      (∃ f : Pt (3 * m) → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
        12 * (violatedLines S f).card = (q ^ 3 - 1) * q ^ 3 * (q - 1) * (q - 2)) := by
  sorry

/-- Target 5 (Theorem 16''): Exact four-qubit C3 global binary completion optima (368 and 344, gap 24). -/
theorem target_c3_exact_binary_optima :
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      368 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y) ∧
    (∃ y₀ : Fin 64 → ℝ, (∀ i, y₀ i = 1 ∨ y₀ i = -1) ∧
      HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y₀ = 368) ∧
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      344 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signB y) ∧
    (∃ y₁ : Fin 64 → ℝ, (∀ i, y₁ i = 1 ∨ y₁ i = -1) ∧
      HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signB y₁ = 344) := by
  sorry

/-- Target 6 (Theorem 19): Jonah's Conjecture E across all nine vertex cases for every `N ≥ 4`
(characteristic polynomial & canonical Hermitian eigenvalue-multiset separation). -/
theorem target_jonah_conjecture_e_all_nine_cases {N : ℕ} (hN : 4 ≤ N) :
    let fails (X : Finset (Pt N)) (d : Pt N) : Prop :=
      ∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
        (opA (HoggarBound.ConjectureE.sectionOf X d) σ).charpoly =
          (opA (HoggarBound.ConjectureE.sectionOf X d) τ).charpoly ∧
        (HoggarBound.ConjectureE.completionMat X d σ).charpoly ≠
          (HoggarBound.ConjectureE.completionMat X d τ).charpoly
    fails (allPoints N) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.quadric N 0) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.quadric N (HoggarBound.ConjectureE.ptY ⟨1, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (allPoints N) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N 0) (HoggarBound.ConjectureE.ptY ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N 0) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N 0) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptY ⟨1, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N (HoggarBound.ConjectureE.ptY ⟨2, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N (HoggarBound.ConjectureE.ptY ⟨2, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptY ⟨1, by omega⟩) := by
  sorry

/-- Target 7 (Classical N=4): Unconditional Kramers-lifted lower bound `d(W(7,2)) ≥ 1455`. -/
theorem target_w72_ge_1455 (f : Pt 4 → ℝ) (hf : ∀ u ∈ allPoints 4, f u = 1 ∨ f u = -1) :
    1455 ≤ (violatedLines (allPoints 4) f).card := by
  sorry

/-- Target 8 (Classical N=5): Unconditional Kramers-lifted lower bound `d(Q⁺(9,2)) ≥ 6444`. -/
theorem target_q9plus_ge_6444 (f : Pt 5 → ℝ) (hf : ∀ u ∈ realPoints 5, f u = 1 ∨ f u = -1) :
    6444 ≤ (violatedLines (realPoints 5) f).card := by
  sorry

end HoggarBound.ComparatorTarget

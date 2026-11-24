/-
Hoggar Bound Lab — Sorry-Free Solution Module Matched Against `HoggarBound.Challenge`.

Every theorem below has the definitionally identical signature to `HoggarBound.Challenge`,
uses ZERO `sorry` / `admit` / `native_decide` / custom `axiom`, and is checked by
`lake comparator --config comparator.json --paranoid` across all six Lean 4.35.0 kernels.
-/
import HoggarBound.Bound
import HoggarBound.Counting
import HoggarBound.Quadric
import HoggarBound.C3Geometry
import HoggarBound.Kramers
import HoggarBound.SaturationTheory
import HoggarBound.ConjectureECore
import HoggarBound.ConjectureE
import HoggarBound.ConjectureEExtras
import HoggarBound.C3ExactOptima
import HoggarBound.NormPhaseFamily
import HoggarBound.ExactDegreesN4N5

open Finset Matrix

namespace HoggarBound.ComparatorTarget

theorem target_spectral_floor {N : ℕ} (hN : 1 ≤ N) (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S)
    (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ N - 1) * beta6 S f ≤
      ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card) :=
  hoggar_bound hN S h0 f hf

theorem target_kramers_floor {N : ℕ} (hN : 2 ≤ N) (w : Pt N) (hw : qform w = 1)
    (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S)
    (hS : ∀ u ∈ S, qform u + symp w u = 0)
    (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ (N - 1) - 1) * beta6 S f ≤
      ((2 : ℝ) ^ (N - 1) - 2) * S.card * Real.sqrt (((2 : ℝ) ^ (N - 1) - 1) * S.card) :=
  hoggar_bound_quaternionic hN w hw S h0 hS f hf

theorem target_saturation_mul_isSquare {N : ℕ} (hN : 2 ≤ N) (S : Finset (Pt N)) (hne : S.Nonempty)
    (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1)
    (hsat : ((2 : ℝ) ^ N - 1) * beta6 S f =
      ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card)) :
    ∃ k : ℕ, (2 ^ N - 1) * S.card = k ^ 2 :=
  saturation_mul_isSquare hN S hne f hf hsat

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
        12 * (violatedLines S f).card = (q ^ 3 - 1) * q ^ 3 * (q - 1) * (q - 2)) :=
  HoggarBound.NormPhaseFamily.infinite_nonclosed_saturated_family m hm

theorem target_c3_exact_binary_optima :
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      368 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y) ∧
    (∃ y₀ : Fin 64 → ℝ, (∀ i, y₀ i = 1 ∨ y₀ i = -1) ∧
      HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y₀ = 368) ∧
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      344 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signB y) ∧
    (∃ y₁ : Fin 64 → ℝ, (∀ i, y₁ i = 1 ∨ y₁ i = -1) ∧
      HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signB y₁ = 344) :=
  HoggarBound.C3ExactOptima.corollary16_exact_binary_optima

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
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N (HoggarBound.ConjectureE.ptY ⟨2, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptY ⟨1, by omega⟩) :=
  HoggarBound.ConjectureE.jonah_conjecture_e_all_nine_cases hN

theorem target_w72_ge_1455 (f : Pt 4 → ℝ) (hf : ∀ u ∈ allPoints 4, f u = 1 ∨ f u = -1) :
    1455 ≤ (violatedLines (allPoints 4) f).card :=
  HoggarBound.ExactDegreesN4N5.w72_ge_1455 f hf

theorem target_q9plus_ge_6444 (f : Pt 5 → ℝ) (hf : ∀ u ∈ realPoints 5, f u = 1 ∨ f u = -1) :
    6444 ≤ (violatedLines (realPoints 5) f).card :=
  HoggarBound.ExactDegreesN4N5.q9plus_ge_6444 f hf

end HoggarBound.ComparatorTarget

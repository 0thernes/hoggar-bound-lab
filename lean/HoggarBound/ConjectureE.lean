/-
Hoggar Bound Lab — Complete Lean 4 formalization of Jonah's Conjecture E
across ALL NINE vertex cases (C1, C3, C5, C6, C8, C11, C12, C14, C15) for every `N ≥ 4`.

This module completes the formalization of Theorem 19 of the unified paper (closing the
formalization gap listed in Sections 1.1, 9.3, and 12, where previously only case C3 was
formalized in Lean). Every statement is about the actual complex Pauli matrices
`HoggarBound.pauli` and real context signs `HoggarBound.lineSign`, with zero `sorry`,
zero `native_decide`, and only the three standard axioms `[propext, Classical.choice, Quot.sound]`.

Main theorems:
* `c1_strict_law_fails`  (`N ≥ 3`): complex graph on `W(2N-1,2)` with `d = Z₀`.
* `c3_strict_law_fails`  (`N ≥ 3`): real graph on `Q⁺(2N-1,2)` with `d = Z₀`.
* `c5_strict_law_fails`  (`N ≥ 4`): quaternionic graph on `Q⁻(2N-1,2)` (`c = Y₁`) with `d = Z₀`.
* `c6_strict_law_fails`  (`N ≥ 3`, in `ConjectureECones`): pair swap on cone `W ∩ Z₀⊥`, `d = Z₁`.
* `c8_strict_law_fails`  (`N ≥ 4`): Y-lifted C1 on `Q⁺ ∩ Y₀⊥`, `d = Z₁`.
* `c11_strict_law_fails` (`N ≥ 3`, in `ConjectureECones`): pair swap on cone `Q⁺ ∩ Z₀⊥`, `d = Z₁`.
* `c12_strict_law_fails` (`N ≥ 4`): complex graph on `Q⁺ ∩ Z₀⊥`, `e = Z₀, d = Y₁`.
* `c14_strict_law_fails` (`N ≥ 4`, in `ConjectureECones`): pair swap on cone `Q⁻ ∩ Z₀⊥`, `d = Z₁`.
* `c15_strict_law_fails` (`N ≥ 4`): complex graph on `Q⁻ ∩ Z₀⊥`, `e = Z₀, d = Y₁`.
* `jonah_conjecture_e_all_nine_cases` (`N ≥ 4`): combined master theorem for all nine vertex cases.
-/
import HoggarBound.ConjectureECones

open Finset Matrix
open scoped Kronecker

namespace HoggarBound.ConjectureE

/-! ### Part 1. Single-qubit prepending, `Z`-block split, `Y`-diagonalization, and Kronecker split -/

section QubitSplit

/-- Prepend qubit 0 with `(a0, c0)` onto an `m`-qubit Pauli label `u`. -/
def consPt {m : ℕ} (a0 c0 : ZMod 2) (u : Pt m) : Pt (m + 1) :=
  (Fin.cons a0 u.1, Fin.cons c0 u.2)

/-- Drop qubit 0 from an `(m+1)`-qubit Pauli label. -/
def tailPt {m : ℕ} (v : Pt (m + 1)) : Pt m :=
  (fun i => v.1 i.succ, fun i => v.2 i.succ)

@[simp] lemma tailPt_consPt {m : ℕ} (a0 c0 : ZMod 2) (u : Pt m) :
    tailPt (consPt a0 c0 u) = u := by
  ext i <;> simp [tailPt, consPt]

@[simp] lemma tailPt_mk_cons {m : ℕ} (a0 c0 : ZMod 2) (a c : Vec m) :
    tailPt (Fin.cons a0 a, Fin.cons c0 c) = (a, c) := by
  ext i <;> simp [tailPt]

@[simp] lemma consPt_fst_zero {m : ℕ} (a0 c0 : ZMod 2) (u : Pt m) :
    (consPt a0 c0 u).1 0 = a0 := rfl

@[simp] lemma consPt_snd_zero {m : ℕ} (a0 c0 : ZMod 2) (u : Pt m) :
    (consPt a0 c0 u).2 0 = c0 := rfl

lemma consPt_zero_ptZ {m : ℕ} (k : Fin m) :
    consPt 0 0 (ptZ k) = ptZ k.succ := by
  ext i <;> refine Fin.cases (by simp [consPt, ptZ, Fin.succ_ne_zero]) (fun j => by
    simp [consPt, ptZ, Pi.single_apply, Fin.succ_inj]) i

lemma consPt_zero_ptY {m : ℕ} (k : Fin m) :
    consPt 0 0 (ptY k) = ptY k.succ := by
  ext i <;> refine Fin.cases (by simp [consPt, ptY, Fin.succ_ne_zero]) (fun j => by
    simp [consPt, ptY, Pi.single_apply, Fin.succ_inj]) i

lemma consPt_tailPt {m : ℕ} (v : Pt (m + 1)) :
    consPt (v.1 0) (v.2 0) (tailPt v) = v := by
  ext i <;> refine Fin.cases ?_ ?_ i <;> simp [consPt, tailPt]

lemma consPt_eq_of_eq {m : ℕ} {v : Pt (m + 1)} {a0 c0 : ZMod 2}
    (ha : v.1 0 = a0) (hc : v.2 0 = c0) : consPt a0 c0 (tailPt v) = v := by
  rw [← ha, ← hc, consPt_tailPt]

lemma consPt_injective {m : ℕ} (a0 c0 : ZMod 2) : Function.Injective (consPt (m := m) a0 c0) :=
  fun u v h => by simpa [tailPt_consPt] using congrArg tailPt h

lemma consPt_add {m : ℕ} (a0 c0 a1 c1 : ZMod 2) (u v : Pt m) :
    consPt a0 c0 u + consPt a1 c1 v = consPt (a0 + a1) (c0 + c1) (u + v) := by
  ext i <;> refine Fin.cases ?_ ?_ i <;> simp [consPt]

lemma consPt_zero {m : ℕ} : consPt (m := m) 0 0 0 = 0 := by
  ext i <;> refine Fin.cases ?_ ?_ i <;> simp [consPt]

lemma consPt_eq_zero_iff {m : ℕ} (a0 c0 : ZMod 2) (u : Pt m) :
    consPt a0 c0 u = 0 ↔ a0 = 0 ∧ c0 = 0 ∧ u = 0 := by
  constructor
  · intro h
    have h1 := congrFun (congrArg Prod.fst h) 0
    have h2 := congrFun (congrArg Prod.snd h) 0
    have h3 := congrArg tailPt h
    simp only [consPt, Fin.cons_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] at h1 h2
    refine ⟨h1, h2, ?_⟩
    rw [tailPt_consPt] at h3
    exact h3
  · rintro ⟨rfl, rfl, rfl⟩; exact consPt_zero

lemma qform_consPt {m : ℕ} (a0 c0 : ZMod 2) (u : Pt m) :
    qform (consPt a0 c0 u) = c0 * a0 + qform u := by
  simp [qform, consPt, dotProduct, Fin.sum_univ_succ]

lemma symp_consPt {m : ℕ} (a0 c0 a1 c1 : ZMod 2) (u v : Pt m) :
    symp (consPt a0 c0 u) (consPt a1 c1 v) = c0 * a1 + c1 * a0 + symp u v := by
  simp only [symp, consPt, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

lemma ycount_consPt {m : ℕ} (a0 c0 : ZMod 2) (u : Pt m) :
    ycount (consPt a0 c0 u) = (if a0 = 1 ∧ c0 = 1 then 1 else 0) + ycount u := by
  unfold ycount
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp [consPt]

/-- Equivalence `Vec (m + 1) ≃ Vec m ⊕ Vec m` splitting by bit 0 (`0 ↦ inl`, `1 ↦ inr`). -/
def splitSum (m : ℕ) : Vec (m + 1) ≃ Vec m ⊕ Vec m where
  toFun x := if x 0 = 0 then Sum.inl (fun i => x i.succ) else Sum.inr (fun i => x i.succ)
  invFun
    | Sum.inl v => Fin.cons 0 v
    | Sum.inr v => Fin.cons 1 v
  left_inv x := by
    ext i
    refine Fin.cases ?_ ?_ i
    · rcases zmod2_cases (x 0) with h | h <;> simp [h]
    · intro j; rcases zmod2_cases (x 0) with h | h <;> simp [h]
  right_inv
    | Sum.inl v => by simp
    | Sum.inr v => by
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      simp [h10]

/-- Equivalence `Vec (m + 1) ≃ ZMod 2 × Vec m` splitting bit 0 into a Kronecker factor. -/
def splitProd (m : ℕ) : Vec (m + 1) ≃ ZMod 2 × Vec m where
  toFun x := (x 0, fun i => x i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv x := by ext i; refine Fin.cases (by simp) (fun j => by simp) i
  right_inv p := by ext <;> simp

/-- Single-qubit Pauli matrix `pauli1 a0 c0` on `ZMod 2`. -/
def pauli1 (a0 c0 : ZMod 2) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  fun x y => Complex.I ^ (if a0 = 1 ∧ c0 = 1 then 1 else 0)
    * (if x = y + a0 then eps (c0 * y) else 0)

lemma fin_cons_add {m : ℕ} (a b : ZMod 2) (u v : Vec m) :
    (Fin.cons a u : Vec (m + 1)) + Fin.cons b v = Fin.cons (a + b) (u + v) := by
  ext i; refine Fin.cases (by simp) (fun j => by simp) i

lemma fin_cons_eq_iff {m : ℕ} (a b : ZMod 2) (u v : Vec m) :
    (Fin.cons a u : Vec (m + 1)) = Fin.cons b v ↔ a = b ∧ u = v := by
  constructor
  · intro h; refine ⟨by simpa using congrFun h 0, ?_⟩; ext i; simpa using congrFun h i.succ
  · rintro ⟨rfl, rfl⟩; rfl

/-- Reindexing `pauli (consPt a0 c0 u)` via `splitProd` yields the exact Kronecker product
`pauli1 a0 c0 ⊗ₖ pauli u`. -/
theorem reindex_pauli_cons_prod {m : ℕ} (a0 c0 : ZMod 2) (u : Pt m) :
    Matrix.reindex (splitProd m) (splitProd m) (pauli (consPt a0 c0 u))
      = pauli1 a0 c0 ⊗ₖ pauli u := by
  have hy := ycount_consPt a0 c0 u
  ext ⟨x0, x⟩ ⟨y0, y⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, splitProd, Equiv.coe_fn_symm_mk,
    kroneckerMap_apply, pauli, pauli1, Matrix.smul_apply, smul_eq_mul, weyl]
  rw [hy, pow_add]
  simp only [consPt, fin_cons_add, fin_cons_eq_iff]
  have hchi : chi (Fin.cons c0 u.2) (Fin.cons y0 y) = eps (c0 * y0) * chi u.2 y := by
    simp only [chi, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, eps_add]
  by_cases h0 : x0 = y0 + a0 <;> by_cases hv : x = y + u.1
  · simp only [h0, hv, hchi, and_self, ↓reduceIte]; ring
  · simp only [h0, hv, and_false, ↓reduceIte, mul_zero]
  · simp only [h0, hv, false_and, ↓reduceIte, mul_zero, zero_mul]
  · simp only [h0, hv, false_and, ↓reduceIte, mul_zero]

/-- Reindexing `pauli (consPt 0 c0 u)` via `splitSum` gives `fromBlocks P_u 0 0 (eps c0 • P_u)`. -/
theorem reindex_pauli_cons_Z {m : ℕ} (c0 : ZMod 2) (u : Pt m) :
    Matrix.reindex (splitSum m) (splitSum m) (pauli (consPt 0 c0 u))
      = fromBlocks (pauli u) 0 0 (eps c0 • pauli u) := by
  have hy : ycount (consPt 0 c0 u) = ycount u := by
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp [ycount_consPt, h01]
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    (simp only [Matrix.reindex_apply, Matrix.submatrix_apply, splitSum, Equiv.coe_fn_symm_mk,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul, pauli, weyl];
     rw [hy]; simp only [consPt, fin_cons_add, fin_cons_eq_iff])
  · have hchi : chi (Fin.cons c0 u.2) (Fin.cons 0 y) = chi u.2 y := by
      simp [chi, dotProduct, Fin.sum_univ_succ]
    simp only [add_zero, true_and]
    by_cases h : x = y + u.1 <;> simp only [h, hchi, ↓reduceIte]
  · simp [h01]
  · simp [h01.symm]
  · have hchi : chi (Fin.cons c0 u.2) (Fin.cons 1 y) = eps c0 * chi u.2 y := by
      simp [chi, dotProduct, Fin.sum_univ_succ, eps_add]
    simp only [add_zero, true_and]
    by_cases h : x = y + u.1 <;> (simp only [h, hchi, ↓reduceIte]; ring)

/-- Reindexing `pauli (consPt 1 1 u)` (`Y ⊗ P_u`) via `splitSum` gives
`fromBlocks 0 (-I • P_u) (I • P_u) 0`. -/
theorem reindex_pauli_cons_Y {m : ℕ} (u : Pt m) :
    Matrix.reindex (splitSum m) (splitSum m) (pauli (consPt 1 1 u))
      = fromBlocks 0 ((-Complex.I) • pauli u) (Complex.I • pauli u) 0 := by
  have hy : ycount (consPt 1 1 u) = 1 + ycount u := by simp [ycount_consPt]
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    (simp only [Matrix.reindex_apply, Matrix.submatrix_apply, splitSum, Equiv.coe_fn_symm_mk,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul, pauli, weyl];
     rw [hy, pow_add, pow_one]; simp only [consPt, fin_cons_add, fin_cons_eq_iff])
  · simp [h01]
  · have hchi : chi (Fin.cons 1 u.2) (Fin.cons 1 y) = -chi u.2 y := by
      simp [chi, dotProduct, Fin.sum_univ_succ, eps_add]
    simp only [h11, true_and]
    by_cases h : x = y + u.1 <;> (simp only [h, hchi, ↓reduceIte]; ring)
  · have hchi : chi (Fin.cons 1 u.2) (Fin.cons 0 y) = chi u.2 y := by
      simp [chi, dotProduct, Fin.sum_univ_succ]
    simp only [zero_add, true_and]
    by_cases h : x = y + u.1 <;> (simp only [h, hchi, ↓reduceIte]; ring)
  · simp [h11, h01.symm]

/-- Invertible change-of-basis matrix `V_Y` diagonalizing `Y` on qubit 0 (no square roots). -/
def matVY (m : ℕ) : Matrix (Vec m ⊕ Vec m) (Vec m ⊕ Vec m) ℂ :=
  fromBlocks 1 1 (Complex.I • 1) ((-Complex.I) • 1)

/-- Inverse of `matVY m`. -/
noncomputable def matVYInv (m : ℕ) : Matrix (Vec m ⊕ Vec m) (Vec m ⊕ Vec m) ℂ :=
  (1 / 2 : ℂ) • fromBlocks 1 ((-Complex.I) • 1) 1 (Complex.I • 1)

lemma matVYInv_mul_matVY (m : ℕ) : matVYInv m * matVY m = 1 := by
  unfold matVYInv matVY
  rw [Matrix.smul_mul, fromBlocks_multiply]
  have h1 : (1 : Matrix (Vec m) (Vec m) ℂ) * 1 + ((-Complex.I) • (1 : Matrix (Vec m) (Vec m) ℂ)) * (Complex.I • 1)
      = (2 : ℂ) • 1 := by
    rw [one_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul]
    have hI : (-Complex.I) * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
    rw [hI, one_smul, two_smul]
  have h2 : (1 : Matrix (Vec m) (Vec m) ℂ) * 1 + ((-Complex.I) • (1 : Matrix (Vec m) (Vec m) ℂ)) * ((-Complex.I) • 1)
      = 0 := by
    rw [one_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul]
    have hI : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
    rw [hI, neg_one_smul, add_neg_cancel]
  have h3 : (1 : Matrix (Vec m) (Vec m) ℂ) * 1 + (Complex.I • (1 : Matrix (Vec m) (Vec m) ℂ)) * (Complex.I • 1)
      = 0 := by
    rw [one_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, Complex.I_mul_I,
      neg_one_smul, add_neg_cancel]
  have h4 : (1 : Matrix (Vec m) (Vec m) ℂ) * 1 + (Complex.I • (1 : Matrix (Vec m) (Vec m) ℂ)) * ((-Complex.I) • 1)
      = (2 : ℂ) • 1 := by
    rw [one_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul]
    have hI : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
    rw [hI, one_smul, two_smul]
  rw [h1, h2, h3, h4, fromBlocks_smul, smul_zero, smul_smul, ← fromBlocks_one]
  norm_num

lemma matVY_mul_matVYInv (m : ℕ) : matVY m * matVYInv m = 1 := by
  unfold matVYInv matVY
  rw [Matrix.mul_smul, fromBlocks_multiply]
  have h1 : (1 : Matrix (Vec m) (Vec m) ℂ) * 1 + (1 : Matrix (Vec m) (Vec m) ℂ) * 1 = (2 : ℂ) • 1 := by
    rw [one_mul, two_smul]
  have h2 : (1 : Matrix (Vec m) (Vec m) ℂ) * ((-Complex.I) • 1) + (1 : Matrix (Vec m) (Vec m) ℂ) * (Complex.I • 1)
      = 0 := by rw [one_mul, one_mul, neg_smul, neg_add_cancel]
  have h3 : (Complex.I • (1 : Matrix (Vec m) (Vec m) ℂ)) * 1 + ((-Complex.I) • (1 : Matrix (Vec m) (Vec m) ℂ)) * 1
      = 0 := by rw [mul_one, mul_one, neg_smul, add_neg_cancel]
  have h4 : (Complex.I • (1 : Matrix (Vec m) (Vec m) ℂ)) * ((-Complex.I) • 1)
      + ((-Complex.I) • (1 : Matrix (Vec m) (Vec m) ℂ)) * (Complex.I • 1) = (2 : ℂ) • 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, smul_smul]
    have ha : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
    have hb : (-Complex.I) * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
    rw [ha, hb, one_smul, two_smul]
  rw [h1, h2, h3, h4, fromBlocks_smul, smul_zero, smul_smul, ← fromBlocks_one]
  norm_num

lemma charpoly_conj_VY {m : ℕ} (M : Matrix (Vec m ⊕ Vec m) (Vec m ⊕ Vec m) ℂ) :
    (matVYInv m * M * matVY m).charpoly = M.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, matVY_mul_matVYInv, one_mul]

/-- Conjugating `I ⊗ P_u` or `Y ⊗ P_u` (`consPt b b u`) by `matVY` gives `P_u ⊕ (eps b • P_u)`. -/
theorem conj_VY_pauli_cons {m : ℕ} (b : ZMod 2) (u : Pt m) :
    matVYInv m * Matrix.reindex (splitSum m) (splitSum m) (pauli (consPt b b u)) * matVY m
      = fromBlocks (pauli u) 0 0 (eps b • pauli u) := by
  rcases zmod2_cases b with rfl | rfl
  · rw [reindex_pauli_cons_Z, eps_zero, one_smul]
    unfold matVYInv matVY
    rw [Matrix.smul_mul, Matrix.smul_mul, fromBlocks_multiply, fromBlocks_multiply]
    simp only [one_mul, mul_one, mul_zero, add_zero, zero_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have ha : (-Complex.I) * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
    have hb : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
    have hc : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
    rw [ha, hb, hc, Complex.I_mul_I, one_smul, neg_one_smul, add_neg_cancel, ← two_smul ℂ,
      fromBlocks_smul, smul_zero, smul_smul]
    norm_num
  · rw [reindex_pauli_cons_Y, eps_one, neg_one_smul]
    unfold matVYInv matVY
    rw [Matrix.smul_mul, Matrix.smul_mul, fromBlocks_multiply, fromBlocks_multiply]
    simp only [one_mul, mul_one, mul_zero, add_zero, zero_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hb : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
    have hc : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
    rw [hb, hc, Complex.I_mul_I, one_smul, neg_one_smul, add_neg_cancel, neg_add_cancel,
      ← two_smul ℂ, ← neg_add, ← two_smul ℂ, fromBlocks_smul, smul_zero, smul_neg, smul_smul]
    norm_num

/-- Transpose of a Pauli matrix: `(pauli u)ᵀ = eps (qform u) • pauli u`. -/
lemma pauli_transpose_eq {m : ℕ} (u : Pt m) : (pauli u)ᵀ = eps (qform u) • pauli u := by
  have hH : (pauli u)ᴴ = pauli u := (pauli_isHermitian u).eq
  have h1 : (pauli u)ᵀ = (pauli u).map star := by
    ext x y
    have hxy := congrFun (congrFun hH y) x
    simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply] using hxy.symm
  rw [h1, pauli_map_star]

/-- Shifted conjugation by `P_c` on `(pauli u)ᵀ`: `P_c * (P_u)ᵀ * P_c = eps(q_c(u)) • P_u`. -/
lemma pauli_conj_transpose_eq {m : ℕ} (c u : Pt m) :
    pauli c * (pauli u)ᵀ * pauli c = eps (qformShift c u) • pauli u := by
  rw [pauli_transpose_eq, Matrix.mul_smul, Matrix.smul_mul, pauli_comm u c, symp_comm u c,
    Matrix.smul_mul, Matrix.mul_assoc, pauli_mul_self, mul_one, smul_smul, ← eps_add]
  rfl

/-- General `Z₀`-block splitting of `opA H σ` when `H = {Z₀} ∪ {I⊗u, Z⊗u : u ∈ R}`. -/
theorem reindex_opA_Z_split {m : ℕ} (R : Finset (Pt m)) (h0 : (0 : Pt m) ∉ R)
    (H : Finset (Pt (m + 1)))
    (hH : H = insert (ptZ 0) (R.image (consPt 0 0) ∪ R.image (consPt 0 1)))
    (σ : Pt (m + 1) → ℝ) (hσ0 : σ (ptZ 0) = 1) :
    Matrix.reindex (splitSum m) (splitSum m) (opA H σ)
      = fromBlocks
          (1 + ∑ u ∈ R, (((σ (consPt 0 0 u) + σ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u) 0 0
          (-1 + ∑ u ∈ R, (((σ (consPt 0 0 u) - σ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u) := by
  have hptZ0 : ptZ (0 : Fin (m + 1)) = consPt 0 1 0 := by
    ext i <;> refine Fin.cases ?_ ?_ i <;> simp [ptZ, consPt]
  have hnot_mem : ptZ (0 : Fin (m + 1)) ∉ R.image (consPt 0 0) ∪ R.image (consPt 0 1) := by
    rw [hptZ0, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rintro (⟨u, _, hu⟩ | ⟨u, huR, hu⟩)
    · have := congrFun (congrArg Prod.snd hu) 0; simp [consPt] at this
    · have hu0 : u = 0 := consPt_injective 0 1 hu
      exact h0 (hu0 ▸ huR)
  have hdisj : Disjoint (R.image (consPt 0 0)) (R.image (consPt 0 1)) := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx0
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hx1
    have := congrFun (congrArg Prod.snd hv) 0
    simp [consPt] at this
  have hre_sum : Matrix.reindex (splitSum m) (splitSum m) (opA H σ)
      = ∑ s ∈ H, ((σ s : ℝ) : ℂ) • Matrix.reindex (splitSum m) (splitSum m) (pauli s) := by
    ext x y; simp [Matrix.reindex_apply, opA, Matrix.sum_apply, Matrix.smul_apply]
  rw [hre_sum, hH, Finset.sum_insert hnot_mem, Finset.sum_union hdisj,
    Finset.sum_image (fun _ _ _ _ h => consPt_injective 0 0 h),
    Finset.sum_image (fun _ _ _ _ h => consPt_injective 0 1 h),
    hσ0, hptZ0, reindex_pauli_cons_Z, pauli_zero, eps_one, neg_one_smul]
  simp only [Complex.ofReal_one, one_smul, reindex_pauli_cons_Z, eps_zero, eps_one, one_smul,
    neg_one_smul, ← Finset.sum_add_distrib]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂] <;>
    · congr 1
      funext u
      ring

end QubitSplit

/-! ### Part 2. Uniform `g ≥ 2` graph blocks (`B₁ * B₂ = 0`) for C1, C3, C5, C12, C15 -/

section GraphBlocks

/-- Graph carrier sign on `g`-qubit Pauli label `u` (`g ≥ 2`). -/
def gSign {g : ℕ} (hg : 2 ≤ g) (u : Pt g) : ℝ :=
  if u.1 = 0 then signEven (gv2 hg) 0 u.2
  else if qform u = 0 then signEven (uEdge hg u.1) u.1 u.2
  else signOdd (uEdge hg u.1) u.1 u.2

lemma gSign_eq_one_or {g : ℕ} (hg : 2 ≤ g) (u : Pt g) : gSign hg u = 1 ∨ gSign hg u = -1 := by
  unfold gSign
  split_ifs
  · exact signEven_eq_one_or _ _ _
  · exact signEven_eq_one_or _ _ _
  · exact signOdd_eq_one_or _ _ _

/-- Real graph `B₁` (diagonal peak at `gv2` + unmoved real edges), scaled by `2`. -/
def realB1 {g : ℕ} (hg : 2 ≤ g) : Matrix (Vec g) (Vec g) ℂ :=
  ((2 : ℂ) * (2 : ℂ) ^ g) • diagProj (gv2 hg)
    + ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => ¬ isMovedDir hg a),
        ((2 : ℂ) * (2 : ℂ) ^ (g - 1)) • edgeReal (uEdge hg a) a

/-- Real graph `B₂` (moved real edges `{gv1, gv2, gv3}`), scaled by `2`. -/
def realB2 {g : ℕ} (hg : 2 ≤ g) : Matrix (Vec g) (Vec g) ℂ :=
  ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => isMovedDir hg a),
    ((2 : ℂ) * (2 : ℂ) ^ (g - 1)) • edgeReal (uEdge hg a) a

/-- Complex graph `B₁` (diagonal peak at `gv2` + unmoved real & imaginary edges), scaled by `2`. -/
def complexB1 {g : ℕ} (hg : 2 ≤ g) : Matrix (Vec g) (Vec g) ℂ :=
  ((2 : ℂ) * (2 : ℂ) ^ g) • diagProj (gv2 hg)
    + ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => ¬ isMovedDir hg a),
        (((2 : ℂ) * (2 : ℂ) ^ (g - 1)) • edgeReal (uEdge hg a) a
          + ((2 : ℂ) * (2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag (uEdge hg a) a)

/-- Complex graph `B₂` (moved real & imaginary edges `{gv1, gv2, gv3}`), scaled by `2`. -/
def complexB2 {g : ℕ} (hg : 2 ≤ g) : Matrix (Vec g) (Vec g) ℂ :=
  ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => isMovedDir hg a),
    (((2 : ℂ) * (2 : ℂ) ^ (g - 1)) • edgeReal (uEdge hg a) a
      + ((2 : ℂ) * (2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag (uEdge hg a) a)

lemma realB1_col_support {g : ℕ} (hg : 2 ≤ g) {x y : Vec g} (hy : inTriVert hg y) :
    realB1 hg x y = 0 := by
  unfold realB1
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, diagProj]
  have h1 : ¬ (x = gv2 hg ∧ y = gv2 hg) := fun h => not_inTriVert_gv2 hg (h.2 ▸ hy)
  rw [ite_eq_right h1, mul_zero, zero_add]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hnot := uEdge_not_inTriVert_of_unmoved hg (Finset.mem_filter.mp ha).2
  have ha1 : ¬ (x = uEdge hg a + a ∧ y = uEdge hg a) := fun h => hnot.1 (h.2 ▸ hy)
  have ha2 : ¬ (x = uEdge hg a ∧ y = uEdge hg a + a) := fun h => hnot.2 (h.2 ▸ hy)
  simp [edgeReal, ha1, ha2]

lemma realB2_row_support {g : ℕ} (hg : 2 ≤ g) {y z : Vec g} (hy : ¬ inTriVert hg y) :
    realB2 hg y z = 0 := by
  unfold realB2
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hin := uEdge_inTriVert_of_moved hg (Finset.mem_filter.mp ha).2
  have ha1 : ¬ (y = uEdge hg a + a ∧ z = uEdge hg a) := fun h => hy (h.1 ▸ hin.2)
  have ha2 : ¬ (y = uEdge hg a ∧ z = uEdge hg a + a) := fun h => hy (h.1 ▸ hin.1)
  simp [edgeReal, ha1, ha2]

lemma realB1_mul_realB2 {g : ℕ} (hg : 2 ≤ g) : realB1 hg * realB2 hg = 0 := by
  ext x z
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hy : inTriVert hg y
  · rw [realB1_col_support hg hy, zero_mul]
  · rw [realB2_row_support hg hy, mul_zero]

lemma complexB1_col_support {g : ℕ} (hg : 2 ≤ g) {x y : Vec g} (hy : inTriVert hg y) :
    complexB1 hg x y = 0 := by
  unfold complexB1
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, diagProj]
  have h1 : ¬ (x = gv2 hg ∧ y = gv2 hg) := fun h => not_inTriVert_gv2 hg (h.2 ▸ hy)
  rw [ite_eq_right h1, mul_zero, zero_add]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hnot := uEdge_not_inTriVert_of_unmoved hg (Finset.mem_filter.mp ha).2
  have ha1 : ¬ (x = uEdge hg a + a ∧ y = uEdge hg a) := fun h => hnot.1 (h.2 ▸ hy)
  have ha2 : ¬ (x = uEdge hg a ∧ y = uEdge hg a + a) := fun h => hnot.2 (h.2 ▸ hy)
  simp [edgeReal, edgeImag, ha1, ha2]

lemma complexB2_row_support {g : ℕ} (hg : 2 ≤ g) {y z : Vec g} (hy : ¬ inTriVert hg y) :
    complexB2 hg y z = 0 := by
  unfold complexB2
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hin := uEdge_inTriVert_of_moved hg (Finset.mem_filter.mp ha).2
  have ha1 : ¬ (y = uEdge hg a + a ∧ z = uEdge hg a) := fun h => hy (h.1 ▸ hin.2)
  have ha2 : ¬ (y = uEdge hg a ∧ z = uEdge hg a + a) := fun h => hy (h.1 ▸ hin.1)
  simp [edgeReal, edgeImag, ha1, ha2]

lemma complexB1_mul_complexB2 {g : ℕ} (hg : 2 ≤ g) : complexB1 hg * complexB2 hg = 0 := by
  ext x z
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hy : inTriVert hg y
  · rw [complexB1_col_support hg hy, zero_mul]
  · rw [complexB2_row_support hg hy, mul_zero]

/-- Sum of `2 • gSign hg u • pauli u` over unmoved points of `allPoints g` is `-2 + complexB1`. -/
lemma sum_complex_unmoved {g : ℕ} (hg : 2 ≤ g) :
    ∑ u ∈ (allPoints g).filter (fun u => ¬ isMovedDir hg u.1),
        (((2 * gSign hg u : ℝ) : ℂ)) • pauli u
      = (-2 : ℂ) • (1 : Matrix (Vec g) (Vec g) ℂ) + complexB1 hg := by
  have h1g : 1 ≤ g := by omega
  -- Split by `u.1 = 0` vs `u.1 ≠ 0`.
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun u : Pt g => u.1 = 0)]
  -- Diagonal part (`u.1 = 0`).
  have hdiag_set : ((allPoints g).filter (fun u => ¬ isMovedDir hg u.1)).filter (fun u => u.1 = 0)
      = ((univ : Finset (Vec g)).erase 0).image (fun c => ((0 : Vec g), c)) := by
    ext ⟨a, c⟩
    simp only [allPoints, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨hne, _⟩, rfl⟩
      exact ⟨c, fun hc => hne (Prod.ext rfl hc), rfl⟩
    · rintro ⟨c', hc', h⟩
      rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      refine ⟨⟨fun h0 => hc' (congrArg Prod.snd h0), ?_⟩, rfl⟩
      rintro (h1 | h2 | h3)
      · exact gv_ne_01 hg h1.symm
      · exact gv_ne_02 hg h2.symm
      · exact gv_ne_03 hg h3.symm
  have hdiag : ∑ u ∈ ((allPoints g).filter (fun u => ¬ isMovedDir hg u.1)).filter (fun u => u.1 = 0),
        (((2 * gSign hg u : ℝ) : ℂ)) • pauli u
      = (-2 : ℂ) • (1 : Matrix (Vec g) (Vec g) ℂ) + ((2 : ℂ) * (2 : ℂ) ^ g) • diagProj (gv2 hg) := by
    rw [hdiag_set, Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)]
    have hterm : ∀ c ∈ (univ : Finset (Vec g)).erase 0,
        (((2 * gSign hg (0, c) : ℝ) : ℂ)) • pauli (0, c)
          = (2 : ℂ) • (((signEven (gv2 hg) 0 c : ℝ) : ℂ) • pauli (0, c)) := by
      intro c _
      rw [gSign, ite_eq_left rfl, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_smul]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, sum_diag_pauli, smul_sub, smul_smul]
    ext x y; simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]; ring
  -- Off-diagonal unmoved part (`u.1 ≠ 0` and `¬ isMovedDir hg u.1`).
  have hoff : ∑ u ∈ ((allPoints g).filter (fun u => ¬ isMovedDir hg u.1)).filter (fun u => ¬ u.1 = 0),
        (((2 * gSign hg u : ℝ) : ℂ)) • pauli u
      = ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => ¬ isMovedDir hg a),
          (((2 : ℂ) * (2 : ℂ) ^ (g - 1)) • edgeReal (uEdge hg a) a
            + ((2 : ℂ) * (2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag (uEdge hg a) a) := by
    have hset : ((allPoints g).filter (fun u => ¬ isMovedDir hg u.1)).filter (fun u => ¬ u.1 = 0)
        = ((univ.erase (0 : Vec g)).filter (fun a => ¬ isMovedDir hg a)) ×ˢ (univ : Finset (Vec g)) := by
      ext ⟨a, c⟩
      simp only [allPoints, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_product]
      constructor
      · rintro ⟨⟨_, hm⟩, ha0⟩; exact ⟨ha0, hm⟩
      · rintro ⟨ha0, hm⟩; exact ⟨⟨fun h => ha0 (congrArg Prod.fst h), hm⟩, ha0⟩
    rw [hset, Finset.sum_product]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_filter.mp ha).1
    rw [← Finset.sum_filter_add_sum_filter_not (s := (univ : Finset (Vec g)))
      (p := fun c => qform (a, c) = 0)]
    have h1 : ∑ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 0),
          (((2 * gSign hg (a, c) : ℝ) : ℂ)) • pauli (a, c)
        = ((2 : ℂ) * (2 : ℂ) ^ (g - 1)) • edgeReal (uEdge hg a) a := by
      have ht : ∀ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 0),
          (((2 * gSign hg (a, c) : ℝ) : ℂ)) • pauli (a, c)
            = (2 : ℂ) • (((signEven (uEdge hg a) a c : ℝ) : ℂ) • pauli (a, c)) := by
        intro c hc
        have hq : qform (a, c) = 0 := (Finset.mem_filter.mp hc).2
        rw [gSign, ite_eq_right ha0, ite_eq_left hq, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_smul]
      rw [Finset.sum_congr rfl ht, ← Finset.smul_sum, sum_real_pauli_dir h1g _ ha0, smul_smul]
    have h2 : ∑ c ∈ univ.filter (fun c : Vec g => ¬ qform (a, c) = 0),
          (((2 * gSign hg (a, c) : ℝ) : ℂ)) • pauli (a, c)
        = ((2 : ℂ) * (2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag (uEdge hg a) a := by
      have hf : univ.filter (fun c : Vec g => ¬ qform (a, c) = 0)
          = univ.filter (fun c : Vec g => qform (a, c) = 1) := by
        ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => (zmod2_cases _).resolve_left h, fun h => by rw [h]; decide⟩
      rw [hf]
      have ht : ∀ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 1),
          (((2 * gSign hg (a, c) : ℝ) : ℂ)) • pauli (a, c)
            = (2 : ℂ) • (((signOdd (uEdge hg a) a c : ℝ) : ℂ) • pauli (a, c)) := by
        intro c hc
        have hq : qform (a, c) = 1 := (Finset.mem_filter.mp hc).2
        have hq0 : qform (a, c) ≠ 0 := by rw [hq]; decide
        rw [gSign, ite_eq_right ha0, ite_eq_right hq0, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_smul]
      rw [Finset.sum_congr rfl ht, ← Finset.smul_sum, sum_imag_pauli_dir h1g _ ha0, smul_smul,
        mul_assoc]
    rw [h1, h2]
  rw [hdiag, hoff, add_assoc]
  rfl

/-- Sum of `2 • gSign hg u • pauli u` over moved points of `allPoints g` is `complexB2`. -/
lemma sum_complex_moved {g : ℕ} (hg : 2 ≤ g) :
    ∑ u ∈ (allPoints g).filter (fun u => isMovedDir hg u.1),
        (((2 * gSign hg u : ℝ) : ℂ)) • pauli u
      = complexB2 hg := by
  have h1g : 1 ≤ g := by omega
  have hset : (allPoints g).filter (fun u => isMovedDir hg u.1)
      = ((univ.erase (0 : Vec g)).filter (fun a => isMovedDir hg a)) ×ˢ (univ : Finset (Vec g)) := by
    ext ⟨a, c⟩
    simp only [allPoints, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_product]
    constructor
    · rintro ⟨_, hm⟩
      refine ⟨?_, hm⟩
      rcases hm with rfl | rfl | rfl
      · exact gv_ne_01 hg
      · exact gv_ne_02 hg
      · exact gv_ne_03 hg
    · rintro ⟨ha0, hm⟩; exact ⟨fun h => ha0 (congrArg Prod.fst h), hm⟩
  rw [hset, Finset.sum_product]
  unfold complexB2
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha0 : a ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_filter.mp ha).1
  rw [← Finset.sum_filter_add_sum_filter_not (s := (univ : Finset (Vec g)))
    (p := fun c => qform (a, c) = 0)]
  have h1 : ∑ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 0),
        (((2 * gSign hg (a, c) : ℝ) : ℂ)) • pauli (a, c)
      = ((2 : ℂ) * (2 : ℂ) ^ (g - 1)) • edgeReal (uEdge hg a) a := by
    have ht : ∀ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 0),
        (((2 * gSign hg (a, c) : ℝ) : ℂ)) • pauli (a, c)
          = (2 : ℂ) • (((signEven (uEdge hg a) a c : ℝ) : ℂ) • pauli (a, c)) := by
      intro c hc
      rw [gSign, ite_eq_right ha0, ite_eq_left (Finset.mem_filter.mp hc).2, Complex.ofReal_mul,
        Complex.ofReal_ofNat, mul_smul]
    rw [Finset.sum_congr rfl ht, ← Finset.smul_sum, sum_real_pauli_dir h1g _ ha0, smul_smul]
  have h2 : ∑ c ∈ univ.filter (fun c : Vec g => ¬ qform (a, c) = 0),
        (((2 * gSign hg (a, c) : ℝ) : ℂ)) • pauli (a, c)
      = ((2 : ℂ) * (2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag (uEdge hg a) a := by
    have hf : univ.filter (fun c : Vec g => ¬ qform (a, c) = 0)
        = univ.filter (fun c : Vec g => qform (a, c) = 1) := by
      ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => (zmod2_cases _).resolve_left h, fun h => by rw [h]; decide⟩
    rw [hf]
    have ht : ∀ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 1),
        (((2 * gSign hg (a, c) : ℝ) : ℂ)) • pauli (a, c)
          = (2 : ℂ) • (((signOdd (uEdge hg a) a c : ℝ) : ℂ) • pauli (a, c)) := by
      intro c hc
      have hq : qform (a, c) = 1 := (Finset.mem_filter.mp hc).2
      have hq0 : qform (a, c) ≠ 0 := by rw [hq]; decide
      rw [gSign, ite_eq_right ha0, ite_eq_right hq0, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_smul]
    rw [Finset.sum_congr rfl ht, ← Finset.smul_sum, sum_imag_pauli_dir h1g _ ha0, smul_smul,
      mul_assoc]
  rw [h1, h2]

/-- Sum of `2 • gSign hg u • pauli u` over unmoved real points `quadric g 0` is `-2 + realB1`. -/
lemma sum_real_unmoved {g : ℕ} (hg : 2 ≤ g) :
    ∑ u ∈ (quadric g 0).filter (fun u => ¬ isMovedDir hg u.1),
        (((2 * gSign hg u : ℝ) : ℂ)) • pauli u
      = (-2 : ℂ) • (1 : Matrix (Vec g) (Vec g) ℂ) + realB1 hg := by
  have h1g : 1 ≤ g := by omega
  have hq0 : ∀ u : Pt g, qformShift (0 : Pt g) u = qform u := fun u => by
    rw [qformShift, symp_comm, symp_zero_right, add_zero]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun u : Pt g => u.1 = 0)]
  have hdiag_set : ((quadric g 0).filter (fun u => ¬ isMovedDir hg u.1)).filter (fun u => u.1 = 0)
      = ((univ : Finset (Vec g)).erase 0).image (fun c => ((0 : Vec g), c)) := by
    ext ⟨a, c⟩
    simp only [quadric, hq0, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      true_and, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨hne, _⟩, _⟩, rfl⟩
      exact ⟨c, fun hc => hne (Prod.ext rfl hc), rfl⟩
    · rintro ⟨c', hc', h⟩
      rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      refine ⟨⟨⟨fun h0 => hc' (congrArg Prod.snd h0), by simp [qform]⟩, ?_⟩, rfl⟩
      rintro (h1 | h2 | h3)
      · exact gv_ne_01 hg h1.symm
      · exact gv_ne_02 hg h2.symm
      · exact gv_ne_03 hg h3.symm
  have hdiag : ∑ u ∈ ((quadric g 0).filter (fun u => ¬ isMovedDir hg u.1)).filter (fun u => u.1 = 0),
        (((2 * gSign hg u : ℝ) : ℂ)) • pauli u
      = (-2 : ℂ) • (1 : Matrix (Vec g) (Vec g) ℂ) + ((2 : ℂ) * (2 : ℂ) ^ g) • diagProj (gv2 hg) := by
    rw [hdiag_set, Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)]
    have hterm : ∀ c ∈ (univ : Finset (Vec g)).erase 0,
        (((2 * gSign hg (0, c) : ℝ) : ℂ)) • pauli (0, c)
          = (2 : ℂ) • (((signEven (gv2 hg) 0 c : ℝ) : ℂ) • pauli (0, c)) := by
      intro c _
      rw [gSign, ite_eq_left rfl, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_smul]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, sum_diag_pauli, smul_sub, smul_smul]
    ext x y; simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]; ring
  have hoff : ∑ u ∈ ((quadric g 0).filter (fun u => ¬ isMovedDir hg u.1)).filter (fun u => ¬ u.1 = 0),
        (((2 * gSign hg u : ℝ) : ℂ)) • pauli u
      = ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => ¬ isMovedDir hg a),
          ((2 : ℂ) * (2 : ℂ) ^ (g - 1)) • edgeReal (uEdge hg a) a := by
    have hset : ((quadric g 0).filter (fun u => ¬ isMovedDir hg u.1)).filter (fun u => ¬ u.1 = 0)
        = (((univ.erase (0 : Vec g)).filter (fun a => ¬ isMovedDir hg a)) ×ˢ (univ : Finset (Vec g))).filter
            (fun u => qform u = 0) := by
      ext ⟨a, c⟩
      simp only [quadric, hq0, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        true_and, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨_, hq⟩, hm⟩, ha0⟩; exact ⟨⟨ha0, hm⟩, hq⟩
      · rintro ⟨⟨ha0, hm⟩, hq⟩; exact ⟨⟨⟨fun h => ha0 (congrArg Prod.fst h), hq⟩, hm⟩, ha0⟩
    rw [hset, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_filter.mp ha).1
    rw [← Finset.sum_filter]
    have ht : ∀ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 0),
        (((2 * gSign hg (a, c) : ℝ) : ℂ)) • pauli (a, c)
          = (2 : ℂ) • (((signEven (uEdge hg a) a c : ℝ) : ℂ) • pauli (a, c)) := by
      intro c hc
      rw [gSign, ite_eq_right ha0, ite_eq_left (Finset.mem_filter.mp hc).2, Complex.ofReal_mul,
        Complex.ofReal_ofNat, mul_smul]
    rw [Finset.sum_congr rfl ht, ← Finset.smul_sum, sum_real_pauli_dir h1g _ ha0, smul_smul]
  rw [hdiag, hoff, add_assoc]
  rfl

/-- Sum of `2 • gSign hg u • pauli u` over moved real points `quadric g 0` is `realB2`. -/
lemma sum_real_moved {g : ℕ} (hg : 2 ≤ g) :
    ∑ u ∈ (quadric g 0).filter (fun u => isMovedDir hg u.1),
        (((2 * gSign hg u : ℝ) : ℂ)) • pauli u
      = realB2 hg := by
  have h1g : 1 ≤ g := by omega
  have hq0 : ∀ u : Pt g, qformShift (0 : Pt g) u = qform u := fun u => by
    rw [qformShift, symp_comm, symp_zero_right, add_zero]
  have hset : (quadric g 0).filter (fun u => isMovedDir hg u.1)
      = (((univ.erase (0 : Vec g)).filter (fun a => isMovedDir hg a)) ×ˢ (univ : Finset (Vec g))).filter
          (fun u => qform u = 0) := by
    ext ⟨a, c⟩
    simp only [quadric, hq0, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      true_and, Finset.mem_product]
    constructor
    · rintro ⟨⟨_, hq⟩, hm⟩
      refine ⟨⟨?_, hm⟩, hq⟩
      rcases hm with rfl | rfl | rfl
      · exact gv_ne_01 hg
      · exact gv_ne_02 hg
      · exact gv_ne_03 hg
    · rintro ⟨⟨ha0, hm⟩, hq⟩; exact ⟨⟨fun h => ha0 (congrArg Prod.fst h), hq⟩, hm⟩
  rw [hset, Finset.sum_filter, Finset.sum_product]
  unfold realB2
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha0 : a ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_filter.mp ha).1
  rw [← Finset.sum_filter]
  have ht : ∀ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 0),
      (((2 * gSign hg (a, c) : ℝ) : ℂ)) • pauli (a, c)
        = (2 : ℂ) • (((signEven (uEdge hg a) a c : ℝ) : ℂ) • pauli (a, c)) := by
    intro c hc
    rw [gSign, ite_eq_right ha0, ite_eq_left (Finset.mem_filter.mp hc).2, Complex.ofReal_mul,
      Complex.ofReal_ofNat, mul_smul]
  rw [Finset.sum_congr rfl ht, ← Finset.smul_sum, sum_real_pauli_dir h1g _ ha0, smul_smul]

end GraphBlocks

/-! ### Part 3. Unified Proof of Cases C1 and C3 (`N ≥ 3`) -/

section CasesC1C3

/-- Carrier `σ` for C1 / C3 on `g + 1` qubits (`d = Z₀`): all block terms in `C`. -/
def c13Sigma {g : ℕ} (hg : 2 ≤ g) (s : Pt (g + 1)) : ℝ :=
  if tailPt s = 0 then 1 else gSign hg (tailPt s)

/-- Carrier `τ` for C1 / C3 on `g + 1` qubits: flips `Z₀ ⊗ u` when `isMovedDir hg u.1`. -/
def c13Tau {g : ℕ} (hg : 2 ≤ g) (s : Pt (g + 1)) : ℝ :=
  if tailPt s = 0 then 1
  else if s.2 0 = 1 ∧ isMovedDir hg (tailPt s).1 then -gSign hg (tailPt s)
  else gSign hg (tailPt s)

lemma c13Sigma_eq_one_or {g : ℕ} (hg : 2 ≤ g) (s : Pt (g + 1)) :
    c13Sigma hg s = 1 ∨ c13Sigma hg s = -1 := by
  unfold c13Sigma
  split_ifs
  · left; rfl
  · exact gSign_eq_one_or hg _

lemma c13Tau_eq_one_or {g : ℕ} (hg : 2 ≤ g) (s : Pt (g + 1)) :
    c13Tau hg s = 1 ∨ c13Tau hg s = -1 := by
  unfold c13Tau
  split_ifs
  · left; rfl
  · rcases gSign_eq_one_or hg (tailPt s) with h | h <;> [right; left] <;> linarith
  · exact gSign_eq_one_or hg _

/-- Helper: trace-square difference at `z = ptZ 0` whenever `τ` flips `Z₀ ⊗ u` for `u` with `P u`
and at least one `u₀ ∈ R` satisfies `P u₀`. -/
lemma trace_sq_ne_of_flipped {m : ℕ} (R : Finset (Pt m)) (h0 : (0 : Pt m) ∉ R)
    (H : Finset (Pt (m + 1)))
    (hH : H = insert (ptZ 0) (R.image (consPt 0 0) ∪ R.image (consPt 0 1)))
    (P : Pt m → Prop) [DecidablePred P]
    (σ τ : Pt (m + 1) → ℝ)
    (hσ1 : ∀ u ∈ R, σ (consPt 0 0 u) = 1 ∨ σ (consPt 0 0 u) = -1)
    (hσeq : ∀ u ∈ R, σ (consPt 0 1 u) = σ (consPt 0 0 u))
    (hτ0 : ∀ u ∈ R, τ (consPt 0 0 u) = σ (consPt 0 0 u))
    (hτ1 : ∀ u ∈ R, τ (consPt 0 1 u) = if P u then -σ (consPt 0 0 u) else σ (consPt 0 0 u))
    (hex : ∃ u₀ ∈ R, P u₀) :
    (opA H σ ^ 2 * pauli (ptZ 0)).trace ≠ (opA H τ ^ 2 * pauli (ptZ 0)).trace := by
  have hcomm : ∀ s ∈ H, symp s (ptZ 0) = 0 := by
    intro s hs
    rw [hH, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hs
    rcases hs with rfl | ⟨u, _, rfl⟩ | ⟨u, _, rfl⟩
    · exact symp_ptZ_ptZ 0 0
    · rw [symp_ptZ]; rfl
    · rw [symp_ptZ]; rfl
  have hptZ0 : ptZ (0 : Fin (m + 1)) = consPt 0 1 0 := by
    ext i <;> refine Fin.cases ?_ ?_ i <;> simp [ptZ, consPt]
  have hfilt : H.filter (fun s => s + ptZ 0 ∈ H)
      = R.image (consPt 0 0) ∪ R.image (consPt 0 1) := by
    ext s
    rw [Finset.mem_filter, hH, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨rfl | h, hadd⟩
      · exfalso
        rw [pt_add_self] at hadd
        rw [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hadd
        rcases hadd with h0' | ⟨u, huR, hu⟩ | ⟨u, huR, hu⟩
        · exact ptZ_ne_zero 0 h0'.symm
        · exact h0 (((consPt_eq_zero_iff 0 0 u).mp hu).2.2 ▸ huR)
        · exact absurd ((consPt_eq_zero_iff 0 1 u).mp hu).2.1 (by decide)
      · exact h
    · intro hs
      refine ⟨Or.inr hs, ?_⟩
      rcases hs with ⟨u, huR, rfl⟩ | ⟨u, huR, rfl⟩
      · refine Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, huR, ?_⟩))
        rw [hptZ0, consPt_add, add_zero, zero_add, add_zero]
      · refine Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, huR, ?_⟩))
        rw [hptZ0, consPt_add, add_zero, zmod2_add_self, add_zero]
  have hdisj : Disjoint (R.image (consPt 0 0)) (R.image (consPt 0 1)) := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx0
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hx1
    have := congrFun (congrArg Prod.snd hv) 0; simp [consPt] at this
  have htau : ∀ s ∈ H, tau s (s + ptZ 0) = 1 := fun s hs =>
    tau_add_ptZ (by simpa [symp_ptZ] using hcomm s hs)
  have heval_diff :
      (∑ s ∈ H.filter (fun s => s + ptZ 0 ∈ H),
          ((σ s : ℝ) : ℂ) * ((σ (s + ptZ 0) : ℝ) : ℂ) * tau s (s + ptZ 0))
      - (∑ s ∈ H.filter (fun s => s + ptZ 0 ∈ H),
          ((τ s : ℝ) : ℂ) * ((τ (s + ptZ 0) : ℝ) : ℂ) * tau s (s + ptZ 0))
      = 4 * (((R.filter P).card : ℕ) : ℂ) := by
    rw [← Finset.sum_sub_distrib]
    have hclean : ∀ s ∈ H.filter (fun s => s + ptZ 0 ∈ H),
        ((σ s : ℝ) : ℂ) * ((σ (s + ptZ 0) : ℝ) : ℂ) * tau s (s + ptZ 0)
          - ((τ s : ℝ) : ℂ) * ((τ (s + ptZ 0) : ℝ) : ℂ) * tau s (s + ptZ 0)
        = ((σ s * σ (s + ptZ 0) - τ s * τ (s + ptZ 0) : ℝ) : ℂ) := by
      intro s hs
      rw [htau s (Finset.mem_filter.mp hs).1, mul_one, mul_one]
      push_cast; ring
    rw [Finset.sum_congr rfl hclean, hfilt, Finset.sum_union hdisj,
      Finset.sum_image (fun _ _ _ _ h => consPt_injective 0 0 h),
      Finset.sum_image (fun _ _ _ _ h => consPt_injective 0 1 h)]
    have hterm0 : ∀ u ∈ R,
        ((σ (consPt 0 0 u) * σ (consPt 0 0 u + ptZ 0)
            - τ (consPt 0 0 u) * τ (consPt 0 0 u + ptZ 0) : ℝ) : ℂ)
          = if P u then 2 else 0 := by
      intro u hu
      have hadd : consPt 0 0 u + ptZ 0 = consPt 0 1 u := by
        rw [hptZ0, consPt_add, add_zero, zero_add, add_zero]
      rw [hadd, hσeq u hu, hτ0 u hu, hτ1 u hu]
      by_cases hP : P u
      · rw [ite_eq_left hP, ite_eq_left hP]
        rcases hσ1 u hu with h | h <;> rw [h] <;> norm_num
      · rw [ite_eq_right hP, ite_eq_right hP]
        simp
    have hterm1 : ∀ u ∈ R,
        ((σ (consPt 0 1 u) * σ (consPt 0 1 u + ptZ 0)
            - τ (consPt 0 1 u) * τ (consPt 0 1 u + ptZ 0) : ℝ) : ℂ)
          = if P u then 2 else 0 := by
      intro u hu
      have hadd : consPt 0 1 u + ptZ 0 = consPt 0 0 u := by
        rw [hptZ0, consPt_add, add_zero, zmod2_add_self, add_zero]
      rw [hadd, hσeq u hu, hτ0 u hu, hτ1 u hu]
      by_cases hP : P u
      · rw [ite_eq_left hP, ite_eq_left hP]
        rcases hσ1 u hu with h | h <;> rw [h] <;> norm_num
      · rw [ite_eq_right hP, ite_eq_right hP]
        simp
    rw [Finset.sum_congr rfl hterm0, Finset.sum_congr rfl hterm1, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    ring
  rw [trace_opA_sq_mul_central σ (ptZ_ne_zero 0) hcomm,
    trace_opA_sq_mul_central τ (ptZ_ne_zero 0) hcomm]
  intro heq
  have hdiff : (2 : ℂ) ^ (m + 1) * (4 * (((R.filter P).card : ℕ) : ℂ)) = 0 := by
    linear_combination heq - (2 : ℂ) ^ (m + 1) * heval_diff
  have h2ne : (2 : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcard0 : (((R.filter P).card : ℕ) : ℂ) = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left h2ne)).resolve_left (by norm_num)
  have hcardN : (R.filter P).card = 0 := by exact_mod_cast hcard0
  obtain ⟨u₀, hu₀R, hu₀P⟩ := hex
  have hpos : 0 < (R.filter P).card := Finset.card_pos.mpr ⟨u₀, Finset.mem_filter.mpr ⟨hu₀R, hu₀P⟩⟩
  omega

/-- **Case C1 (all `N ≥ 3`).** Full symplectic space `W(2N-1, 2)` cut by `d = Z₀`. -/
theorem c1_strict_law_fails {g : ℕ} (hg : 2 ≤ g) :
    let d : Pt (g + 1) := ptZ 0
    let X : Finset (Pt (g + 1)) := allPoints (g + 1)
    ∃ σ τ : Pt (g + 1) → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  intro d X
  set R : Finset (Pt g) := allPoints g
  have h0R : (0 : Pt g) ∉ R := by simp [R, allPoints]
  have hH : sectionOf X d = insert (ptZ 0) (R.image (consPt 0 0) ∪ R.image (consPt 0 1)) := by
    ext s
    simp only [sectionOf, X, d, allPoints, R, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, Finset.mem_insert, Finset.mem_union, Finset.mem_image, symp_ptZ]
    constructor
    · rintro ⟨hs0, ha0⟩
      by_cases ht : tailPt s = 0
      · left
        rw [← consPt_tailPt s, ha0, ht]
        rcases zmod2_cases (s.2 0) with hc | hc
        · exfalso; apply hs0; rw [← consPt_tailPt s, ha0, hc, ht]; exact consPt_zero
        · rw [hc]; ext i <;> refine Fin.cases (by simp [ptZ, consPt]) (fun j => by simp [ptZ, consPt]) i
      · right
        rcases zmod2_cases (s.2 0) with hc | hc
        · left; exact ⟨tailPt s, ht, consPt_eq_of_eq ha0 hc⟩
        · right; exact ⟨tailPt s, ht, consPt_eq_of_eq ha0 hc⟩
    · rintro (rfl | ⟨u, hu0, rfl⟩ | ⟨u, hu0, rfl⟩)
      · exact ⟨ptZ_ne_zero 0, rfl⟩
      · exact ⟨fun h => hu0 ((consPt_eq_zero_iff 0 0 u).mp h).2.2, rfl⟩
      · exact ⟨fun h => hu0 ((consPt_eq_zero_iff 0 1 u).mp h).2.2, rfl⟩
  have hσ0 : c13Sigma hg (ptZ 0) = 1 := by
    have ht : tailPt (ptZ (0 : Fin (g + 1))) = 0 := by ext i <;> simp [tailPt, ptZ]
    simp [c13Sigma, ht]
  have hτ0 : c13Tau hg (ptZ 0) = 1 := by
    have ht : tailPt (ptZ (0 : Fin (g + 1))) = 0 := by ext i <;> simp [tailPt, ptZ]
    simp [c13Tau, ht]
  have hcpA : (opA (sectionOf X d) (c13Sigma hg)).charpoly
      = (opA (sectionOf X d) (c13Tau hg)).charpoly := by
    have hre1 := reindex_opA_Z_split R h0R (sectionOf X d) hH (c13Sigma hg) hσ0
    have hre2 := reindex_opA_Z_split R h0R (sectionOf X d) hH (c13Tau hg) hτ0
    have hCσ : 1 + ∑ u ∈ R, (((c13Sigma hg (consPt 0 0 u) + c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = -1 + (complexB1 hg + complexB2 hg) := by
      have hterm : ∀ u ∈ R, (((c13Sigma hg (consPt 0 0 u) + c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = (((2 * gSign hg u : ℝ) : ℂ)) • pauli u := by
        intro u hu
        have hu0 : u ≠ 0 := Finset.ne_of_mem_erase hu
        simp only [c13Sigma, tailPt_consPt, hu0, ↓reduceIte]
        congr 1; push_cast; ring
      rw [Finset.sum_congr rfl hterm,
        ← Finset.sum_filter_add_sum_filter_not R (fun u => ¬ isMovedDir hg u.1)]
      simp only [not_not]
      rw [sum_complex_unmoved hg, sum_complex_moved hg]
      ext x y; simp [Matrix.add_apply, Matrix.smul_apply]; ring
    have hDσ : -1 + ∑ u ∈ R, (((c13Sigma hg (consPt 0 0 u) - c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = (-1 : Matrix (Vec g) (Vec g) ℂ) := by
      have hterm : ∀ u ∈ R, (((c13Sigma hg (consPt 0 0 u) - c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u = 0 := by
        intro u _; simp [c13Sigma]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero, add_zero]
    have hCτ : 1 + ∑ u ∈ R, (((c13Tau hg (consPt 0 0 u) + c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = -1 + complexB1 hg := by
      have hterm : ∀ u ∈ R, (((c13Tau hg (consPt 0 0 u) + c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = if ¬ isMovedDir hg u.1 then (((2 * gSign hg u : ℝ) : ℂ)) • pauli u else 0 := by
        intro u hu
        have hu0 : u ≠ 0 := Finset.ne_of_mem_erase hu
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        by_cases hm : isMovedDir hg u.1
        · simp [c13Tau, hu0, h01, hm]
        · simp only [c13Tau, tailPt_consPt, consPt_snd_zero, hu0, h01, hm, ↓reduceIte,
            and_false, not_false_eq_true]
          congr 1; push_cast; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, sum_complex_unmoved hg]
      ext x y; simp [Matrix.add_apply, Matrix.smul_apply]; ring
    have hDτ : -1 + ∑ u ∈ R, (((c13Tau hg (consPt 0 0 u) - c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = -1 + complexB2 hg := by
      have hterm : ∀ u ∈ R, (((c13Tau hg (consPt 0 0 u) - c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = if isMovedDir hg u.1 then (((2 * gSign hg u : ℝ) : ℂ)) • pauli u else 0 := by
        intro u hu
        have hu0 : u ≠ 0 := Finset.ne_of_mem_erase hu
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        by_cases hm : isMovedDir hg u.1
        · simp only [c13Tau, tailPt_consPt, consPt_snd_zero, hu0, h01, hm, ↓reduceIte,
            false_and, true_and]
          congr 1; push_cast; ring
        · simp [c13Tau, hu0, h01, hm]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, sum_complex_moved hg]
    rw [hCσ, hDσ] at hre1
    rw [hCτ, hDτ] at hre2
    rw [← Matrix.charpoly_reindex (splitSum g), hre1,
      ← Matrix.charpoly_reindex (splitSum g), hre2]
    exact charpoly_block_split (complexB1 hg) (complexB2 hg) (complexB1_mul_complexB2 hg)
  refine ⟨c13Sigma hg, c13Tau hg, c13Sigma_eq_one_or hg, c13Tau_eq_one_or hg, hcpA, ?_⟩
  have hd_mem : d ∈ sectionOf X d := by
    rw [hH]; exact Finset.mem_insert_self _ _
  apply completion_charpoly_ne_of_trace_sq_ne isClosedCfg_allPoints d d hd_mem
    (-((4 : ℂ) ^ (g + 1) / 2)) 0
    (neg_ne_zero.mpr (div_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)))
    (fun s hs => by
      have hs0 : s ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_filter.mp hs).1
      rw [charSumOut_C1 hs0, add_zero])
    hσ0 hτ0 hcpA
  refine trace_sq_ne_of_flipped R h0R (sectionOf X d) hH (fun u => isMovedDir hg u.1)
    (c13Sigma hg) (c13Tau hg)
    (fun u _ => c13Sigma_eq_one_or hg _)
    (fun u hu => by simp [c13Sigma, Finset.ne_of_mem_erase hu])
    (fun u hu => by
      have h01 : (0 : ZMod 2) ≠ 1 := by decide
      simp [c13Sigma, c13Tau, consPt, Finset.ne_of_mem_erase hu, h01])
    (fun u hu => by
      have h01 : (0 : ZMod 2) ≠ 1 := by decide
      by_cases hm : isMovedDir hg u.1 <;>
        simp [c13Sigma, c13Tau, consPt, Finset.ne_of_mem_erase hu, hm])
    ⟨(gv1 hg, 0), Finset.mem_erase.mpr ⟨fun h => gv_ne_01 hg (congrArg Prod.fst h), mem_univ _⟩,
      Or.inl rfl⟩

/-- **Case C3 (all `N ≥ 3`).** Hyperbolic quadric `Q⁺(2N-1, 2)` cut by `d = Z₀`. -/
theorem c3_strict_law_fails {g : ℕ} (hg : 2 ≤ g) :
    let d : Pt (g + 1) := ptZ 0
    let X : Finset (Pt (g + 1)) := quadric (g + 1) 0
    ∃ σ τ : Pt (g + 1) → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  intro d X
  set R : Finset (Pt g) := quadric g 0
  have h0R : (0 : Pt g) ∉ R := by simp [R, quadric]
  have hq0_g : ∀ u : Pt g, qformShift (0 : Pt g) u = qform u := fun u => by
    rw [qformShift, symp_comm, symp_zero_right, add_zero]
  have hq0_N : ∀ s : Pt (g + 1), qformShift (0 : Pt (g + 1)) s = qform s := fun s => by
    rw [qformShift, symp_comm, symp_zero_right, add_zero]
  have hH : sectionOf X d = insert (ptZ 0) (R.image (consPt 0 0) ∪ R.image (consPt 0 1)) := by
    ext s
    simp only [sectionOf, X, d, quadric, R, hq0_g, hq0_N, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_union, Finset.mem_image, symp_ptZ]
    constructor
    · rintro ⟨⟨hs0, hqs⟩, ha0⟩
      have hqt : qform (tailPt s) = 0 := by
        have h := qform_consPt (s.1 0) (s.2 0) (tailPt s)
        rw [consPt_tailPt, ha0, mul_zero, zero_add] at h
        rwa [← h]
      by_cases ht : tailPt s = 0
      · left
        rw [← consPt_tailPt s, ha0, ht]
        rcases zmod2_cases (s.2 0) with hc | hc
        · exfalso; apply hs0; rw [← consPt_tailPt s, ha0, hc, ht]; exact consPt_zero
        · rw [hc]; ext i <;> refine Fin.cases (by simp [ptZ, consPt]) (fun j => by simp [ptZ, consPt]) i
      · right
        rcases zmod2_cases (s.2 0) with hc | hc
        · left; exact ⟨tailPt s, ⟨ht, hqt⟩, consPt_eq_of_eq ha0 hc⟩
        · right; exact ⟨tailPt s, ⟨ht, hqt⟩, consPt_eq_of_eq ha0 hc⟩
    · rintro (rfl | ⟨u, ⟨hu0, hqu⟩, rfl⟩ | ⟨u, ⟨hu0, hqu⟩, rfl⟩)
      · exact ⟨⟨ptZ_ne_zero 0, qform_ptZ 0⟩, rfl⟩
      · exact ⟨⟨fun h => hu0 ((consPt_eq_zero_iff 0 0 u).mp h).2.2, by rw [qform_consPt, hqu]; simp⟩, rfl⟩
      · exact ⟨⟨fun h => hu0 ((consPt_eq_zero_iff 0 1 u).mp h).2.2, by rw [qform_consPt, hqu]; simp⟩, rfl⟩
  have hσ0 : c13Sigma hg (ptZ 0) = 1 := by
    have ht : tailPt (ptZ (0 : Fin (g + 1))) = 0 := by ext i <;> simp [tailPt, ptZ]
    simp [c13Sigma, ht]
  have hτ0 : c13Tau hg (ptZ 0) = 1 := by
    have ht : tailPt (ptZ (0 : Fin (g + 1))) = 0 := by ext i <;> simp [tailPt, ptZ]
    simp [c13Tau, ht]
  have hcpA : (opA (sectionOf X d) (c13Sigma hg)).charpoly
      = (opA (sectionOf X d) (c13Tau hg)).charpoly := by
    have hre1 := reindex_opA_Z_split R h0R (sectionOf X d) hH (c13Sigma hg) hσ0
    have hre2 := reindex_opA_Z_split R h0R (sectionOf X d) hH (c13Tau hg) hτ0
    have hCσ : 1 + ∑ u ∈ R, (((c13Sigma hg (consPt 0 0 u) + c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = -1 + (realB1 hg + realB2 hg) := by
      have hterm : ∀ u ∈ R, (((c13Sigma hg (consPt 0 0 u) + c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = (((2 * gSign hg u : ℝ) : ℂ)) • pauli u := by
        intro u hu
        have hu0 : u ≠ 0 := (Finset.mem_filter.mp hu).2.1
        simp only [c13Sigma, tailPt_consPt, hu0, ↓reduceIte]
        congr 1; push_cast; ring
      rw [Finset.sum_congr rfl hterm,
        ← Finset.sum_filter_add_sum_filter_not R (fun u => ¬ isMovedDir hg u.1)]
      simp only [not_not]
      rw [sum_real_unmoved hg, sum_real_moved hg]
      ext x y; simp [Matrix.add_apply, Matrix.smul_apply]; ring
    have hDσ : -1 + ∑ u ∈ R, (((c13Sigma hg (consPt 0 0 u) - c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = (-1 : Matrix (Vec g) (Vec g) ℂ) := by
      have hterm : ∀ u ∈ R, (((c13Sigma hg (consPt 0 0 u) - c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u = 0 := by
        intro u _; simp [c13Sigma]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero, add_zero]
    have hCτ : 1 + ∑ u ∈ R, (((c13Tau hg (consPt 0 0 u) + c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = -1 + realB1 hg := by
      have hterm : ∀ u ∈ R, (((c13Tau hg (consPt 0 0 u) + c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = if ¬ isMovedDir hg u.1 then (((2 * gSign hg u : ℝ) : ℂ)) • pauli u else 0 := by
        intro u hu
        have hu0 : u ≠ 0 := (Finset.mem_filter.mp hu).2.1
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        by_cases hm : isMovedDir hg u.1
        · simp [c13Tau, hu0, h01, hm]
        · simp only [c13Tau, tailPt_consPt, consPt_snd_zero, hu0, h01, hm, ↓reduceIte,
            and_false, not_false_eq_true]
          congr 1; push_cast; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, sum_real_unmoved hg]
      ext x y; simp [Matrix.add_apply, Matrix.smul_apply]; ring
    have hDτ : -1 + ∑ u ∈ R, (((c13Tau hg (consPt 0 0 u) - c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = -1 + realB2 hg := by
      have hterm : ∀ u ∈ R, (((c13Tau hg (consPt 0 0 u) - c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = if isMovedDir hg u.1 then (((2 * gSign hg u : ℝ) : ℂ)) • pauli u else 0 := by
        intro u hu
        have hu0 : u ≠ 0 := (Finset.mem_filter.mp hu).2.1
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        by_cases hm : isMovedDir hg u.1
        · simp only [c13Tau, tailPt_consPt, consPt_snd_zero, hu0, h01, hm, ↓reduceIte,
            false_and, true_and]
          congr 1; push_cast; ring
        · simp [c13Tau, hu0, h01, hm]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, sum_real_moved hg]
    rw [hCσ, hDσ] at hre1
    rw [hCτ, hDτ] at hre2
    rw [← Matrix.charpoly_reindex (splitSum g), hre1,
      ← Matrix.charpoly_reindex (splitSum g), hre2]
    exact charpoly_block_split (realB1 hg) (realB2 hg) (realB1_mul_realB2 hg)
  refine ⟨c13Sigma hg, c13Tau hg, c13Sigma_eq_one_or hg, c13Tau_eq_one_or hg, hcpA, ?_⟩
  have hd_mem : d ∈ sectionOf X d := by rw [hH]; exact Finset.mem_insert_self _ _
  apply completion_charpoly_ne_of_trace_sq_ne (isClosedCfg_quadric 0) d d hd_mem
    (-((4 : ℂ) ^ (g + 1) / 4)) 0
    (neg_ne_zero.mpr (div_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)))
    (fun s hs => by
      obtain ⟨hsQ, hsd⟩ := Finset.mem_filter.mp hs
      obtain ⟨hs0, hqs⟩ := (Finset.mem_filter.mp hsQ).2
      rw [charSumOut_C3_C5 (by rw [hq0_N]; exact qform_ptZ 0) hs0 hqs hsd, add_zero])
    hσ0 hτ0 hcpA
  refine trace_sq_ne_of_flipped R h0R (sectionOf X d) hH (fun u => isMovedDir hg u.1)
    (c13Sigma hg) (c13Tau hg)
    (fun u _ => c13Sigma_eq_one_or hg _)
    (fun u hu => by simp [c13Sigma, (Finset.mem_filter.mp hu).2.1])
    (fun u hu => by
      have h01 : (0 : ZMod 2) ≠ 1 := by decide
      simp [c13Sigma, c13Tau, consPt, (Finset.mem_filter.mp hu).2.1, h01])
    (fun u hu => by
      by_cases hm : isMovedDir hg u.1 <;>
        simp [c13Sigma, c13Tau, consPt, (Finset.mem_filter.mp hu).2.1, hm])
    ⟨(gv1 hg, 0), Finset.mem_filter.mpr ⟨mem_univ _, fun h => gv_ne_01 hg (congrArg Prod.fst h),
      by rw [hq0_g]; simp [qform]⟩, Or.inl rfl⟩

end CasesC1C3

/-! ### Part 4. Case C8 (`N ≥ 4`, Y-lifted C1 on `Q⁺ ∩ Y₀⊥`, `d = Z₁`) -/

section CaseC8

/-- **Case C8 (all `N ≥ 4`).** `X = Q⁺(2N-1,2) ∩ Y₀⊥` cut by `d = Z₁`. -/
theorem c8_strict_law_fails {g : ℕ} (hg : 2 ≤ g) :
    let e : Pt (g + 2) := ptY 0
    let d : Pt (g + 2) := ptZ ⟨1, by omega⟩
    let X : Finset (Pt (g + 2)) := perpSet (quadric (g + 2) 0) e
    ∃ σ τ : Pt (g + 2) → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  intro e d X
  obtain ⟨σ₁, τ₁, hσ₁, hτ₁, hcp₁, hL₁⟩ := c1_strict_law_fails hg
  -- Actually we directly use `c13Sigma hg` and `c13Tau hg` so we know their exact values on `Z₁`!
  clear σ₁ τ₁ hσ₁ hτ₁ hcp₁ hL₁
  set H1 : Finset (Pt (g + 1)) := sectionOf (allPoints (g + 1)) (ptZ 0)
  have hcp1 : (opA H1 (c13Sigma hg)).charpoly = (opA H1 (c13Tau hg)).charpoly := by
    -- Re-derive directly from `c1_strict_law_fails` setup or reuse `reindex_opA_Z_split`!
    set R : Finset (Pt g) := allPoints g
    have h0R : (0 : Pt g) ∉ R := by simp [R, allPoints]
    have hH1 : H1 = insert (ptZ 0) (R.image (consPt 0 0) ∪ R.image (consPt 0 1)) := by
      ext s
      simp only [H1, sectionOf, allPoints, R, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
        and_true, Finset.mem_insert, Finset.mem_union, Finset.mem_image, symp_ptZ]
      constructor
      · rintro ⟨hs0, ha0⟩
        by_cases ht : tailPt s = 0
        · left
          rw [← consPt_tailPt s, ha0, ht]
          rcases zmod2_cases (s.2 0) with hc | hc
          · exfalso; apply hs0; rw [← consPt_tailPt s, ha0, hc, ht]; exact consPt_zero
          · rw [hc]; ext i <;> refine Fin.cases (by simp [ptZ, consPt]) (fun j => by simp [ptZ, consPt]) i
        · right
          rcases zmod2_cases (s.2 0) with hc | hc
          · left; exact ⟨tailPt s, ht, consPt_eq_of_eq ha0 hc⟩
          · right; exact ⟨tailPt s, ht, consPt_eq_of_eq ha0 hc⟩
      · rintro (rfl | ⟨u, hu0, rfl⟩ | ⟨u, hu0, rfl⟩)
        · exact ⟨ptZ_ne_zero 0, rfl⟩
        · exact ⟨fun h => hu0 ((consPt_eq_zero_iff 0 0 u).mp h).2.2, rfl⟩
        · exact ⟨fun h => hu0 ((consPt_eq_zero_iff 0 1 u).mp h).2.2, rfl⟩
    have hσ0 : c13Sigma hg (ptZ 0) = 1 := by
      have ht : tailPt (ptZ (0 : Fin (g + 1))) = 0 := by ext i <;> simp [tailPt, ptZ]
      simp [c13Sigma, ht]
    have hτ0 : c13Tau hg (ptZ 0) = 1 := by
      have ht : tailPt (ptZ (0 : Fin (g + 1))) = 0 := by ext i <;> simp [tailPt, ptZ]
      simp [c13Tau, ht]
    have hre1 := reindex_opA_Z_split R h0R H1 hH1 (c13Sigma hg) hσ0
    have hre2 := reindex_opA_Z_split R h0R H1 hH1 (c13Tau hg) hτ0
    have hCσ : 1 + ∑ u ∈ R, (((c13Sigma hg (consPt 0 0 u) + c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = -1 + (complexB1 hg + complexB2 hg) := by
      have ht : ∀ u ∈ R, (((c13Sigma hg (consPt 0 0 u) + c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = (((2 * gSign hg u : ℝ) : ℂ)) • pauli u := by
        intro u hu; simp only [c13Sigma, tailPt_consPt, Finset.ne_of_mem_erase hu, ↓reduceIte]
        congr 1; push_cast; ring
      rw [Finset.sum_congr rfl ht, ← Finset.sum_filter_add_sum_filter_not R (fun u => ¬ isMovedDir hg u.1)]
      simp only [not_not]; rw [sum_complex_unmoved hg, sum_complex_moved hg]
      ext x y; simp [Matrix.add_apply, Matrix.smul_apply]; ring
    have hDσ : -1 + ∑ u ∈ R, (((c13Sigma hg (consPt 0 0 u) - c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = (-1 : Matrix (Vec g) (Vec g) ℂ) := by
      have ht : ∀ u ∈ R, (((c13Sigma hg (consPt 0 0 u) - c13Sigma hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u = 0 :=
        fun u _ => by simp [c13Sigma]
      rw [Finset.sum_congr rfl ht, Finset.sum_const_zero, add_zero]
    have hCτ : 1 + ∑ u ∈ R, (((c13Tau hg (consPt 0 0 u) + c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = -1 + complexB1 hg := by
      have ht : ∀ u ∈ R, (((c13Tau hg (consPt 0 0 u) + c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = if ¬ isMovedDir hg u.1 then (((2 * gSign hg u : ℝ) : ℂ)) • pauli u else 0 := by
        intro u hu
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        by_cases hm : isMovedDir hg u.1
        · simp [c13Tau, Finset.ne_of_mem_erase hu, h01, hm]
        · simp only [c13Tau, tailPt_consPt, consPt_snd_zero, Finset.ne_of_mem_erase hu, h01, hm,
            ↓reduceIte, and_false, not_false_eq_true]
          congr 1; push_cast; ring
      rw [Finset.sum_congr rfl ht, ← Finset.sum_filter, sum_complex_unmoved hg]
      ext x y; simp [Matrix.add_apply, Matrix.smul_apply]; ring
    have hDτ : -1 + ∑ u ∈ R, (((c13Tau hg (consPt 0 0 u) - c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = -1 + complexB2 hg := by
      have ht : ∀ u ∈ R, (((c13Tau hg (consPt 0 0 u) - c13Tau hg (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = if isMovedDir hg u.1 then (((2 * gSign hg u : ℝ) : ℂ)) • pauli u else 0 := by
        intro u hu
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        by_cases hm : isMovedDir hg u.1
        · simp only [c13Tau, tailPt_consPt, consPt_snd_zero, Finset.ne_of_mem_erase hu, h01, hm,
            ↓reduceIte, false_and, true_and]
          congr 1; push_cast; ring
        · simp [c13Tau, Finset.ne_of_mem_erase hu, h01, hm]
      rw [Finset.sum_congr rfl ht, ← Finset.sum_filter, sum_complex_moved hg]
    rw [hCσ, hDσ] at hre1; rw [hCτ, hDτ] at hre2
    rw [← Matrix.charpoly_reindex (splitSum g), hre1,
      ← Matrix.charpoly_reindex (splitSum g), hre2]
    exact charpoly_block_split (complexB1 hg) (complexB2 hg) (complexB1_mul_complexB2 hg)
  -- Bijection between `H1` and `sectionOf X d` via `u ↦ consPt (qform u) (qform u) u`.
  let lift8 : Pt (g + 1) → Pt (g + 2) := fun u => consPt (qform u) (qform u) u
  have hlift_inj : Function.Injective lift8 := fun u v h => by
    simpa [lift8, tailPt_consPt] using congrArg tailPt h
  have hd_eq : d = lift8 (ptZ 0) := by
    simp only [lift8, qform_ptZ, d]
    rw [consPt_zero_ptZ]; rfl
  have hq0_N : ∀ s : Pt (g + 2), qformShift (0 : Pt (g + 2)) s = qform s := fun s => by
    rw [qformShift, symp_comm, symp_zero_right, add_zero]
  have hH_eq : sectionOf X d = H1.image lift8 := by
    ext s
    simp only [sectionOf, X, perpSet, quadric, hq0_N, H1, allPoints, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_erase, and_true]
    constructor
    · rintro ⟨⟨⟨hs0, hqs⟩, hse⟩, hsd⟩
      have ha_eq_c' : s.1 0 = s.2 0 := by
        rw [symp_ptY] at hse
        rcases zmod2_cases (s.1 0) with h1 | h1 <;> rcases zmod2_cases (s.2 0) with h2 | h2
        · rw [h1, h2]
        · rw [h1, h2] at hse; exact absurd hse (by decide)
        · rw [h1, h2] at hse; exact absurd hse (by decide)
        · rw [h1, h2]
      have hqt : qform (tailPt s) = s.1 0 := by
        have h := qform_consPt (s.1 0) (s.2 0) (tailPt s)
        rw [consPt_tailPt, hqs, ← ha_eq_c'] at h
        rcases zmod2_cases (s.1 0) with h1 | h1 <;> rcases zmod2_cases (qform (tailPt s)) with h2 | h2 <;>
          simp [h1, h2] at h ⊢
      have ht0 : tailPt s ≠ 0 := by
        intro h; apply hs0
        rw [← consPt_tailPt s, ← ha_eq_c', ← hqt, h, qform_zero]
        exact consPt_zero
      have htd : symp (tailPt s) (ptZ 0) = 0 := by
        rw [symp_ptZ] at hsd ⊢; exact hsd
      refine ⟨tailPt s, ⟨ht0, htd⟩, ?_⟩
      exact consPt_eq_of_eq hqt.symm (by rw [← ha_eq_c', hqt])
    · rintro ⟨u, ⟨hu0, hud⟩, rfl⟩
      refine ⟨⟨⟨fun h => hu0 ((consPt_eq_zero_iff _ _ u).mp h).2.2, ?_⟩, ?_⟩, ?_⟩
      · rw [qform_consPt]
        rcases zmod2_cases (qform u) with h | h <;> (simp [h]; try decide)
      · rw [symp_ptY]; simp [lift8, consPt, zmod2_add_self]
      · rw [symp_ptZ]; simpa [lift8, consPt, symp_ptZ] using hud
  -- Lifted carriers: `σ = c13Sigma ∘ tailPt`, `τ = c13Tau ∘ tailPt`.
  let σ8 : Pt (g + 2) → ℝ := fun s => c13Sigma hg (tailPt s)
  let τ8 : Pt (g + 2) → ℝ := fun s => c13Tau hg (tailPt s)
  have hconj_opA : ∀ f : Pt (g + 1) → ℝ,
      matVYInv (g + 1) * Matrix.reindex (splitSum (g + 1)) (splitSum (g + 1))
          (opA (sectionOf X d) (fun s => f (tailPt s))) * matVY (g + 1)
        = fromBlocks (opA H1 f) 0 0 (opA H1 f)ᵀ := by
    intro f
    have hre : Matrix.reindex (splitSum (g + 1)) (splitSum (g + 1))
          (opA (sectionOf X d) (fun s => f (tailPt s)))
        = ∑ u ∈ H1, ((f u : ℝ) : ℂ) •
            Matrix.reindex (splitSum (g + 1)) (splitSum (g + 1)) (pauli (lift8 u)) := by
      rw [hH_eq]
      ext x y
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, opA, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul]
      rw [Finset.sum_image (fun _ _ _ _ h => hlift_inj h)]
      refine Finset.sum_congr rfl fun u _ => by simp [lift8]
    rw [hre, Finset.mul_sum, Finset.sum_mul]
    have hterm : ∀ u ∈ H1,
        matVYInv (g + 1) * (((f u : ℝ) : ℂ) • Matrix.reindex (splitSum (g + 1)) (splitSum (g + 1))
          (pauli (lift8 u))) * matVY (g + 1)
        = fromBlocks (((f u : ℝ) : ℂ) • pauli u) 0 0 (((f u : ℝ) : ℂ) • (pauli u)ᵀ) := by
      intro u _
      rw [Matrix.mul_smul, Matrix.smul_mul, conj_VY_pauli_cons, fromBlocks_smul, smul_zero,
        ← pauli_transpose_eq]
    rw [Finset.sum_congr rfl hterm]
    ext x y
    rcases x with x | x <;> rcases y with y | y <;>
      simp [opA, Matrix.sum_apply, Matrix.smul_apply, Matrix.transpose_apply,
        fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  have hcp8 : (opA (sectionOf X d) σ8).charpoly = (opA (sectionOf X d) τ8).charpoly := by
    have h1 := hconj_opA (c13Sigma hg)
    have h2 := hconj_opA (c13Tau hg)
    have hp1 : (opA (sectionOf X d) σ8).charpoly = (opA H1 (c13Sigma hg)).charpoly ^ 2 := by
      rw [← Matrix.charpoly_reindex (splitSum (g + 1)), ← charpoly_conj_VY, h1,
        charpoly_fromBlocks_zero₁₂, Matrix.charpoly_transpose, sq]
    have hp2 : (opA (sectionOf X d) τ8).charpoly = (opA H1 (c13Tau hg)).charpoly ^ 2 := by
      rw [← Matrix.charpoly_reindex (splitSum (g + 1)), ← charpoly_conj_VY, h2,
        charpoly_fromBlocks_zero₁₂, Matrix.charpoly_transpose, sq]
    rw [hp1, hp2, hcp1]
  refine ⟨σ8, τ8, fun s => c13Sigma_eq_one_or hg _, fun s => c13Tau_eq_one_or hg _, hcp8, ?_⟩
  have hσd : σ8 d = 1 := by
    rw [hd_eq]; dsimp only [σ8, lift8]; rw [tailPt_consPt]
    have ht : tailPt (ptZ (0 : Fin (g + 1))) = 0 := by ext i <;> simp [tailPt, ptZ]
    simp [c13Sigma, ht]
  have hτd : τ8 d = 1 := by
    rw [hd_eq]; dsimp only [τ8, lift8]; rw [tailPt_consPt]
    have ht : tailPt (ptZ (0 : Fin (g + 1))) = 0 := by ext i <;> simp [tailPt, ptZ]
    simp [c13Tau, ht]
  have hd_mem : d ∈ sectionOf X d := by
    rw [hH_eq, hd_eq]
    exact Finset.mem_image_of_mem lift8
      (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ptZ_ne_zero 0, mem_univ _⟩, symp_ptZ_ptZ 0 0⟩)
  have h01 : (0 : Fin (g + 2)) ≠ ⟨1, by omega⟩ := by simp
  apply completion_charpoly_ne_of_trace_sq_ne
    (isClosedCfg_perpSet (isClosedCfg_quadric 0) e) d d hd_mem
    (-((4 : ℂ) ^ (g + 2) / 8)) 0
    (neg_ne_zero.mpr (div_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)))
    (fun s hs => by
      obtain ⟨hsX, hsd⟩ := Finset.mem_filter.mp hs
      obtain ⟨hsQ, hse⟩ := Finset.mem_filter.mp hsX
      obtain ⟨hs0, hqs⟩ := (Finset.mem_filter.mp hsQ).2
      rw [hq0_N] at hqs
      rw [charSumOut_C8 (qform_ptY 0) (qform_ptZ _) (by rw [symp_comm]; exact symp_ptY_ptZ h01)
        hs0 hqs hse hsd, add_zero])
    hσd hτd hcp8
  -- Trace difference at `d = ptZ 1`: `tau s (s + d) = 1`, lifted sum equals C1 trace sum!
  have hcomm_d : ∀ s ∈ sectionOf X d, symp s d = 0 := fun s hs => (Finset.mem_filter.mp hs).2
  have hcomm_0 : ∀ u ∈ H1, symp u (ptZ 0) = 0 := fun u hu => (Finset.mem_filter.mp hu).2
  rw [trace_opA_sq_mul_central σ8 (ptZ_ne_zero _) hcomm_d,
    trace_opA_sq_mul_central τ8 (ptZ_ne_zero _) hcomm_d]
  have hlift_add : ∀ u ∈ H1, lift8 u + d = lift8 (u + ptZ 0) := by
    intro u hu
    have hu0 : u.1 0 = 0 := by simpa [symp_ptZ] using hcomm_0 u hu
    have hq_add : qform (u + ptZ 0) = qform u := by
      rw [qform_add, qform_ptZ, symp_ptZ, hu0]; simp
    rw [hd_eq]; dsimp only [lift8]
    rw [consPt_add, qform_ptZ, add_zero, hq_add]
  have hfilt_eq : (sectionOf X d).filter (fun s => s + d ∈ sectionOf X d)
      = (H1.filter (fun u => u + ptZ 0 ∈ H1)).image lift8 := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_image, hH_eq]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
      refine ⟨u, ⟨hu, ?_⟩, rfl⟩
      rw [hlift_add u hu] at hvu
      rwa [← hlift_inj hvu]
    · rintro ⟨u, ⟨hu, hu'⟩, rfl⟩
      exact ⟨⟨u, hu, rfl⟩, ⟨u + ptZ 0, hu', (hlift_add u hu).symm⟩⟩
  have htau8 : ∀ s ∈ sectionOf X d, tau s (s + d) = 1 := fun s hs =>
    tau_add_ptZ (by simpa [symp_ptZ, d] using hcomm_d s hs)
  have htau1 : ∀ u ∈ H1, tau u (u + ptZ 0) = 1 := fun u hu =>
    tau_add_ptZ (by simpa [symp_ptZ] using hcomm_0 u hu)
  have hsum_eq : ∀ f : Pt (g + 1) → ℝ,
      ∑ s ∈ (sectionOf X d).filter (fun s => s + d ∈ sectionOf X d),
          ((f (tailPt s) : ℝ) : ℂ) * ((f (tailPt (s + d)) : ℝ) : ℂ) * tau s (s + d)
        = ∑ u ∈ H1.filter (fun u => u + ptZ 0 ∈ H1),
            ((f u : ℝ) : ℂ) * ((f (u + ptZ 0) : ℝ) : ℂ) * tau u (u + ptZ 0) := by
    intro f
    rw [hfilt_eq, Finset.sum_image (fun _ _ _ _ h => hlift_inj h)]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu1 : u ∈ H1 := (Finset.mem_filter.mp hu).1
    have hlu : lift8 u ∈ sectionOf X d := by rw [hH_eq]; exact Finset.mem_image_of_mem lift8 hu1
    rw [htau8 (lift8 u) hlu, htau1 u hu1, hlift_add u hu1]
    simp [lift8]
  rw [show (∑ s ∈ (sectionOf X d).filter (fun s => s + d ∈ sectionOf X d),
        ((σ8 s : ℝ) : ℂ) * ((σ8 (s + d) : ℝ) : ℂ) * tau s (s + d))
      = ∑ u ∈ H1.filter (fun u => u + ptZ 0 ∈ H1),
          ((c13Sigma hg u : ℝ) : ℂ) * ((c13Sigma hg (u + ptZ 0) : ℝ) : ℂ) * tau u (u + ptZ 0)
    from hsum_eq (c13Sigma hg)]
  rw [show (∑ s ∈ (sectionOf X d).filter (fun s => s + d ∈ sectionOf X d),
        ((τ8 s : ℝ) : ℂ) * ((τ8 (s + d) : ℝ) : ℂ) * tau s (s + d))
      = ∑ u ∈ H1.filter (fun u => u + ptZ 0 ∈ H1),
          ((c13Tau hg u : ℝ) : ℂ) * ((c13Tau hg (u + ptZ 0) : ℝ) : ℂ) * tau u (u + ptZ 0)
    from hsum_eq (c13Tau hg)]
  -- Use `trace_sq_ne_of_flipped` on `H1`!
  set R : Finset (Pt g) := allPoints g
  have h0R : (0 : Pt g) ∉ R := by simp [R, allPoints]
  have hH1 : H1 = insert (ptZ 0) (R.image (consPt 0 0) ∪ R.image (consPt 0 1)) := by
    ext s
    simp only [H1, sectionOf, allPoints, R, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, Finset.mem_insert, Finset.mem_union, Finset.mem_image, symp_ptZ]
    constructor
    · rintro ⟨hs0, ha0⟩
      by_cases ht : tailPt s = 0
      · left
        rw [← consPt_tailPt s, ha0, ht]
        rcases zmod2_cases (s.2 0) with hc | hc
        · exfalso; apply hs0; rw [← consPt_tailPt s, ha0, hc, ht]; exact consPt_zero
        · rw [hc]; ext i <;> refine Fin.cases (by simp [ptZ, consPt]) (fun j => by simp [ptZ, consPt]) i
      · right
        rcases zmod2_cases (s.2 0) with hc | hc
        · left; exact ⟨tailPt s, ht, consPt_eq_of_eq ha0 hc⟩
        · right; exact ⟨tailPt s, ht, consPt_eq_of_eq ha0 hc⟩
    · rintro (rfl | ⟨u, hu0, rfl⟩ | ⟨u, hu0, rfl⟩)
      · exact ⟨ptZ_ne_zero 0, rfl⟩
      · exact ⟨fun h => hu0 ((consPt_eq_zero_iff 0 0 u).mp h).2.2, rfl⟩
      · exact ⟨fun h => hu0 ((consPt_eq_zero_iff 0 1 u).mp h).2.2, rfl⟩
  have hne1 := trace_sq_ne_of_flipped R h0R H1 hH1 (fun u => isMovedDir hg u.1)
    (c13Sigma hg) (c13Tau hg)
    (fun u _ => c13Sigma_eq_one_or hg _)
    (fun u hu => by simp [c13Sigma, Finset.ne_of_mem_erase hu])
    (fun u hu => by
      have h01 : (0 : ZMod 2) ≠ 1 := by decide
      simp [c13Sigma, c13Tau, consPt, Finset.ne_of_mem_erase hu, h01])
    (fun u hu => by
      by_cases hm : isMovedDir hg u.1 <;>
        simp [c13Sigma, c13Tau, consPt, Finset.ne_of_mem_erase hu, hm])
    ⟨(gv1 hg, 0), Finset.mem_erase.mpr ⟨fun h => gv_ne_01 hg (congrArg Prod.fst h), mem_univ _⟩,
      Or.inl rfl⟩
  rw [trace_opA_sq_mul_central (c13Sigma hg) (ptZ_ne_zero 0) hcomm_0,
    trace_opA_sq_mul_central (c13Tau hg) (ptZ_ne_zero 0) hcomm_0] at hne1
  intro heq
  apply hne1
  have h2ne1 : (2 : ℂ) ^ (g + 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hseq := mul_left_cancel₀ h2ne1 heq
  rw [hseq]

end CaseC8

/-! ### Part 5. Unified Proof of Cases C12 and C15 (`N ≥ 4`) -/

section CasesC12C15

/-- Unified proof for C12 (`c_base = 0`) and C15 (`c_base = Y₀` on `g` qubits):
`X = Q_c ∩ Z₀⊥` with `e = Z₀`, `d = Y₁`, `c = consPt 0 0 (consPt 0 0 c_base)`. -/
theorem c12_c15_strict_law_fails {g : ℕ} (hg : 2 ≤ g) (c_base : Pt g) :
    let c : Pt (g + 2) := consPt 0 0 (consPt 0 0 c_base)
    let e : Pt (g + 2) := ptZ 0
    let d : Pt (g + 2) := ptY ⟨1, by omega⟩
    let X : Finset (Pt (g + 2)) := perpSet (quadric (g + 2) c) e
    ∃ σ τ : Pt (g + 2) → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  intro c e d X
  -- Embedding of `w ∈ allPoints g` into `(g+1)`-qubit block: `u(w) = consPt b b w` where `b = q_c(w)`.
  let liftW : Pt g → Pt (g + 1) := fun w => consPt (qformShift c_base w) (qformShift c_base w) w
  have hliftW_inj : Function.Injective liftW := fun u v h => by
    simpa [liftW, tailPt_consPt] using congrArg tailPt h
  set R : Finset (Pt (g + 1)) := (allPoints g).image liftW
  have h0R : (0 : Pt (g + 1)) ∉ R := by
    rw [Finset.mem_image]; rintro ⟨w, hw, hw0⟩
    exact Finset.ne_of_mem_erase hw ((consPt_eq_zero_iff _ _ w).mp hw0).2.2
  have hc_qshift : ∀ (a0 c0 a1 c1 : ZMod 2) (w : Pt g),
      qformShift c (consPt a0 c0 (consPt a1 c1 w)) = c0 * a0 + c1 * a1 + qformShift c_base w := by
    intro a0 c0 a1 c1 w
    simp only [qformShift, c, qform_consPt, symp_consPt]
    ring
  have hH : sectionOf X d = insert (ptZ 0) (R.image (consPt 0 0) ∪ R.image (consPt 0 1)) := by
    ext s
    have hd_cons : d = consPt 0 0 (ptY 0) := by
      rw [consPt_zero_ptY]; rfl
    simp only [sectionOf, X, perpSet, quadric, e, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_union, Finset.mem_image, R]
    constructor
    · rintro ⟨⟨⟨hs0, hqs⟩, hse⟩, hsd⟩
      have ha0 : s.1 0 = 0 := by simpa [symp_ptZ] using hse
      set u := tailPt s
      set w := tailPt u
      have hs_eq : s = consPt 0 (s.2 0) (consPt (u.1 0) (u.2 0) w) := by
        rw [consPt_tailPt u, ← ha0, consPt_tailPt s]
      have ha1_eq_c1 : u.1 0 = u.2 0 := by
        rw [symp_ptY] at hsd
        have h1 : s.1 ⟨1, by omega⟩ = u.1 0 := rfl
        have h2 : s.2 ⟨1, by omega⟩ = u.2 0 := rfl
        rw [h1, h2] at hsd
        rcases zmod2_cases (u.1 0) with x | x <;> rcases zmod2_cases (u.2 0) with y | y
        · rw [x, y]
        · rw [x, y] at hsd; exact absurd hsd (by decide)
        · rw [x, y] at hsd; exact absurd hsd (by decide)
        · rw [x, y]
      have hqw : qformShift c_base w = u.1 0 := by
        rw [hs_eq, hc_qshift, mul_zero, zero_add, ← ha1_eq_c1] at hqs
        rcases zmod2_cases (u.1 0) with x | x <;> rcases zmod2_cases (qformShift c_base w) with y | y <;>
          simp [x, y] at hqs ⊢
      by_cases hw0 : w = 0
      · left
        have hu1 : u.1 0 = 0 := by rw [← hqw, hw0, qformShift_zero]
        have hu2 : u.2 0 = 0 := by rw [← ha1_eq_c1, hu1]
        have hu0 : u = 0 := by
          rw [← consPt_tailPt u, hu1, hu2]
          change consPt 0 0 w = 0
          rw [hw0]; exact consPt_zero
        rcases zmod2_cases (s.2 0) with hc0 | hc0
        · exfalso; apply hs0
          rw [← consPt_tailPt s, ha0, hc0]
          change consPt 0 0 u = 0
          rw [hu0]; exact consPt_zero
        · rw [← consPt_tailPt s, ha0, hc0]
          change consPt 0 1 u = ptZ 0
          rw [hu0]
          ext i <;> refine Fin.cases (by simp [ptZ, consPt]) (fun j => by simp [ptZ, consPt]) i
      · right
        have hu_eq : u = liftW w :=
          (consPt_eq_of_eq hqw.symm (by rw [← ha1_eq_c1, hqw])).symm
        have huR : ∃ a ∈ allPoints g, liftW a = u :=
          ⟨w, Finset.mem_erase.mpr ⟨hw0, mem_univ _⟩, hu_eq.symm⟩
        rcases zmod2_cases (s.2 0) with hc0 | hc0
        · left; exact ⟨u, huR, consPt_eq_of_eq ha0 hc0⟩
        · right; exact ⟨u, huR, consPt_eq_of_eq ha0 hc0⟩
    · rintro (rfl | ⟨u, ⟨w, hw, rfl⟩, rfl⟩ | ⟨u, ⟨w, hw, rfl⟩, rfl⟩)
      · refine ⟨⟨⟨ptZ_ne_zero 0, ?_⟩, symp_ptZ_ptZ 0 0⟩, ?_⟩
        · have hptZ0 : ptZ (0 : Fin (g + 2)) = consPt 0 1 (consPt 0 0 0) := by
            ext i <;> refine Fin.cases (by simp [ptZ, consPt]) (fun j => by
              refine Fin.cases (by simp [ptZ, consPt]) (fun k => by simp [ptZ, consPt]) j) i
          rw [hptZ0, hc_qshift, qformShift_zero]; simp
        · rw [symp_comm]; exact symp_ptY_ptZ (by simp)
      · refine ⟨⟨⟨fun h => Finset.ne_of_mem_erase hw
            ((consPt_eq_zero_iff _ _ w).mp ((consPt_eq_zero_iff 0 0 _).mp h).2.2).2.2, ?_⟩,
            by rw [symp_ptZ]; rfl⟩, ?_⟩
        · dsimp only [liftW]; rw [hc_qshift]
          rcases zmod2_cases (qformShift c_base w) with h | h <;> (simp [h]; try decide)
        · rw [symp_ptY]; simp [liftW, consPt, zmod2_add_self]
      · refine ⟨⟨⟨fun h => Finset.ne_of_mem_erase hw
            ((consPt_eq_zero_iff _ _ w).mp ((consPt_eq_zero_iff 0 1 _).mp h).2.2).2.2, ?_⟩,
            by rw [symp_ptZ]; rfl⟩, ?_⟩
        · dsimp only [liftW]; rw [hc_qshift]
          rcases zmod2_cases (qformShift c_base w) with h | h <;> (simp [h]; try decide)
        · rw [symp_ptY]; simp [liftW, consPt, zmod2_add_self]
  -- Define carriers `σ, τ` from the `g`-qubit complex graph on `tailPt (tailPt s)`.
  let σ : Pt (g + 2) → ℝ := fun s =>
    if tailPt (tailPt s) = 0 then 1 else gSign hg (tailPt (tailPt s))
  let τ : Pt (g + 2) → ℝ := fun s =>
    if tailPt (tailPt s) = 0 then 1
    else if s.2 0 = 1 ∧ isMovedDir hg (tailPt (tailPt s)).1 then -gSign hg (tailPt (tailPt s))
    else gSign hg (tailPt (tailPt s))
  have hσ_val : ∀ s, σ s = 1 ∨ σ s = -1 := fun s => by
    dsimp only [σ]
    split_ifs
    · left; rfl
    · exact gSign_eq_one_or hg _
  have hτ_val : ∀ s, τ s = 1 ∨ τ s = -1 := fun s => by
    dsimp only [τ]; split_ifs
    · left; rfl
    · rcases gSign_eq_one_or hg _ with h | h <;> [right; left] <;> linarith
    · exact gSign_eq_one_or hg _
  have hσe : σ e = 1 := by
    have ht : tailPt (tailPt e) = 0 := by ext i <;> simp [e, tailPt, ptZ]
    simp [σ, ht]
  have hτe : τ e = 1 := by
    have ht : tailPt (tailPt e) = 0 := by ext i <;> simp [e, tailPt, ptZ]
    simp [τ, ht]
  -- Helper: `Y₁` conjugation turns `c + ∑_{w ∈ W} α(w) • P_{liftW w}` into
  -- `fromBlocks (c + ∑ α P_w) 0 0 (P_{c_base} * (c + ∑ α P_w)ᵀ * P_{c_base})`.
  have hY_conj : ∀ (k : ℂ) (α : Pt g → ℂ),
      matVYInv g * Matrix.reindex (splitSum g) (splitSum g)
          (k • (1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ)
            + ∑ u ∈ R, α (tailPt u) • pauli u) * matVY g
        = fromBlocks
            (k • 1 + ∑ w ∈ allPoints g, α w • pauli w) 0 0
            (pauli c_base * (k • 1 + ∑ w ∈ allPoints g, α w • pauli w)ᵀ * pauli c_base) := by
    intro k α
    have hre1 : Matrix.reindex (splitSum g) (splitSum g) (1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ)
        = fromBlocks 1 0 0 1 := by
      rw [← pauli_zero, ← consPt_zero, reindex_pauli_cons_Z, pauli_zero, eps_zero, one_smul]
    have hre : Matrix.reindex (splitSum g) (splitSum g)
          (k • (1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ) + ∑ u ∈ R, α (tailPt u) • pauli u)
        = k • Matrix.reindex (splitSum g) (splitSum g) 1
          + ∑ w ∈ allPoints g, α w • Matrix.reindex (splitSum g) (splitSum g) (pauli (liftW w)) := by
      ext x y
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.sum_apply, smul_eq_mul, R]
      rw [Finset.sum_image (fun _ _ _ _ h => hliftW_inj h)]
      congr 1
    rw [hre, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hre1, fromBlocks_one,
      mul_one, matVYInv_mul_matVY, Finset.mul_sum, Finset.sum_mul]
    have hterm : ∀ w ∈ allPoints g,
        matVYInv g * (α w • Matrix.reindex (splitSum g) (splitSum g) (pauli (liftW w))) * matVY g
        = fromBlocks (α w • pauli w) 0 0 (α w • (pauli c_base * (pauli w)ᵀ * pauli c_base)) := by
      intro w _
      rw [Matrix.mul_smul, Matrix.smul_mul, conj_VY_pauli_cons, fromBlocks_smul, smul_zero,
        pauli_conj_transpose_eq]
    rw [Finset.sum_congr rfl hterm]
    have hpc1 : pauli c_base * (1 : Matrix (Vec g) (Vec g) ℂ) * pauli c_base = 1 := by
      rw [mul_one, pauli_mul_self]
    have hrhs_bot : pauli c_base * (k • (1 : Matrix (Vec g) (Vec g) ℂ) + ∑ w ∈ allPoints g, α w • pauli w)ᵀ * pauli c_base
        = k • 1 + ∑ w ∈ allPoints g, α w • (pauli c_base * (pauli w)ᵀ * pauli c_base) := by
      rw [transpose_add, transpose_smul, transpose_one, transpose_sum, mul_add, add_mul,
        Matrix.mul_smul, Matrix.smul_mul, hpc1, Finset.mul_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun w _ => by
        rw [transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hrhs_bot, ← fromBlocks_one, fromBlocks_smul, smul_zero]
    ext x y
    rcases x with x | x <;> rcases y with y | y <;>
      simp [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
        fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  have hchar_Y : ∀ (k : ℂ) (α : Pt g → ℂ),
      (k • (1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ) + ∑ u ∈ R, α (tailPt u) • pauli u).charpoly
        = (k • (1 : Matrix (Vec g) (Vec g) ℂ) + ∑ w ∈ allPoints g, α w • pauli w).charpoly ^ 2 := by
    intro k α
    rw [← Matrix.charpoly_reindex (splitSum g), ← charpoly_conj_VY, hY_conj,
      charpoly_fromBlocks_zero₁₂, sq]
    congr 1
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, pauli_mul_self, one_mul,
      Matrix.charpoly_transpose]
  -- Now prove `(opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly`.
  have hcpA : (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly := by
    have hre1 := reindex_opA_Z_split R h0R (sectionOf X d) hH σ hσe
    have hre2 := reindex_opA_Z_split R h0R (sectionOf X d) hH τ hτe
    rw [← Matrix.charpoly_reindex (splitSum (g + 1)), hre1, charpoly_fromBlocks_zero₁₂,
      ← Matrix.charpoly_reindex (splitSum (g + 1)), hre2, charpoly_fromBlocks_zero₁₂]
    -- Rewrite all four blocks in the `k • 1 + ∑ u ∈ R, α (tailPt u) • pauli u` form.
    have h1 : (1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ) = (1 : ℂ) • 1 := by simp
    have hneg1 : (-1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ) = (-1 : ℂ) • 1 := by simp
    have hCσ_eq : (1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ)
          + ∑ u ∈ R, (((σ (consPt 0 0 u) + σ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = (1 : ℂ) • 1 + ∑ u ∈ R, ((((2 * gSign hg (tailPt u) : ℝ) : ℂ))) • pauli u := by
      conv_lhs => rw [h1]
      congr 1; refine Finset.sum_congr rfl fun u hu => ?_
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      have hw0 : w ≠ 0 := Finset.ne_of_mem_erase hw
      simp only [σ, liftW, tailPt_consPt, hw0, ↓reduceIte]; congr 1; push_cast; ring
    have hDσ_eq : (-1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ)
          + ∑ u ∈ R, (((σ (consPt 0 0 u) - σ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = (-1 : ℂ) • 1 + ∑ u ∈ R, (0 : ℂ) • pauli u := by
      conv_lhs => rw [hneg1]
      congr 1; refine Finset.sum_congr rfl fun u hu => ?_
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      simp [σ, liftW]
    have hCτ_eq : (1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ)
          + ∑ u ∈ R, (((τ (consPt 0 0 u) + τ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = (1 : ℂ) • 1 + ∑ u ∈ R,
            (if ¬ isMovedDir hg (tailPt u).1 then (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) else 0) • pauli u := by
      conv_lhs => rw [h1]
      congr 1; refine Finset.sum_congr rfl fun u hu => ?_
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      have hw0 : w ≠ 0 := Finset.ne_of_mem_erase hw
      have h01 : (0 : ZMod 2) ≠ 1 := by decide
      by_cases hm : isMovedDir hg w.1
      · simp [τ, liftW, hw0, h01, hm]
      · simp only [τ, liftW, tailPt_consPt, consPt_snd_zero, hw0, h01, hm, ↓reduceIte,
          and_false, not_false_eq_true]
        congr 1; push_cast; ring
    have hDτ_eq : (-1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ)
          + ∑ u ∈ R, (((τ (consPt 0 0 u) - τ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
        = (-1 : ℂ) • 1 + ∑ u ∈ R,
            (if isMovedDir hg (tailPt u).1 then (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) else 0) • pauli u := by
      conv_lhs => rw [hneg1]
      congr 1; refine Finset.sum_congr rfl fun u hu => ?_
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      have hw0 : w ≠ 0 := Finset.ne_of_mem_erase hw
      have h01 : (0 : ZMod 2) ≠ 1 := by decide
      by_cases hm : isMovedDir hg w.1
      · simp only [τ, liftW, tailPt_consPt, consPt_snd_zero, hw0, h01, hm, ↓reduceIte,
          false_and, true_and]
        congr 1; push_cast; ring
      · simp [τ, liftW, hw0, h01, hm]
    rw [hCσ_eq, hDσ_eq, hCτ_eq, hDτ_eq,
      hchar_Y 1 (fun w => (((2 * gSign hg w : ℝ) : ℂ))),
      hchar_Y (-1) (fun _ => (0 : ℂ)),
      hchar_Y 1 (fun w => if ¬ isMovedDir hg w.1 then (((2 * gSign hg w : ℝ) : ℂ)) else 0),
      hchar_Y (-1) (fun w => if isMovedDir hg w.1 then (((2 * gSign hg w : ℝ) : ℂ)) else 0)]
    -- Identify the four `g`-qubit matrices with `-1 + (complexB1 + complexB2)`, `-1`, `-1 + complexB1`, `-1 + complexB2`!
    have hm1 : (1 : ℂ) • (1 : Matrix (Vec g) (Vec g) ℂ)
          + ∑ w ∈ allPoints g, (((2 * gSign hg w : ℝ) : ℂ)) • pauli w
        = -1 + (complexB1 hg + complexB2 hg) := by
      rw [← Finset.sum_filter_add_sum_filter_not (allPoints g) (fun w => ¬ isMovedDir hg w.1)]
      simp only [not_not]
      rw [sum_complex_unmoved hg, sum_complex_moved hg]
      ext x y; simp [Matrix.add_apply, Matrix.smul_apply]; ring
    have hm2 : (-1 : ℂ) • (1 : Matrix (Vec g) (Vec g) ℂ) + ∑ w ∈ allPoints g, (0 : ℂ) • pauli w
        = (-1 : Matrix (Vec g) (Vec g) ℂ) := by simp
    have hm3 : (1 : ℂ) • (1 : Matrix (Vec g) (Vec g) ℂ)
          + ∑ w ∈ allPoints g, (if ¬ isMovedDir hg w.1 then (((2 * gSign hg w : ℝ) : ℂ)) else 0) • pauli w
        = -1 + complexB1 hg := by
      have ht : ∀ w ∈ allPoints g,
          (if ¬ isMovedDir hg w.1 then (((2 * gSign hg w : ℝ) : ℂ)) else 0) • pauli w
            = if ¬ isMovedDir hg w.1 then (((2 * gSign hg w : ℝ) : ℂ)) • pauli w else 0 := by
        intro w _; split_ifs <;> simp
      rw [Finset.sum_congr rfl ht, ← Finset.sum_filter, sum_complex_unmoved hg]
      ext x y; simp [Matrix.add_apply, Matrix.smul_apply]; ring
    have hm4 : (-1 : ℂ) • (1 : Matrix (Vec g) (Vec g) ℂ)
          + ∑ w ∈ allPoints g, (if isMovedDir hg w.1 then (((2 * gSign hg w : ℝ) : ℂ)) else 0) • pauli w
        = -1 + complexB2 hg := by
      have ht : ∀ w ∈ allPoints g,
          (if isMovedDir hg w.1 then (((2 * gSign hg w : ℝ) : ℂ)) else 0) • pauli w
            = if isMovedDir hg w.1 then (((2 * gSign hg w : ℝ) : ℂ)) • pauli w else 0 := by
        intro w _; split_ifs <;> simp
      rw [Finset.sum_congr rfl ht, ← Finset.sum_filter, sum_complex_moved hg]
      simp
    rw [hm1, hm2, hm3, hm4]
    have hsplit := charpoly_block_split (complexB1 hg) (complexB2 hg) (complexB1_mul_complexB2 hg)
    rw [charpoly_fromBlocks_zero₁₂, charpoly_fromBlocks_zero₁₂] at hsplit
    calc (-1 + (complexB1 hg + complexB2 hg)).charpoly ^ 2 * (-1 : Matrix (Vec g) (Vec g) ℂ).charpoly ^ 2
        = ((-1 + (complexB1 hg + complexB2 hg)).charpoly * (-1 : Matrix (Vec g) (Vec g) ℂ).charpoly) ^ 2 := by ring
      _ = ((-1 + complexB1 hg).charpoly * (-1 + complexB2 hg).charpoly) ^ 2 := by rw [hsplit]
      _ = (-1 + complexB1 hg).charpoly ^ 2 * (-1 + complexB2 hg).charpoly ^ 2 := by ring
  refine ⟨σ, τ, hσ_val, hτ_val, hcpA, ?_⟩
  have he_mem : e ∈ sectionOf X d := by rw [hH]; exact Finset.mem_insert_self _ _
  have hqe : qformShift c e = 0 := by
    have hptZ0 : e = consPt 0 1 (consPt 0 0 0) := by
      ext i <;> refine Fin.cases (by simp [e, ptZ, consPt]) (fun j => by
        refine Fin.cases (by simp [e, ptZ, consPt]) (fun k => by simp [e, ptZ, consPt]) j) i
    rw [hptZ0, hc_qshift, qformShift_zero]; simp
  have hqd : qformShift c d = 1 := by
    have hd_cons : d = consPt 0 0 (consPt 1 1 0) := by
      have h0 : ptY (0 : Fin (g + 1)) = consPt 1 1 0 := by
        ext i <;> refine Fin.cases (by simp [ptY, consPt]) (fun j => by simp [ptY, consPt]) i
      rw [← h0, consPt_zero_ptY]; rfl
    rw [hd_cons, hc_qshift, qformShift_zero]; simp
  have hde : symp d e = 0 := symp_ptY_ptZ (by simp)
  apply completion_charpoly_ne_of_trace_sq_ne
    (isClosedCfg_perpSet (isClosedCfg_quadric c) e) d e he_mem
    ((4 : ℂ) ^ (g + 2) / 8) (eps (qform c) * (2 : ℂ) ^ (g + 2) / 2)
    (div_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num))
    (fun s hs => by
      obtain ⟨hsX, hsd⟩ := Finset.mem_filter.mp hs
      obtain ⟨hsQ, hse⟩ := Finset.mem_filter.mp hsX
      obtain ⟨hs0, hqs⟩ := (Finset.mem_filter.mp hsQ).2
      exact charSumOut_C12_C15 hqe hqd hde hs0 hqs hse hsd)
    hσe hτe hcpA
  refine trace_sq_ne_of_flipped R h0R (sectionOf X d) hH (fun u => isMovedDir hg (tailPt u).1) σ τ
    (fun u _ => hσ_val _)
    (fun u hu => by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      simp [σ, liftW, Finset.ne_of_mem_erase hw])
    (fun u hu => by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      have h01 : (0 : ZMod 2) ≠ 1 := by decide
      simp [σ, τ, liftW, consPt, Finset.ne_of_mem_erase hw, h01])
    (fun u hu => by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      by_cases hm : isMovedDir hg w.1 <;>
        simp [σ, τ, liftW, consPt, Finset.ne_of_mem_erase hw, hm])
    ⟨liftW (gv1 hg, 0), Finset.mem_image.mpr
      ⟨(gv1 hg, 0), Finset.mem_erase.mpr ⟨fun h => gv_ne_01 hg (congrArg Prod.fst h), mem_univ _⟩, rfl⟩,
      by simp [liftW, isMovedDir]⟩

/-- **Case C12 (all `N ≥ 4`).** `X = Q⁺(2N-1,2) ∩ Z₀⊥`, `e = Z₀`, `d = Y₁`. -/
theorem c12_strict_law_fails {g : ℕ} (hg : 2 ≤ g) :
    let e : Pt (g + 2) := ptZ 0
    let d : Pt (g + 2) := ptY ⟨1, by omega⟩
    let X : Finset (Pt (g + 2)) := perpSet (quadric (g + 2) 0) e
    ∃ σ τ : Pt (g + 2) → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  have hc0 : consPt 0 0 (consPt 0 0 (0 : Pt g)) = 0 := by rw [consPt_zero, consPt_zero]
  dsimp only
  rw [← hc0]
  exact c12_c15_strict_law_fails hg (0 : Pt g)

/-- **Case C15 (all `N ≥ 4`).** `X = Q⁻(2N-1,2) ∩ Z₀⊥` (`c = Y₂`), `e = Z₀`, `d = Y₁`. -/
theorem c15_strict_law_fails {g : ℕ} (hg : 2 ≤ g) :
    let c : Pt (g + 2) := ptY ⟨2, by omega⟩
    let e : Pt (g + 2) := ptZ 0
    let d : Pt (g + 2) := ptY ⟨1, by omega⟩
    let X : Finset (Pt (g + 2)) := perpSet (quadric (g + 2) c) e
    ∃ σ τ : Pt (g + 2) → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  have hc2 : consPt 0 0 (consPt 0 0 (ptY (⟨0, by omega⟩ : Fin g))) = ptY ⟨2, by omega⟩ := by
    rw [consPt_zero_ptY, consPt_zero_ptY]; rfl
  dsimp only
  rw [← hc2]
  exact c12_c15_strict_law_fails hg (ptY ⟨0, by omega⟩)

end CasesC12C15

/-! ### Part 6. Case C5 (`N ≥ 4`, quaternionic graph on `Q⁻(2N-1,2)`, `c = Y₁`, `d = Z₀`) -/

section CaseC5

/-- Sum of the three single-qubit Pauli matrices `X + Z + Y` on `ZMod 2`. -/
def pauliXYZ : Matrix (ZMod 2) (ZMod 2) ℂ :=
  pauli1 1 0 + pauli1 0 1 + pauli1 1 1

/-- Quaternionic graph `B₁` on `ZMod 2 × Vec g`, scaled by `2`. -/
def quatB1 {g : ℕ} (hg : 2 ≤ g) : Matrix (ZMod 2 × Vec g) (ZMod 2 × Vec g) ℂ :=
  (1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ (((2 : ℂ) * (2 : ℂ) ^ g) • diagProj (gv2 hg))
    + ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => ¬ isMovedDir hg a),
        ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ (((2 : ℂ) * (2 : ℂ) ^ (g - 1)) • edgeReal (uEdge hg a) a)
          + pauliXYZ ⊗ₖ (((2 : ℂ) * (2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag (uEdge hg a) a))

/-- Quaternionic graph `B₂` on `ZMod 2 × Vec g`, scaled by `2`. -/
def quatB2 {g : ℕ} (hg : 2 ≤ g) : Matrix (ZMod 2 × Vec g) (ZMod 2 × Vec g) ℂ :=
  ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => isMovedDir hg a),
    ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ (((2 : ℂ) * (2 : ℂ) ^ (g - 1)) • edgeReal (uEdge hg a) a)
      + pauliXYZ ⊗ₖ (((2 : ℂ) * (2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag (uEdge hg a) a))

lemma quatB1_col_support {g : ℕ} (hg : 2 ≤ g) {x y : ZMod 2 × Vec g} (hy : inTriVert hg y.2) :
    quatB1 hg x y = 0 := by
  unfold quatB1
  simp only [Matrix.add_apply, Matrix.sum_apply, kroneckerMap_apply, Matrix.smul_apply,
    smul_eq_mul, diagProj]
  have h1 : ¬ (x.2 = gv2 hg ∧ y.2 = gv2 hg) := fun h => not_inTriVert_gv2 hg (h.2 ▸ hy)
  rw [ite_eq_right h1, mul_zero, mul_zero, zero_add]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hnot := uEdge_not_inTriVert_of_unmoved hg (Finset.mem_filter.mp ha).2
  have ha1 : ¬ (x.2 = uEdge hg a + a ∧ y.2 = uEdge hg a) := fun h => hnot.1 (h.2 ▸ hy)
  have ha2 : ¬ (x.2 = uEdge hg a ∧ y.2 = uEdge hg a + a) := fun h => hnot.2 (h.2 ▸ hy)
  simp [edgeReal, edgeImag, ha1, ha2]

lemma quatB2_row_support {g : ℕ} (hg : 2 ≤ g) {y z : ZMod 2 × Vec g} (hy : ¬ inTriVert hg y.2) :
    quatB2 hg y z = 0 := by
  unfold quatB2
  simp only [Matrix.sum_apply, Matrix.add_apply, kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hin := uEdge_inTriVert_of_moved hg (Finset.mem_filter.mp ha).2
  have ha1 : ¬ (y.2 = uEdge hg a + a ∧ z.2 = uEdge hg a) := fun h => hy (h.1 ▸ hin.2)
  have ha2 : ¬ (y.2 = uEdge hg a ∧ z.2 = uEdge hg a + a) := fun h => hy (h.1 ▸ hin.1)
  simp [edgeReal, edgeImag, ha1, ha2]

lemma quatB1_mul_quatB2 {g : ℕ} (hg : 2 ≤ g) : quatB1 hg * quatB2 hg = 0 := by
  ext x z
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hy : inTriVert hg y.2
  · rw [quatB1_col_support hg hy, zero_mul]
  · rw [quatB2_row_support hg hy, mul_zero]

lemma pauli1_zero_zero : pauli1 0 0 = (1 : Matrix (ZMod 2) (ZMod 2) ℂ) := by
  ext x y
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  simp [pauli1, h01, Matrix.one_apply]

/-- Quaternionic block sum for unmoved points of `R = quadric (g + 1) (ptY 0)`. -/
lemma sum_quat_unmoved {g : ℕ} (hg : 2 ≤ g) :
    Matrix.reindex (splitProd g) (splitProd g)
        (∑ u ∈ (quadric (g + 1) (ptY 0)).filter (fun u => ¬ isMovedDir hg (tailPt u).1),
          (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) • pauli u)
      = (-2 : ℂ) • (1 : Matrix (ZMod 2 × Vec g) (ZMod 2 × Vec g) ℂ) + quatB1 hg := by
  have h1g : 1 ≤ g := by omega
  have hq0_g : ∀ w : Pt g, qformShift (0 : Pt g) w = qform w := fun w => by
    rw [qformShift, symp_comm, symp_zero_right, add_zero]
  have hqY : ∀ (a1 c1 : ZMod 2) (w : Pt g),
      qformShift (ptY 0) (consPt a1 c1 w) = c1 * a1 + c1 + a1 + qform w := by
    intro a1 c1 w
    have hpt : ptY (0 : Fin (g + 1)) = consPt 1 1 0 := by
      ext i <;> refine Fin.cases (by simp [ptY, consPt]) (fun j => by simp [ptY, consPt]) i
    rw [qformShift, qform_consPt, hpt, symp_consPt]
    simp [symp]; ring
  -- Partition `R_unmoved` into `(a1, c1) = (0, 0)` (real `w ∈ quadric g 0`) and `(a1, c1) ≠ (0, 0)` (imaginary `w`).
  set S := (quadric (g + 1) (ptY 0)).filter (fun u => ¬ isMovedDir hg (tailPt u).1)
  have hre_sum : Matrix.reindex (splitProd g) (splitProd g)
        (∑ u ∈ S, (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) • pauli u)
      = ∑ u ∈ S, (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) •
          Matrix.reindex (splitProd g) (splitProd g) (pauli u) := by
    ext x y; simp [Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply]
  rw [hre_sum, ← Finset.sum_filter_add_sum_filter_not S (fun u => u.1 0 = 0 ∧ u.2 0 = 0)]
  -- Part A: `(a1, c1) = (0, 0)`, i.e. `consPt 0 0 w` for `w ∈ (quadric g 0).filter (¬ isMovedDir)`.
  have hA_set : S.filter (fun u => u.1 0 = 0 ∧ u.2 0 = 0)
      = ((quadric g 0).filter (fun w => ¬ isMovedDir hg w.1)).image (consPt 0 0) := by
    ext u
    simp only [S, quadric, hq0_g, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨hu0, hqu⟩, hm⟩, ha0, hc0⟩
      refine ⟨tailPt u, ⟨⟨?_, ?_⟩, hm⟩, ?_⟩
      · intro hw; apply hu0; rw [← consPt_tailPt u, ha0, hc0, hw]; exact consPt_zero
      · have h := hqY (u.1 0) (u.2 0) (tailPt u)
        rw [consPt_tailPt, ha0, hc0] at h
        simpa [h] using hqu
      · exact consPt_eq_of_eq ha0 hc0
    · rintro ⟨w, ⟨⟨hw0, hqw⟩, hm⟩, rfl⟩
      refine ⟨⟨⟨fun h => hw0 ((consPt_eq_zero_iff 0 0 w).mp h).2.2, ?_⟩, by simpa using hm⟩, rfl, rfl⟩
      rw [hqY, hqw]; simp
  have hA : ∑ u ∈ S.filter (fun u => u.1 0 = 0 ∧ u.2 0 = 0),
        (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) • Matrix.reindex (splitProd g) (splitProd g) (pauli u)
      = (1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ ((-2 : ℂ) • (1 : Matrix (Vec g) (Vec g) ℂ) + realB1 hg) := by
    rw [hA_set, Finset.sum_image (fun _ _ _ _ h => consPt_injective 0 0 h)]
    have hterm : ∀ w ∈ (quadric g 0).filter (fun w => ¬ isMovedDir hg w.1),
        (((2 * gSign hg (tailPt (consPt 0 0 w)) : ℝ) : ℂ)) •
            Matrix.reindex (splitProd g) (splitProd g) (pauli (consPt 0 0 w))
          = (1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ ((((2 * gSign hg w : ℝ) : ℂ)) • pauli w) := by
      intro w _
      rw [tailPt_consPt, reindex_pauli_cons_prod, pauli1_zero_zero, kronecker_smul]
    rw [Finset.sum_congr rfl hterm, ← sum_real_unmoved hg]
    ext ⟨i, x⟩ ⟨j, y⟩
    simp [Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]
  -- Part B: `(a1, c1) ∈ {(1,0), (0,1), (1,1)}` and `qform w = 1` (hence `w.1 ≠ 0`).
  have hB_set : S.filter (fun u => ¬ (u.1 0 = 0 ∧ u.2 0 = 0))
      = (({(1, 0), (0, 1), (1, 1)} : Finset (ZMod 2 × ZMod 2))
          ×ˢ (((univ.erase (0 : Vec g)).filter (fun a => ¬ isMovedDir hg a)) ×ˢ (univ : Finset (Vec g))).filter
                (fun w => qform w = 1)).image (fun p => consPt p.1.1 p.1.2 p.2) := by
    ext u
    simp only [S, quadric, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, and_true]
    constructor
    · rintro ⟨⟨⟨_, hqu⟩, hm⟩, hne00⟩
      have hpair : (u.1 0, u.2 0) = (1, 0) ∨ (u.1 0, u.2 0) = (0, 1) ∨ (u.1 0, u.2 0) = (1, 1) := by
        rcases zmod2_cases (u.1 0) with h1 | h1 <;> rcases zmod2_cases (u.2 0) with h2 | h2
        · exact absurd ⟨h1, h2⟩ hne00
        · right; left; exact Prod.ext h1 h2
        · left; exact Prod.ext h1 h2
        · right; right; exact Prod.ext h1 h2
      have hq1 : qform (tailPt u) = 1 := by
        have h := hqY (u.1 0) (u.2 0) (tailPt u)
        rw [consPt_tailPt, hqu] at h
        rcases hpair with hp | hp | hp
        · have h1 := congrArg Prod.fst hp; have h2 := congrArg Prod.snd hp
          simp only at h1 h2; rw [h1, h2] at h
          rcases zmod2_cases (qform (tailPt u)) with hq | hq
          · rw [hq] at h; exact absurd h (by decide)
          · exact hq
        · have h1 := congrArg Prod.fst hp; have h2 := congrArg Prod.snd hp
          simp only at h1 h2; rw [h1, h2] at h
          rcases zmod2_cases (qform (tailPt u)) with hq | hq
          · rw [hq] at h; exact absurd h (by decide)
          · exact hq
        · have h1 := congrArg Prod.fst hp; have h2 := congrArg Prod.snd hp
          simp only at h1 h2; rw [h1, h2] at h
          rcases zmod2_cases (qform (tailPt u)) with hq | hq
          · rw [hq] at h; exact absurd h (by decide)
          · exact hq
      have ha_ne : (tailPt u).1 ≠ 0 := by
        intro ha; rw [qform, ha, dotProduct_zero] at hq1; exact absurd hq1 (by decide)
      refine ⟨((u.1 0, u.2 0), tailPt u), ⟨hpair, ⟨⟨ha_ne, hm⟩, hq1⟩⟩, ?_⟩
      exact consPt_tailPt u
    · rintro ⟨⟨⟨a1, c1⟩, ⟨a, c⟩⟩, ⟨hpair, ⟨⟨ha0, hm⟩, hq1⟩⟩, rfl⟩
      have hne00 : ¬ (a1 = 0 ∧ c1 = 0) := by
        rcases hpair with h | h | h <;> rcases Prod.mk.inj h with ⟨rfl, rfl⟩ <;> decide
      have hq_cons : qformShift (ptY 0) (consPt a1 c1 (a, c)) = 0 := by
        rw [hqY, hq1]
        rcases hpair with h | h | h <;> rcases Prod.mk.inj h with ⟨rfl, rfl⟩ <;> decide
      refine ⟨⟨⟨fun h => ha0 (congrArg Prod.fst ((consPt_eq_zero_iff _ _ _).mp h).2.2), hq_cons⟩,
        by simpa using hm⟩, by simpa [consPt] using hne00⟩
  have hB : ∑ u ∈ S.filter (fun u => ¬ (u.1 0 = 0 ∧ u.2 0 = 0)),
        (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) • Matrix.reindex (splitProd g) (splitProd g) (pauli u)
      = ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => ¬ isMovedDir hg a),
          pauliXYZ ⊗ₖ (((2 : ℂ) * (2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag (uEdge hg a) a) := by
    have hinj : Function.Injective (fun p : (ZMod 2 × ZMod 2) × Pt g => consPt p.1.1 p.1.2 p.2) := by
      rintro ⟨⟨a1, c1⟩, w1⟩ ⟨⟨a2, c2⟩, w2⟩ h
      have h1 := congrFun (congrArg Prod.fst h) 0
      have h2 := congrFun (congrArg Prod.snd h) 0
      have h3 := congrArg tailPt h
      simp only [consPt, Fin.cons_zero] at h1 h2 h3
      exact Prod.ext (Prod.ext h1 h2) h3
    rw [hB_set, Finset.sum_image (fun _ _ _ _ h => hinj h), Finset.sum_product]
    have htriple : ∀ f : ZMod 2 × ZMod 2 → Matrix (ZMod 2 × Vec g) (ZMod 2 × Vec g) ℂ,
        ∑ p ∈ ({(1, 0), (0, 1), (1, 1)} : Finset (ZMod 2 × ZMod 2)), f p
          = f (1, 0) + f (0, 1) + f (1, 1) := by
      intro f
      have h1 : ((1 : ZMod 2), (0 : ZMod 2)) ∉ ({(0, 1), (1, 1)} : Finset (ZMod 2 × ZMod 2)) := by decide
      have h2 : ((0 : ZMod 2), (1 : ZMod 2)) ∉ ({(1, 1)} : Finset (ZMod 2 × ZMod 2)) := by decide
      rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton, add_assoc]
    rw [htriple]
    have hdir : ∀ (a1 c1 : ZMod 2),
        ∑ w ∈ (((univ.erase (0 : Vec g)).filter (fun a => ¬ isMovedDir hg a)) ×ˢ (univ : Finset (Vec g))).filter
              (fun w => qform w = 1),
            (((2 * gSign hg (tailPt (consPt a1 c1 w)) : ℝ) : ℂ)) •
              Matrix.reindex (splitProd g) (splitProd g) (pauli (consPt a1 c1 w))
          = ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => ¬ isMovedDir hg a),
              pauli1 a1 c1 ⊗ₖ (((2 : ℂ) * (2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag (uEdge hg a) a) := by
      intro a1 c1
      rw [Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha0 : a ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_filter.mp ha).1
      rw [← Finset.sum_filter]
      have hterm : ∀ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 1),
          (((2 * gSign hg (tailPt (consPt a1 c1 (a, c))) : ℝ) : ℂ)) •
              Matrix.reindex (splitProd g) (splitProd g) (pauli (consPt a1 c1 (a, c)))
            = pauli1 a1 c1 ⊗ₖ ((2 : ℂ) • (((signOdd (uEdge hg a) a c : ℝ) : ℂ) • pauli (a, c))) := by
        intro c hc
        have hq : qform (a, c) = 1 := (Finset.mem_filter.mp hc).2
        have hq0 : qform (a, c) ≠ 0 := by rw [hq]; decide
        rw [tailPt_consPt, reindex_pauli_cons_prod, gSign, ite_eq_right ha0, ite_eq_right hq0,
          Complex.ofReal_mul, Complex.ofReal_ofNat, mul_smul, kronecker_smul, kronecker_smul]
      rw [Finset.sum_congr rfl hterm]
      have hsum_k : ∀ (P : Matrix (ZMod 2) (ZMod 2) ℂ) (T : Finset (Vec g))
          (F : Vec g → Matrix (Vec g) (Vec g) ℂ),
          ∑ c ∈ T, P ⊗ₖ F c = P ⊗ₖ ∑ c ∈ T, F c := by
        intro P T F; ext ⟨i, x⟩ ⟨j, y⟩; simp [Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]
      rw [hsum_k, ← Finset.smul_sum, sum_imag_pauli_dir h1g _ ha0, smul_smul, mul_assoc]
    rw [hdir 1 0, hdir 0 1, hdir 1 1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ext ⟨i, x⟩ ⟨j, y⟩
    simp [pauliXYZ, kroneckerMap_apply, Matrix.add_apply]; ring
  rw [hA, hB]
  unfold quatB1 realB1
  ext ⟨i, x⟩ ⟨j, y⟩
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, kroneckerMap_apply,
    Matrix.one_apply, smul_eq_mul, Finset.sum_add_distrib]
  by_cases hij : i = j <;> by_cases hxy : x = y <;> simp [hij, hxy, Prod.mk.injEq] <;> ring

/-- Quaternionic block sum for moved points of `R = quadric (g + 1) (ptY 0)`. -/
lemma sum_quat_moved {g : ℕ} (hg : 2 ≤ g) :
    Matrix.reindex (splitProd g) (splitProd g)
        (∑ u ∈ (quadric (g + 1) (ptY 0)).filter (fun u => isMovedDir hg (tailPt u).1),
          (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) • pauli u)
      = quatB2 hg := by
  have h1g : 1 ≤ g := by omega
  have hq0_g : ∀ w : Pt g, qformShift (0 : Pt g) w = qform w := fun w => by
    rw [qformShift, symp_comm, symp_zero_right, add_zero]
  have hqY : ∀ (a1 c1 : ZMod 2) (w : Pt g),
      qformShift (ptY 0) (consPt a1 c1 w) = c1 * a1 + c1 + a1 + qform w := by
    intro a1 c1 w
    have hpt : ptY (0 : Fin (g + 1)) = consPt 1 1 0 := by
      ext i <;> refine Fin.cases (by simp [ptY, consPt]) (fun j => by simp [ptY, consPt]) i
    rw [qformShift, qform_consPt, hpt, symp_consPt]
    simp [symp]; ring
  set S := (quadric (g + 1) (ptY 0)).filter (fun u => isMovedDir hg (tailPt u).1)
  have hre_sum : Matrix.reindex (splitProd g) (splitProd g)
        (∑ u ∈ S, (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) • pauli u)
      = ∑ u ∈ S, (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) •
          Matrix.reindex (splitProd g) (splitProd g) (pauli u) := by
    ext x y; simp [Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply]
  rw [hre_sum, ← Finset.sum_filter_add_sum_filter_not S (fun u => u.1 0 = 0 ∧ u.2 0 = 0)]
  have hA_set : S.filter (fun u => u.1 0 = 0 ∧ u.2 0 = 0)
      = ((quadric g 0).filter (fun w => isMovedDir hg w.1)).image (consPt 0 0) := by
    ext u
    simp only [S, quadric, hq0_g, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨hu0, hqu⟩, hm⟩, ha0, hc0⟩
      refine ⟨tailPt u, ⟨⟨?_, ?_⟩, hm⟩, ?_⟩
      · intro hw; apply hu0; rw [← consPt_tailPt u, ha0, hc0, hw]; exact consPt_zero
      · have h := hqY (u.1 0) (u.2 0) (tailPt u)
        rw [consPt_tailPt, ha0, hc0] at h
        simpa [h] using hqu
      · exact consPt_eq_of_eq ha0 hc0
    · rintro ⟨w, ⟨⟨hw0, hqw⟩, hm⟩, rfl⟩
      refine ⟨⟨⟨fun h => hw0 ((consPt_eq_zero_iff 0 0 w).mp h).2.2, ?_⟩, by simpa using hm⟩, rfl, rfl⟩
      rw [hqY, hqw]; simp
  have hA : ∑ u ∈ S.filter (fun u => u.1 0 = 0 ∧ u.2 0 = 0),
        (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) • Matrix.reindex (splitProd g) (splitProd g) (pauli u)
      = (1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ realB2 hg := by
    rw [hA_set, Finset.sum_image (fun _ _ _ _ h => consPt_injective 0 0 h)]
    have hterm : ∀ w ∈ (quadric g 0).filter (fun w => isMovedDir hg w.1),
        (((2 * gSign hg (tailPt (consPt 0 0 w)) : ℝ) : ℂ)) •
            Matrix.reindex (splitProd g) (splitProd g) (pauli (consPt 0 0 w))
          = (1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ ((((2 * gSign hg w : ℝ) : ℂ)) • pauli w) := by
      intro w _
      rw [tailPt_consPt, reindex_pauli_cons_prod, pauli1_zero_zero, kronecker_smul]
    rw [Finset.sum_congr rfl hterm, ← sum_real_moved hg]
    ext ⟨i, x⟩ ⟨j, y⟩
    simp [Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]
  have hB_set : S.filter (fun u => ¬ (u.1 0 = 0 ∧ u.2 0 = 0))
      = (({(1, 0), (0, 1), (1, 1)} : Finset (ZMod 2 × ZMod 2))
          ×ˢ (((univ.erase (0 : Vec g)).filter (fun a => isMovedDir hg a)) ×ˢ (univ : Finset (Vec g))).filter
                (fun w => qform w = 1)).image (fun p => consPt p.1.1 p.1.2 p.2) := by
    ext u
    simp only [S, quadric, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, and_true]
    constructor
    · rintro ⟨⟨⟨_, hqu⟩, hm⟩, hne00⟩
      have hpair : (u.1 0, u.2 0) = (1, 0) ∨ (u.1 0, u.2 0) = (0, 1) ∨ (u.1 0, u.2 0) = (1, 1) := by
        rcases zmod2_cases (u.1 0) with h1 | h1 <;> rcases zmod2_cases (u.2 0) with h2 | h2
        · exact absurd ⟨h1, h2⟩ hne00
        · right; left; exact Prod.ext h1 h2
        · left; exact Prod.ext h1 h2
        · right; right; exact Prod.ext h1 h2
      have hq1 : qform (tailPt u) = 1 := by
        have h := hqY (u.1 0) (u.2 0) (tailPt u)
        rw [consPt_tailPt, hqu] at h
        rcases hpair with hp | hp | hp
        · have h1 := congrArg Prod.fst hp; have h2 := congrArg Prod.snd hp
          simp only at h1 h2; rw [h1, h2] at h
          rcases zmod2_cases (qform (tailPt u)) with hq | hq
          · rw [hq] at h; exact absurd h (by decide)
          · exact hq
        · have h1 := congrArg Prod.fst hp; have h2 := congrArg Prod.snd hp
          simp only at h1 h2; rw [h1, h2] at h
          rcases zmod2_cases (qform (tailPt u)) with hq | hq
          · rw [hq] at h; exact absurd h (by decide)
          · exact hq
        · have h1 := congrArg Prod.fst hp; have h2 := congrArg Prod.snd hp
          simp only at h1 h2; rw [h1, h2] at h
          rcases zmod2_cases (qform (tailPt u)) with hq | hq
          · rw [hq] at h; exact absurd h (by decide)
          · exact hq
      have ha_ne : (tailPt u).1 ≠ 0 := by
        intro ha; rw [qform, ha, dotProduct_zero] at hq1; exact absurd hq1 (by decide)
      refine ⟨((u.1 0, u.2 0), tailPt u), ⟨hpair, ⟨⟨ha_ne, hm⟩, hq1⟩⟩, ?_⟩
      exact consPt_tailPt u
    · rintro ⟨⟨⟨a1, c1⟩, ⟨a, c⟩⟩, ⟨hpair, ⟨⟨ha0, hm⟩, hq1⟩⟩, rfl⟩
      have hne00 : ¬ (a1 = 0 ∧ c1 = 0) := by
        rcases hpair with h | h | h <;> rcases Prod.mk.inj h with ⟨rfl, rfl⟩ <;> decide
      have hq_cons : qformShift (ptY 0) (consPt a1 c1 (a, c)) = 0 := by
        rw [hqY, hq1]
        rcases hpair with h | h | h <;> rcases Prod.mk.inj h with ⟨rfl, rfl⟩ <;> decide
      refine ⟨⟨⟨fun h => ha0 (congrArg Prod.fst ((consPt_eq_zero_iff _ _ _).mp h).2.2), hq_cons⟩,
        by simpa using hm⟩, by simpa [consPt] using hne00⟩
  have hB : ∑ u ∈ S.filter (fun u => ¬ (u.1 0 = 0 ∧ u.2 0 = 0)),
        (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) • Matrix.reindex (splitProd g) (splitProd g) (pauli u)
      = ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => isMovedDir hg a),
          pauliXYZ ⊗ₖ (((2 : ℂ) * (2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag (uEdge hg a) a) := by
    have hinj : Function.Injective (fun p : (ZMod 2 × ZMod 2) × Pt g => consPt p.1.1 p.1.2 p.2) := by
      rintro ⟨⟨a1, c1⟩, w1⟩ ⟨⟨a2, c2⟩, w2⟩ h
      have h1 := congrFun (congrArg Prod.fst h) 0
      have h2 := congrFun (congrArg Prod.snd h) 0
      have h3 := congrArg tailPt h
      simp only [consPt, Fin.cons_zero] at h1 h2 h3
      exact Prod.ext (Prod.ext h1 h2) h3
    rw [hB_set, Finset.sum_image (fun _ _ _ _ h => hinj h), Finset.sum_product]
    have htriple : ∀ f : ZMod 2 × ZMod 2 → Matrix (ZMod 2 × Vec g) (ZMod 2 × Vec g) ℂ,
        ∑ p ∈ ({(1, 0), (0, 1), (1, 1)} : Finset (ZMod 2 × ZMod 2)), f p
          = f (1, 0) + f (0, 1) + f (1, 1) := by
      intro f
      have h1 : ((1 : ZMod 2), (0 : ZMod 2)) ∉ ({(0, 1), (1, 1)} : Finset (ZMod 2 × ZMod 2)) := by decide
      have h2 : ((0 : ZMod 2), (1 : ZMod 2)) ∉ ({(1, 1)} : Finset (ZMod 2 × ZMod 2)) := by decide
      rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton, add_assoc]
    rw [htriple]
    have hdir : ∀ (a1 c1 : ZMod 2),
        ∑ w ∈ (((univ.erase (0 : Vec g)).filter (fun a => isMovedDir hg a)) ×ˢ (univ : Finset (Vec g))).filter
              (fun w => qform w = 1),
            (((2 * gSign hg (tailPt (consPt a1 c1 w)) : ℝ) : ℂ)) •
              Matrix.reindex (splitProd g) (splitProd g) (pauli (consPt a1 c1 w))
          = ∑ a ∈ (univ.erase (0 : Vec g)).filter (fun a => isMovedDir hg a),
              pauli1 a1 c1 ⊗ₖ (((2 : ℂ) * (2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag (uEdge hg a) a) := by
      intro a1 c1
      rw [Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha0 : a ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_filter.mp ha).1
      rw [← Finset.sum_filter]
      have hterm : ∀ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 1),
          (((2 * gSign hg (tailPt (consPt a1 c1 (a, c))) : ℝ) : ℂ)) •
              Matrix.reindex (splitProd g) (splitProd g) (pauli (consPt a1 c1 (a, c)))
            = pauli1 a1 c1 ⊗ₖ ((2 : ℂ) • (((signOdd (uEdge hg a) a c : ℝ) : ℂ) • pauli (a, c))) := by
        intro c hc
        have hq : qform (a, c) = 1 := (Finset.mem_filter.mp hc).2
        have hq0 : qform (a, c) ≠ 0 := by rw [hq]; decide
        rw [tailPt_consPt, reindex_pauli_cons_prod, gSign, ite_eq_right ha0, ite_eq_right hq0,
          Complex.ofReal_mul, Complex.ofReal_ofNat, mul_smul, kronecker_smul, kronecker_smul]
      rw [Finset.sum_congr rfl hterm]
      have hsum_k : ∀ (P : Matrix (ZMod 2) (ZMod 2) ℂ) (T : Finset (Vec g))
          (F : Vec g → Matrix (Vec g) (Vec g) ℂ),
          ∑ c ∈ T, P ⊗ₖ F c = P ⊗ₖ ∑ c ∈ T, F c := by
        intro P T F; ext ⟨i, x⟩ ⟨j, y⟩; simp [Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]
      rw [hsum_k, ← Finset.smul_sum, sum_imag_pauli_dir h1g _ ha0, smul_smul, mul_assoc]
    rw [hdir 1 0, hdir 0 1, hdir 1 1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ext ⟨i, x⟩ ⟨j, y⟩
    simp [pauliXYZ, kroneckerMap_apply, Matrix.add_apply]; ring
  rw [hA, hB]
  unfold quatB2 realB2
  ext ⟨i, x⟩ ⟨j, y⟩
  simp [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, kroneckerMap_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib]

/-- **Case C5 (all `N ≥ 4`).** Elliptic quadric `Q⁻(2N-1,2)` (`c = Y₁`) cut by `d = Z₀`. -/
theorem c5_strict_law_fails {g : ℕ} (hg : 2 ≤ g) :
    let c : Pt (g + 2) := ptY ⟨1, by omega⟩
    let d : Pt (g + 2) := ptZ 0
    let X : Finset (Pt (g + 2)) := quadric (g + 2) c
    ∃ σ τ : Pt (g + 2) → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  intro c d X
  set R : Finset (Pt (g + 1)) := quadric (g + 1) (ptY 0)
  have h0R : (0 : Pt (g + 1)) ∉ R := by simp [R, quadric]
  have hc_cons : c = consPt 0 0 (ptY 0) := by
    rw [consPt_zero_ptY]; rfl
  have hH : sectionOf X d = insert (ptZ 0) (R.image (consPt 0 0) ∪ R.image (consPt 0 1)) := by
    ext s
    simp only [sectionOf, X, d, quadric, R, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_union, Finset.mem_image, symp_ptZ]
    constructor
    · rintro ⟨⟨hs0, hqs⟩, ha0⟩
      have hqt : qformShift (ptY 0) (tailPt s) = 0 := by
        have h : qformShift c s = qformShift (ptY 0) (tailPt s) := by
          rw [← consPt_tailPt s, ha0, hc_cons, qformShift, qform_consPt, symp_consPt, qformShift]
          simp
        rwa [← h]
      by_cases ht : tailPt s = 0
      · left
        rw [← consPt_tailPt s, ha0, ht]
        rcases zmod2_cases (s.2 0) with hc | hc
        · exfalso; apply hs0; rw [← consPt_tailPt s, ha0, hc, ht]; exact consPt_zero
        · rw [hc]; ext i <;> refine Fin.cases (by simp [ptZ, consPt]) (fun j => by simp [ptZ, consPt]) i
      · right
        rcases zmod2_cases (s.2 0) with hc | hc
        · left; exact ⟨tailPt s, ⟨ht, hqt⟩, consPt_eq_of_eq ha0 hc⟩
        · right; exact ⟨tailPt s, ⟨ht, hqt⟩, consPt_eq_of_eq ha0 hc⟩
    · rintro (rfl | ⟨u, ⟨hu0, hqu⟩, rfl⟩ | ⟨u, ⟨hu0, hqu⟩, rfl⟩)
      · refine ⟨⟨ptZ_ne_zero 0, ?_⟩, rfl⟩
        rw [qformShift, qform_ptZ, symp_ptY_ptZ (by simp), add_zero]
      · refine ⟨⟨fun h => hu0 ((consPt_eq_zero_iff 0 0 u).mp h).2.2, ?_⟩, rfl⟩
        rw [hc_cons, qformShift, qform_consPt, symp_consPt]; simpa [qformShift] using hqu
      · refine ⟨⟨fun h => hu0 ((consPt_eq_zero_iff 0 1 u).mp h).2.2, ?_⟩, rfl⟩
        rw [hc_cons, qformShift, qform_consPt, symp_consPt]; simpa [qformShift] using hqu
  let σ : Pt (g + 2) → ℝ := fun s =>
    if tailPt s = 0 then 1 else gSign hg (tailPt (tailPt s))
  let τ : Pt (g + 2) → ℝ := fun s =>
    if tailPt s = 0 then 1
    else if s.2 0 = 1 ∧ isMovedDir hg (tailPt (tailPt s)).1 then -gSign hg (tailPt (tailPt s))
    else gSign hg (tailPt (tailPt s))
  have hσ_val : ∀ s, σ s = 1 ∨ σ s = -1 := fun s => by
    dsimp only [σ]
    split_ifs
    · left; rfl
    · exact gSign_eq_one_or hg _
  have hτ_val : ∀ s, τ s = 1 ∨ τ s = -1 := fun s => by
    dsimp only [τ]; split_ifs
    · left; rfl
    · rcases gSign_eq_one_or hg _ with h | h <;> [right; left] <;> linarith
    · exact gSign_eq_one_or hg _
  have hσd : σ d = 1 := by
    have ht : tailPt d = 0 := by ext i <;> simp [d, tailPt, ptZ]
    simp [σ, ht]
  have hτd : τ d = 1 := by
    have ht : tailPt d = 0 := by ext i <;> simp [d, tailPt, ptZ]
    simp [τ, ht]
  have hcpA : (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly := by
    have hre1 := reindex_opA_Z_split R h0R (sectionOf X d) hH σ hσd
    have hre2 := reindex_opA_Z_split R h0R (sectionOf X d) hH τ hτd
    rw [← Matrix.charpoly_reindex (splitSum (g + 1)), hre1, charpoly_fromBlocks_zero₁₂,
      ← Matrix.charpoly_reindex (splitSum (g + 1)), hre2, charpoly_fromBlocks_zero₁₂]
    -- Reindex each `(g+1)`-qubit block via `splitProd g` to match `quatB1`, `quatB2`!
    have hre_Cσ : Matrix.reindex (splitProd g) (splitProd g)
          (1 + ∑ u ∈ R, (((σ (consPt 0 0 u) + σ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u)
        = -1 + (quatB1 hg + quatB2 hg) := by
      have hterm : ∀ u ∈ R, (((σ (consPt 0 0 u) + σ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) • pauli u := by
        intro u hu
        have hu0 : u ≠ 0 := (Finset.mem_filter.mp hu).2.1
        simp only [σ, tailPt_consPt, hu0, ↓reduceIte]; congr 1; push_cast; ring
      rw [Finset.sum_congr rfl hterm,
        ← Finset.sum_filter_add_sum_filter_not R (fun u => ¬ isMovedDir hg (tailPt u).1)]
      simp only [not_not]
      have hadd : ∀ A B C : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ,
          Matrix.reindex (splitProd g) (splitProd g) (A + (B + C))
            = Matrix.reindex (splitProd g) (splitProd g) A
              + Matrix.reindex (splitProd g) (splitProd g) B
              + Matrix.reindex (splitProd g) (splitProd g) C := by
        intro A B C; ext x y; simp [Matrix.reindex_apply, Matrix.add_apply]; ring
      rw [hadd, show Matrix.reindex (splitProd g) (splitProd g) (1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ) = 1 by
          ext x y; simp [Matrix.reindex_apply, Matrix.one_apply], sum_quat_unmoved hg, sum_quat_moved hg]
      ext x y; simp [Matrix.add_apply, Matrix.smul_apply]; ring
    have hre_Dσ : Matrix.reindex (splitProd g) (splitProd g)
          (-1 + ∑ u ∈ R, (((σ (consPt 0 0 u) - σ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u)
        = (-1 : Matrix (ZMod 2 × Vec g) (ZMod 2 × Vec g) ℂ) := by
      have hterm : ∀ u ∈ R, (((σ (consPt 0 0 u) - σ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u = 0 :=
        fun u _ => by simp [σ]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero, add_zero]
      ext x y; simp [Matrix.reindex_apply, Matrix.one_apply]
    have hre_Cτ : Matrix.reindex (splitProd g) (splitProd g)
          (1 + ∑ u ∈ R, (((τ (consPt 0 0 u) + τ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u)
        = -1 + quatB1 hg := by
      have hterm : ∀ u ∈ R, (((τ (consPt 0 0 u) + τ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = if ¬ isMovedDir hg (tailPt u).1 then (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) • pauli u else 0 := by
        intro u hu
        have hu0 : u ≠ 0 := (Finset.mem_filter.mp hu).2.1
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        by_cases hm : isMovedDir hg (tailPt u).1
        · simp [τ, hu0, h01, hm]
        · simp only [τ, tailPt_consPt, consPt_snd_zero, hu0, h01, hm, ↓reduceIte,
            and_false, not_false_eq_true]
          congr 1; push_cast; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
      have hadd : ∀ A B : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ,
          Matrix.reindex (splitProd g) (splitProd g) (A + B)
            = Matrix.reindex (splitProd g) (splitProd g) A
              + Matrix.reindex (splitProd g) (splitProd g) B := by
        intro A B; ext x y; simp [Matrix.reindex_apply, Matrix.add_apply]
      rw [hadd, show Matrix.reindex (splitProd g) (splitProd g) (1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ) = 1 by
          ext x y; simp [Matrix.reindex_apply, Matrix.one_apply], sum_quat_unmoved hg]
      ext x y; simp [Matrix.add_apply, Matrix.smul_apply]; ring
    have hre_Dτ : Matrix.reindex (splitProd g) (splitProd g)
          (-1 + ∑ u ∈ R, (((τ (consPt 0 0 u) - τ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u)
        = -1 + quatB2 hg := by
      have hterm : ∀ u ∈ R, (((τ (consPt 0 0 u) - τ (consPt 0 1 u) : ℝ) : ℂ)) • pauli u
          = if isMovedDir hg (tailPt u).1 then (((2 * gSign hg (tailPt u) : ℝ) : ℂ)) • pauli u else 0 := by
        intro u hu
        have hu0 : u ≠ 0 := (Finset.mem_filter.mp hu).2.1
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        by_cases hm : isMovedDir hg (tailPt u).1
        · simp only [τ, tailPt_consPt, consPt_snd_zero, hu0, h01, hm, ↓reduceIte,
            false_and, true_and]
          congr 1; push_cast; ring
        · simp [τ, hu0, h01, hm]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
      have hadd : ∀ A B : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ,
          Matrix.reindex (splitProd g) (splitProd g) (A + B)
            = Matrix.reindex (splitProd g) (splitProd g) A
              + Matrix.reindex (splitProd g) (splitProd g) B := by
        intro A B; ext x y; simp [Matrix.reindex_apply, Matrix.add_apply]
      rw [hadd, show Matrix.reindex (splitProd g) (splitProd g) (-1 : Matrix (Vec (g + 1)) (Vec (g + 1)) ℂ) = -1 by
        ext x y; simp [Matrix.reindex_apply, Matrix.one_apply], sum_quat_moved hg]
    rw [← Matrix.charpoly_reindex (splitProd g) (1 + _),
      ← Matrix.charpoly_reindex (splitProd g) (-1 + _),
      ← Matrix.charpoly_reindex (splitProd g) (1 + _),
      ← Matrix.charpoly_reindex (splitProd g) (-1 + _),
      hre_Cσ, hre_Dσ, hre_Cτ, hre_Dτ]
    have hsplit := charpoly_block_split (quatB1 hg) (quatB2 hg) (quatB1_mul_quatB2 hg)
    rw [charpoly_fromBlocks_zero₁₂, charpoly_fromBlocks_zero₁₂] at hsplit
    exact hsplit
  refine ⟨σ, τ, hσ_val, hτ_val, hcpA, ?_⟩
  have hd_mem : d ∈ sectionOf X d := by rw [hH]; exact Finset.mem_insert_self _ _
  have hqd : qformShift c d = 0 := by
    rw [qformShift, qform_ptZ, symp_ptY_ptZ (by simp), add_zero]
  apply completion_charpoly_ne_of_trace_sq_ne (isClosedCfg_quadric c) d d hd_mem
    (-((4 : ℂ) ^ (g + 2) / 4)) 0
    (neg_ne_zero.mpr (div_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)))
    (fun s hs => by
      obtain ⟨hsQ, hsd⟩ := Finset.mem_filter.mp hs
      obtain ⟨hs0, hqs⟩ := (Finset.mem_filter.mp hsQ).2
      rw [charSumOut_C3_C5 hqd hs0 hqs hsd, add_zero])
    hσd hτd hcpA
  refine trace_sq_ne_of_flipped R h0R (sectionOf X d) hH (fun u => isMovedDir hg (tailPt u).1) σ τ
    (fun u _ => hσ_val _)
    (fun u hu => by simp [σ, (Finset.mem_filter.mp hu).2.1])
    (fun u hu => by
      have h01 : (0 : ZMod 2) ≠ 1 := by decide
      simp [σ, τ, consPt, (Finset.mem_filter.mp hu).2.1, h01])
    (fun u hu => by
      by_cases hm : isMovedDir hg (tailPt u).1 <;>
        simp [σ, τ, consPt, (Finset.mem_filter.mp hu).2.1, hm])
    ⟨consPt 0 0 (gv1 hg, 0), Finset.mem_filter.mpr ⟨mem_univ _,
      fun h => gv_ne_01 hg (congrArg Prod.fst ((consPt_eq_zero_iff 0 0 _).mp h).2.2),
      by
        have hpt : ptY (0 : Fin (g + 1)) = consPt 1 1 0 := by
          ext i <;> refine Fin.cases (by simp [ptY, consPt]) (fun j => by simp [ptY, consPt]) i
        rw [qformShift, qform_consPt, hpt, symp_consPt]; simp [qform, symp]⟩,
      by simp [isMovedDir]⟩

end CaseC5

/-! ### Part 7. Master Theorem: Jonah's Conjecture E in All Nine Vertex Cases (`N ≥ 4`) -/

/-- **Theorem 19 (Jonah's Conjecture E — complete formalization in Lean 4).**
For every number of qubits `N ≥ 4`, the strict law fails for `±1`-valued sign carriers in
**all nine vertex cases** of Jonah's classification (`C1, C3, C5, C6, C8, C11, C12, C14, C15`),
stated directly about the complex Pauli matrices `HoggarBound.pauli` and real signed-context
completion matrices `completionMat`. -/
theorem jonah_conjecture_e_all_nine_cases {N : ℕ} (hN : 4 ≤ N) :
    -- C1: W(2N-1,2), d = Z₀
    (∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf (allPoints N) (ptZ ⟨0, by omega⟩)) σ).charpoly
        = (opA (sectionOf (allPoints N) (ptZ ⟨0, by omega⟩)) τ).charpoly ∧
      (completionMat (allPoints N) (ptZ ⟨0, by omega⟩) σ).charpoly
        ≠ (completionMat (allPoints N) (ptZ ⟨0, by omega⟩) τ).charpoly) ∧
    -- C3: Q⁺(2N-1,2), d = Z₀
    (∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf (quadric N 0) (ptZ ⟨0, by omega⟩)) σ).charpoly
        = (opA (sectionOf (quadric N 0) (ptZ ⟨0, by omega⟩)) τ).charpoly ∧
      (completionMat (quadric N 0) (ptZ ⟨0, by omega⟩) σ).charpoly
        ≠ (completionMat (quadric N 0) (ptZ ⟨0, by omega⟩) τ).charpoly) ∧
    -- C5: Q⁻(2N-1,2) (c = Y₁), d = Z₀
    (∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf (quadric N (ptY ⟨1, by omega⟩)) (ptZ ⟨0, by omega⟩)) σ).charpoly
        = (opA (sectionOf (quadric N (ptY ⟨1, by omega⟩)) (ptZ ⟨0, by omega⟩)) τ).charpoly ∧
      (completionMat (quadric N (ptY ⟨1, by omega⟩)) (ptZ ⟨0, by omega⟩) σ).charpoly
        ≠ (completionMat (quadric N (ptY ⟨1, by omega⟩)) (ptZ ⟨0, by omega⟩) τ).charpoly) ∧
    -- C6: W ∩ Z₀⊥, d = Z₁
    (∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf (perpSet (allPoints N) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩)) σ).charpoly
        = (opA (sectionOf (perpSet (allPoints N) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩)) τ).charpoly ∧
      (completionMat (perpSet (allPoints N) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) σ).charpoly
        ≠ (completionMat (perpSet (allPoints N) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) τ).charpoly) ∧
    -- C8: Q⁺ ∩ Y₀⊥, d = Z₁
    (∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf (perpSet (quadric N 0) (ptY ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩)) σ).charpoly
        = (opA (sectionOf (perpSet (quadric N 0) (ptY ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩)) τ).charpoly ∧
      (completionMat (perpSet (quadric N 0) (ptY ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) σ).charpoly
        ≠ (completionMat (perpSet (quadric N 0) (ptY ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) τ).charpoly) ∧
    -- C11: Q⁺ ∩ Z₀⊥, d = Z₁
    (∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf (perpSet (quadric N 0) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩)) σ).charpoly
        = (opA (sectionOf (perpSet (quadric N 0) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩)) τ).charpoly ∧
      (completionMat (perpSet (quadric N 0) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) σ).charpoly
        ≠ (completionMat (perpSet (quadric N 0) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) τ).charpoly) ∧
    -- C12: Q⁺ ∩ Z₀⊥, d = Y₁
    (∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf (perpSet (quadric N 0) (ptZ ⟨0, by omega⟩)) (ptY ⟨1, by omega⟩)) σ).charpoly
        = (opA (sectionOf (perpSet (quadric N 0) (ptZ ⟨0, by omega⟩)) (ptY ⟨1, by omega⟩)) τ).charpoly ∧
      (completionMat (perpSet (quadric N 0) (ptZ ⟨0, by omega⟩)) (ptY ⟨1, by omega⟩) σ).charpoly
        ≠ (completionMat (perpSet (quadric N 0) (ptZ ⟨0, by omega⟩)) (ptY ⟨1, by omega⟩) τ).charpoly) ∧
    -- C14: Q⁻(c = Y₂) ∩ Z₀⊥, d = Z₁
    (∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf (perpSet (quadric N (ptY ⟨2, by omega⟩)) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩)) σ).charpoly
        = (opA (sectionOf (perpSet (quadric N (ptY ⟨2, by omega⟩)) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩)) τ).charpoly ∧
      (completionMat (perpSet (quadric N (ptY ⟨2, by omega⟩)) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) σ).charpoly
        ≠ (completionMat (perpSet (quadric N (ptY ⟨2, by omega⟩)) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) τ).charpoly) ∧
    -- C15: Q⁻(c = Y₂) ∩ Z₀⊥, d = Y₁
    (∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf (perpSet (quadric N (ptY ⟨2, by omega⟩)) (ptZ ⟨0, by omega⟩)) (ptY ⟨1, by omega⟩)) σ).charpoly
        = (opA (sectionOf (perpSet (quadric N (ptY ⟨2, by omega⟩)) (ptZ ⟨0, by omega⟩)) (ptY ⟨1, by omega⟩)) τ).charpoly ∧
      (completionMat (perpSet (quadric N (ptY ⟨2, by omega⟩)) (ptZ ⟨0, by omega⟩)) (ptY ⟨1, by omega⟩) σ).charpoly
        ≠ (completionMat (perpSet (quadric N (ptY ⟨2, by omega⟩)) (ptZ ⟨0, by omega⟩)) (ptY ⟨1, by omega⟩) τ).charpoly) := by
  obtain ⟨g, rfl⟩ : ∃ g, N = g + 2 := ⟨N - 2, by omega⟩
  have hg : 2 ≤ g := by omega
  have hg1 : 2 ≤ g + 1 := by omega
  have hN3 : 3 ≤ g + 2 := by omega
  exact ⟨c1_strict_law_fails hg1, c3_strict_law_fails hg1, c5_strict_law_fails hg,
    c6_strict_law_fails hN3, c8_strict_law_fails hg, c11_strict_law_fails hN3,
    c12_strict_law_fails hg, c14_strict_law_fails hN, c15_strict_law_fails hg⟩

end HoggarBound.ConjectureE

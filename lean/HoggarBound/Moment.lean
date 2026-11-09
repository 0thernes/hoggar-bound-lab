/-
Hoggar Bound Lab — the analytic core.

1. `sum_cube_le`: among real numbers with prescribed sum (zero) and sum of squares, the sum of
   cubes is largest when one number stands alone and all the others coincide
   ("maximal skewness").
2. `trace_pow_eq_sum_eigenvalues_pow`: `tr (A ^ k) = ∑ λᵢ ^ k` for a Hermitian matrix.
3. `trace_cube_le`: the same extremal statement for the spectrum of a traceless Hermitian matrix.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

open Finset Matrix

namespace HoggarBound

/-- **Maximal third moment.**  Let `x₁, …, xₙ` (`n ≥ 2`) be real numbers with `∑ xᵢ = 0` and
`∑ xᵢ² = n·m`, and let `a ≥ 0` satisfy `a² = (n-1)·m`.  Then
`(n-1) · ∑ xᵢ³ ≤ n · m · (n-2) · a`.
Equality holds exactly for the "one outlier" configuration `(a, -a/(n-1), …, -a/(n-1))`. -/
theorem sum_cube_le {ι : Type*} [Fintype ι] (x : ι → ℝ) (m a : ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (h1 : ∑ i, x i = 0) (h2 : ∑ i, x i ^ 2 = Fintype.card ι * m)
    (ha : 0 ≤ a) (ha2 : a ^ 2 = ((Fintype.card ι : ℝ) - 1) * m) :
    ((Fintype.card ι : ℝ) - 1) * ∑ i, x i ^ 3
      ≤ Fintype.card ι * m * ((Fintype.card ι : ℝ) - 2) * a := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn2 : (2 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hcard
  set c : ℝ := n - 1 with hc
  have hcpos : 0 < c := by linarith
  have hnpos : 0 < n := by linarith
  -- Samuelson's inequality: no entry exceeds `a`.
  have hle : ∀ i, x i ≤ a := by
    intro i
    have hs1 : ∑ j ∈ univ.erase i, x j = - x i := by
      have := Finset.add_sum_erase univ x (mem_univ i)
      linarith
    have hs2 : ∑ j ∈ univ.erase i, x j ^ 2 = n * m - x i ^ 2 := by
      have := Finset.add_sum_erase univ (fun j => x j ^ 2) (mem_univ i)
      linarith
    have hcs := sq_sum_le_card_mul_sum_sq (s := univ.erase i) (f := x)
    rw [hs1, hs2, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ] at hcs
    have hcard' : ((Fintype.card ι - 1 : ℕ) : ℝ) = c := by
      rw [Nat.cast_sub (by omega)]; simp [hc, hn]
    rw [hcard'] at hcs
    have h3 : x i ^ 2 ≤ a ^ 2 := by
      have h4 : n * x i ^ 2 ≤ n * (c * m) := by nlinarith
      rw [ha2]
      exact le_of_mul_le_mul_left h4 hnpos
    by_contra hcon
    have hcon := not_le.1 hcon
    nlinarith [mul_pos (sub_pos.2 hcon) (lt_of_le_of_lt ha hcon)]
  -- The cubic `(x - a)(c x + a)²` is nonpositive on `(-∞, a]`.
  have key : ∀ i, (x i - a) * (c * x i + a) ^ 2 ≤ 0 := fun i =>
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hle i)) (sq_nonneg _)
  have hsum : ∑ i, (x i - a) * (c * x i + a) ^ 2 ≤ 0 := Finset.sum_nonpos (fun i _ => key i)
  have hexp : ∑ i, (x i - a) * (c * x i + a) ^ 2
      = c ^ 2 * ∑ i, x i ^ 3 + (2 * a * c - a * c ^ 2) * ∑ i, x i ^ 2
        + (a ^ 2 - 2 * a ^ 2 * c) * ∑ i, x i - n * a ^ 3 := by
    have hconst : n * a ^ 3 = ∑ _i : ι, a ^ 3 := by simp [hn]
    rw [hconst, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hexp, h1, h2] at hsum
  have ha3 : a ^ 3 = a * (c * m) := by rw [← ha2]; ring
  rw [ha3] at hsum
  have hfin : c * (c * ∑ i, x i ^ 3) ≤ c * (n * m * (n - 2) * a) := by
    have hnc : n - 2 = c - 1 := by rw [hc]; ring
    rw [hnc]
    linear_combination hsum
  exact le_of_mul_le_mul_left hfin hcpos

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Power sums of the eigenvalues of a Hermitian matrix are the traces of its powers. -/
theorem trace_pow_eq_sum_eigenvalues_pow {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) ^ k := by
  have hU := hA.spectral_theorem
  have hpow : A ^ k = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues) ^ k) := by
    conv_lhs => rw [hU]
    rw [map_pow]
  rw [hpow, Unitary.conjStarAlgAut_apply, Matrix.diagonal_pow, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp]

/-- **Third-moment bound for a traceless Hermitian matrix.**  If `A` is `d × d` Hermitian with
`tr A = 0` and `tr A² = d·m`, and `a ≥ 0` satisfies `a² = (d-1)·m`, then
`(d-1) · tr A³ ≤ d · m · (d-2) · a`. -/
theorem trace_cube_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (m a : ℝ)
    (hcard : 2 ≤ Fintype.card n) (h1 : A.trace = 0)
    (h2 : (A ^ 2).trace = (((Fintype.card n : ℝ) * m : ℝ) : ℂ))
    (ha : 0 ≤ a) (ha2 : a ^ 2 = ((Fintype.card n : ℝ) - 1) * m) :
    ((Fintype.card n : ℝ) - 1) * ((A ^ 3).trace).re
      ≤ Fintype.card n * m * ((Fintype.card n : ℝ) - 2) * a := by
  have e1 : ∑ i, hA.eigenvalues i = 0 := by
    have h := hA.trace_eq_sum_eigenvalues
    rw [h1] at h
    exact RCLike.ofReal_eq_zero.mp (by exact_mod_cast h.symm)
  have e2 : ∑ i, hA.eigenvalues i ^ 2 = (Fintype.card n : ℝ) * m := by
    have h := trace_pow_eq_sum_eigenvalues_pow hA 2
    rw [h2] at h
    exact_mod_cast h.symm
  have e3 : ((A ^ 3).trace).re = ∑ i, hA.eigenvalues i ^ 3 := by
    rw [trace_pow_eq_sum_eigenvalues_pow hA 3]
    have : (∑ i, ((hA.eigenvalues i : ℝ) : ℂ) ^ 3) = ((∑ i, hA.eigenvalues i ^ 3 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  rw [e3]
  exact sum_cube_le _ m a hcard e1 e2 ha ha2

end HoggarBound

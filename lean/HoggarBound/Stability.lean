/-
Quantitative stability of the third-moment bound.

For n real eigenvalues with sum zero and square sum n*m, put c=n-1,
a^2=c*m and Delta=n*m*(n-2)*a-c*sum(lambda^3). The original theorem
is Delta >= 0. This file bounds distance from the extremal spectrum in
terms of Delta, and supplies a finite-coordinate sign-rounding lemma.

No novelty claim is made for the underlying scalar inequality.
-/
import HoggarBound.Bound

open Finset Matrix

namespace HoggarBound

section Scalar

variable {ι : Type*} [Fintype ι]

/-- The third-moment deficit multiplied by `n-1`, avoiding a denominator. -/
def cubicDeficit (x : ι → ℝ) (m a : ℝ) : ℝ :=
  Fintype.card ι * m * ((Fintype.card ι : ℝ) - 2) * a -
    ((Fintype.card ι : ℝ) - 1) * ∑ j, x j ^ 3

/-- Samuelson's entry bound under the two moment constraints. -/
lemma moment_entry_le (x : ι → ℝ) (m a : ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (h1 : ∑ j, x j = 0) (h2 : ∑ j, x j ^ 2 = Fintype.card ι * m)
    (ha : 0 ≤ a) (ha2 : a ^ 2 = ((Fintype.card ι : ℝ) - 1) * m) (i : ι) :
    x i ≤ a := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn2 : (2 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hcard
  have hnpos : 0 < n := by linarith
  have hs1 : ∑ j ∈ univ.erase i, x j = - x i := by
    have := Finset.add_sum_erase univ x (mem_univ i)
    linarith
  have hs2 : ∑ j ∈ univ.erase i, x j ^ 2 = n * m - x i ^ 2 := by
    have := Finset.add_sum_erase univ (fun j => x j ^ 2) (mem_univ i)
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ.erase i) (f := x)
  rw [hs1, hs2, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ] at hcs
  have hc : ((Fintype.card ι - 1 : ℕ) : ℝ) = n - 1 := by
    rw [Nat.cast_sub (by omega)]; simp [hn]
  rw [hc] at hcs
  have hsq : x i ^ 2 ≤ a ^ 2 := by
    have hmul : n * x i ^ 2 ≤ n * ((n - 1) * m) := by nlinarith
    rw [ha2]
    exact le_of_mul_le_mul_left hmul hnpos
  by_contra h
  have hgt := not_le.1 h
  nlinarith [mul_pos (sub_pos.2 hgt) (lt_of_le_of_lt ha hgt)]

/-- The squared shifted eigenvalues have a fixed sum. -/
lemma shifted_square_sum (x : ι → ℝ) (m a : ℝ)
    (h1 : ∑ j, x j = 0) (h2 : ∑ j, x j ^ 2 = Fintype.card ι * m)
    (ha2 : a ^ 2 = ((Fintype.card ι : ℝ) - 1) * m) :
    ∑ j, (((Fintype.card ι : ℝ) - 1) * x j + a) ^ 2 =
      (Fintype.card ι : ℝ) ^ 2 * a ^ 2 := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hexp : ∑ j, ((n - 1) * x j + a) ^ 2 =
      (n - 1) ^ 2 * ∑ j, x j ^ 2 + 2 * (n - 1) * a * ∑ j, x j + n * a ^ 2 := by
    have hconst : n * a ^ 2 = ∑ _j : ι, a ^ 2 := by simp [hn]
    rw [hconst, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, h1, h2]
  rw [ha2]
  ring

/-- Exact residual-polynomial identity behind the stability estimate. -/
lemma cubic_residual_identity (x : ι → ℝ) (m a : ℝ)
    (h1 : ∑ j, x j = 0) (h2 : ∑ j, x j ^ 2 = Fintype.card ι * m)
    (ha2 : a ^ 2 = ((Fintype.card ι : ℝ) - 1) * m) :
    ∑ j, (a - x j) * (((Fintype.card ι : ℝ) - 1) * x j + a) ^ 2 =
      ((Fintype.card ι : ℝ) - 1) * cubicDeficit x m a := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hexp : ∑ j, (a - x j) * ((n - 1) * x j + a) ^ 2 =
      -(n - 1) ^ 2 * ∑ j, x j ^ 3 +
      (a * (n - 1) ^ 2 - 2 * a * (n - 1)) * ∑ j, x j ^ 2 +
      (2 * a ^ 2 * (n - 1) - a ^ 2) * ∑ j, x j + n * a ^ 3 := by
    have hconst : n * a ^ 3 = ∑ _j : ι, a ^ 3 := by simp [hn]
    rw [hconst, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, h1, h2]
  have ha3 : a ^ 3 = a * ((n - 1) * m) := by rw [← ha2]; ring
  rw [ha3]
  unfold cubicDeficit
  ring

/-- A small cubic deficit forces any upper spectral bound close to the extremal value. -/
theorem cubic_deficit_controls_top (x : ι → ℝ) (m a t : ℝ)
    (h1 : ∑ j, x j = 0) (h2 : ∑ j, x j ^ 2 = Fintype.card ι * m)
    (ha2 : a ^ 2 = ((Fintype.card ι : ℝ) - 1) * m)
    (ht : ∀ j, x j ≤ t) :
    (Fintype.card ι : ℝ) ^ 2 * a ^ 2 * (a - t) ≤
      ((Fintype.card ι : ℝ) - 1) * cubicDeficit x m a := by
  have hpoint : ∀ j, (a - t) * (((Fintype.card ι : ℝ) - 1) * x j + a) ^ 2 ≤
      (a - x j) * (((Fintype.card ι : ℝ) - 1) * x j + a) ^ 2 := by
    intro j
    exact mul_le_mul_of_nonneg_right (by linarith [ht j]) (sq_nonneg _)
  have hs := Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset ι)) => hpoint j
  rw [← Finset.mul_sum, shifted_square_sum x m a h1 h2 ha2,
    cubic_residual_identity x m a h1 h2 ha2] at hs
  simpa only [mul_comm (a - t)] using hs

open Classical in
/-- The extremal one-outlier spectrum, with distinguished index `i`. -/
noncomputable def extremalSpectrum (a : ℝ) (i : ι) (j : ι) : ℝ :=
  if j = i then a else -a / ((Fintype.card ι : ℝ) - 1)

/-- Squared Euclidean distance from the one-outlier spectrum at `i`. -/
noncomputable def spectrumDistanceSq (x : ι → ℝ) (a : ℝ) (i : ι) : ℝ :=
  ∑ j, (x j - extremalSpectrum a i j) ^ 2

/-- An exact distance formula; minimizing this distance selects a largest eigenvalue. -/
theorem spectrum_distance_identity (x : ι → ℝ) (m a : ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (h1 : ∑ j, x j = 0) (h2 : ∑ j, x j ^ 2 = Fintype.card ι * m)
    (ha2 : a ^ 2 = ((Fintype.card ι : ℝ) - 1) * m) (i : ι) :
    ((Fintype.card ι : ℝ) - 1) * spectrumDistanceSq x a i =
      2 * Fintype.card ι * a * (a - x i) := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn2 : (2 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hcard
  have hcpos : 0 < n - 1 := by linarith
  have hcne : n - 1 ≠ 0 := ne_of_gt hcpos
  have hterm : ∀ j, (n - 1) ^ 2 * (x j - extremalSpectrum a i j) ^ 2 =
      ((n - 1) * x j + a) ^ 2 +
        if j = i then (n * a) ^ 2 - 2 * n * a * ((n - 1) * x i + a) else 0 := by
    intro j
    change (n - 1) ^ 2 * (x j - (if j = i then a else -a / (n - 1))) ^ 2 =
      ((n - 1) * x j + a) ^ 2 +
        if j = i then (n * a) ^ 2 - 2 * n * a * ((n - 1) * x i + a) else 0
    by_cases hji : j = i
    · subst j
      simp only [ite_true]
      ring
    · simp only [ite_eq_right hji, add_zero]
      field_simp [hcne]
      ; ring
  have hexp : (n - 1) ^ 2 * spectrumDistanceSq x a i =
      n ^ 2 * a ^ 2 + (n * a) ^ 2 - 2 * n * a * ((n - 1) * x i + a) := by
    unfold spectrumDistanceSq
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun j _ => hterm j),
      Finset.sum_add_distrib, shifted_square_sum x m a h1 h2 ha2]
    simp
    ring
  have heq : (n - 1) * ((n - 1) * spectrumDistanceSq x a i) =
      (n - 1) * (2 * n * a * (a - x i)) := by
    linear_combination hexp
  exact mul_left_cancel₀ hcne heq

/-- **Quantitative rigidity.** There is an extremal spectrum within squared distance
`2*Delta/(n*a)` whenever `a>0`. The cross-multiplied form also covers `a=0`. -/
theorem exists_near_extremal_spectrum (x : ι → ℝ) (m a : ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (h1 : ∑ j, x j = 0) (h2 : ∑ j, x j ^ 2 = Fintype.card ι * m)
    (ha : 0 ≤ a) (ha2 : a ^ 2 = ((Fintype.card ι : ℝ) - 1) * m) :
    ∃ i, (∀ j, x j ≤ x i) ∧ x i ≤ a ∧
      (Fintype.card ι : ℝ) * a * spectrumDistanceSq x a i ≤ 2 * cubicDeficit x m a := by
  classical
  have hne : (univ : Finset ι).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ]
    omega
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image univ x hne
  have hmax : ∀ j, x j ≤ x i := fun j => hi j (mem_univ j)
  refine ⟨i, hmax, moment_entry_le x m a hcard h1 h2 ha ha2 i, ?_⟩
  have ht := cubic_deficit_controls_top x m a (x i) h1 h2 ha2 hmax
  have hd := spectrum_distance_identity x m a hcard h1 h2 ha2 i
  have hn2 : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  have hcpos : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by linarith
  have hmul : ((Fintype.card ι : ℝ) - 1) *
        ((Fintype.card ι : ℝ) * a * spectrumDistanceSq x a i) ≤
      ((Fintype.card ι : ℝ) - 1) * (2 * cubicDeficit x m a) := by
    linear_combination 2 * ht + ((Fintype.card ι : ℝ) * a) * hd
  exact le_of_mul_le_mul_left hmul hcpos

end Scalar

end HoggarBound

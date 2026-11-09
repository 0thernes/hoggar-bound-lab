/-
Hoggar Bound Lab — corollaries for the full space `W(2N−1, 2)` (all non-identity observables).

* `full_space_bound`    : for every `N ≥ 1`,  `#flags − 2·#violated ≤ (D−2)(D²−1)√(D+1)`.
* `full_space_fraction` : for every `N ≥ 1`,  `#violated ≥ (1/2 − √(D+1)/(D+2)) · #flags`;
                          the violated fraction tends to 1/2 as `N → ∞`.
* `three_qubit_contexts`: at least 63 of the 315 three-qubit contexts are violated (this is the
                          exact value; the bound is attained by the Hoggar sign pattern).
* `five_qubit_contexts` : at least 28786 of the 86955 five-qubit contexts are violated.
-/
import HoggarBound.Counting

open Finset Matrix

namespace HoggarBound

variable {N : ℕ}

lemma card_allPoints_cast : (((allPoints N).card : ℕ) : ℝ) = ((2 : ℝ) ^ N) ^ 2 - 1 := by
  rw [card_allPoints, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
  push_cast
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 N, pow_mul]

lemma card_flags_all_cast (hN : 1 ≤ N) :
    (((flags (allPoints N)).card : ℕ) : ℝ) = (((2 : ℝ) ^ N) ^ 2 - 1) * (((2 : ℝ) ^ N) ^ 2 - 4) / 2 := by
  have h := card_flags_all (N := N)
  have h4 : 4 ≤ 4 ^ N := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have hR : (2 : ℝ) * ((flags (allPoints N)).card : ℝ) = ((4 : ℝ) ^ N - 1) * ((4 : ℝ) ^ N - 4) := by
    have : ((2 * (flags (allPoints N)).card : ℕ) : ℝ) = (((4 ^ N - 1) * (4 ^ N - 4) : ℕ) : ℝ) := by
      rw [h]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub h4] at this
    push_cast at this
    exact this
  have h42 : (4 : ℝ) ^ N = ((2 : ℝ) ^ N) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 N, pow_mul]
  rw [h42] at hR
  linarith

/-- **Full space, all `N`.**  `#flags − 2·#violated ≤ (D − 2)(D² − 1)√(D + 1)` with `D = 2^N`. -/
theorem full_space_bound (hN : 1 ≤ N) (f : Pt N → ℝ)
    (hf : ∀ u ∈ allPoints N, f u = 1 ∨ f u = -1) :
    ((flags (allPoints N)).card : ℝ) - 2 * ((violated (allPoints N) f).card : ℝ)
      ≤ ((2 : ℝ) ^ N - 2) * (((2 : ℝ) ^ N) ^ 2 - 1) * Real.sqrt ((2 : ℝ) ^ N + 1) := by
  have h0 : (0 : Pt N) ∉ allPoints N := by simp [allPoints]
  have hb := hoggar_bound_violated hN (allPoints N) h0 f hf
  rw [card_allPoints_cast] at hb
  set D : ℝ := (2 : ℝ) ^ N with hD
  have hD2 : (2 : ℝ) ≤ D := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hsq : Real.sqrt ((D - 1) * (D ^ 2 - 1)) = (D - 1) * Real.sqrt (D + 1) := by
    have h1 : (D - 1) * (D ^ 2 - 1) = (D - 1) ^ 2 * (D + 1) := by ring
    rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  rw [hsq] at hb
  have hpos : (0 : ℝ) < D - 1 := by linarith
  have h2 : (D - 1) * (((flags (allPoints N)).card : ℝ) - 2 * ((violated (allPoints N) f).card : ℝ))
      ≤ (D - 1) * ((D - 2) * (D ^ 2 - 1) * Real.sqrt (D + 1)) := by
    linear_combination hb
  exact le_of_mul_le_mul_left h2 hpos

/-- **Macroscopic contextuality.**  For every `N ≥ 1`, every noncontextual assignment violates at
least the fraction `1/2 − √(D+1)/(D+2)` of all flags (equivalently, of all contexts), `D = 2^N`.
The fraction tends to `1/2`, the value achieved by a uniformly random assignment. -/
theorem full_space_fraction (hN : 1 ≤ N) (f : Pt N → ℝ)
    (hf : ∀ u ∈ allPoints N, f u = 1 ∨ f u = -1) :
    (1 / 2 - Real.sqrt ((2 : ℝ) ^ N + 1) / ((2 : ℝ) ^ N + 2)) * ((flags (allPoints N)).card : ℝ)
      ≤ ((violated (allPoints N) f).card : ℝ) := by
  have hb := full_space_bound hN f hf
  have hF := card_flags_all_cast hN
  set D : ℝ := (2 : ℝ) ^ N with hD
  have hD2 : (2 : ℝ) ≤ D := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hpos : (0 : ℝ) < D + 2 := by linarith
  set F : ℝ := ((flags (allPoints N)).card : ℝ) with hFdef
  set V : ℝ := ((violated (allPoints N) f).card : ℝ) with hVdef
  set s : ℝ := Real.sqrt (D + 1) with hs
  -- F · 2 / (D + 2) = (D² − 1)(D − 2)
  have hkey : (D - 2) * (D ^ 2 - 1) * s = F * (2 * s / (D + 2)) := by
    rw [hF]
    field_simp
    ring
  rw [hkey] at hb
  have : (1 / 2 - s / (D + 2)) * F = (F - F * (2 * s / (D + 2))) / 2 := by
    field_simp
  rw [this]
  linarith

/-- **Three qubits.**  At least 63 of the 315 contexts are violated by every assignment. -/
theorem three_qubit_contexts (f : Pt 3 → ℝ) (hf : ∀ u ∈ allPoints 3, f u = 1 ∨ f u = -1) :
    63 ≤ (violatedLines (allPoints 3) f).card := by
  have h0 : (0 : Pt 3) ∉ allPoints 3 := by simp [allPoints]
  have hb := hoggar_bound_violated (N := 3) (by norm_num) (allPoints 3) h0 f hf
  have hF : (flags (allPoints 3)).card = 1890 := by
    have := card_flags_all (N := 3)
    norm_num at this
    omega
  have hS : (allPoints 3).card = 63 := by
    rw [card_allPoints]; norm_num
  rw [hF, hS] at hb
  have e1 : ((2 : ℝ) ^ 3 - 1) * ((63 : ℕ) : ℝ) = 441 := by norm_num
  have e3 : ((2 : ℝ) ^ 3 - 2) * ((63 : ℕ) : ℝ) = 378 := by norm_num
  have e2 : ((2 : ℝ) ^ 3 - 1) = 7 := by norm_num
  rw [e1, e3, e2] at hb
  have hs : Real.sqrt 441 = 21 := by
    rw [show (441 : ℝ) = 21 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hF' : ((1890 : ℕ) : ℝ) = 1890 := by norm_num
  rw [hs, hF'] at hb
  have hV : (378 : ℝ) ≤ ((violated (allPoints 3) f).card : ℝ) := by linarith
  have hV' : 378 ≤ (violated (allPoints 3) f).card := by exact_mod_cast hV
  have h2 := card_violated_le (allPoints 3) h0 f
  omega

/-- **Five qubits.**  At least 28786 of the 86955 contexts are violated by every assignment. -/
theorem five_qubit_contexts (f : Pt 5 → ℝ) (hf : ∀ u ∈ allPoints 5, f u = 1 ∨ f u = -1) :
    28786 ≤ (violatedLines (allPoints 5) f).card := by
  have h0 : (0 : Pt 5) ∉ allPoints 5 := by simp [allPoints]
  have hb := hoggar_bound_violated (N := 5) (by norm_num) (allPoints 5) h0 f hf
  have hF : (flags (allPoints 5)).card = 521730 := by
    have := card_flags_all (N := 5)
    norm_num at this
    omega
  have hS : (allPoints 5).card = 1023 := by
    rw [card_allPoints]; norm_num
  rw [hF, hS] at hb
  have e1 : ((2 : ℝ) ^ 5 - 1) * ((1023 : ℕ) : ℝ) = 31713 := by norm_num
  have e3 : ((2 : ℝ) ^ 5 - 2) * ((1023 : ℕ) : ℝ) = 30690 := by norm_num
  have e2 : ((2 : ℝ) ^ 5 - 1) = 31 := by norm_num
  rw [e1, e3, e2] at hb
  have hF' : ((521730 : ℕ) : ℝ) = 521730 := by norm_num
  rw [hF'] at hb
  have hsqrt : Real.sqrt 31713 < 178.0815 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hV' : 172715 ≤ (violated (allPoints 5) f).card := by
    by_contra hlt
    have hV : ((violated (allPoints 5) f).card : ℝ) ≤ 172714 := by
      have : (violated (allPoints 5) f).card ≤ 172714 := by omega
      exact_mod_cast this
    linarith
  have h2 := card_violated_le (allPoints 5) h0 f
  omega

end HoggarBound

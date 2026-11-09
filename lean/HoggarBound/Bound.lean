/-
Hoggar Bound Lab — the main theorem.

Fix `N` qubits (`D = 2^N`), a set `S` of non-identity Pauli observables and a noncontextual
assignment `f : S → {+1, -1}`.  A *flag* is an ordered pair `(u, v)` of points of `S` whose
operators commute and whose product `u + v` again lies in `S`; every context (a "line"
`{u, v, u+v}`) gives exactly six flags.  The flag is *satisfied* when
`f u · f v · f (u+v)` equals the sign of the operator product `P_u P_v P_{u+v} = ± 1`.

`beta6 S f` = (#satisfied flags) − (#violated flags) = 6 · (#satisfied lines − #violated lines).

Main theorem (`hoggar_bound`):

    (D − 1) · beta6 S f  ≤  (D − 2) · |S| · √((D − 1) · |S|).
-/
import HoggarBound.Moment
import HoggarBound.Pauli

open Finset Matrix

namespace HoggarBound

variable {N : ℕ}

/-- Ordered pairs of commuting observables of `S` whose product is in `S`. -/
def flags (S : Finset (Pt N)) : Finset (Pt N × Pt N) :=
  (S ×ˢ S).filter fun p => p.1 + p.2 ∈ S ∧ symp p.1 p.2 = 0

/-- The sign `±1` of the context `{u, v, u+v}` (meaningful when `u` and `v` commute). -/
noncomputable def lineSign (u v : Pt N) : ℝ := (tau u v).re

/-- Six times (number of satisfied lines minus number of violated lines). -/
noncomputable def beta6 (S : Finset (Pt N)) (f : Pt N → ℝ) : ℝ :=
  ∑ p ∈ flags S, f p.1 * f p.2 * f (p.1 + p.2) * lineSign p.1 p.2

/-- The Hermitian operator `∑_{u ∈ S} f(u) P_u` attached to an assignment. -/
noncomputable def opA (S : Finset (Pt N)) (f : Pt N → ℝ) : Matrix (Vec N) (Vec N) ℂ :=
  ∑ u ∈ S, ((f u : ℝ) : ℂ) • pauli u

lemma tau_eq_lineSign {u v : Pt N} (h : symp u v = 0) : tau u v = ((lineSign u v : ℝ) : ℂ) := by
  rcases tau_eq_one_or_neg_one h with h1 | h1 <;> simp [lineSign, h1]

lemma lineSign_eq_one_or_neg_one {u v : Pt N} (h : symp u v = 0) :
    lineSign u v = 1 ∨ lineSign u v = -1 := by
  rcases tau_eq_one_or_neg_one h with h1 | h1
  · left; simp [lineSign, h1]
  · right; simp [lineSign, h1]

lemma opA_isHermitian (S : Finset (Pt N)) (f : Pt N → ℝ) : (opA S f).IsHermitian := by
  unfold Matrix.IsHermitian opA
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.conjTranspose_smul, (pauli_isHermitian u).eq]
  simp

lemma trace_opA (S : Finset (Pt N)) (f : Pt N → ℝ) (h0 : (0 : Pt N) ∉ S) :
    (opA S f).trace = 0 := by
  simp only [opA, Matrix.trace_sum, Matrix.trace_smul, trace_pauli, smul_eq_mul]
  refine Finset.sum_eq_zero fun u hu => ?_
  have hne : u ≠ 0 := fun h => h0 (h ▸ hu)
  simp [hne]

lemma trace_pauli_mul_opA (S : Finset (Pt N)) (f : Pt N → ℝ) (x : Pt N) :
    (pauli x * opA S f).trace = if x ∈ S then ((f x : ℝ) : ℂ) * (2 : ℂ) ^ N else 0 := by
  rw [opA, Finset.mul_sum, Matrix.trace_sum]
  have hterm : ∀ w ∈ S, (pauli x * (((f w : ℝ) : ℂ) • pauli w)).trace
      = if x = w then ((f w : ℝ) : ℂ) * (2 : ℂ) ^ N else 0 := by
    intro w _
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_pauli_mul, smul_eq_mul]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]

lemma trace_opA_sq (S : Finset (Pt N)) (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    (opA S f ^ 2).trace = (((2 : ℝ) ^ N * S.card : ℝ) : ℂ) := by
  rw [pow_two]
  nth_rewrite 1 [opA]
  rw [Finset.sum_mul, Matrix.trace_sum]
  have hterm : ∀ u ∈ S, ((((f u : ℝ) : ℂ) • pauli u) * opA S f).trace = (2 : ℂ) ^ N := by
    intro u hu
    rw [Matrix.smul_mul, Matrix.trace_smul, trace_pauli_mul_opA, ite_eq_left hu, smul_eq_mul]
    rcases hf u hu with h | h <;> simp [h]
  rw [Finset.sum_congr rfl hterm]
  simp
  ring

lemma opA_mul_opA (S : Finset (Pt N)) (f : Pt N → ℝ) :
    opA S f * opA S f
      = ∑ u ∈ S, ∑ v ∈ S, (((f u : ℝ) : ℂ) * ((f v : ℝ) : ℂ) * tau u v) • pauli (u + v) := by
  rw [opA, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, pauli_mul, smul_smul, smul_smul]

/-- The cubic trace counts satisfied minus violated flags. -/
theorem trace_opA_cube (S : Finset (Pt N)) (f : Pt N → ℝ) :
    (opA S f ^ 3).trace = (((2 : ℝ) ^ N * beta6 S f : ℝ) : ℂ) := by
  classical
  -- the summand attached to an ordered pair
  set G : Pt N × Pt N → ℂ := fun p =>
    ((f p.1 : ℝ) : ℂ) * ((f p.2 : ℝ) : ℂ) * ((f (p.1 + p.2) : ℝ) : ℂ) * tau p.1 p.2 with hG
  -- Step 1: expand the triple product.
  have step1 : (opA S f ^ 3).trace
      = (2 : ℂ) ^ N * ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 ∈ S), G p := by
    rw [pow_succ, pow_two, opA_mul_opA, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum,
      Finset.sum_filter, Finset.sum_product, Finset.sum_congr rfl]
    intro u _
    rw [Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, trace_pauli_mul_opA, smul_eq_mul]
    by_cases hmem : u + v ∈ S
    · simp only [hmem, ↓reduceIte, hG]
      ring
    · simp [hmem]
  -- Step 2: anticommuting pairs cancel in pairs under the swap.
  have step2 : ∑ p ∈ ((S ×ˢ S).filter (fun p => p.1 + p.2 ∈ S)).filter
      (fun p => ¬ symp p.1 p.2 = 0), G p = 0 := by
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      have hs : symp p.1 p.2 = 1 :=
        (zmod2_cases _).resolve_left (Finset.mem_filter.1 hp).2
      simp only [hG]
      rw [tau_swap p.1 p.2, hs, eps_one, add_comm p.2 p.1]
      ring
    · intro p hp _ hfix
      have hs : ¬ symp p.1 p.2 = 0 := (Finset.mem_filter.1 hp).2
      have h12 : p.2 = p.1 := congrArg Prod.fst hfix
      apply hs
      rw [h12]
      simp only [symp]
      exact zmod2_add_self _
    · intro p hp
      rcases Finset.mem_filter.1 hp with ⟨hp1, hs⟩
      rcases Finset.mem_filter.1 hp1 with ⟨hp2, hsum⟩
      rcases Finset.mem_product.1 hp2 with ⟨h1, h2⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h2, h1⟩, ?_⟩, ?_⟩
      · simpa [add_comm] using hsum
      · simpa [symp_comm] using hs
    · intro p _
      rfl
  -- Step 3: on commuting pairs the summand is real.
  have step3 : ∑ p ∈ ((S ×ˢ S).filter (fun p => p.1 + p.2 ∈ S)).filter
      (fun p => symp p.1 p.2 = 0), G p = ((beta6 S f : ℝ) : ℂ) := by
    have hfl : ((S ×ˢ S).filter (fun p => p.1 + p.2 ∈ S)).filter (fun p => symp p.1 p.2 = 0)
        = flags S := by
      simp only [flags, Finset.filter_filter]
    rw [hfl, beta6, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hs : symp p.1 p.2 = 0 := (Finset.mem_filter.1 hp).2.2
    simp only [hG]
    rw [tau_eq_lineSign hs]
    push_cast
    ring
  rw [step1, ← Finset.sum_filter_add_sum_filter_not _ (fun p : Pt N × Pt N => symp p.1 p.2 = 0),
    step2, step3, add_zero]
  push_cast
  ring

lemma card_vec : Fintype.card (Vec N) = 2 ^ N := by
  simp [ZMod.card]

/-- **The Hoggar bound** (third-moment bound), complex case.

For `N ≥ 1` qubits (`D = 2^N`), every set `S` of non-identity Pauli observables and every
`±1` assignment `f`:

    (D − 1) · β₆(f)  ≤  (D − 2) · |S| · √((D − 1) · |S|),

where `β₆(f) = 6 · (#satisfied lines − #violated lines)`. -/
theorem hoggar_bound (hN : 1 ≤ N) (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S) (f : Pt N → ℝ)
    (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ N - 1) * beta6 S f
      ≤ ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card) := by
  have hD : (2 : ℝ) ≤ (2 : ℝ) ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hcardR : ((Fintype.card (Vec N) : ℕ) : ℝ) = (2 : ℝ) ^ N := by
    rw [card_vec]; push_cast; rfl
  have hcard2 : 2 ≤ Fintype.card (Vec N) := by
    rw [card_vec]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have hnonneg : 0 ≤ ((2 : ℝ) ^ N - 1) * S.card :=
    mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have key := trace_cube_le (opA_isHermitian S f) (S.card : ℝ)
    (Real.sqrt (((2 : ℝ) ^ N - 1) * S.card)) hcard2 (trace_opA S f h0)
    (by rw [trace_opA_sq S f hf, hcardR]) (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt hnonneg, hcardR])
  rw [trace_opA_cube, Complex.ofReal_re, hcardR] at key
  have hDpos : (0 : ℝ) < (2 : ℝ) ^ N := by linarith
  have h2 : (2 : ℝ) ^ N * (((2 : ℝ) ^ N - 1) * beta6 S f)
      ≤ (2 : ℝ) ^ N * (((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card)) := by
    linear_combination key
  exact le_of_mul_le_mul_left h2 hDpos

end HoggarBound

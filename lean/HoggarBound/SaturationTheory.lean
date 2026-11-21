/-
Hoggar Bound Lab — Theorems 3 and 4 (Exact saturation criterion and Pauli-flat states).

This module formalizes Theorems 3 and 4 of the unified paper for arbitrary nonempty subsets `S`
of non-identity `N`-qubit Pauli observables (`N ≥ 1`), closing the formalization gap listed in
Sections 9.1 and 12 of the paper.

Main results:
* `sum_cube_eq_iff`          : exact equality case of Okumura's lemma (`sum_cube_le`).
* `matrix_eq_sum_pauli`      : Pauli expansion `2^N • M = ∑ u, tr (M * P_u) • P_u`.
* `opA_sq_eq`                : Theorem 4 identity
                               `A² = |S|·I + 2 ∑_{w ∈ S} e_w f(w) P_w + 2 ∑_{w ∉ S, w ≠ 0} b_w P_w`.
* `saturation_tfae`          : for nonempty `S` (`0 ∉ S`) and `f : S → {±1}`, the five conditions
                               (a) `hoggar_bound` holds with equality,
                               (b) `A` has simple top eigenvalue `a = √((D-1)|S|)` and `(D-1)` copies
                                   of `-a/(D-1)`,
                               (b') `A² = |S|·I + ((D-2)a/(D-1))·A`,
                               (c) Theorem 3: some unit vector `ψ` is Pauli-flat on `S` with signs `f`,
                               (d) Theorem 4: constant excess `e_w = (D-2)√|S|/(2√(D-1))` on `S` and
                                   vanishing outside sums `b_w = 0` outside `S`,
                               are all equivalent.
* `saturation_mul_isSquare`  : for `N ≥ 2`, saturation forces `(2^N - 1) * |S|` to be a perfect square.
-/
import HoggarBound.Stability
import HoggarBound.Counting

open Finset Matrix

namespace HoggarBound

/-! ### Part 1. Equality case of Okumura's lemma -/

/-- Exact equality characterization for `sum_cube_le` when `m > 0`. -/
theorem sum_cube_eq_iff {ι : Type*} [Fintype ι] (x : ι → ℝ) (m a : ℝ)
    (hcard : 2 ≤ Fintype.card ι) (hm : 0 < m)
    (h1 : ∑ i, x i = 0) (h2 : ∑ i, x i ^ 2 = Fintype.card ι * m)
    (ha : 0 ≤ a) (ha2 : a ^ 2 = ((Fintype.card ι : ℝ) - 1) * m) :
    ((Fintype.card ι : ℝ) - 1) * ∑ i, x i ^ 3 = Fintype.card ι * m * ((Fintype.card ι : ℝ) - 2) * a
      ↔ ∃ i₀ : ι, x i₀ = a ∧ ∀ i ≠ i₀, x i = -a / ((Fintype.card ι : ℝ) - 1) := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn2 : (2 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hcard
  have hcpos : 0 < n - 1 := by linarith
  have hnpos : 0 < n := by linarith
  have hapos : 0 < a := by
    have ha2pos : 0 < a ^ 2 := by rw [ha2]; exact mul_pos hcpos hm
    exact lt_of_le_of_ne ha (fun h => by rw [← h] at ha2pos; norm_num at ha2pos)
  constructor
  · intro heq
    have hdef : cubicDeficit x m a = 0 := by
      unfold cubicDeficit; linarith
    have hres := cubic_residual_identity x m a h1 h2 ha2
    rw [hdef, mul_zero] at hres
    have hnonneg : ∀ j ∈ (univ : Finset ι), 0 ≤ (a - x j) * ((n - 1) * x j + a) ^ 2 := by
      intro j _
      have hle := moment_entry_le x m a hcard h1 h2 ha ha2 j
      exact mul_nonneg (by linarith) (sq_nonneg _)
    have hall : ∀ j : ι, (a - x j) * ((n - 1) * x j + a) ^ 2 = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hres j (mem_univ j)
    have htwo : ∀ j : ι, x j = a ∨ x j = -a / (n - 1) := by
      intro j
      rcases mul_eq_zero.mp (hall j) with h | h
      · left; linarith
      · right
        have h0 : (n - 1) * x j + a = 0 := sq_eq_zero_iff.mp h
        field_simp [ne_of_gt hcpos]
        linarith
    set T : Finset ι := univ.filter fun j => x j = a
    have hsumT : ∑ j : ι, x j = (T.card : ℝ) * a + ((Fintype.card ι - T.card : ℕ) : ℝ) * (-a / (n - 1)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := univ) (p := fun j => x j = a)]
      have h1' : ∑ j ∈ T, x j = (T.card : ℝ) * a := by
        rw [Finset.sum_congr rfl (fun j hj => (Finset.mem_filter.mp hj).2), Finset.sum_const, nsmul_eq_mul]
      have h2' : ∑ j ∈ univ.filter (fun j => ¬ x j = a), x j
          = ((univ.filter (fun j => ¬ x j = a)).card : ℝ) * (-a / (n - 1)) := by
        have hval : ∀ j ∈ univ.filter (fun j => ¬ x j = a), x j = -a / (n - 1) := by
          intro j hj
          exact (htwo j).resolve_left (Finset.mem_filter.mp hj).2
        rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
      have hcard_not : (univ.filter (fun j => ¬ x j = a)).card = Fintype.card ι - T.card := by
        have hs := Finset.card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun j => x j = a)
        rw [Finset.card_univ] at hs
        change T.card + (univ.filter (fun j => ¬ x j = a)).card = Fintype.card ι at hs
        omega
      rw [h1', h2', hcard_not]
    have hTle : T.card ≤ Fintype.card ι := by
      simpa using Finset.card_le_univ T
    have hcast_sub : ((Fintype.card ι - T.card : ℕ) : ℝ) = n - (T.card : ℝ) := by
      rw [Nat.cast_sub hTle, hn]
    rw [h1, hcast_sub] at hsumT
    have hTcardR : (T.card : ℝ) = 1 := by
      have hmul : (n - 1) * ((T.card : ℝ) * a + (n - (T.card : ℝ)) * (-a / (n - 1))) = 0 := by
        rw [← hsumT, mul_zero]
      have hmul' : n * a * ((T.card : ℝ) - 1) = 0 := by
        have hcne : n - 1 ≠ 0 := ne_of_gt hcpos
        field_simp [hcne] at hmul
        linarith
      have hna : n * a ≠ 0 := mul_ne_zero (ne_of_gt hnpos) (ne_of_gt hapos)
      linarith [(mul_eq_zero.mp hmul').resolve_left hna]
    have hTcard : T.card = 1 := by exact_mod_cast hTcardR
    obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hTcard
    have hi₀_mem : i₀ ∈ T := by rw [hi₀]; exact Finset.mem_singleton_self i₀
    refine ⟨i₀, (Finset.mem_filter.mp hi₀_mem).2, fun i hne => ?_⟩
    apply (htwo i).resolve_left
    intro hxa
    have hiT : i ∈ T := Finset.mem_filter.mpr ⟨mem_univ _, hxa⟩
    rw [hi₀, Finset.mem_singleton] at hiT
    exact hne hiT
  · rintro ⟨i₀, hi₀, hother⟩
    have hsum3 : ∑ i : ι, x i ^ 3 = a ^ 3 + (n - 1) * (-a / (n - 1)) ^ 3 := by
      rw [← Finset.add_sum_erase univ (fun i => x i ^ 3) (mem_univ i₀), hi₀]
      have hterm : ∀ i ∈ univ.erase i₀, x i ^ 3 = (-a / (n - 1)) ^ 3 := by
        intro i hi
        rw [hother i (Finset.ne_of_mem_erase hi)]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
        Finset.card_erase_of_mem (mem_univ i₀), Finset.card_univ]
      have hc : ((Fintype.card ι - 1 : ℕ) : ℝ) = n - 1 := by
        rw [Nat.cast_sub (by omega), hn]; simp
      rw [hc]
    rw [hsum3]
    have hcne : n - 1 ≠ 0 := ne_of_gt hcpos
    have ha3 : a ^ 3 = a * ((n - 1) * m) := by rw [← ha2]; ring
    field_simp [hcne]
    nlinarith [ha2]

/-! ### Part 2. Pauli completeness identity -/

section PauliBasis

variable {N : ℕ}

/-- Every `2^N × 2^N` complex matrix is a linear combination of the `4^N` Pauli matrices,
with coefficients `tr (M * P_u) / 2^N`. -/
theorem matrix_eq_sum_pauli (M : Matrix (Vec N) (Vec N) ℂ) :
    ((2 : ℂ) ^ N) • M = ∑ u : Pt N, (M * pauli u).trace • pauli u := by
  ext x y
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, pauli]
  -- Pull out `I^{2·ycount u} = chi u.2 u.1`.
  have hterm : ∀ u : Pt N,
      (∑ r : Vec N, ∑ s : Vec N, M r s * ((Complex.I ^ ycount u) * weyl u s r)) *
        ((Complex.I ^ ycount u) * weyl u x y)
      = ∑ r : Vec N, ∑ s : Vec N, M r s * (chi u.2 u.1 * weyl u s r * weyl u x y) := by
    intro u
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hI2 : Complex.I ^ ycount u * Complex.I ^ ycount u = chi u.2 u.1 := by
      rw [← mul_pow, Complex.I_mul_I, chi_self]
    linear_combination M r s * weyl u s r * weyl u x y * hI2
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hswap : ∀ r : Vec N,
      (∑ u : Pt N, ∑ s : Vec N, M r s * (chi u.2 u.1 * weyl u s r * weyl u x y))
      = ∑ s : Vec N, M r s * ∑ u : Pt N, chi u.2 u.1 * weyl u s r * weyl u x y := by
    intro r
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
  simp_rw [hswap]
  have hkernel : ∀ r s : Vec N,
      ∑ u : Pt N, chi u.2 u.1 * weyl u s r * weyl u x y
        = if r = x ∧ s = y then (2 : ℂ) ^ N else 0 := by
    intro r s
    rw [Fintype.sum_prod_type]
    -- Only `a = x + y` contributes because `weyl (a, c) x y` requires `x = y + a`.
    rw [Finset.sum_eq_single (x + y)]
    · by_cases hs : s = r + (x + y)
      · have hterm_c : ∀ c : Vec N,
            chi c (x + y) * weyl (x + y, c) s r * weyl (x + y, c) x y = chi (x + r) c := by
          intro c
          have hx : x = y + (x + y) := by
            calc x = x + (y + y) := by rw [vec_add_self, add_zero]
              _ = y + (x + y) := by abel
          unfold weyl
          rw [ite_eq_left hs, ite_eq_left hx]
          rw [← chi_add_right, ← chi_add_right]
          have harg : x + y + r + y = x + r := by
            calc x + y + r + y = x + r + (y + y) := by abel
              _ = x + r := by rw [vec_add_self, add_zero]
          rw [harg]
          unfold chi
          rw [dotProduct_comm]
        simp_rw [hterm_c, sum_chi]
        by_cases hrx : r = x
        · subst hrx
          have hs' : s = y := by
            calc s = r + (r + y) := hs
              _ = (r + r) + y := by abel
              _ = y := by rw [vec_add_self, zero_add]
          simp [vec_add_self, hs']
        · have hxr : x + r ≠ 0 := by
            intro h0
            apply hrx
            calc r = (x + x) + r := by rw [vec_add_self, zero_add]
              _ = x + (x + r) := by abel
              _ = x + 0 := by rw [h0]
              _ = x := add_zero x
          simp [hxr, hrx]
      · have h0 : ∀ c : Vec N, chi c (x + y) * weyl (x + y, c) s r * weyl (x + y, c) x y = 0 := by
          intro c
          simp [weyl, hs]
        simp_rw [h0, Finset.sum_const_zero]
        have hnot : ¬ (r = x ∧ s = y) := by
          rintro ⟨rfl, rfl⟩
          apply hs
          calc s = (r + r) + s := by rw [vec_add_self, zero_add]
            _ = r + (r + s) := by abel
        simp [hnot]
    · intro a _ ha
      refine Finset.sum_eq_zero fun c _ => ?_
      have hne : x ≠ y + a := by
        intro hx
        apply ha
        calc a = (y + y) + a := by rw [vec_add_self, zero_add]
          _ = (y + a) + y := by abel
          _ = x + y := by rw [← hx]
      simp [weyl, hne]
    · intro h; exact absurd (mem_univ _) h
  simp_rw [hkernel]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · simp [mul_comm]
    · intro s _ hsy; simp [hsy]
    · intro h; exact absurd (mem_univ _) h
  · intro r _ hrx
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [hrx]
  · intro h; exact absurd (mem_univ _) h

/-- Two matrices with identical Pauli traces are equal. -/
lemma eq_of_trace_pauli_eq {M₁ M₂ : Matrix (Vec N) (Vec N) ℂ}
    (h : ∀ u : Pt N, (M₁ * pauli u).trace = (M₂ * pauli u).trace) : M₁ = M₂ := by
  have h1 : ((2 : ℂ) ^ N) • M₁ = ((2 : ℂ) ^ N) • M₂ := by
    rw [matrix_eq_sum_pauli M₁, matrix_eq_sum_pauli M₂]
    exact Finset.sum_congr rfl fun u _ => by rw [h u]
  have hne : ((2 : ℂ) ^ N) ≠ 0 := pow_ne_zero N (by norm_num)
  exact smul_right_injective _ hne h1

end PauliBasis

/-! ### Part 3. Theorem 4 Pauli expansion of `A²` -/

section SquareIdentity

variable {N : ℕ}

/-- Excess at `w ∈ S`: satisfied minus violated contexts of `S` through `w`.
(Each unordered commuting pair `{u, u + w}` appears twice in the ordered sum over `u`.) -/
noncomputable def excess (S : Finset (Pt N)) (f : Pt N → ℝ) (w : Pt N) : ℝ :=
  (∑ u ∈ S.filter fun u => u + w ∈ S ∧ symp u w = 0,
    f u * f (u + w) * f w * lineSign u w) / 2

/-- Outside sum at `w ∉ S, w ≠ 0`: `∑ s(u, v) f(u) f(v)` over unordered commuting pairs
`{u, v} ⊆ S` with `u + v = w`. -/
noncomputable def outsideSum (S : Finset (Pt N)) (f : Pt N → ℝ) (w : Pt N) : ℝ :=
  (∑ u ∈ S.filter fun u => u + w ∈ S ∧ symp u w = 0,
    f u * f (u + w) * lineSign u w) / 2

lemma tau_add_right {u w : Pt N} (hs : symp u w = 0) : tau u (u + w) = tau u w := by
  have h1 : pauli u * pauli (u + w) = tau u (u + w) • pauli w := by
    rw [pauli_mul]
    have : u + (u + w) = w := by rw [← add_assoc, pt_add_self, zero_add]
    rw [this]
  have h2 : pauli u * pauli (u + w) = tau u w • pauli w := by
    have hmul : pauli (u + w) = (tau u w)⁻¹ • (pauli u * pauli w) := by
      rw [pauli_mul, smul_smul, inv_mul_cancel₀, one_smul]
      rcases tau_eq_one_or_neg_one hs with h | h <;> simp [h]
    rw [hmul, Matrix.mul_smul, ← Matrix.mul_assoc, pauli_mul_self, one_mul]
    congr 1
    rcases tau_eq_one_or_neg_one hs with h | h <;> simp [h]
  have h3 : tau u (u + w) • pauli w = tau u w • pauli w := h1.symm.trans h2
  have htr : (tau u (u + w) • pauli w * pauli w).trace = (tau u w • pauli w * pauli w).trace := by
    rw [h3]
  rw [Matrix.smul_mul, Matrix.smul_mul, pauli_mul_self, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, card_vec, smul_eq_mul, smul_eq_mul] at htr
  have hne : ((2 ^ N : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero N (by norm_num : (2 : ℕ) ≠ 0))
  exact mul_right_cancel₀ hne htr

/-- Trace of `A² * P_w` for any `w ≠ 0` (the Pauli coefficient of `A²`). -/
lemma trace_opA_sq_mul_pauli (S : Finset (Pt N)) (f : Pt N → ℝ) {w : Pt N} (hw : w ≠ 0) :
    (opA S f ^ 2 * pauli w).trace
      = (2 : ℂ) ^ N * ((2 * outsideSum S f w : ℝ) : ℂ) := by
  classical
  set g : Pt N → ℂ := fun u => ((f u : ℝ) : ℂ) * ((f (u + w) : ℝ) : ℂ) * tau u (u + w) with hg
  have step1 : (opA S f ^ 2 * pauli w).trace
      = (2 : ℂ) ^ N * ∑ u ∈ S.filter (fun u => u + w ∈ S), g u := by
    rw [pow_two, opA_mul_opA, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.sum_mul, Matrix.trace_sum]
    have hinner : ∀ v ∈ S,
        ((((f u : ℝ) : ℂ) * ((f v : ℝ) : ℂ) * tau u v) • pauli (u + v) * pauli w).trace
          = if v = u + w then (2 : ℂ) ^ N * g u else 0 := by
      intro v _
      rw [Matrix.smul_mul, Matrix.trace_smul, trace_pauli_mul, smul_eq_mul]
      have hiff : u + v = w ↔ v = u + w := by
        constructor
        · intro h
          calc v = (u + u) + v := by rw [pt_add_self, zero_add]
            _ = u + (u + v) := by abel
            _ = u + w := by rw [h]
        · intro h
          rw [h, ← add_assoc, pt_add_self, zero_add]
      by_cases hv : v = u + w
      · rw [ite_eq_left (hiff.mpr hv), ite_eq_left hv, hv, hg]; ring
      · rw [ite_eq_right (fun h => hv (hiff.mp h)), ite_eq_right hv, mul_zero]
    rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
  -- Anticommuting terms (`symp u w = 1`) cancel under `u ↦ u + w`.
  have step2 : ∑ u ∈ (S.filter fun u => u + w ∈ S).filter (fun u => ¬ symp u w = 0), g u = 0 := by
    refine Finset.sum_involution (fun u _ => u + w) ?_ ?_ ?_ ?_
    · intro u hu
      have hs : symp u w = 1 := (zmod2_cases _).resolve_left (Finset.mem_filter.mp hu).2
      have hsu : symp u (u + w) = 1 := by rw [symp_add_right, symp_self, zero_add, hs]
      have hadd : u + w + w = u := by rw [add_assoc, pt_add_self, add_zero]
      simp only [hg, hadd]
      rw [tau_swap u (u + w), hsu, eps_one]
      ring
    · intro u _ _ hfix
      apply hw
      have h1 : u + w = u := hfix
      calc w = (u + u) + w := by rw [pt_add_self, zero_add]
        _ = u + (u + w) := by abel
        _ = u + u := by rw [h1]
        _ = 0 := pt_add_self u
    · intro u hu
      obtain ⟨hu1, hs⟩ := Finset.mem_filter.mp hu
      obtain ⟨huS, huwS⟩ := Finset.mem_filter.mp hu1
      have hadd : u + w + w = u := by rw [add_assoc, pt_add_self, add_zero]
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨huwS, by rwa [hadd]⟩, ?_⟩
      rwa [symp_comm (u + w) w, symp_add_right, symp_self, add_zero, symp_comm]
    · intro u _
      rw [add_assoc, pt_add_self, add_zero]
  have step3 : ∑ u ∈ (S.filter fun u => u + w ∈ S).filter (fun u => symp u w = 0), g u
      = ((2 * outsideSum S f w : ℝ) : ℂ) := by
    have hfl : (S.filter fun u => u + w ∈ S).filter (fun u => symp u w = 0)
        = S.filter fun u => u + w ∈ S ∧ symp u w = 0 := by
      rw [Finset.filter_filter]
    rw [hfl, outsideSum, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hs : symp u w = 0 := (Finset.mem_filter.mp hu).2.2
    simp only [hg, tau_add_right hs, tau_eq_lineSign hs]
    push_cast
    ring
  rw [step1, ← Finset.sum_filter_add_sum_filter_not _ (fun u : Pt N => symp u w = 0),
    step2, step3, add_zero]

lemma outsideSum_eq_excess_mul {S : Finset (Pt N)} {f : Pt N → ℝ}
    (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) {w : Pt N} (hw : w ∈ S) :
    outsideSum S f w = excess S f w * f w := by
  unfold outsideSum excess
  rw [div_mul_eq_mul_div]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rcases hf w hw with h | h <;> rw [h] <;> ring

/-- **Theorem 4 (Pauli expansion of `A²`).**
For any `S` (`0 ∉ S`) and `f : S → {±1}`:
`A² = |S|·1 + ∑_{w ∈ S} (2 e_w f(w)) P_w + ∑_{w ∉ S, w ≠ 0} (2 b_w) P_w`. -/
theorem opA_sq_eq (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S) (f : Pt N → ℝ)
    (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    opA S f ^ 2
      = (S.card : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ)
        + ∑ w ∈ S, (((2 * excess S f w * f w : ℝ) : ℂ)) • pauli w
        + ∑ w ∈ (univ.erase (0 : Pt N)) \ S, (((2 * outsideSum S f w : ℝ) : ℂ)) • pauli w := by
  apply eq_of_trace_pauli_eq
  intro u
  have htr_rhs :
      (((S.card : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ)
          + ∑ w ∈ S, (((2 * excess S f w * f w : ℝ) : ℂ)) • pauli w
          + ∑ w ∈ (univ.erase (0 : Pt N)) \ S, (((2 * outsideSum S f w : ℝ) : ℂ)) • pauli w)
        * pauli u).trace
      = (if u = 0 then (S.card : ℂ) * (2 : ℂ) ^ N
         else if u ∈ S then ((2 * excess S f u * f u : ℝ) : ℂ) * (2 : ℂ) ^ N
         else ((2 * outsideSum S f u : ℝ) : ℂ) * (2 : ℂ) ^ N) := by
    simp only [add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul, one_mul,
      trace_pauli, Finset.sum_mul, Matrix.trace_sum, trace_pauli_mul, smul_eq_mul]
    have hs1 : ∑ w ∈ S, ((2 * excess S f w * f w : ℝ) : ℂ) * (if w = u then (2 : ℂ) ^ N else 0)
        = if u ∈ S then ((2 * excess S f u * f u : ℝ) : ℂ) * (2 : ℂ) ^ N else 0 := by
      have : ∀ w ∈ S, ((2 * excess S f w * f w : ℝ) : ℂ) * (if w = u then (2 : ℂ) ^ N else 0)
          = if u = w then ((2 * excess S f w * f w : ℝ) : ℂ) * (2 : ℂ) ^ N else 0 := by
        intro w _
        by_cases h : w = u
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    have hs2 : ∑ w ∈ (univ.erase (0 : Pt N)) \ S,
          ((2 * outsideSum S f w : ℝ) : ℂ) * (if w = u then (2 : ℂ) ^ N else 0)
        = if u ∈ (univ.erase (0 : Pt N)) \ S
          then ((2 * outsideSum S f u : ℝ) : ℂ) * (2 : ℂ) ^ N else 0 := by
      have : ∀ w ∈ (univ.erase (0 : Pt N)) \ S,
            ((2 * outsideSum S f w : ℝ) : ℂ) * (if w = u then (2 : ℂ) ^ N else 0)
          = if u = w then ((2 * outsideSum S f w : ℝ) : ℂ) * (2 : ℂ) ^ N else 0 := by
        intro w _
        by_cases h : w = u
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    rw [hs1, hs2]
    by_cases hu0 : u = 0
    · subst hu0; simp [h0]
    · by_cases huS : u ∈ S
      · simp [hu0, huS]
      · simp [hu0, huS]
  rw [htr_rhs]
  by_cases hu0 : u = 0
  · subst hu0
    rw [pauli_zero, mul_one, trace_opA_sq S f hf, ite_eq_left rfl]
    push_cast; ring
  · rw [ite_eq_right hu0, trace_opA_sq_mul_pauli S f hu0]
    by_cases huS : u ∈ S
    · rw [ite_eq_left huS, outsideSum_eq_excess_mul hf huS]
      push_cast; ring
    · rw [ite_eq_right huS]
      ring

end SquareIdentity

/-! ### Part 4. Theorems 3 and 4: five-way saturation equivalence and integrality -/

section SaturationEquivalences

variable {N : ℕ}

/-- A pure state `ψ : Vec N → ℂ` (unit vector) is flat on `S` with signs `f` if
`⟨ψ | P_v | ψ⟩ = f(v) √((D-1)/|S|)` on `S` and `0` on non-identity observables outside `S`. -/
def IsFlatState (S : Finset (Pt N)) (f : Pt N → ℝ) (ψ : Vec N → ℂ) : Prop :=
  (∑ x : Vec N, Complex.normSq (ψ x) = 1) ∧
  (∀ v ∈ S, ((star ψ) ⬝ᵥ (pauli v *ᵥ ψ))
      = ((f v * Real.sqrt (((2 : ℝ) ^ N - 1) / (S.card : ℝ)) : ℝ) : ℂ)) ∧
  (∀ v : Pt N, v ≠ 0 → v ∉ S → ((star ψ) ⬝ᵥ (pauli v *ᵥ ψ)) = 0)

/-- The rank-one projector `|ψ⟩⟨ψ|` as a matrix. -/
def projMat (ψ : Vec N → ℂ) : Matrix (Vec N) (Vec N) ℂ :=
  fun x y => ψ x * star (ψ y)

lemma trace_projMat_mul (ψ : Vec N → ℂ) (M : Matrix (Vec N) (Vec N) ℂ) :
    (projMat ψ * M).trace = (star ψ) ⬝ᵥ (M *ᵥ ψ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, projMat, dotProduct, mulVec,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun x _ => by ring

lemma projMat_sq {ψ : Vec N → ℂ} (hψ : ∑ x : Vec N, Complex.normSq (ψ x) = 1) :
    projMat ψ * projMat ψ = projMat ψ := by
  ext x y
  simp only [Matrix.mul_apply, projMat]
  have hfac : (∑ z : Vec N, ψ x * star (ψ z) * (ψ z * star (ψ y)))
      = (ψ x * star (ψ y)) * ∑ z : Vec N, (star (ψ z) * ψ z) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => by ring
  rw [hfac]
  have hnorm : ∑ z : Vec N, star (ψ z) * ψ z = 1 := by
    have hterm : ∀ z : Vec N, star (ψ z) * ψ z = (Complex.normSq (ψ z) : ℂ) := by
      intro z
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
    simp_rw [hterm, ← Complex.ofReal_sum, hψ, Complex.ofReal_one]
  rw [hnorm, mul_one]

/-- **Theorems 3 & 4 (Complete saturation equivalence).**
For `N ≥ 1`, any nonempty set `S` of non-identity Pauli observables, and `f : S → {±1}`,
with `D = 2^N` and `a = √((D - 1) |S|)`, the following five conditions are equivalent:
1. `(D - 1) · β₆(S, f) = (D - 2) · |S| · a` (exact saturation of `hoggar_bound`),
2. `opA S f` has simple top eigenvalue `a` and `D - 1` copies of `-a / (D - 1)`,
3. `(opA S f)² = |S| · I + ((D - 2) a / (D - 1)) · opA S f`,
4. There exists a pure state `ψ` flat on `S` with signs `f` (Theorem 3),
5. `2 e_w(f) = (D - 2) a / (D - 1)` for every `w ∈ S` and `b_w(f) = 0` for every `w ∉ S, w ≠ 0`
   (Theorem 4(d)). -/
theorem saturation_tfae (hN : 1 ≤ N) (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S)
    (hne : S.Nonempty) (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    let D : ℝ := (2 : ℝ) ^ N
    let a : ℝ := Real.sqrt ((D - 1) * S.card)
    let hA := opA_isHermitian S f
    List.TFAE [
      (D - 1) * beta6 S f = (D - 2) * S.card * a,
      ∃ i₀ : Vec N, hA.eigenvalues i₀ = a ∧ ∀ i ≠ i₀, hA.eigenvalues i = -a / (D - 1),
      opA S f ^ 2 = (S.card : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ)
        + (((D - 2) * a / (D - 1) : ℝ) : ℂ) • opA S f,
      ∃ ψ : Vec N → ℂ, IsFlatState S f ψ,
      (∀ w ∈ S, 2 * excess S f w = (D - 2) * a / (D - 1)) ∧
        (∀ w : Pt N, w ≠ 0 → w ∉ S → outsideSum S f w = 0)
    ] := by
  intro D a hA
  have hD2 : (2 : ℝ) ≤ D := by
    dsimp [D]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hDpos : (0 : ℝ) < D := by linarith
  have hDm1 : (0 : ℝ) < D - 1 := by linarith
  have hSpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hnonneg : 0 ≤ (D - 1) * (S.card : ℝ) := mul_nonneg (le_of_lt hDm1) (le_of_lt hSpos)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = (D - 1) * S.card := Real.sq_sqrt hnonneg
  have hapos : 0 < a := Real.sqrt_pos.mpr (mul_pos hDm1 hSpos)
  have hcard2 : 2 ≤ Fintype.card (Vec N) := by
    rw [card_vec]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have hcardR : (Fintype.card (Vec N) : ℝ) = D := by rw [card_vec]; push_cast; rfl
  have he1 : ∑ i : Vec N, hA.eigenvalues i = 0 := by
    have h := hA.trace_eq_sum_eigenvalues
    rw [trace_opA S f h0] at h
    exact RCLike.ofReal_eq_zero.mp (by exact_mod_cast h.symm)
  have he2 : ∑ i : Vec N, hA.eigenvalues i ^ 2 = D * S.card := by
    have h := trace_pow_eq_sum_eigenvalues_pow hA 2
    rw [trace_opA_sq S f hf] at h
    have hR : ((∑ i : Vec N, hA.eigenvalues i ^ 2 : ℝ) : ℂ) = ((D * S.card : ℝ) : ℂ) := by
      dsimp [D]
      simpa using h.symm
    exact Complex.ofReal_injective hR
  have he3 : ((opA S f ^ 3).trace).re = ∑ i : Vec N, hA.eigenvalues i ^ 3 := by
    rw [trace_pow_eq_sum_eigenvalues_pow hA 3]
    have : (∑ i, ((hA.eigenvalues i : ℝ) : ℂ) ^ 3) = ((∑ i, hA.eigenvalues i ^ 3 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  -- (1) → (2)
  have h12 : (D - 1) * beta6 S f = (D - 2) * S.card * a →
      ∃ i₀ : Vec N, hA.eigenvalues i₀ = a ∧ ∀ i ≠ i₀, hA.eigenvalues i = -a / (D - 1) := by
    intro hsat
    have hsum : (D - 1) * ∑ i, hA.eigenvalues i ^ 3 = D * S.card * (D - 2) * a := by
      rw [← he3, trace_opA_cube, Complex.ofReal_re]
      linear_combination D * hsat
    have hiff := sum_cube_eq_iff hA.eigenvalues (S.card : ℝ) a hcard2 hSpos he1
      (by rw [hcardR]; exact he2) ha0 (by rw [hcardR]; exact ha2)
    rw [hcardR] at hiff
    exact hiff.mp hsum
  -- (2) → (4)
  have h24 : (∃ i₀ : Vec N, hA.eigenvalues i₀ = a ∧ ∀ i ≠ i₀, hA.eigenvalues i = -a / (D - 1)) →
      ∃ ψ : Vec N → ℂ, IsFlatState S f ψ := by
    rintro ⟨i₀, hi₀, hother⟩
    set ψ : Vec N → ℂ := fun x => hA.eigenvectorBasis i₀ x
    have hψ_norm : ∑ x : Vec N, Complex.normSq (ψ x) = 1 := by
      have h1 : ‖hA.eigenvectorBasis i₀‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i₀
      have h2 : ‖hA.eigenvectorBasis i₀‖ ^ 2 = ∑ x : Vec N, ‖hA.eigenvectorBasis i₀ x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
      rw [h1, one_pow] at h2
      have h3 : ∀ x : Vec N, ‖hA.eigenvectorBasis i₀ x‖ ^ 2 = Complex.normSq (ψ x) := fun x => by
        rw [Complex.normSq_eq_norm_sq]
      simpa [h3] using h2.symm
    -- Express `opA S f = (D * a / (D - 1)) • projMat ψ - (a / (D - 1)) • 1`.
    have hA_eq : opA S f
        = ((D * a / (D - 1) : ℝ) : ℂ) • projMat ψ
          - ((a / (D - 1) : ℝ) : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ) := by
      classical
      have hspec := hA.spectral_theorem
      rw [hspec, Unitary.conjStarAlgAut_apply]
      ext x y
      have hlhs : (((hA.eigenvectorUnitary : Matrix (Vec N) (Vec N) ℂ)
            * diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ))
            * star (hA.eigenvectorUnitary : Matrix (Vec N) (Vec N) ℂ)) x y)
          = ∑ k : Vec N, (hA.eigenvectorBasis k x) * ((hA.eigenvalues k : ℝ) : ℂ)
              * star (hA.eigenvectorBasis k y) := by
        simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
          Matrix.IsHermitian.eigenvectorUnitary_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte]
      have hrhs : (((D * a / (D - 1) : ℝ) : ℂ) • projMat ψ
            - ((a / (D - 1) : ℝ) : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ)) x y
          = ((D * a / (D - 1) : ℝ) : ℂ) * (ψ x * star (ψ y))
            - ((a / (D - 1) : ℝ) : ℂ) * (if x = y then 1 else 0) := by
        simp [projMat, Matrix.one_apply]
      change (((hA.eigenvectorUnitary : Matrix (Vec N) (Vec N) ℂ)
            * diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ))
            * star (hA.eigenvectorUnitary : Matrix (Vec N) (Vec N) ℂ)) x y)
          = (((D * a / (D - 1) : ℝ) : ℂ) • projMat ψ
            - ((a / (D - 1) : ℝ) : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ)) x y
      rw [hlhs, hrhs]
      have hsplit : ∀ k : Vec N,
          ((hA.eigenvalues k : ℝ) : ℂ)
            = ((if k = i₀ then (D * a / (D - 1) : ℝ) else 0 : ℝ) : ℂ)
              - ((a / (D - 1) : ℝ) : ℂ) := by
        intro k
        by_cases hk : k = i₀
        · subst hk
          rw [hi₀, ite_eq_left rfl]
          have hR : a = D * a / (D - 1) - a / (D - 1) := by
            have hcne : D - 1 ≠ 0 := ne_of_gt hDm1
            field_simp [hcne]
          exact_mod_cast hR
        · rw [hother k hk, ite_eq_right hk]
          push_cast; ring
      have hU_ortho : ∑ k : Vec N, (hA.eigenvectorBasis k x) * star (hA.eigenvectorBasis k y)
          = if x = y then 1 else 0 := by
        have hUU : (hA.eigenvectorUnitary : Matrix (Vec N) (Vec N) ℂ) *
            star (hA.eigenvectorUnitary : Matrix (Vec N) (Vec N) ℂ) = 1 :=
          Unitary.coe_mul_star_self hA.eigenvectorUnitary
        have hxy := congrFun (congrFun hUU x) y
        simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply,
          Matrix.IsHermitian.eigenvectorUnitary_apply] using hxy
      calc ∑ k : Vec N, (hA.eigenvectorBasis k x) * ((hA.eigenvalues k : ℝ) : ℂ)
              * star (hA.eigenvectorBasis k y)
          = ∑ k : Vec N, ((((if k = i₀ then D * a / (D - 1) else 0 : ℝ) : ℂ)
                * (hA.eigenvectorBasis k x * star (hA.eigenvectorBasis k y)))
              - ((a / (D - 1) : ℝ) : ℂ)
                * (hA.eigenvectorBasis k x * star (hA.eigenvectorBasis k y))) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsplit k]; ring
        _ = (∑ k : Vec N, ((if k = i₀ then D * a / (D - 1) else 0 : ℝ) : ℂ)
                * (hA.eigenvectorBasis k x * star (hA.eigenvectorBasis k y)))
            - ((a / (D - 1) : ℝ) : ℂ) * ∑ k : Vec N, hA.eigenvectorBasis k x * star (hA.eigenvectorBasis k y) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        _ = ((D * a / (D - 1) : ℝ) : ℂ) * (ψ x * star (ψ y))
            - ((a / (D - 1) : ℝ) : ℂ) * (if x = y then 1 else 0) := by
            rw [hU_ortho, Finset.sum_eq_single i₀]
            · simp [ψ]
            · intro k _ hk; simp [hk]
            · intro h; exact absurd (mem_univ _) h
    -- Read off `⟨ψ | P_v | ψ⟩` from `tr(A * P_v)`.
    have hexp : ∀ v : Pt N, v ≠ 0 →
        ((star ψ) ⬝ᵥ (pauli v *ᵥ ψ))
          = if v ∈ S then ((f v * Real.sqrt ((D - 1) / S.card) : ℝ) : ℂ) else 0 := by
      intro v hv0
      have htr1 : (opA S f * pauli v).trace = if v ∈ S then ((f v : ℝ) : ℂ) * (D : ℂ) else 0 := by
        rw [Matrix.trace_mul_comm, trace_pauli_mul_opA]
        dsimp [D]; push_cast; rfl
      have htr2 : (opA S f * pauli v).trace
          = ((D * a / (D - 1) : ℝ) : ℂ) * ((star ψ) ⬝ᵥ (pauli v *ᵥ ψ)) := by
        rw [hA_eq, sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.smul_mul,
          Matrix.trace_smul, Matrix.trace_smul, one_mul, trace_pauli, ite_eq_right hv0,
          smul_zero, sub_zero, trace_projMat_mul, smul_eq_mul]
      have hcoeff_ne : ((D * a / (D - 1) : ℝ) : ℂ) ≠ 0 := by
        have : D * a / (D - 1) ≠ 0 := div_ne_zero (mul_ne_zero (ne_of_gt hDpos) (ne_of_gt hapos)) (ne_of_gt hDm1)
        exact_mod_cast this
      rw [htr2] at htr1
      by_cases hvS : v ∈ S
      · rw [ite_eq_left hvS] at htr1 ⊢
        apply mul_left_cancel₀ hcoeff_ne
        rw [htr1]
        have hsqrt_id : (D * a / (D - 1)) * Real.sqrt ((D - 1) / S.card) = D := by
          have h1 : a * Real.sqrt ((D - 1) / S.card) = D - 1 := by
            dsimp [a]
            rw [← Real.sqrt_mul hnonneg]
            have hmul : (D - 1) * S.card * ((D - 1) / S.card) = (D - 1) ^ 2 := by
              calc (D - 1) * S.card * ((D - 1) / S.card)
                  = (D - 1) * (D - 1) * ((S.card : ℝ) / (S.card : ℝ)) := by ring
                _ = (D - 1) ^ 2 := by rw [div_self (ne_of_gt hSpos), mul_one, sq]
            rw [hmul, Real.sqrt_sq (le_of_lt hDm1)]
          have hcne : D - 1 ≠ 0 := ne_of_gt hDm1
          calc (D * a / (D - 1)) * Real.sqrt ((D - 1) / S.card)
              = D * (a * Real.sqrt ((D - 1) / S.card)) / (D - 1) := by ring
            _ = D * (D - 1) / (D - 1) := by rw [h1]
            _ = D := mul_div_cancel_right₀ D hcne
        have hC : ((D * a / (D - 1) : ℝ) : ℂ) * ((f v * Real.sqrt ((D - 1) / S.card) : ℝ) : ℂ)
            = ((f v : ℝ) : ℂ) * (D : ℂ) := by
          have : (D * a / (D - 1)) * (f v * Real.sqrt ((D - 1) / S.card)) = f v * D := by
            calc (D * a / (D - 1)) * (f v * Real.sqrt ((D - 1) / S.card))
                = f v * ((D * a / (D - 1)) * Real.sqrt ((D - 1) / S.card)) := by ring
              _ = f v * D := by rw [hsqrt_id]
          exact_mod_cast this
        exact hC.symm
      · rw [ite_eq_right hvS] at htr1 ⊢
        exact (mul_eq_zero.mp htr1).resolve_left hcoeff_ne
    refine ⟨ψ, hψ_norm, fun v hvS => ?_, fun v hv0 hvS => ?_⟩
    · have hv0 : v ≠ 0 := fun h => h0 (h ▸ hvS)
      have h := hexp v hv0
      rw [ite_eq_left hvS] at h
      exact h
    · have h := hexp v hv0
      rw [ite_eq_right hvS] at h
      exact h
  -- (4) → (3)
  have h43 : (∃ ψ : Vec N → ℂ, IsFlatState S f ψ) →
      opA S f ^ 2 = (S.card : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ)
        + (((D - 2) * a / (D - 1) : ℝ) : ℂ) • opA S f := by
    rintro ⟨ψ, hψ_norm, hψ_in, hψ_out⟩
    have hA_eq : opA S f
        = ((D * a / (D - 1) : ℝ) : ℂ) • projMat ψ
          - ((a / (D - 1) : ℝ) : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ) := by
      apply eq_of_trace_pauli_eq
      intro v
      rw [sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.trace_smul, Matrix.trace_smul, one_mul, trace_projMat_mul, trace_pauli,
        Matrix.trace_mul_comm, trace_pauli_mul_opA, smul_eq_mul, smul_eq_mul]
      by_cases hv0 : v = 0
      · subst hv0
        rw [ite_eq_right h0, ite_eq_left rfl, pauli_zero, one_mulVec]
        have hdot : (star ψ) ⬝ᵥ ψ = 1 := by
          simp only [dotProduct, Pi.star_apply]
          have hterm : ∀ z : Vec N, star (ψ z) * ψ z = (Complex.normSq (ψ z) : ℂ) := fun z => by
            rw [Complex.star_def, mul_comm, Complex.mul_conj]
          simp_rw [hterm, ← Complex.ofReal_sum, hψ_norm, Complex.ofReal_one]
        rw [hdot]
        have hR : (0 : ℝ) = (D * a / (D - 1)) * 1 - (a / (D - 1)) * D := by
          have hcne : D - 1 ≠ 0 := ne_of_gt hDm1
          field_simp [hcne]; ring
        have hC : (0 : ℂ) = ((D * a / (D - 1) : ℝ) : ℂ) * 1 - ((a / (D - 1) : ℝ) : ℂ) * (D : ℂ) := by
          exact_mod_cast hR
        simpa [D] using hC
      · rw [ite_eq_right hv0, mul_zero, sub_zero]
        by_cases hvS : v ∈ S
        · rw [ite_eq_left hvS, hψ_in v hvS]
          have hsqrt_id : (D * a / (D - 1)) * Real.sqrt ((D - 1) / S.card) = D := by
            have h1 : a * Real.sqrt ((D - 1) / S.card) = D - 1 := by
              dsimp [a]
              rw [← Real.sqrt_mul hnonneg]
              have hmul : (D - 1) * S.card * ((D - 1) / S.card) = (D - 1) ^ 2 := by
                field_simp [ne_of_gt hSpos]
              rw [hmul, Real.sqrt_sq (le_of_lt hDm1)]
            calc (D * a / (D - 1)) * Real.sqrt ((D - 1) / S.card)
                = D * (a * Real.sqrt ((D - 1) / S.card)) / (D - 1) := by ring
              _ = D * (D - 1) / (D - 1) := by rw [h1]
              _ = D := mul_div_cancel_right₀ D (ne_of_gt hDm1)
          have hC : ((f v : ℝ) : ℂ) * (D : ℂ)
              = ((D * a / (D - 1) : ℝ) : ℂ) * ((f v * Real.sqrt ((D - 1) / S.card) : ℝ) : ℂ) := by
            have : f v * D = (D * a / (D - 1)) * (f v * Real.sqrt ((D - 1) / S.card)) := by
              calc f v * D = f v * ((D * a / (D - 1)) * Real.sqrt ((D - 1) / S.card)) := by rw [hsqrt_id]
                _ = (D * a / (D - 1)) * (f v * Real.sqrt ((D - 1) / S.card)) := by ring
            exact_mod_cast this
          simpa [D] using hC
        · rw [ite_eq_right hvS, hψ_out v hv0 hvS, mul_zero]
    rw [pow_two, hA_eq]
    set α : ℂ := ((D * a / (D - 1) : ℝ) : ℂ)
    set β : ℂ := ((a / (D - 1) : ℝ) : ℂ)
    set γ : ℂ := (((D - 2) * a / (D - 1) : ℝ) : ℂ)
    have hP2 : projMat ψ * projMat ψ = projMat ψ := projMat_sq hψ_norm
    have hcalc : (α • projMat ψ - β • (1 : Matrix (Vec N) (Vec N) ℂ))
          * (α • projMat ψ - β • (1 : Matrix (Vec N) (Vec N) ℂ))
        = (α * α - 2 * α * β) • projMat ψ + (β * β) • (1 : Matrix (Vec N) (Vec N) ℂ) := by
      simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP2,
        one_mul, mul_one]
      ext x y
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hcalc]
    have hαβ : α * α - 2 * α * β = γ * α := by
      have hR : (D * a / (D - 1)) * (D * a / (D - 1)) - 2 * (D * a / (D - 1)) * (a / (D - 1))
          = ((D - 2) * a / (D - 1)) * (D * a / (D - 1)) := by
        have hcne : D - 1 ≠ 0 := ne_of_gt hDm1
        field_simp [hcne]
      dsimp [α, β, γ]
      exact_mod_cast hR
    have hβ2 : β * β = (S.card : ℂ) - γ * β := by
      have hR : (a / (D - 1)) * (a / (D - 1)) = (S.card : ℝ) - ((D - 2) * a / (D - 1)) * (a / (D - 1)) := by
        have hcne : D - 1 ≠ 0 := ne_of_gt hDm1
        field_simp [hcne]
        nlinarith [ha2]
      dsimp [β, γ]
      exact_mod_cast hR
    rw [hαβ, hβ2]
    ext x y
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  -- (3) → (1)
  have h31 : opA S f ^ 2 = (S.card : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ)
        + (((D - 2) * a / (D - 1) : ℝ) : ℂ) • opA S f →
      (D - 1) * beta6 S f = (D - 2) * S.card * a := by
    intro hsq
    have hcube : (opA S f ^ 3).trace = (((D - 2) * a / (D - 1) : ℝ) : ℂ) * (opA S f ^ 2).trace := by
      conv_lhs => rw [show opA S f ^ 3 = opA S f ^ 2 * opA S f by rw [pow_succ], hsq]
      rw [add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.trace_smul, Matrix.trace_smul, one_mul, trace_opA S f h0, smul_zero, zero_add,
        ← pow_two, smul_eq_mul]
    rw [trace_opA_cube, trace_opA_sq S f hf] at hcube
    have hre := congrArg Complex.re hcube
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
    have hDne : D ≠ 0 := ne_of_gt hDpos
    have hcne : D - 1 ≠ 0 := ne_of_gt hDm1
    have hre' : D * beta6 S f = ((D - 2) * a / (D - 1)) * (D * S.card) := hre
    field_simp [hcne] at hre'
    nlinarith
  -- (3) ↔ (5)
  have h35 : (opA S f ^ 2 = (S.card : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ)
        + (((D - 2) * a / (D - 1) : ℝ) : ℂ) • opA S f) ↔
      ((∀ w ∈ S, 2 * excess S f w = (D - 2) * a / (D - 1)) ∧
        (∀ w : Pt N, w ≠ 0 → w ∉ S → outsideSum S f w = 0)) := by
    constructor
    · intro hsq
      constructor
      · intro w hwS
        have hw0 : w ≠ 0 := fun h => h0 (h ▸ hwS)
        have htr := congrArg (fun M => (M * pauli w).trace) hsq
        rw [trace_opA_sq_mul_pauli S f hw0, outsideSum_eq_excess_mul hf hwS, add_mul,
          Matrix.trace_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul,
          one_mul, trace_pauli, ite_eq_right hw0, smul_zero, zero_add, Matrix.trace_mul_comm,
          trace_pauli_mul_opA, ite_eq_left hwS, smul_eq_mul] at htr
        have hneC : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
        have h1 : ((2 * (excess S f w * f w) : ℝ) : ℂ)
            = (((D - 2) * a / (D - 1) : ℝ) : ℂ) * ((f w : ℝ) : ℂ) := by
          apply mul_left_cancel₀ hneC
          linear_combination htr
        have hR : 2 * (excess S f w * f w) = ((D - 2) * a / (D - 1)) * f w := by
          exact_mod_cast h1
        rcases hf w hwS with h | h <;> rw [h] at hR <;> linarith
      · intro w hw0 hwS
        have htr := congrArg (fun M => (M * pauli w).trace) hsq
        rw [trace_opA_sq_mul_pauli S f hw0, add_mul, Matrix.trace_add, Matrix.smul_mul,
          Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul, one_mul, trace_pauli,
          ite_eq_right hw0, smul_zero, zero_add, Matrix.trace_mul_comm, trace_pauli_mul_opA,
          ite_eq_right hwS, smul_zero] at htr
        have hneC : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
        have h1 : ((2 * outsideSum S f w : ℝ) : ℂ) = 0 := (mul_eq_zero.mp htr).resolve_left hneC
        have hR : 2 * outsideSum S f w = 0 := by exact_mod_cast h1
        linarith
    · rintro ⟨hex, hout⟩
      rw [opA_sq_eq S h0 f hf]
      have hzero : ∑ w ∈ (univ.erase (0 : Pt N)) \ S,
          ((2 * outsideSum S f w : ℝ) : ℂ) • pauli w = 0 := by
        refine Finset.sum_eq_zero fun w hw => ?_
        have hw1 := Finset.mem_sdiff.mp hw
        have hw0 : w ≠ 0 := Finset.ne_of_mem_erase hw1.1
        rw [hout w hw0 hw1.2]; simp
      rw [hzero, add_zero]
      congr 1
      rw [opA, Finset.smul_sum]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [smul_smul]
      congr 1
      have hR : 2 * excess S f w * f w = ((D - 2) * a / (D - 1)) * f w := by
        rw [hex w hw]
      exact_mod_cast hR
  tfae_have 1 → 2 := h12
  tfae_have 2 → 4 := h24
  tfae_have 4 → 3 := h43
  tfae_have 3 → 1 := h31
  tfae_have 3 ↔ 5 := h35
  tfae_finish

/-- **Integrality condition for saturation (Theorem 4).**
For `N ≥ 2` and a nonempty set `S` of non-identity Pauli observables, if an assignment `f : S → {±1}`
saturates `hoggar_bound`, then `(2^N - 1) * |S|` is a perfect square. -/
theorem saturation_mul_isSquare (hN : 2 ≤ N) (S : Finset (Pt N)) (hne : S.Nonempty)
    (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1)
    (hsat : ((2 : ℝ) ^ N - 1) * beta6 S f
      = ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card)) :
    ∃ k : ℕ, (2 ^ N - 1) * S.card = k ^ 2 := by
  have hD4 : 4 ≤ 2 ^ N := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  set b : ℤ := ((flags S).card : ℤ) - 2 * ((violated S f).card : ℤ)
  have hb : beta6 S f = (b : ℝ) := by
    rw [beta6_eq_card S f hf]; push_cast [b]; ring
  set p : ℤ := ((2 ^ N - 1 : ℕ) : ℤ) * b
  set q : ℕ := (2 ^ N - 2) * S.card
  set n : ℕ := (2 ^ N - 1) * S.card
  have hqpos : 0 < q := mul_pos (by omega) (Finset.card_pos.mpr hne)
  have hcast_d1 : (((2 ^ N - 1 : ℕ) : ℝ)) = (2 : ℝ) ^ N - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hcast_d2 : (((2 ^ N - 2 : ℕ) : ℝ)) = (2 : ℝ) ^ N - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hp_eq : (p : ℝ) = (q : ℝ) * Real.sqrt (n : ℝ) := by
    have hpR : (p : ℝ) = ((2 : ℝ) ^ N - 1) * beta6 S f := by
      rw [hb]; dsimp [p]; rw [Int.cast_mul, Int.cast_natCast, hcast_d1]
    have hqR : (q : ℝ) = ((2 : ℝ) ^ N - 2) * (S.card : ℝ) := by
      dsimp [q]; rw [Nat.cast_mul, hcast_d2]
    have hnR : (n : ℝ) = ((2 : ℝ) ^ N - 1) * (S.card : ℝ) := by
      dsimp [n]; rw [Nat.cast_mul, hcast_d1]
    rw [hpR, hqR, hnR]
    exact hsat
  have hsqR : (p : ℝ) ^ 2 = (q : ℝ) ^ 2 * (n : ℝ) := by
    rw [hp_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hsqZ : p ^ 2 = (q : ℤ) ^ 2 * (n : ℤ) := by exact_mod_cast hsqR
  have hsqN : p.natAbs ^ 2 = q ^ 2 * n := by
    have h1 : ((p.natAbs ^ 2 : ℕ) : ℤ) = ((q ^ 2 * n : ℕ) : ℤ) := by
      rw [Nat.cast_pow, Int.natAbs_sq, hsqZ]; push_cast; rfl
    exact_mod_cast h1
  have hdvd : q ∣ p.natAbs := by
    have hdvd2 : q ^ 2 ∣ p.natAbs ^ 2 := ⟨n, hsqN⟩
    exact (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp hdvd2
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, ?_⟩
  rw [hk, mul_pow] at hsqN
  have hq2pos : 0 < q ^ 2 := pow_pos hqpos 2
  exact Nat.eq_of_mul_eq_mul_left hq2pos hsqN.symm

end SaturationEquivalences

end HoggarBound

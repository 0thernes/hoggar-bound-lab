/-
Hoggar Bound Lab — Audit Upgrades (v1.7.0).

This self-contained module closes six remaining formalization gaps and formalizes a new,
strictly tighter QUBO SDP-dual lower bound for Corollary 16 without modifying any
previously audited Lean file:

1. **Asymptotic limit theorems** (`full_space_fraction_tendsto_half`,
   `hyperbolic_fraction_tendsto_half`, `full_space_violated_fraction_eventually_gt`,
   `elliptic_violated_fraction_eventually_gt`): formal `Filter.Tendsto` proofs that the
   spectral floor violated fraction converges to `1/2` as `N → ∞`.
2. **Quantum metric and Berry curvature — Propositions 3 & 8**
   (`proposition3_violated_iff`, `proposition3_satisfied_iff`,
   `proposition8_flat_state_qgt`): exact Fubini–Study metric and Berry curvature
   characterizations of violated vs. satisfied contexts and flat pure states.
3. **Two-character set & hyperplane intersections — Proposition 10**
   (`pure_state_pauli_sq_transform`, `proposition10_two_character_sum`,
   `proposition10_hyperplane_card`): for every flat pure state on `S`,
   `∑_{v ∈ S} (-1)^{⟨v, w⟩} = D · [w ∈ S] - |S|/(D - 1)` and exact hyperplane intersection
   cardinalities for every `w ≠ 0`.
4. **Signed-Clifford / symplectic orbit transport**
   (`clifford_transport_opA`, `clifford_transport_carrier_charpoly`,
   `clifford_transport_completion_charpoly`, `clifford_transport_strict_law_fails`):
   any unitary `U` satisfying `U P_v Uᴴ = ν(v) P_{g v}` (`ν(v) ∈ {±1}`) preserves both
   carrier and completion characteristic polynomials (and hence lifts any canonical
   counterexample `(X, d)` to every image `(X.image g, g d)` in its Clifford orbit).
5. **Eigenvalue-multiset level Conjecture E across all nine vertex cases (`N ≥ 4`)**
   (`completionMat_isHermitian`, `jonah_conjecture_e_all_nine_cases_spectra`):
   upgrades `jonah_conjecture_e_all_nine_cases` from characteristic polynomials to
   literal equality of canonical Hermitian carrier eigenvalue lists and literal inequality
   of real completion eigenvalue lists and root multisets (with multiplicities).
6. **Tightened Corollary 16 via exact QUBO SDP dual**
   (`corollary16_sigmaB_sdp_lower`, `corollary16_sigmaA_witness`,
   `corollary16_binary_minima_tightened`):
   introduces the zero-sum geometric diagonal shift `d₁₆(p) ∈ {-40, +8, +8, +24}` depending
   only on `(a₁(p), a₀(p))`, proves its exact vanishing on every binary vector `y ∈ {±1}^64`,
   reduces `231 I₆₄ - 16 Λ₁ - diag(d₁₆) ≻ 0` via Lemma 20 to four `8 × 8` pure-integer
   fraction-free `L D Lᵀ` certificates, and proves **`330 ≤ min_y F(σ₁, y) ≤ 344`**
   (tightening the lower bound by +15 from 315 to the exact SDP-dual ceiling 330, halving
   the uncertainty interval) alongside the kernel-checked two-sided enclosure
   **`347 ≤ min_y F(σ₀, y) ≤ 368`**.
-/
import HoggarBound.Corollaries
import HoggarBound.Kramers
import HoggarBound.SaturationTheory
import HoggarBound.ConjectureE
import HoggarBound.ConjectureEExtras

open Finset Matrix Filter Topology

namespace HoggarBound.AuditUpgrades

/-! ### Part 1. Asymptotic Limit Theorems (`N → ∞`) -/

section Asymptotics

/-- Elementary bound: for every `N : ℕ`, `0 ≤ √(2^N + 1) / (2^N + 2) ≤ 1 / √(2^N + 1)`. -/
lemma sqrt_ratio_le_inv_sqrt (N : ℕ) :
    Real.sqrt ((2 : ℝ) ^ N + 1) / ((2 : ℝ) ^ N + 2) ≤ (Real.sqrt ((2 : ℝ) ^ N + 1))⁻¹ := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ N + 1 := by positivity
  have hspos : (0 : ℝ) < Real.sqrt ((2 : ℝ) ^ N + 1) := Real.sqrt_pos.mpr hpos
  have hden : (0 : ℝ) < (2 : ℝ) ^ N + 2 := by linarith
  rw [div_le_iff₀ hden, inv_mul_eq_div, le_div_iff₀ hspos, ← sq, Real.sq_sqrt (le_of_lt hpos)]
  linarith

/-- The spectral-floor deficit `√(2^N + 1) / (2^N + 2)` tends to `0` as `N → ∞`. -/
theorem floor_deficit_tendsto_zero :
    Tendsto (fun N : ℕ => Real.sqrt ((2 : ℝ) ^ N + 1) / ((2 : ℝ) ^ N + 2)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => (2 : ℝ) ^ N) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hadd : Tendsto (fun N : ℕ => (2 : ℝ) ^ N + 1) atTop atTop :=
    hpow.atTop_add tendsto_const_nhds
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt ((2 : ℝ) ^ N + 1)) atTop atTop :=
    (Filter.tendsto_atTop.mpr fun b => by
      filter_upwards [Filter.tendsto_atTop.mp hadd (max b 0 ^ 2)] with N hN
      have h1 : max b 0 ≤ Real.sqrt ((2 : ℝ) ^ N + 1) := by
        rw [← Real.sqrt_sq (le_max_right b 0)]
        exact Real.sqrt_le_sqrt hN
      exact le_trans (le_max_left b 0) h1)
  have hinv : Tendsto (fun N : ℕ => (Real.sqrt ((2 : ℝ) ^ N + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  exact squeeze_zero (fun N => by positivity) sqrt_ratio_le_inv_sqrt hinv

/-- **Asymptotic spectral floor (full space & elliptic quadrics):**
`1/2 - √(2^N + 1) / (2^N + 2) → 1/2` as `N → ∞`. -/
theorem full_space_fraction_tendsto_half :
    Tendsto (fun N : ℕ => (1 / 2 : ℝ) - Real.sqrt ((2 : ℝ) ^ N + 1) / ((2 : ℝ) ^ N + 2))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  simpa using tendsto_const_nhds.sub floor_deficit_tendsto_zero

/-- **Asymptotic spectral floor (hyperbolic quadrics):**
`1/2 - √(2^(N-1) + 1) / (2^(N-1) + 2) → 1/2` as `N → ∞`. -/
theorem hyperbolic_fraction_tendsto_half :
    Tendsto (fun N : ℕ => (1 / 2 : ℝ) - Real.sqrt ((2 : ℝ) ^ (N - 1) + 1) / ((2 : ℝ) ^ (N - 1) + 2))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hsub : Tendsto (fun N : ℕ => N - 1) atTop atTop :=
    Filter.tendsto_atTop.mpr fun b => Filter.eventually_atTop.mpr ⟨b + 1, fun n hn => by omega⟩
  exact full_space_fraction_tendsto_half.comp hsub

/-- **Macroscopic contextuality limit (full space `W(2N-1, 2)`):**
For every `ε > 0`, eventually for all `N` and every noncontextual sign assignment `f`,
the violated flag fraction exceeds `1/2 - ε`. -/
theorem full_space_violated_fraction_eventually_gt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (f : Pt N → ℝ), (∀ u ∈ allPoints N, f u = 1 ∨ f u = -1) →
      (1 / 2 - ε) < ((violated (allPoints N) f).card : ℝ) / ((flags (allPoints N)).card : ℝ) := by
  have hev1 : ∀ᶠ N : ℕ in atTop,
      (1 / 2 - ε) < (1 / 2 : ℝ) - Real.sqrt ((2 : ℝ) ^ N + 1) / ((2 : ℝ) ^ N + 2) :=
    (tendsto_order.mp full_space_fraction_tendsto_half).1 (1 / 2 - ε) (by linarith)
  have hev2 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := Filter.eventually_atTop.mpr ⟨2, fun _ h => h⟩
  filter_upwards [hev1, hev2] with N hlt hN f hf
  have hfrac := full_space_fraction (by omega : 1 ≤ N) f hf
  have hFcast := card_flags_all_cast (N := N) (by omega : 1 ≤ N)
  have hD4 : (4 : ℝ) ≤ (2 : ℝ) ^ N := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hFpos : (0 : ℝ) < ((flags (allPoints N)).card : ℝ) := by
    rw [hFcast]
    have h1 : (0 : ℝ) < ((2 : ℝ) ^ N) ^ 2 - 1 := by nlinarith
    have h2 : (0 : ℝ) < ((2 : ℝ) ^ N) ^ 2 - 4 := by nlinarith
    positivity
  have hdiv : (1 / 2 : ℝ) - Real.sqrt ((2 : ℝ) ^ N + 1) / ((2 : ℝ) ^ N + 2)
      ≤ ((violated (allPoints N) f).card : ℝ) / ((flags (allPoints N)).card : ℝ) :=
    (le_div_iff₀ hFpos).mpr hfrac
  linarith

/-- **Macroscopic contextuality limit (elliptic quadrics `Q⁻(2N-1, 2)`):**
For every `ε > 0`, eventually for all `N`, every `w` with `qform w = 1`, and every sign
assignment `f`, the violated flag fraction on `Q⁻(2N-1, 2)` exceeds `1/2 - ε`. -/
theorem elliptic_violated_fraction_eventually_gt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (w : Pt N), qform w = 1 →
      ∀ (f : Pt N → ℝ), (∀ u ∈ ellipticPoints N w, f u = 1 ∨ f u = -1) →
      (1 / 2 - ε) < ((violated (ellipticPoints N w) f).card : ℝ) /
        ((flags (ellipticPoints N w)).card : ℝ) := by
  have hev1 : ∀ᶠ N : ℕ in atTop,
      (1 / 2 - ε) < (1 / 2 : ℝ) - Real.sqrt ((2 : ℝ) ^ N + 1) / ((2 : ℝ) ^ N + 2) :=
    (tendsto_order.mp full_space_fraction_tendsto_half).1 (1 / 2 - ε) (by linarith)
  have hev2 : ∀ᶠ N : ℕ in atTop, 3 ≤ N := Filter.eventually_atTop.mpr ⟨3, fun _ h => h⟩
  filter_upwards [hev1, hev2] with N hlt hN w hw f hf
  have hfrac := elliptic_fraction (by omega : 2 ≤ N) w hw f hf
  have hFcast := card_flags_elliptic_cast (N := N) (w := w) hw
  have hD8 : (8 : ℝ) ≤ (2 : ℝ) ^ N := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hFpos : (0 : ℝ) < ((flags (ellipticPoints N w)).card : ℝ) := by
    rw [hFcast]
    have h1 : (0 : ℝ) < ((2 : ℝ) ^ N + 1) * ((2 : ℝ) ^ N - 2) := by nlinarith
    have h2 : (0 : ℝ) < ((2 : ℝ) ^ N + 2) * ((2 : ℝ) ^ N - 4) := by nlinarith
    nlinarith
  have hdiv : (1 / 2 : ℝ) - Real.sqrt ((2 : ℝ) ^ N + 1) / ((2 : ℝ) ^ N + 2)
      ≤ ((violated (ellipticPoints N w) f).card : ℝ) / ((flags (ellipticPoints N w)).card : ℝ) :=
    (le_div_iff₀ hFpos).mpr hfrac
  linarith

end Asymptotics

/-! ### Part 2. Quantum Metric & Berry Curvature (Propositions 3 & 8) -/

section QuantumGeometry

variable {N : ℕ}

/-- Real expectation value `p_v = ⟨ψ | P_v | ψ⟩ = Re tr(|ψ⟩⟨ψ| P_v)`. -/
noncomputable def pauliExpVal (ψ : Vec N → ℂ) (v : Pt N) : ℝ :=
  (projMat ψ * pauli v).trace.re

/-- For any vector `ψ`, `tr(|ψ⟩⟨ψ| P_v)` equals `pauliExpVal ψ v` as a real complex number. -/
lemma trace_projMat_mul_pauli_eq_ofReal (ψ : Vec N → ℂ) (v : Pt N) :
    (projMat ψ * pauli v).trace = (pauliExpVal ψ v : ℂ) := by
  have hstar : star ((projMat ψ * pauli v).trace) = (projMat ψ * pauli v).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, (pauli_isHermitian v).eq]
    have hP : (projMat ψ)ᴴ = projMat ψ := by
      ext x y; simp [projMat, mul_comm]
    rw [hP, Matrix.trace_mul_comm]
  have him : ((projMat ψ * pauli v).trace).im = 0 := by
    have := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  exact Complex.ext rfl (by simp [him])

lemma pauliExpVal_zero {ψ : Vec N → ℂ} (hψ : ∑ x : Vec N, Complex.normSq (ψ x) = 1) :
    pauliExpVal ψ 0 = 1 := by
  have h0 : (projMat ψ * pauli (0 : Pt N)).trace = 1 := by
    rw [pauli_zero, mul_one]
    simp only [Matrix.trace, Matrix.diag_apply, projMat]
    have hterm : ∀ x : Vec N, ψ x * star (ψ x) = (Complex.normSq (ψ x) : ℂ) := fun x => by
      rw [Complex.star_def, Complex.mul_conj]
    simp_rw [hterm, ← Complex.ofReal_sum, hψ, Complex.ofReal_one]
  simp [pauliExpVal, h0]

/-- Quantum geometric tensor entry `Q_{uv} = (1/4)(⟨P_u P_v⟩ - p_u p_v)` along `e^{-itP_v/2}`. -/
noncomputable def qgtEntry (ψ : Vec N → ℂ) (u v : Pt N) : ℂ :=
  (1 / 4 : ℂ) * ((projMat ψ * (pauli u * pauli v)).trace
    - (pauliExpVal ψ u : ℂ) * (pauliExpVal ψ v : ℂ))

/-- Fubini–Study metric `g_{uv} = Re Q_{uv}`. -/
noncomputable def fubiniStudyMetric (ψ : Vec N → ℂ) (u v : Pt N) : ℝ :=
  (qgtEntry ψ u v).re

/-- Berry curvature `F_{uv} = -2 Im Q_{uv}`. -/
noncomputable def berryCurvature (ψ : Vec N → ℂ) (u v : Pt N) : ℝ :=
  -2 * (qgtEntry ψ u v).im

/-- Exact Fubini–Study metric and Berry curvature for commuting observables `⟨u, v⟩ = 0`. -/
theorem proposition3_commuting_qgt (ψ : Vec N → ℂ) {u v : Pt N} (hcomm : symp u v = 0) :
    fubiniStudyMetric ψ u v = (lineSign u v * pauliExpVal ψ (u + v) - pauliExpVal ψ u * pauliExpVal ψ v) / 4 ∧
    berryCurvature ψ u v = 0 := by
  have hQ : qgtEntry ψ u v
      = (((lineSign u v * pauliExpVal ψ (u + v) - pauliExpVal ψ u * pauliExpVal ψ v) / 4 : ℝ) : ℂ) := by
    unfold qgtEntry
    rw [pauli_mul, tau_eq_lineSign hcomm, Matrix.mul_smul, Matrix.trace_smul,
      trace_projMat_mul_pauli_eq_ofReal, smul_eq_mul]
    push_cast; ring
  constructor
  · simp [fubiniStudyMetric, hQ]
  · simp [berryCurvature, hQ]

/-- Exact Fubini–Study metric and Berry curvature for anticommuting observables `⟨u, v⟩ = 1`. -/
theorem anticommuting_qgt (ψ : Vec N → ℂ) {u v : Pt N} (hanti : symp u v = 1) :
    fubiniStudyMetric ψ u v = -(pauliExpVal ψ u * pauliExpVal ψ v) / 4 ∧
    |berryCurvature ψ u v| = |pauliExpVal ψ (u + v)| / 2 := by
  have htau2 : tau u v ^ 2 = -1 := by
    rw [tau_sq, hanti, eps_one]
  have htau : tau u v = Complex.I ∨ tau u v = -Complex.I := by
    have hfac : (tau u v - Complex.I) * (tau u v + Complex.I) = 0 := by
      linear_combination htau2 - Complex.I_sq
    rcases mul_eq_zero.mp hfac with h | h
    · left; linear_combination h
    · right; linear_combination h
  have htr : (projMat ψ * (pauli u * pauli v)).trace
      = tau u v * (pauliExpVal ψ (u + v) : ℂ) := by
    rw [pauli_mul, Matrix.mul_smul, Matrix.trace_smul, trace_projMat_mul_pauli_eq_ofReal, smul_eq_mul]
  rcases htau with h | h
  · constructor
    · unfold fubiniStudyMetric qgtEntry; rw [htr, h]
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    · unfold berryCurvature qgtEntry; rw [htr, h]
      simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
        Complex.one_re, Complex.one_im, mul_zero, zero_mul, zero_div, sub_zero,
        add_zero, zero_add, one_mul]
      rw [show -2 * (1 / 4 * pauliExpVal ψ (u + v)) = -(pauliExpVal ψ (u + v) / 2) by ring,
        abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  · constructor
    · unfold fubiniStudyMetric qgtEntry; rw [htr, h]
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    · unfold berryCurvature qgtEntry; rw [htr, h]
      simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.neg_im, Complex.div_ofNat_re,
        Complex.div_ofNat_im, Complex.one_re, Complex.one_im, mul_zero, zero_mul, zero_div,
        sub_zero, add_zero, zero_add, neg_mul, one_mul]
      rw [show -(2 * (1 / 4 * -pauliExpVal ψ (u + v))) = pauliExpVal ψ (u + v) / 2 by ring,
        abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Elementary real-analysis lemma: for `a ≠ 0`, `b ≠ 0`, `|a - b| = |a| + |b| ↔ a * b < 0`. -/
private lemma abs_sub_eq_add_iff_mul_neg {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    |a - b| = |a| + |b| ↔ a * b < 0 := by
  have hsq : |a - b| ^ 2 = (|a| + |b|) ^ 2 ↔ a * b < 0 := by
    rw [sq_abs, add_sq, sq_abs, sq_abs]
    constructor
    · intro h
      have h1 : -(a * b) = |a| * |b| := by linarith
      have hab : 0 < |a| * |b| := mul_pos (abs_pos.mpr ha) (abs_pos.mpr hb)
      linarith
    · intro h
      have h1 : |a| * |b| = -(a * b) := by
        rw [← abs_mul, abs_of_neg h]
      linarith
  rw [← hsq]
  constructor
  · intro h; rw [h]
  · intro h
    have hnn1 : 0 ≤ |a - b| := abs_nonneg _
    have hnn2 : 0 ≤ |a| + |b| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith

/-- Elementary real-analysis lemma: for `a ≠ 0`, `b ≠ 0`, `|a - b| = |(|a| - |b|)| ↔ 0 < a * b`. -/
private lemma abs_sub_eq_abs_sub_iff_mul_pos {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    |a - b| = abs (|a| - |b|) ↔ 0 < a * b := by
  have hsq : |a - b| ^ 2 = abs (|a| - |b|) ^ 2 ↔ 0 < a * b := by
    rw [sq_abs, sq_abs, sub_sq, sub_sq, sq_abs, sq_abs]
    constructor
    · intro h
      have h1 : a * b = |a| * |b| := by linarith
      have hab : 0 < |a| * |b| := mul_pos (abs_pos.mpr ha) (abs_pos.mpr hb)
      linarith
    · intro h
      have h1 : |a| * |b| = a * b := by
        rw [← abs_mul, abs_of_pos h]
      linarith
  rw [← hsq]
  constructor
  · intro h; rw [h]
  · intro h
    have hnn1 : 0 ≤ |a - b| := abs_nonneg _
    have hnn2 : 0 ≤ abs (|a| - |b|) := abs_nonneg _
    nlinarith

private lemma lineSign_eq_one_or_neg_one' {u v : Pt N} (hcomm : symp u v = 0) :
    lineSign u v = 1 ∨ lineSign u v = -1 := by
  have h2 := tau_sq u v
  rw [tau_eq_lineSign hcomm, hcomm, eps_zero] at h2
  have hR : lineSign u v ^ 2 = 1 := by exact_mod_cast h2
  have : (lineSign u v - 1) * (lineSign u v + 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h <;> [left; right] <;> linarith

private lemma sign_mul_pos_iff {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (sa sb : ℝ) (hsa : sa = if 0 < a then 1 else -1) (hsb : sb = if 0 < b then 1 else -1) :
    (sa = sb ↔ 0 < a * b) ∧ (sa ≠ sb ↔ a * b < 0) := by
  rw [hsa, hsb]
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
  · have hna : ¬ (0 < a) := not_lt.mpr (le_of_lt ha')
    have hnb : ¬ (0 < b) := not_lt.mpr (le_of_lt hb')
    rw [ite_eq_right hna, ite_eq_right hnb]
    exact ⟨⟨fun _ => mul_pos_of_neg_of_neg ha' hb', fun _ => rfl⟩,
      ⟨fun h => absurd rfl h, fun h => by linarith [mul_pos_of_neg_of_neg ha' hb']⟩⟩
  · have hna : ¬ (0 < a) := not_lt.mpr (le_of_lt ha')
    rw [ite_eq_right hna, ite_eq_left hb']
    exact ⟨⟨fun h => by norm_num at h, fun h => by linarith [mul_neg_of_neg_of_pos ha' hb']⟩,
      ⟨fun _ => mul_neg_of_neg_of_pos ha' hb', fun _ => by norm_num⟩⟩
  · have hnb : ¬ (0 < b) := not_lt.mpr (le_of_lt hb')
    rw [ite_eq_left ha', ite_eq_right hnb]
    exact ⟨⟨fun h => by norm_num at h, fun h => by linarith [mul_neg_of_pos_of_neg ha' hb']⟩,
      ⟨fun _ => mul_neg_of_pos_of_neg ha' hb', fun _ => by norm_num⟩⟩
  · rw [ite_eq_left ha', ite_eq_left hb']
    exact ⟨⟨fun _ => mul_pos ha' hb', fun _ => rfl⟩,
      ⟨fun h => absurd rfl h, fun h => by linarith [mul_pos ha' hb']⟩⟩

/-- **Proposition 3(a) (violated context in the Fubini–Study metric):**
For a context `{u, v, u + v}` with nonzero expectation values and sign assignment `f = sign(p)`,
the context is violated if and only if `4 |g_{uv}| = |p_{u+v}| + |p_u p_v|`. -/
theorem proposition3_violated_iff (ψ : Vec N → ℂ) {u v : Pt N} (hcomm : symp u v = 0)
    (hu : pauliExpVal ψ u ≠ 0) (hv : pauliExpVal ψ v ≠ 0) (hw : pauliExpVal ψ (u + v) ≠ 0)
    (f : Pt N → ℝ)
    (hfu : f u = if 0 < pauliExpVal ψ u then 1 else -1)
    (hfv : f v = if 0 < pauliExpVal ψ v then 1 else -1)
    (hfw : f (u + v) = if 0 < pauliExpVal ψ (u + v) then 1 else -1) :
    f u * f v * f (u + v) ≠ lineSign u v ↔
      4 * |fubiniStudyMetric ψ u v| = |pauliExpVal ψ (u + v)| + |pauliExpVal ψ u * pauliExpVal ψ v| := by
  have hg := (proposition3_commuting_qgt ψ hcomm).1
  have hs := lineSign_eq_one_or_neg_one' hcomm
  have hsne : lineSign u v ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hsabs : |lineSign u v| = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have ha : lineSign u v * pauliExpVal ψ (u + v) ≠ 0 := mul_ne_zero hsne hw
  have hb : pauliExpVal ψ u * pauliExpVal ψ v ≠ 0 := mul_ne_zero hu hv
  have h4g : 4 * |fubiniStudyMetric ψ u v|
      = |lineSign u v * pauliExpVal ψ (u + v) - pauliExpVal ψ u * pauliExpVal ψ v| := by
    rw [hg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; ring
  have hsp : |lineSign u v * pauliExpVal ψ (u + v)| = |pauliExpVal ψ (u + v)| := by
    rw [abs_mul, hsabs, one_mul]
  rw [h4g, ← hsp, abs_sub_eq_add_iff_mul_neg ha hb]
  -- Compare `f u * f v * f (u + v) ≠ lineSign u v` with `(lineSign u v * pw) * (pu * pv) < 0`!
  have hsign_a : lineSign u v * f (u + v) = if 0 < lineSign u v * pauliExpVal ψ (u + v) then 1 else -1 := by
    rw [hfw]; rcases hs with h | h <;> rw [h] <;> rcases lt_or_gt_of_ne hw with hw' | hw'
    · rw [ite_eq_right (not_lt.mpr (le_of_lt hw')), ite_eq_right (by linarith)]; norm_num
    · rw [ite_eq_left hw', ite_eq_left (by linarith)]; norm_num
    · rw [ite_eq_right (not_lt.mpr (le_of_lt hw')), ite_eq_left (by linarith)]; norm_num
    · rw [ite_eq_left hw', ite_eq_right (by linarith)]; norm_num
  have hsign_b : f u * f v = if 0 < pauliExpVal ψ u * pauliExpVal ψ v then 1 else -1 := by
    rw [hfu, hfv]; rcases lt_or_gt_of_ne hu with hu' | hu' <;> rcases lt_or_gt_of_ne hv with hv' | hv'
    · rw [ite_eq_right (not_lt.mpr (le_of_lt hu')), ite_eq_right (not_lt.mpr (le_of_lt hv')),
        ite_eq_left (mul_pos_of_neg_of_neg hu' hv')]; norm_num
    · rw [ite_eq_right (not_lt.mpr (le_of_lt hu')), ite_eq_left hv',
        ite_eq_right (not_lt.mpr (le_of_lt (mul_neg_of_neg_of_pos hu' hv')))]; norm_num
    · rw [ite_eq_left hu', ite_eq_right (not_lt.mpr (le_of_lt hv')),
        ite_eq_right (not_lt.mpr (le_of_lt (mul_neg_of_pos_of_neg hu' hv')))]; norm_num
    · rw [ite_eq_left hu', ite_eq_left hv', ite_eq_left (mul_pos hu' hv')]; norm_num
  have hiff := (sign_mul_pos_iff ha hb (lineSign u v * f (u + v)) (f u * f v) hsign_a hsign_b).2
  rw [← hiff]
  have hf_val : ∀ x : ℝ, (x = if 0 < pauliExpVal ψ (u + v) then 1 else -1) → x * x = 1 := fun x hx => by
    rw [hx]; split_ifs <;> norm_num
  have hfw2 : f (u + v) * f (u + v) = 1 := hf_val _ hfw
  have heq : f u * f v * f (u + v) = lineSign u v ↔ lineSign u v * f (u + v) = f u * f v := by
    constructor
    · intro h
      calc lineSign u v * f (u + v) = (f u * f v * f (u + v)) * f (u + v) := by rw [h]
        _ = f u * f v * (f (u + v) * f (u + v)) := by ring
        _ = f u * f v := by rw [hfw2, mul_one]
    · intro h
      calc f u * f v * f (u + v) = (lineSign u v * f (u + v)) * f (u + v) := by rw [← h]
        _ = lineSign u v * (f (u + v) * f (u + v)) := by ring
        _ = lineSign u v := by rw [hfw2, mul_one]
  exact not_congr heq

/-- **Proposition 3(b) (satisfied context in the Fubini–Study metric):**
The context is satisfied if and only if `4 |g_{uv}| = | |p_{u+v}| - |p_u p_v| |`. -/
theorem proposition3_satisfied_iff (ψ : Vec N → ℂ) {u v : Pt N} (hcomm : symp u v = 0)
    (hu : pauliExpVal ψ u ≠ 0) (hv : pauliExpVal ψ v ≠ 0) (hw : pauliExpVal ψ (u + v) ≠ 0)
    (f : Pt N → ℝ)
    (hfu : f u = if 0 < pauliExpVal ψ u then 1 else -1)
    (hfv : f v = if 0 < pauliExpVal ψ v then 1 else -1)
    (hfw : f (u + v) = if 0 < pauliExpVal ψ (u + v) then 1 else -1) :
    f u * f v * f (u + v) = lineSign u v ↔
      4 * |fubiniStudyMetric ψ u v| = abs (|pauliExpVal ψ (u + v)| - |pauliExpVal ψ u * pauliExpVal ψ v|) := by
  have hg := (proposition3_commuting_qgt ψ hcomm).1
  have hs := lineSign_eq_one_or_neg_one' hcomm
  have hsne : lineSign u v ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hsabs : |lineSign u v| = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have ha : lineSign u v * pauliExpVal ψ (u + v) ≠ 0 := mul_ne_zero hsne hw
  have hb : pauliExpVal ψ u * pauliExpVal ψ v ≠ 0 := mul_ne_zero hu hv
  have h4g : 4 * |fubiniStudyMetric ψ u v|
      = |lineSign u v * pauliExpVal ψ (u + v) - pauliExpVal ψ u * pauliExpVal ψ v| := by
    rw [hg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; ring
  have hsp : |lineSign u v * pauliExpVal ψ (u + v)| = |pauliExpVal ψ (u + v)| := by
    rw [abs_mul, hsabs, one_mul]
  rw [h4g, ← hsp, abs_sub_eq_abs_sub_iff_mul_pos ha hb]
  have hsign_a : lineSign u v * f (u + v) = if 0 < lineSign u v * pauliExpVal ψ (u + v) then 1 else -1 := by
    rw [hfw]; rcases hs with h | h <;> rw [h] <;> rcases lt_or_gt_of_ne hw with hw' | hw'
    · rw [ite_eq_right (not_lt.mpr (le_of_lt hw')), ite_eq_right (by linarith)]; norm_num
    · rw [ite_eq_left hw', ite_eq_left (by linarith)]; norm_num
    · rw [ite_eq_right (not_lt.mpr (le_of_lt hw')), ite_eq_left (by linarith)]; norm_num
    · rw [ite_eq_left hw', ite_eq_right (by linarith)]; norm_num
  have hsign_b : f u * f v = if 0 < pauliExpVal ψ u * pauliExpVal ψ v then 1 else -1 := by
    rw [hfu, hfv]; rcases lt_or_gt_of_ne hu with hu' | hu' <;> rcases lt_or_gt_of_ne hv with hv' | hv'
    · rw [ite_eq_right (not_lt.mpr (le_of_lt hu')), ite_eq_right (not_lt.mpr (le_of_lt hv')),
        ite_eq_left (mul_pos_of_neg_of_neg hu' hv')]; norm_num
    · rw [ite_eq_right (not_lt.mpr (le_of_lt hu')), ite_eq_left hv',
        ite_eq_right (not_lt.mpr (le_of_lt (mul_neg_of_neg_of_pos hu' hv')))]; norm_num
    · rw [ite_eq_left hu', ite_eq_right (not_lt.mpr (le_of_lt hv')),
        ite_eq_right (not_lt.mpr (le_of_lt (mul_neg_of_pos_of_neg hu' hv')))]; norm_num
    · rw [ite_eq_left hu', ite_eq_left hv', ite_eq_left (mul_pos hu' hv')]; norm_num
  have hiff := (sign_mul_pos_iff ha hb (lineSign u v * f (u + v)) (f u * f v) hsign_a hsign_b).1
  rw [← hiff]
  have hfw2 : f (u + v) * f (u + v) = 1 := by rw [hfw]; split_ifs <;> norm_num
  constructor
  · intro h
    have : f u * f v * (f (u + v) * f (u + v)) = lineSign u v * f (u + v) := by
      linear_combination h * f (u + v)
    rw [hfw2, mul_one] at this; exact this.symm
  · intro h
    calc f u * f v * f (u + v) = (lineSign u v * f (u + v)) * f (u + v) := by rw [← h]
      _ = lineSign u v * (f (u + v) * f (u + v)) := by ring
      _ = lineSign u v := by rw [hfw2, mul_one]

/-- Helper connecting `IsFlatState` to `pauliExpVal`. -/
lemma isFlatState_pauliExpVal {S : Finset (Pt N)} {f : Pt N → ℝ} {ψ : Vec N → ℂ}
    (hflat : IsFlatState S f ψ) :
    (∀ v ∈ S, pauliExpVal ψ v = f v * Real.sqrt (((2 : ℝ) ^ N - 1) / S.card)) ∧
    (∀ v : Pt N, v ≠ 0 → v ∉ S → pauliExpVal ψ v = 0) := by
  constructor
  · intro v hv
    have h1 := hflat.2.1 v hv
    rw [← trace_projMat_mul, trace_projMat_mul_pauli_eq_ofReal] at h1
    exact_mod_cast h1
  · intro v hv0 hvS
    have h1 := hflat.2.2 v hv0 hvS
    rw [← trace_projMat_mul, trace_projMat_mul_pauli_eq_ofReal] at h1
    exact_mod_cast h1

/-- **Proposition 8 (the optimum in the quantum metric and Berry curvature):**
For any flat pure state `ψ` on `S` (`0 ∉ S`) with signs `f : S → {±1}` and modulus
`μ = √((2^N - 1) / |S|)`, for any distinct `u, v ∈ S`:
1. On a violated context of `S`, `|g_{uv}| = (μ + μ²) / 4` and `F_{uv} = 0`.
2. On a satisfied context of `S`, `|g_{uv}| = |μ - μ²| / 4` and `F_{uv} = 0`.
3. Otherwise (anticommuting or `u + v ∉ S`), `|g_{uv}| = μ² / 4`.
4. `|F_{uv}| = μ / 2` if `u, v` anticommute with `u + v ∈ S`, and `F_{uv} = 0` otherwise. -/
theorem proposition8_flat_state_qgt {S : Finset (Pt N)} {f : Pt N → ℝ} {ψ : Vec N → ℂ}
    (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) (hflat : IsFlatState S f ψ)
    {u v : Pt N} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    let μ : ℝ := Real.sqrt (((2 : ℝ) ^ N - 1) / S.card)
    ((symp u v = 0 ∧ u + v ∈ S ∧ f u * f v * f (u + v) ≠ lineSign u v →
        |fubiniStudyMetric ψ u v| = (μ + μ ^ 2) / 4 ∧ berryCurvature ψ u v = 0) ∧
     (symp u v = 0 ∧ u + v ∈ S ∧ f u * f v * f (u + v) = lineSign u v →
        |fubiniStudyMetric ψ u v| = |μ - μ ^ 2| / 4 ∧ berryCurvature ψ u v = 0) ∧
     ((symp u v = 1 ∨ u + v ∉ S) →
        |fubiniStudyMetric ψ u v| = μ ^ 2 / 4) ∧
     (symp u v = 1 ∧ u + v ∈ S → |berryCurvature ψ u v| = μ / 2) ∧
     (symp u v = 0 ∨ u + v ∉ S → berryCurvature ψ u v = 0)) := by
  intro μ
  have hμ0 : 0 ≤ μ := Real.sqrt_nonneg _
  obtain ⟨hpS, hpOut⟩ := isFlatState_pauliExpVal hflat
  have hpu : pauliExpVal ψ u = f u * μ := hpS u hu
  have hpv : pauliExpVal ψ v = f v * μ := hpS v hv
  have huv0 : u + v ≠ 0 := by
    intro h0; apply huv
    calc u = u + (v + v) := by rw [pt_add_self, add_zero]
      _ = (u + v) + v := by abel
      _ = v := by rw [h0, zero_add]
  have hf_abs : ∀ w ∈ S, |f w| = 1 := fun w hw => by
    rcases hf w hw with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hcomm, huvS, hviol⟩
    obtain ⟨hg, hb⟩ := proposition3_commuting_qgt ψ hcomm
    refine ⟨?_, hb⟩
    have hpw : pauliExpVal ψ (u + v) = f (u + v) * μ := hpS (u + v) huvS
    have hs := lineSign_eq_one_or_neg_one' hcomm
    have hneg : lineSign u v = -(f u * f v * f (u + v)) := by
      rcases hf u hu with h1 | h1 <;> rcases hf v hv with h2 | h2 <;>
      rcases hf (u + v) huvS with h3 | h3 <;> rcases hs with h4 | h4 <;>
      rw [h1, h2, h3, h4] at hviol ⊢ <;>
      first | (norm_num; done) | (exfalso; apply hviol; norm_num)
    have hfw2 : f (u + v) * f (u + v) = 1 := by
      rcases hf (u + v) huvS with h | h <;> rw [h] <;> norm_num
    rw [hg, hpu, hpv, hpw, hneg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    congr 1
    have hrew : -(f u * f v * f (u + v)) * (f (u + v) * μ) - f u * μ * (f v * μ)
        = -(f u * f v) * (μ + μ ^ 2) := by
      calc -(f u * f v * f (u + v)) * (f (u + v) * μ) - f u * μ * (f v * μ)
          = -(f u * f v) * (f (u + v) * f (u + v)) * μ - (f u * f v) * μ ^ 2 := by ring
        _ = -(f u * f v) * 1 * μ - (f u * f v) * μ ^ 2 := by rw [hfw2]
        _ = -(f u * f v) * (μ + μ ^ 2) := by ring
    rw [hrew, abs_mul, abs_neg, abs_mul, hf_abs u hu, hf_abs v hv, one_mul, one_mul,
      abs_of_nonneg (by positivity)]
  · rintro ⟨hcomm, huvS, hsat⟩
    obtain ⟨hg, hb⟩ := proposition3_commuting_qgt ψ hcomm
    refine ⟨?_, hb⟩
    have hpw : pauliExpVal ψ (u + v) = f (u + v) * μ := hpS (u + v) huvS
    rw [hg, hpu, hpv, hpw, ← hsat, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    congr 1
    have hfw2 : f (u + v) * f (u + v) = 1 := by
      rcases hf (u + v) huvS with h | h <;> rw [h] <;> norm_num
    have hrew : f u * f v * f (u + v) * (f (u + v) * μ) - f u * μ * (f v * μ)
        = (f u * f v) * (μ - μ ^ 2) := by
      calc f u * f v * f (u + v) * (f (u + v) * μ) - f u * μ * (f v * μ)
          = f u * f v * (f (u + v) * f (u + v)) * μ - f u * f v * μ ^ 2 := by ring
        _ = f u * f v * 1 * μ - f u * f v * μ ^ 2 := by rw [hfw2]
        _ = (f u * f v) * (μ - μ ^ 2) := by ring
    rw [hrew, abs_mul, abs_mul, hf_abs u hu, hf_abs v hv, one_mul, one_mul]
  · intro hor
    rcases hor with hanti | hout
    · have hg := (anticommuting_qgt ψ hanti).1
      rw [hg, hpu, hpv, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      congr 1
      rw [show f u * μ * (f v * μ) = (f u * f v) * μ ^ 2 by ring, abs_mul, abs_mul,
        hf_abs u hu, hf_abs v hv, one_mul, one_mul, abs_of_nonneg (sq_nonneg μ)]
    · rcases zmod2_cases (symp u v) with hcomm | hanti
      · have hg := (proposition3_commuting_qgt ψ hcomm).1
        have hpw : pauliExpVal ψ (u + v) = 0 := hpOut (u + v) huv0 hout
        rw [hg, hpu, hpv, hpw, mul_zero, zero_sub, abs_div, abs_neg,
          abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        congr 1
        rw [show f u * μ * (f v * μ) = (f u * f v) * μ ^ 2 by ring, abs_mul, abs_mul,
          hf_abs u hu, hf_abs v hv, one_mul, one_mul, abs_of_nonneg (sq_nonneg μ)]
      · have hg := (anticommuting_qgt ψ hanti).1
        rw [hg, hpu, hpv, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        congr 1
        rw [show f u * μ * (f v * μ) = (f u * f v) * μ ^ 2 by ring, abs_mul, abs_mul,
          hf_abs u hu, hf_abs v hv, one_mul, one_mul, abs_of_nonneg (sq_nonneg μ)]
  · rintro ⟨hanti, huvS⟩
    have hb := (anticommuting_qgt ψ hanti).2
    rw [hb, hpS (u + v) huvS, abs_mul, hf_abs (u + v) huvS, one_mul, abs_of_nonneg hμ0]
  · intro hor
    rcases hor with hcomm | hout
    · exact (proposition3_commuting_qgt ψ hcomm).2
    · rcases zmod2_cases (symp u v) with hcomm | hanti
      · exact (proposition3_commuting_qgt ψ hcomm).2
      · have hb := (anticommuting_qgt ψ hanti).2
        rw [hpOut (u + v) huv0 hout, abs_zero, zero_div] at hb
        exact abs_eq_zero.mp hb

end QuantumGeometry

/-! ### Part 3. Two-Character Set & Hyperplane Intersections (Proposition 10) -/

section TwoCharacter

variable {N : ℕ}

/-- **Pure-state symplectic Walsh–Hadamard identity:**
For every unit vector `ψ : Vec N → ℂ` and every `w : Pt N`,
`2^N · p_w² = ∑_{v : Pt N} (-1)^{⟨v, w⟩} p_v²`, where `p_v = ⟨ψ | P_v | ψ⟩`. -/
theorem pure_state_pauli_sq_transform {ψ : Vec N → ℂ}
    (_hψ : ∑ x : Vec N, Complex.normSq (ψ x) = 1) (w : Pt N) :
    (2 : ℝ) ^ N * pauliExpVal ψ w ^ 2 =
      ∑ v : Pt N, (if symp v w = 0 then (1 : ℝ) else -1) * pauliExpVal ψ v ^ 2 := by
  have hρ_exp : ((2 : ℂ) ^ N) • projMat ψ = ∑ v : Pt N, (pauliExpVal ψ v : ℂ) • pauli v := by
    rw [matrix_eq_sum_pauli (projMat ψ)]
    refine Finset.sum_congr rfl fun v _ => by rw [trace_projMat_mul_pauli_eq_ofReal]
  have htr_rank1 : (projMat ψ * pauli w * projMat ψ * pauli w).trace
      = (pauliExpVal ψ w : ℂ) ^ 2 := by
    have hmul : projMat ψ * pauli w * projMat ψ = (pauliExpVal ψ w : ℂ) • projMat ψ := by
      ext x y
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, projMat]
      have hrew : (∑ b : Vec N, (∑ a : Vec N, ψ x * star (ψ a) * pauli w a b) * (ψ b * star (ψ y)))
          = (∑ a : Vec N, ∑ b : Vec N, star (ψ a) * pauli w a b * ψ b) * (ψ x * star (ψ y)) := by
        rw [Finset.sum_mul]
        trans (∑ b : Vec N, ∑ a : Vec N, (star (ψ a) * pauli w a b * ψ b) * (ψ x * star (ψ y)))
        · refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => by ring
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_mul]
      rw [hrew]
      have hexp : (∑ a : Vec N, ∑ b : Vec N, star (ψ a) * pauli w a b * ψ b)
          = (pauliExpVal ψ w : ℂ) := by
        rw [← trace_projMat_mul_pauli_eq_ofReal, trace_projMat_mul]
        simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      rw [hexp]
    rw [hmul, Matrix.smul_mul, Matrix.trace_smul, trace_projMat_mul_pauli_eq_ofReal, smul_eq_mul, sq]
  have htr_expand : (((2 : ℂ) ^ N • projMat ψ) * pauli w * ((2 : ℂ) ^ N • projMat ψ) * pauli w).trace
      = (2 : ℂ) ^ N * ∑ v : Pt N, (eps (symp v w)) * (pauliExpVal ψ v : ℂ) ^ 2 := by
    rw [hρ_exp]
    have hconj : (∑ v : Pt N, (pauliExpVal ψ v : ℂ) • pauli v) * pauli w
        = pauli w * ∑ v : Pt N, (eps (symp v w) * (pauliExpVal ψ v : ℂ)) • pauli v := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, pauli_comm w v, symp_comm w v, smul_smul, mul_comm]
    have h1 : (∑ v : Pt N, (pauliExpVal ψ v : ℂ) • pauli v) * pauli w *
          (∑ u : Pt N, (pauliExpVal ψ u : ℂ) • pauli u) * pauli w
        = (∑ v : Pt N, (pauliExpVal ψ v : ℂ) • pauli v) *
          (∑ u : Pt N, (eps (symp u w) * (pauliExpVal ψ u : ℂ)) • pauli u) := by
      calc (∑ v : Pt N, (pauliExpVal ψ v : ℂ) • pauli v) * pauli w *
            (∑ u : Pt N, (pauliExpVal ψ u : ℂ) • pauli u) * pauli w
          = (∑ v : Pt N, (pauliExpVal ψ v : ℂ) • pauli v) *
            (pauli w * ((∑ u : Pt N, (pauliExpVal ψ u : ℂ) • pauli u) * pauli w)) := by
            simp only [Matrix.mul_assoc]
        _ = (∑ v : Pt N, (pauliExpVal ψ v : ℂ) • pauli v) *
            (pauli w * (pauli w * ∑ u : Pt N, (eps (symp u w) * (pauliExpVal ψ u : ℂ)) • pauli u)) := by
            rw [hconj]
        _ = (∑ v : Pt N, (pauliExpVal ψ v : ℂ) • pauli v) *
            (∑ u : Pt N, (eps (symp u w) * (pauliExpVal ψ u : ℂ)) • pauli u) := by
            rw [← Matrix.mul_assoc (pauli w), pauli_mul_self, one_mul]
    rw [h1, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum, Matrix.trace_sum, Finset.sum_eq_single v]
    · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
        trace_pauli_mul, ite_eq_left rfl, smul_eq_mul, smul_eq_mul]
      ring
    · intro u _ huv
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
        trace_pauli_mul, ite_eq_right (Ne.symm huv), smul_zero, smul_zero]
    · intro hv; exact absurd (mem_univ v) hv
  have htr_lhs : (((2 : ℂ) ^ N • projMat ψ) * pauli w * ((2 : ℂ) ^ N • projMat ψ) * pauli w).trace
      = (2 : ℂ) ^ N * ((2 : ℂ) ^ N * (pauliExpVal ψ w : ℂ) ^ 2) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul, htr_rank1, smul_eq_mul, smul_eq_mul]
  have hC : (2 : ℂ) ^ N * (pauliExpVal ψ w : ℂ) ^ 2
      = ∑ v : Pt N, (eps (symp v w)) * (pauliExpVal ψ v : ℂ) ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero N (by norm_num : (2 : ℂ) ≠ 0))
    rw [← htr_lhs, htr_expand]
  have heps : ∀ v : Pt N, eps (symp v w) = ((if symp v w = 0 then (1 : ℝ) else -1 : ℝ) : ℂ) := by
    intro v
    rcases zmod2_cases (symp v w) with h0 | h1
    · simp [h0, eps_zero]
    · have hne : (1 : ZMod 2) ≠ 0 := by decide
      simp [h1, hne, eps_one]
  simp_rw [heps] at hC
  have hC' : (((2 : ℝ) ^ N * pauliExpVal ψ w ^ 2 : ℝ) : ℂ)
      = ((∑ v : Pt N, (if symp v w = 0 then (1 : ℝ) else -1) * pauliExpVal ψ v ^ 2 : ℝ) : ℂ) := by
    push_cast; exact hC
  exact Complex.ofReal_injective hC'

/-- **Proposition 10 (two-character set):**
For any `N ≥ 1`, any nonempty non-identity set `S`, and any pure state `ψ` flat on `S`,
with `D = 2^N`, for every nonzero point `w : Pt N`:
`∑_{v ∈ S} (-1)^{⟨v, w⟩} = D · [w ∈ S] - |S| / (D - 1)`. -/
theorem proposition10_two_character_sum (hN : 1 ≤ N) {S : Finset (Pt N)} (h0 : (0 : Pt N) ∉ S)
    (hne : S.Nonempty) {f : Pt N → ℝ} (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1)
    {ψ : Vec N → ℂ} (hflat : IsFlatState S f ψ) {w : Pt N} (hw : w ≠ 0) :
    ∑ v ∈ S, (if symp v w = 0 then (1 : ℝ) else -1)
      = (if w ∈ S then (2 : ℝ) ^ N else 0) - (S.card : ℝ) / ((2 : ℝ) ^ N - 1) := by
  have hD2 : (2 : ℝ) ≤ (2 : ℝ) ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hDm1 : (0 : ℝ) < (2 : ℝ) ^ N - 1 := by linarith
  have hSpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  obtain ⟨hpS, hpOut⟩ := isFlatState_pauliExpVal hflat
  have hμ2 : (Real.sqrt (((2 : ℝ) ^ N - 1) / S.card)) ^ 2 = ((2 : ℝ) ^ N - 1) / S.card :=
    Real.sq_sqrt (div_nonneg (le_of_lt hDm1) (le_of_lt hSpos))
  have hp2 : ∀ v : Pt N, pauliExpVal ψ v ^ 2 =
      if v = 0 then 1 else if v ∈ S then ((2 : ℝ) ^ N - 1) / S.card else 0 := by
    intro v
    by_cases hv0 : v = 0
    · subst hv0; rw [ite_eq_left rfl, pauliExpVal_zero hflat.1]; norm_num
    · rw [ite_eq_right hv0]
      by_cases hvS : v ∈ S
      · rw [ite_eq_left hvS, hpS v hvS, mul_pow, hμ2]
        rcases hf v hvS with h | h <;> rw [h] <;> norm_num
      · rw [ite_eq_right hvS, hpOut v hv0 hvS]; norm_num
  have htr := pure_state_pauli_sq_transform hflat.1 w
  have hsum : ∑ v : Pt N, (if symp v w = 0 then (1 : ℝ) else -1) * pauliExpVal ψ v ^ 2
      = 1 + (((2 : ℝ) ^ N - 1) / S.card) * ∑ v ∈ S, (if symp v w = 0 then (1 : ℝ) else -1) := by
    rw [← Finset.add_sum_erase univ _ (mem_univ (0 : Pt N))]
    have h0term : (if symp (0 : Pt N) w = 0 then (1 : ℝ) else -1) * pauliExpVal ψ 0 ^ 2 = 1 := by
      have hs0 : symp (0 : Pt N) w = 0 := by simp [symp]
      rw [hs0, ite_eq_left rfl, pauliExpVal_zero hflat.1]; norm_num
    rw [h0term]
    congr 1
    have hsub : S ⊆ univ.erase (0 : Pt N) := fun v hv =>
      Finset.mem_erase.mpr ⟨fun h => h0 (h ▸ hv), mem_univ v⟩
    rw [← Finset.sum_subset hsub]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hv0 : v ≠ 0 := fun h => h0 (h ▸ hv)
      rw [hp2 v, ite_eq_right hv0, ite_eq_left hv]; ring
    · intro v hv hvS
      have hv0 : v ≠ 0 := Finset.ne_of_mem_erase hv
      rw [hp2 v, ite_eq_right hv0, ite_eq_right hvS, mul_zero]
  rw [hsum, hp2 w, ite_eq_right hw] at htr
  have hDm1ne : ((2 : ℝ) ^ N - 1) ≠ 0 := ne_of_gt hDm1
  have hSne : (S.card : ℝ) ≠ 0 := ne_of_gt hSpos
  by_cases hwS : w ∈ S
  · rw [ite_eq_left hwS] at htr ⊢
    field_simp [hDm1ne, hSne] at htr ⊢
    nlinarith
  · rw [ite_eq_right hwS] at htr ⊢
    field_simp [hDm1ne, hSne] at htr ⊢
    nlinarith

/-- **Proposition 10 (hyperplane intersection cardinality):**
Under the same hypotheses, for every `w ≠ 0`, the number of observables in `S` commuting
with `P_w` is `((2^N - 2) |S|) / (2 (2^N - 1)) + (2^N / 2) · [w ∈ S]`. -/
theorem proposition10_hyperplane_card (hN : 1 ≤ N) {S : Finset (Pt N)} (h0 : (0 : Pt N) ∉ S)
    (hne : S.Nonempty) {f : Pt N → ℝ} (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1)
    {ψ : Vec N → ℂ} (hflat : IsFlatState S f ψ) {w : Pt N} (hw : w ≠ 0) :
    ((S.filter fun v => symp v w = 0).card : ℝ)
      = ((2 : ℝ) ^ N - 2) * (S.card : ℝ) / (2 * ((2 : ℝ) ^ N - 1))
        + (if w ∈ S then (2 : ℝ) ^ N / 2 else 0) := by
  have h2char := proposition10_two_character_sum hN h0 hne hf hflat hw
  have hsplit : ∑ v ∈ S, (if symp v w = 0 then (1 : ℝ) else -1)
      = 2 * ((S.filter fun v => symp v w = 0).card : ℝ) - (S.card : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun v => symp v w = 0)]
    have h1 : ∑ v ∈ S.filter (fun v => symp v w = 0), (if symp v w = 0 then (1 : ℝ) else -1)
        = ((S.filter fun v => symp v w = 0).card : ℝ) := by
      rw [Finset.sum_congr rfl fun v hv => ite_eq_left (Finset.mem_filter.mp hv).2,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : ∑ v ∈ S.filter (fun v => ¬ symp v w = 0), (if symp v w = 0 then (1 : ℝ) else -1)
        = -((S.filter fun v => ¬ symp v w = 0).card : ℝ) := by
      rw [Finset.sum_congr rfl fun v hv => ite_eq_right (Finset.mem_filter.mp hv).2,
        Finset.sum_const, nsmul_eq_mul, mul_neg_one]
    have hcard : ((S.filter fun v => symp v w = 0).card : ℝ)
        + ((S.filter fun v => ¬ symp v w = 0).card : ℝ) = (S.card : ℝ) := by
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := S) (fun v => symp v w = 0)
    rw [h1, h2]; linarith
  have hD2 : (2 : ℝ) ≤ (2 : ℝ) ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hDm1ne : ((2 : ℝ) ^ N - 1) ≠ 0 := by linarith
  rw [hsplit] at h2char
  by_cases hwS : w ∈ S <;> simp only [hwS, ↓reduceIte] at h2char ⊢ <;>
    field_simp [hDm1ne] at h2char ⊢ <;> linarith

end TwoCharacter

/-! ### Part 4. Signed-Clifford / Symplectic Orbit Transport -/

section CliffordTransport

open HoggarBound.ConjectureE

variable {N : ℕ}

/-- Any unitary `U` sending `P_v ↦ ν(v) P_{g v}` (`ν(v) ∈ {±1}`) automatically induces a
symplectic bijection `g` preserving `symp`. -/
theorem clifford_preserves_symp (U : Matrix (Vec N) (Vec N) ℂ)
    (_hU1 : U * Uᴴ = 1) (hU2 : Uᴴ * U = 1)
    (g : Pt N ≃ Pt N) (ν : Pt N → ℝ) (hν : ∀ v, ν v = 1 ∨ ν v = -1)
    (hconj : ∀ v : Pt N, U * pauli v * Uᴴ = (ν v : ℂ) • pauli (g v))
    (u v : Pt N) : symp (g u) (g v) = symp u v := by
  have hmul : (U * pauli u * Uᴴ) * (U * pauli v * Uᴴ) = U * (pauli u * pauli v) * Uᴴ := by
    calc (U * pauli u * Uᴴ) * (U * pauli v * Uᴴ)
        = U * pauli u * ((Uᴴ * U) * pauli v) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * (pauli u * pauli v) * Uᴴ := by rw [hU2, one_mul]; simp only [Matrix.mul_assoc]
  have hmul' : (U * pauli v * Uᴴ) * (U * pauli u * Uᴴ) = U * (pauli v * pauli u) * Uᴴ := by
    calc (U * pauli v * Uᴴ) * (U * pauli u * Uᴴ)
        = U * pauli v * ((Uᴴ * U) * pauli u) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * (pauli v * pauli u) * Uᴴ := by rw [hU2, one_mul]; simp only [Matrix.mul_assoc]
  have hcomm1 : ((ν u : ℂ) * (ν v : ℂ)) • (pauli (g u) * pauli (g v))
      = (eps (symp u v) * (ν v : ℂ) * (ν u : ℂ) * eps (symp (g u) (g v))) •
          (pauli (g u) * pauli (g v)) := by
    have h1 : (U * pauli u * Uᴴ) * (U * pauli v * Uᴴ)
        = eps (symp u v) • ((U * pauli v * Uᴴ) * (U * pauli u * Uᴴ)) := by
      rw [hmul, hmul']
      conv_lhs => rw [pauli_comm v u, symp_comm v u]
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hconj u, hconj v, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, smul_smul, smul_smul] at h1
    conv_rhs at h1 => rw [pauli_comm (g u) (g v), smul_smul]
    simpa [mul_assoc, mul_left_comm, mul_comm] using h1
  have htr := congrArg (fun M => (M * (pauli (g v) * pauli (g u))).trace) hcomm1
  have hprod : (pauli (g u) * pauli (g v)) * (pauli (g v) * pauli (g u))
      = (1 : Matrix (Vec N) (Vec N) ℂ) := by
    calc (pauli (g u) * pauli (g v)) * (pauli (g v) * pauli (g u))
        = pauli (g u) * ((pauli (g v) * pauli (g v)) * pauli (g u)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [pauli_mul_self, one_mul, pauli_mul_self]
  rw [Matrix.smul_mul, Matrix.smul_mul, hprod, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul, smul_eq_mul] at htr
  simp only [Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const, Finset.card_univ,
    Nat.cast_pow, Nat.cast_ofNat] at htr
  have hνu : (ν u : ℂ) ≠ 0 := by rcases hν u with h | h <;> rw [h] <;> norm_num
  have hνv : (ν v : ℂ) ≠ 0 := by rcases hν v with h | h <;> rw [h] <;> norm_num
  have h2N : ((2 : ℂ) ^ N) ≠ 0 := pow_ne_zero N (by norm_num)
  have h1eq : (1 : ℂ) = eps (symp u v) * eps (symp (g u) (g v)) := by
    have hfac : (ν u : ℂ) * (ν v : ℂ) * (2 : ℂ) ^ N ≠ 0 :=
      mul_ne_zero (mul_ne_zero hνu hνv) h2N
    apply mul_right_cancel₀ hfac
    linear_combination htr
  rcases zmod2_cases (symp (g u) (g v)) with h1 | h1 <;>
  rcases zmod2_cases (symp u v) with h2 | h2 <;>
  rw [h1, h2] at h1eq ⊢
  · exfalso; simp [eps_zero, eps_one] at h1eq; norm_num at h1eq
  · exfalso; simp [eps_zero, eps_one] at h1eq; norm_num at h1eq

/-- On any commuting pair `u, v`, a signed Clifford unitary preserves addition (`g(u + v) = g u + g v`)
and transports the context sign by `lineSign (g u) (g v) = ν(u) ν(v) ν(u + v) lineSign u v`. -/
theorem clifford_transport_comm_product (U : Matrix (Vec N) (Vec N) ℂ)
    (hU1 : U * Uᴴ = 1) (hU2 : Uᴴ * U = 1)
    (g : Pt N ≃ Pt N) (ν : Pt N → ℝ) (hν : ∀ v, ν v = 1 ∨ ν v = -1)
    (hconj : ∀ v : Pt N, U * pauli v * Uᴴ = (ν v : ℂ) • pauli (g v))
    {u v : Pt N} (hcomm : symp u v = 0) :
    g (u + v) = g u + g v ∧
    lineSign (g u) (g v) = ν u * ν v * ν (u + v) * lineSign u v := by
  have hcomm' : symp (g u) (g v) = 0 := by
    rw [clifford_preserves_symp U hU1 hU2 g ν hν hconj u v, hcomm]
  have hprod : ((ν u : ℂ) * (ν v : ℂ) * (lineSign (g u) (g v) : ℂ)) • pauli (g u + g v)
      = ((lineSign u v : ℂ) * (ν (u + v) : ℂ)) • pauli (g (u + v)) := by
    calc ((ν u : ℂ) * (ν v : ℂ) * (lineSign (g u) (g v) : ℂ)) • pauli (g u + g v)
        = ((ν u : ℂ) • pauli (g u)) * ((ν v : ℂ) • pauli (g v)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, pauli_mul, tau_eq_lineSign hcomm', smul_smul, smul_smul]
      _ = (U * pauli u * Uᴴ) * (U * pauli v * Uᴴ) := by rw [← hconj u, ← hconj v]
      _ = U * (pauli u * pauli v) * Uᴴ := by
          calc (U * pauli u * Uᴴ) * (U * pauli v * Uᴴ)
              = U * pauli u * ((Uᴴ * U) * pauli v) * Uᴴ := by simp only [Matrix.mul_assoc]
            _ = U * (pauli u * pauli v) * Uᴴ := by rw [hU2, one_mul]; simp only [Matrix.mul_assoc]
      _ = ((lineSign u v : ℂ) * (ν (u + v) : ℂ)) • pauli (g (u + v)) := by
          rw [pauli_mul, tau_eq_lineSign hcomm, Matrix.mul_smul, Matrix.smul_mul, hconj (u + v),
            smul_smul]
  have htr := congrArg (fun M => (M * pauli (g (u + v))).trace) hprod
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul,
    trace_pauli_mul, trace_pauli_mul, ite_eq_left rfl, smul_eq_mul, smul_eq_mul] at htr
  have hν_sq : ∀ w : Pt N, ν w * ν w = 1 := fun w => by
    rcases hν w with h | h <;> rw [h] <;> norm_num
  have hls_ne : (lineSign u v : ℂ) ≠ 0 := by
    have h2 := tau_sq u v
    rw [tau_eq_lineSign hcomm, hcomm, eps_zero] at h2
    intro hz; rw [hz] at h2; norm_num at h2
  have hνuv_ne : (ν (u + v) : ℂ) ≠ 0 := by rcases hν (u + v) with h | h <;> rw [h] <;> norm_num
  have h2N : ((2 : ℂ) ^ N) ≠ 0 := pow_ne_zero N (by norm_num)
  have hadd : g (u + v) = g u + g v := by
    by_contra hne
    rw [ite_eq_right (Ne.symm hne), mul_zero] at htr
    exact mul_ne_zero (mul_ne_zero hls_ne hνuv_ne) h2N htr.symm
  refine ⟨hadd, ?_⟩
  rw [hadd, ite_eq_left rfl] at htr
  have hC : (ν u : ℂ) * (ν v : ℂ) * (lineSign (g u) (g v) : ℂ)
      = (lineSign u v : ℂ) * (ν (u + v) : ℂ) := mul_right_cancel₀ h2N htr
  have hR : ν u * ν v * lineSign (g u) (g v) = lineSign u v * ν (u + v) := by exact_mod_cast hC
  calc lineSign (g u) (g v)
      = (ν u * ν u) * (ν v * ν v) * lineSign (g u) (g v) := by rw [hν_sq u, hν_sq v]; ring
    _ = ν u * ν v * (ν u * ν v * lineSign (g u) (g v)) := by ring
    _ = ν u * ν v * (lineSign u v * ν (u + v)) := by rw [hR]
    _ = ν u * ν v * ν (u + v) * lineSign u v := by ring

/-- Transported sign carrier `σ'(v) = ν(g⁻¹ v) · σ(g⁻¹ v)`. -/
def transportCarrier (g : Pt N ≃ Pt N) (ν : Pt N → ℝ) (σ : Pt N → ℝ) (v : Pt N) : ℝ :=
  ν (g.symm v) * σ (g.symm v)

lemma transportCarrier_values (g : Pt N ≃ Pt N) (ν : Pt N → ℝ) (hν : ∀ v, ν v = 1 ∨ ν v = -1)
    {σ : Pt N → ℝ} (hσ : ∀ s, σ s = 1 ∨ σ s = -1) (v : Pt N) :
    transportCarrier g ν σ v = 1 ∨ transportCarrier g ν σ v = -1 := by
  unfold transportCarrier
  rcases hν (g.symm v) with h1 | h1 <;> rcases hσ (g.symm v) with h2 | h2 <;>
    rw [h1, h2] <;> norm_num

/-- **Clifford transport of carrier operators:**
`A_{σ'} = U A_σ Uᴴ`, hence `(A_{σ'}).charpoly = (A_σ).charpoly`. -/
theorem clifford_transport_opA (U : Matrix (Vec N) (Vec N) ℂ)
    (hU1 : U * Uᴴ = 1) (hU2 : Uᴴ * U = 1)
    (g : Pt N ≃ Pt N) (ν : Pt N → ℝ) (hν : ∀ v, ν v = 1 ∨ ν v = -1)
    (hconj : ∀ v : Pt N, U * pauli v * Uᴴ = (ν v : ℂ) • pauli (g v))
    (X : Finset (Pt N)) (d : Pt N) (σ : Pt N → ℝ) :
    opA (sectionOf (X.image g) (g d)) (transportCarrier g ν σ)
      = U * opA (sectionOf X d) σ * Uᴴ := by
  have hsec : sectionOf (X.image g) (g d) = (sectionOf X d).image g := by
    ext v
    simp only [sectionOf, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hcomm⟩
      rw [clifford_preserves_symp U hU1 hU2 g ν hν hconj u d] at hcomm
      exact ⟨u, ⟨hu, hcomm⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hcomm⟩, rfl⟩
      exact ⟨⟨u, hu, rfl⟩, by rw [clifford_preserves_symp U hU1 hU2 g ν hν hconj u d, hcomm]⟩
  rw [hsec, opA, opA, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_image (fun a _ b _ h => g.injective h)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, hconj s, smul_smul, transportCarrier, g.symm_apply_apply]
  push_cast; congr 1; ring

theorem clifford_transport_carrier_charpoly (U : Matrix (Vec N) (Vec N) ℂ)
    (hU1 : U * Uᴴ = 1) (hU2 : Uᴴ * U = 1)
    (g : Pt N ≃ Pt N) (ν : Pt N → ℝ) (hν : ∀ v, ν v = 1 ∨ ν v = -1)
    (hconj : ∀ v : Pt N, U * pauli v * Uᴴ = (ν v : ℂ) • pauli (g v))
    (X : Finset (Pt N)) (d : Pt N) (σ : Pt N → ℝ) :
    (opA (sectionOf (X.image g) (g d)) (transportCarrier g ν σ)).charpoly
      = (opA (sectionOf X d) σ).charpoly := by
  rw [clifford_transport_opA U hU1 hU2 g ν hν hconj X d σ,
    Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU2, one_mul]

/-- **Clifford transport of completion matrices:**
`(Λ_{σ'})` is orthogonally similar (via a signed permutation) to `Λ_σ`, so they have the
exact same characteristic polynomial. -/
theorem clifford_transport_completion_charpoly (U : Matrix (Vec N) (Vec N) ℂ)
    (hU1 : U * Uᴴ = 1) (hU2 : Uᴴ * U = 1)
    (g : Pt N ≃ Pt N) (ν : Pt N → ℝ) (hν : ∀ v, ν v = 1 ∨ ν v = -1)
    (hconj : ∀ v : Pt N, U * pauli v * Uᴴ = (ν v : ℂ) • pauli (g v))
    (X : Finset (Pt N)) (d : Pt N) (σ : Pt N → ℝ) :
    (completionMat (X.image g) (g d) (transportCarrier g ν σ)).charpoly
      = (completionMat X d σ).charpoly := by
  have hout : outsideOf (X.image g) (g d) = (outsideOf X d).image g := by
    ext v
    simp only [outsideOf, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hanti⟩
      rw [clifford_preserves_symp U hU1 hU2 g ν hν hconj u d] at hanti
      exact ⟨u, ⟨hu, hanti⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hanti⟩, rfl⟩
      exact ⟨⟨u, hu, rfl⟩, by rw [clifford_preserves_symp U hU1 hU2 g ν hν hconj u d, hanti]⟩
  have hmem_inv : ∀ v : Pt N, v ∈ outsideOf (X.image g) (g d) → g.symm v ∈ outsideOf X d := by
    intro v hv
    rw [hout] at hv
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hv
    have : g.symm v = u := by rw [← heq, g.symm_apply_apply]
    rwa [this]
  let e : {p // p ∈ outsideOf X d} ≃ {p // p ∈ outsideOf (X.image g) (g d)} :=
    { toFun := fun p => ⟨g p.1, by rw [hout]; exact Finset.mem_image_of_mem g p.2⟩
      invFun := fun q => ⟨g.symm q.1, hmem_inv q.1 q.2⟩
      left_inv := fun p => Subtype.ext (g.symm_apply_apply p.1)
      right_inv := fun q => Subtype.ext (g.apply_symm_apply q.1) }
  have hre : (completionMat (X.image g) (g d) (transportCarrier g ν σ)).charpoly
      = (Matrix.reindex e.symm e.symm
          (completionMat (X.image g) (g d) (transportCarrier g ν σ))).charpoly :=
    (Matrix.charpoly_reindex e.symm _).symm
  rw [hre]
  let D : Matrix {p // p ∈ outsideOf X d} {p // p ∈ outsideOf X d} ℝ :=
    Matrix.diagonal fun p => ν p.1
  have hDsq : D * D = 1 := by
    ext p q
    simp only [D, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases h : p = q
    · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
      rcases hν p.1 with h1 | h1 <;> rw [h1] <;> norm_num
    · rw [ite_eq_right h, ite_eq_right h]
  have hsim : Matrix.reindex e.symm e.symm
        (completionMat (X.image g) (g d) (transportCarrier g ν σ))
      = D * completionMat X d σ * D := by
    ext q p
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      D, Matrix.diagonal_mul, Matrix.mul_diagonal, completionMat]
    have hcomm_iff : symp (g q.1) (g p.1) = 0 ↔ symp q.1 p.1 = 0 := by
      rw [clifford_preserves_symp U hU1 hU2 g ν hν hconj q.1 p.1]
    have hne_iff : g q.1 ≠ g p.1 ↔ q.1 ≠ p.1 := not_congr g.injective.eq_iff
    by_cases h : q.1 ≠ p.1 ∧ symp q.1 p.1 = 0
    · have hgcond : (e q).1 ≠ (e p).1 ∧ symp (e q).1 (e p).1 = 0 :=
        ⟨hne_iff.mpr h.1, hcomm_iff.mpr h.2⟩
      rw [ite_eq_left hgcond, ite_eq_left h]
      obtain ⟨hadd, _⟩ := clifford_transport_comm_product U hU1 hU2 g ν hν hconj h.2
      have hcomm_add : symp (q.1 + p.1) p.1 = 0 := by
        rw [symp_comm, symp_add_right, symp_self, add_zero, symp_comm, h.2]
      obtain ⟨_, hls2⟩ := clifford_transport_comm_product U hU1 hU2 g ν hν hconj hcomm_add
      have he_add : (e q).1 + (e p).1 = g (q.1 + p.1) := hadd.symm
      change lineSign ((e q).1 + (e p).1) (e p).1 * transportCarrier g ν σ ((e q).1 + (e p).1)
        = ν q.1 * (lineSign (q.1 + p.1) p.1 * σ (q.1 + p.1)) * ν p.1
      rw [he_add, show (e p).1 = g p.1 from rfl, hls2, transportCarrier, g.symm_apply_apply]
      have hqp_p : q.1 + p.1 + p.1 = q.1 := by rw [add_assoc, pt_add_self, add_zero]
      rw [hqp_p]
      have hνsq : ∀ w : Pt N, ν w * ν w = 1 := fun w => by
        rcases hν w with h1 | h1 <;> rw [h1] <;> norm_num
      calc ν (q.1 + p.1) * ν p.1 * ν q.1 * lineSign (q.1 + p.1) p.1 * (ν (q.1 + p.1) * σ (q.1 + p.1))
          = (ν (q.1 + p.1) * ν (q.1 + p.1)) * (ν q.1 * (lineSign (q.1 + p.1) p.1 * σ (q.1 + p.1)) * ν p.1) := by ring
        _ = ν q.1 * (lineSign (q.1 + p.1) p.1 * σ (q.1 + p.1)) * ν p.1 := by rw [hνsq, one_mul]
    · have hgcond : ¬ ((e q).1 ≠ (e p).1 ∧ symp (e q).1 (e p).1 = 0) := fun hh =>
        h ⟨hne_iff.mp hh.1, hcomm_iff.mp hh.2⟩
      rw [ite_eq_right hgcond, ite_eq_right h, mul_zero, zero_mul]
  rw [hsim, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hDsq, one_mul]

/-- **Clifford orbit transport of strict-law failure:**
If a canonical hyperplane representative `(X, d)` admits cospectral `±1`-valued carriers
with unequal completion characteristic polynomials, then every Clifford image `(X.image g, g d)`
admits such a pair as well. -/
theorem clifford_transport_strict_law_fails (U : Matrix (Vec N) (Vec N) ℂ)
    (hU1 : U * Uᴴ = 1) (hU2 : Uᴴ * U = 1)
    (g : Pt N ≃ Pt N) (ν : Pt N → ℝ) (hν : ∀ v, ν v = 1 ∨ ν v = -1)
    (hconj : ∀ v : Pt N, U * pauli v * Uᴴ = (ν v : ℂ) • pauli (g v))
    (X : Finset (Pt N)) (d : Pt N)
    (hfail : ∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly) :
    ∃ σ' τ' : Pt N → ℝ, (∀ s, σ' s = 1 ∨ σ' s = -1) ∧ (∀ s, τ' s = 1 ∨ τ' s = -1) ∧
      (opA (sectionOf (X.image g) (g d)) σ').charpoly
        = (opA (sectionOf (X.image g) (g d)) τ').charpoly ∧
      (completionMat (X.image g) (g d) σ').charpoly
        ≠ (completionMat (X.image g) (g d) τ').charpoly := by
  obtain ⟨σ, τ, hσ, hτ, hA, hL⟩ := hfail
  refine ⟨transportCarrier g ν σ, transportCarrier g ν τ,
    transportCarrier_values g ν hν hσ, transportCarrier_values g ν hν hτ, ?_, ?_⟩
  · rw [clifford_transport_carrier_charpoly U hU1 hU2 g ν hν hconj X d σ,
      clifford_transport_carrier_charpoly U hU1 hU2 g ν hν hconj X d τ, hA]
  · rw [clifford_transport_completion_charpoly U hU1 hU2 g ν hν hconj X d σ,
      clifford_transport_completion_charpoly U hU1 hU2 g ν hν hconj X d τ]
    exact hL

end CliffordTransport

/-! ### Part 5. Eigenvalue-Multiset Level Conjecture E Across All Nine Cases (`N ≥ 4`) -/

section SpectralUpgrade

open HoggarBound.ConjectureE

/-- Every real symmetric completion matrix `completionMat X d σ` is Hermitian. -/
theorem completionMat_isHermitian {N : ℕ} (X : Finset (Pt N)) (d : Pt N) (σ : Pt N → ℝ) :
    (completionMat X d σ).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact completionMat_transpose X d σ

/-- For real Hermitian matrices, equal characteristic polynomials are equivalent to equal
real eigenvalue multisets (roots with multiplicities). -/
theorem real_hermitian_charpoly_eq_iff_roots_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A.charpoly = B.charpoly ↔ A.charpoly.roots = B.charpoly.roots := by
  constructor
  · intro h; rw [h]
  · intro h
    conv_lhs => rw [hA.splits_charpoly.eq_prod_roots_of_monic A.charpoly_monic]
    conv_rhs => rw [hB.splits_charpoly.eq_prod_roots_of_monic B.charpoly_monic]
    rw [h]

/-- Upgrade any charpoly-level counterexample `(X, d)` to full spectral form:
equal canonical real Hermitian carrier eigenvalue lists, unequal completion characteristic
polynomials, unequal canonical real completion eigenvalue lists, and unequal real
completion eigenvalue multisets with multiplicities. -/
theorem strict_law_fails_to_spectra {N : ℕ} (X : Finset (Pt N)) (d : Pt N)
    (hfail : ∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly) :
    ∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (opA_isHermitian (sectionOf X d) σ).eigenvalues
        = (opA_isHermitian (sectionOf X d) τ).eigenvalues ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly ∧
      (completionMat_isHermitian X d σ).eigenvalues
        ≠ (completionMat_isHermitian X d τ).eigenvalues ∧
      (completionMat X d σ).charpoly.roots ≠ (completionMat X d τ).charpoly.roots := by
  obtain ⟨σ, τ, hσ, hτ, hA, hL⟩ := hfail
  refine ⟨σ, τ, hσ, hτ, hA, ?_, hL, ?_, ?_⟩
  · exact ((opA_isHermitian (sectionOf X d) σ).eigenvalues_eq_eigenvalues_iff
      (opA_isHermitian (sectionOf X d) τ)).2 hA
  · intro hev
    exact hL (((completionMat_isHermitian X d σ).eigenvalues_eq_eigenvalues_iff
      (completionMat_isHermitian X d τ)).1 hev)
  · intro hroots
    exact hL ((real_hermitian_charpoly_eq_iff_roots_eq
      (completionMat_isHermitian X d σ) (completionMat_isHermitian X d τ)).2 hroots)

/-- Predicate asserting full spectral strict-law failure on `(X, d)` with multiplicities. -/
def StrictLawFailsSpectra {N : ℕ} (X : Finset (Pt N)) (d : Pt N) : Prop :=
  ∃ σ τ : Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
    (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
    (opA_isHermitian (sectionOf X d) σ).eigenvalues
      = (opA_isHermitian (sectionOf X d) τ).eigenvalues ∧
    (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly ∧
    (completionMat_isHermitian X d σ).eigenvalues
      ≠ (completionMat_isHermitian X d τ).eigenvalues ∧
    (completionMat X d σ).charpoly.roots ≠ (completionMat X d τ).charpoly.roots

/-- **Theorem 19 (full eigenvalue-multiset form across all nine vertex cases, `N ≥ 4`):**
For every `N ≥ 4` and every one of Jonah's nine vertex cases (`C1, C3, C5, C6, C8, C11,
C12, C14, C15`), there exist `±1`-valued sign carriers with identical canonical Hermitian
carrier eigenvalue lists and distinct completion eigenvalue lists and root multisets. -/
theorem jonah_conjecture_e_all_nine_cases_spectra {N : ℕ} (hN : 4 ≤ N) :
    StrictLawFailsSpectra (allPoints N) (ptZ ⟨0, by omega⟩) ∧
    StrictLawFailsSpectra (quadric N 0) (ptZ ⟨0, by omega⟩) ∧
    StrictLawFailsSpectra (quadric N (ptY ⟨1, by omega⟩)) (ptZ ⟨0, by omega⟩) ∧
    StrictLawFailsSpectra (perpSet (allPoints N) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) ∧
    StrictLawFailsSpectra (perpSet (quadric N 0) (ptY ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) ∧
    StrictLawFailsSpectra (perpSet (quadric N 0) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) ∧
    StrictLawFailsSpectra (perpSet (quadric N 0) (ptZ ⟨0, by omega⟩)) (ptY ⟨1, by omega⟩) ∧
    StrictLawFailsSpectra (perpSet (quadric N (ptY ⟨2, by omega⟩)) (ptZ ⟨0, by omega⟩)) (ptZ ⟨1, by omega⟩) ∧
    StrictLawFailsSpectra (perpSet (quadric N (ptY ⟨2, by omega⟩)) (ptZ ⟨0, by omega⟩)) (ptY ⟨1, by omega⟩) := by
  obtain ⟨h1, h3, h5, h6, h8, h11, h12, h14, h15⟩ := jonah_conjecture_e_all_nine_cases hN
  exact ⟨strict_law_fails_to_spectra _ _ h1, strict_law_fails_to_spectra _ _ h3,
    strict_law_fails_to_spectra _ _ h5, strict_law_fails_to_spectra _ _ h6,
    strict_law_fails_to_spectra _ _ h8, strict_law_fails_to_spectra _ _ h11,
    strict_law_fails_to_spectra _ _ h12, strict_law_fails_to_spectra _ _ h14,
    strict_law_fails_to_spectra _ _ h15⟩

end SpectralUpgrade

/-! ### Part 6. Tightened Corollary 16 via Exact QUBO SDP Dual (`330 ≤ F(σ₁, y) ≤ 344` & `347 ≤ F(σ₀, y) ≤ 368`) -/

section TightenedCorollary16

open HoggarBound.C3 HoggarBound.ConjectureE

/-- Geometric zero-sum diagonal shift `16 · d(p)` on the 64 outside points of four-qubit C3,
depending only on `(a₁(p), a₀(p)) = p mod 4`: `-40` on `00`, `+24` on `11`, `+8` on `01, 10`. -/
def c3Shift16 (r : ℕ) : ℤ :=
  match r % 4 with
  | 0 => -40
  | 3 => 24
  | _ => 8

/-- The diagonal `D₁` block of `carrierB` (`signB`). -/
def c3BlockB_D (k : Fin 8) : ℤ :=
  (![3, -5, -1, -1, 3, -5, -1, -1] : Fin 8 → ℤ) k

/-- The four `8 × 8` shifted residual blocks `B_k = 231 I - 8 (C₁ + (D₁)_k I) - diag_i(d₁₆(i ⊕ k))`. -/
def c3SdpBlock (k : Fin 4) : Matrix (Fin 8) (Fin 8) ℤ := fun i j =>
  (if i = j then 231 - 8 * c3BlockB_D ⟨k.val, by omega⟩ - c3Shift16 (Nat.xor i.val k.val) else 0)
    - 8 * c3BlockB i j

/-- Pure-integer fraction-free `L D Lᵀ` certificates for the four `8 × 8` blocks `c3SdpBlock 0..3`. -/
def sdpScale0 : ℤ := 514482260100738982971
def sdpW0 : Fin 8 → ℤ :=
  ![3235737484910308069, 136362151161461, 7180399349, 98266111679241145747461,
    1257637, 13539094890971228238933, 106497827840852969474997, 98266111679241145747461]
def sdpL0 : Matrix (Fin 8) (Fin 8) ℤ := !![
  159, 0, 0, 0, 0, 0, 0, 0;
  -64, 23729, 0, 0, 0, 0, 0, 0;
  -64, -14272, 3019551, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0, 0;
  -64, -14272, -3411008, 0, 135479233, 0, 0, 0;
  0, 0, -1518656, 0, -218304512, 1, 0, 0;
  0, 0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 1]

def sdpScale1 : ℤ := 25914963568192907323325
def sdpW1 : Fin 8 → ℤ :=
  ![148085506103959470419, 3210247482147011, 60108921635, 7022955126980277884621075,
    1614515, 6723074715731810416155875, 6608315709889191367447875, 7022955126980277884621075]
def sdpL1 : Matrix (Fin 8) (Fin 8) ℤ := !![
  175, 0, 0, 0, 0, 0, 0, 0;
  -64, 46129, 0, 0, 0, 0, 0, 0;
  -64, -15296, 9346255, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0, 0;
  -64, -15296, -5368896, 0, 1717397761, 0, 0, 0;
  0, 0, -2952256, 0, -343609344, 1, 0, 0;
  0, 0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 1]

def sdpScale2 : ℤ := 5377628548612118799
def sdpW2 : Fin 8 → ℤ :=
  ![37605794046238593, 14577772598361, 436942649, 1285253223118296392961,
    49800465, 792203013117053723185, 1543379393451678095313, 1285253223118296392961]
def sdpL2 : Matrix (Fin 8) (Fin 8) ℤ := !![
  143, 0, 0, 0, 0, 0, 0, 0;
  -64, 7739, 0, 0, 0, 0, 0, 0;
  -64, -4416, 1590309, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0, 0;
  -64, -4416, -1126080, 0, 3055543, 0, 0, 0;
  0, 0, -495296, 0, -1601536, 1, 0, 0;
  0, 0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 1]

def sdpScale3 : ℤ := 813590682324977243825
def sdpW3 : Fin 8 → ℤ :=
  ![6406225845078560975, 288659750600575, 10745077951, 233500525827268468977775,
    2818511, 20045391670191561484575, 194448173075669561274175, 233500525827268468977775]
def sdpL3 : Matrix (Fin 8) (Fin 8) ℤ := !![
  127, 0, 0, 0, 0, 0, 0, 0;
  -64, 22193, 0, 0, 0, 0, 0, 0;
  -64, -12224, 3411775, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0, 0;
  -64, -12224, -3312704, 0, 84606913, 0, 0, 0;
  0, 0, -1420352, 0, -212013056, 1, 0, 0;
  0, 0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 1]

/-- General positive-definiteness criterion from a pure-integer `L D Lᵀ` certificate
for any `8 × 8` integer matrix `B`. -/
theorem pos_def_of_int_ldlt_mat (B : Matrix (Fin 8) (Fin 8) ℤ)
    (scale : ℤ) (L : Matrix (Fin 8) (Fin 8) ℤ) (W : Fin 8 → ℤ)
    (hscale : 0 < scale) (hL_lo : ∀ i j : Fin 8, i < j → L i j = 0)
    (hL_diag : ∀ i : Fin 8, 0 < L i i) (hW_pos : ∀ k : Fin 8, 0 < W k)
    (hfac : ∀ i j : Fin 8, scale * B i j = ∑ k : Fin 8, W k * L i k * L j k)
    (v : Fin 8 → ℂ) (hv : v ≠ 0) :
    0 < (∑ i : Fin 8, ∑ j : Fin 8, star (v i) * (B i j : ℂ) * v j).re := by
  let w : Fin 8 → ℂ := fun k => ∑ i : Fin 8, (L i k : ℂ) * v i
  have hcomplex : (scale : ℂ) * (∑ i : Fin 8, ∑ j : Fin 8, star (v i) * (B i j : ℂ) * v j)
      = ∑ k : Fin 8, (W k : ℂ) * (star (w k) * w k) := by
    have hrhs : ∑ k : Fin 8, (W k : ℂ) * (star (w k) * w k)
        = ∑ i : Fin 8, ∑ j : Fin 8, star (v i) *
            (∑ k : Fin 8, (W k : ℂ) * (L i k : ℂ) * (L j k : ℂ)) * v j := by
      have hexp : ∀ k : Fin 8, (W k : ℂ) * (star (w k) * w k)
          = ∑ i : Fin 8, ∑ j : Fin 8, star (v i) * ((W k : ℂ) * (L i k : ℂ) * (L j k : ℂ)) * v j := by
        intro k
        dsimp only [w]
        rw [star_sum, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [star_mul', show star (L i k : ℂ) = (L i k : ℂ) by simp]
        ring
      simp_rw [hexp]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hrhs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hfacC : (scale : ℂ) * (B i j : ℂ) = ∑ k : Fin 8, (W k : ℂ) * (L i k : ℂ) * (L j k : ℂ) := by
      exact_mod_cast hfac i j
    rw [← hfacC]; ring
  have hQ_eq : (scale : ℝ) * (∑ i : Fin 8, ∑ j : Fin 8, star (v i) * (B i j : ℂ) * v j).re
      = ∑ k : Fin 8, (W k : ℝ) * ((w k).re ^ 2 + (w k).im ^ 2) := by
    have hre := congrArg Complex.re hcomplex
    have hscaleC : (scale : ℂ) = ((scale : ℝ) : ℂ) := by push_cast; rfl
    rw [hscaleC, Complex.re_ofReal_mul] at hre
    rw [hre, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hWkC : (W k : ℂ) = ((W k : ℝ) : ℂ) := by push_cast; rfl
    rw [hWkC, Complex.re_ofReal_mul]
    congr 1; simp [Complex.mul_re, sq]
  have hne : w ≠ 0 := by
    intro hw0; apply hv
    have hback : ∀ m : ℕ, ∀ i : Fin 8, 7 - i.val < m → v i = 0 := by
      intro m
      induction m with
      | zero => intro i hi; omega
      | succ m ih =>
        intro i hi
        have hwi : w i = 0 := congrFun hw0 i
        have hsum : w i = (L i i : ℂ) * v i + ∑ j ∈ univ.erase i, (L j i : ℂ) * v j := by
          dsimp only [w]; rw [← Finset.add_sum_erase _ _ (mem_univ i)]
        have hrest : ∑ j ∈ univ.erase i, (L j i : ℂ) * v j = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          rcases lt_or_gt_of_ne hji with hlt | hgt
          · rw [hL_lo j i hlt]; simp
          · have hltm : 7 - j.val < m := by have := hgt; omega
            rw [ih j hltm, mul_zero]
        rw [hsum, hrest, add_zero] at hwi
        have hdiag_ne : (L i i : ℂ) ≠ 0 := by
          have : L i i ≠ 0 := ne_of_gt (hL_diag i)
          exact_mod_cast this
        exact (mul_eq_zero.mp hwi).resolve_left hdiag_ne
    funext i; exact hback 8 i (by omega)
  have hex : ∃ k : Fin 8, w k ≠ 0 := by
    by_contra hall; push Not at hall; exact hne (funext hall)
  obtain ⟨k₀, hk₀⟩ := hex
  have hpos : 0 < ∑ k : Fin 8, (W k : ℝ) * ((w k).re ^ 2 + (w k).im ^ 2) := by
    refine Finset.sum_pos' (fun k _ => ?_) ⟨k₀, mem_univ k₀, ?_⟩
    · have hWk : (0 : ℝ) < (W k : ℝ) := by exact_mod_cast hW_pos k
      positivity
    · have hWk : (0 : ℝ) < (W k₀ : ℝ) := by exact_mod_cast hW_pos k₀
      have hnorm : 0 < (w k₀).re ^ 2 + (w k₀).im ^ 2 := by
        by_contra hle; push Not at hle
        have hre0 : (w k₀).re = 0 := by nlinarith [sq_nonneg (w k₀).re, sq_nonneg (w k₀).im]
        have him0 : (w k₀).im = 0 := by nlinarith [sq_nonneg (w k₀).re, sq_nonneg (w k₀).im]
        exact hk₀ (Complex.ext (by simp [hre0]) (by simp [him0]))
      exact mul_pos hWk hnorm
  have hsc : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hscale
  nlinarith

private lemma sdpBlock0_valid :
    0 < sdpScale0 ∧ (∀ i j : Fin 8, i < j → sdpL0 i j = 0) ∧
    (∀ i : Fin 8, 0 < sdpL0 i i) ∧ (∀ k : Fin 8, 0 < sdpW0 k) ∧
    (∀ i j : Fin 8, sdpScale0 * c3SdpBlock 0 i j = ∑ k : Fin 8, sdpW0 k * sdpL0 i k * sdpL0 j k) := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [sdpL0]

private lemma sdpBlock1_valid :
    0 < sdpScale1 ∧ (∀ i j : Fin 8, i < j → sdpL1 i j = 0) ∧
    (∀ i : Fin 8, 0 < sdpL1 i i) ∧ (∀ k : Fin 8, 0 < sdpW1 k) ∧
    (∀ i j : Fin 8, sdpScale1 * c3SdpBlock 1 i j = ∑ k : Fin 8, sdpW1 k * sdpL1 i k * sdpL1 j k) := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [sdpL1]

private lemma sdpBlock2_valid :
    0 < sdpScale2 ∧ (∀ i j : Fin 8, i < j → sdpL2 i j = 0) ∧
    (∀ i : Fin 8, 0 < sdpL2 i i) ∧ (∀ k : Fin 8, 0 < sdpW2 k) ∧
    (∀ i j : Fin 8, sdpScale2 * c3SdpBlock 2 i j = ∑ k : Fin 8, sdpW2 k * sdpL2 i k * sdpL2 j k) := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [sdpL2]

private lemma sdpBlock3_valid :
    0 < sdpScale3 ∧ (∀ i j : Fin 8, i < j → sdpL3 i j = 0) ∧
    (∀ i : Fin 8, 0 < sdpL3 i i) ∧ (∀ k : Fin 8, 0 < sdpW3 k) ∧
    (∀ i j : Fin 8, sdpScale3 * c3SdpBlock 3 i j = ∑ k : Fin 8, sdpW3 k * sdpL3 i k * sdpL3 j k) := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [sdpL3]

/-- All four shifted `8 × 8` blocks `c3SdpBlock 0..3` are strictly positive definite. -/
theorem c3SdpBlock_pos_def (k : Fin 4) (v : Fin 8 → ℂ) (hv : v ≠ 0) :
    0 < (∑ i : Fin 8, ∑ j : Fin 8, star (v i) * (c3SdpBlock k i j : ℂ) * v j).re := by
  fin_cases k
  · exact pos_def_of_int_ldlt_mat (c3SdpBlock 0) sdpScale0 sdpL0 sdpW0
      sdpBlock0_valid.1 sdpBlock0_valid.2.1 sdpBlock0_valid.2.2.1 sdpBlock0_valid.2.2.2.1 sdpBlock0_valid.2.2.2.2 v hv
  · exact pos_def_of_int_ldlt_mat (c3SdpBlock 1) sdpScale1 sdpL1 sdpW1
      sdpBlock1_valid.1 sdpBlock1_valid.2.1 sdpBlock1_valid.2.2.1 sdpBlock1_valid.2.2.2.1 sdpBlock1_valid.2.2.2.2 v hv
  · exact pos_def_of_int_ldlt_mat (c3SdpBlock 2) sdpScale2 sdpL2 sdpW2
      sdpBlock2_valid.1 sdpBlock2_valid.2.1 sdpBlock2_valid.2.2.1 sdpBlock2_valid.2.2.2.1 sdpBlock2_valid.2.2.2.2 v hv
  · exact pos_def_of_int_ldlt_mat (c3SdpBlock 3) sdpScale3 sdpL3 sdpW3
      sdpBlock3_valid.1 sdpBlock3_valid.2.1 sdpBlock3_valid.2.2.1 sdpBlock3_valid.2.2.2.1 sdpBlock3_valid.2.2.2.2 v hv

private lemma c3Shift16_sum_zero_int :
    (∑ i : Fin 64, c3Shift16 (outsideLabel i).val) = 0 := by
  decide +kernel

private lemma c3Shift16_mod4_eq_xor (p : Fin 64) (i j : Fin 8)
    (h : (Fin.castAdd 8 i).val = Nat.xor (Fin.natAdd 8 j).val (xCode (outsideLabel p)).val) :
    c3Shift16 (outsideLabel p).val = c3Shift16 (Nat.xor i.val j.val) := by
  have hmod : (outsideLabel p).val % 4 = (Nat.xor i.val j.val) % 4 := by
    have h4 : i.val % 4 = Nat.xor (j.val % 4) ((outsideLabel p).val % 4) := by
      have hc := congrArg (fun n => n % 4) h
      simp only [Fin.castAdd, Fin.natAdd, xCode] at hc
      have hx : Nat.xor (8 + j.val) ((outsideLabel p).val % 16) % 4
          = Nat.xor ((8 + j.val) % 4) (((outsideLabel p).val % 16) % 4) :=
        Nat.xor_mod_two_pow (n := 2)
      rw [hx] at hc
      have h1 : (8 + j.val) % 4 = j.val % 4 := by omega
      have h2 : ((outsideLabel p).val % 16) % 4 = (outsideLabel p).val % 4 := by omega
      rw [h1, h2] at hc
      exact hc
    have hxij : (Nat.xor i.val j.val) % 4 = Nat.xor (i.val % 4) (j.val % 4) :=
      Nat.xor_mod_two_pow (n := 2)
    rw [hxij, h4]
    have hfin4 : ∀ a b : Fin 4, b.val = Nat.xor (Nat.xor a.val b.val) a.val := by decide +kernel
    exact hfin4 ⟨j.val % 4, Nat.mod_lt _ (by norm_num)⟩ ⟨(outsideLabel p).val % 4, Nat.mod_lt _ (by norm_num)⟩
  unfold c3Shift16
  rw [hmod]

private lemma realPauliCode_outside_off (i : Fin 64) (a b : Fin 16)
    (h : (a.val < 8 ↔ b.val < 8)) : realPauliCode (outsideLabel i) a b = 0 := by
  have hout_bit3 : (xCode (outsideLabel i)).val.testBit 3 = true := by
    have hmem : outsideLabel i ∈ outsideCodes := by
      rw [← outside_labels_complete]; exact Finset.mem_image_of_mem _ (mem_univ i)
    have hb : (outsideLabel i).val.testBit 3 = true := (Finset.mem_filter.mp hmem).2
    have hmod : (outsideLabel i).val % 2 ^ 4 = (xCode (outsideLabel i)).val := rfl
    rw [← hmod, Nat.testBit_mod_two_pow]
    simp [hb]
  have hfin16_bit3 : ∀ x : Fin 16, x.val.testBit 3 = decide (8 ≤ x.val) := by decide +kernel
  unfold realPauliCode
  rw [ite_eq_right]
  intro heq
  have hbit : a.val.testBit 3 = (b.val ^^^ (xCode (outsideLabel i)).val).testBit 3 :=
    congrArg (fun n : ℕ => n.testBit 3) heq
  rw [Nat.testBit_xor, hout_bit3, hfin16_bit3 a, hfin16_bit3 b] at hbit
  by_cases ha : a.val < 8
  · have hb : b.val < 8 := h.mp ha
    simp [not_le.mpr ha, not_le.mpr hb] at hbit
  · have hb : ¬ b.val < 8 := fun hh => ha (h.mpr hh)
    simp [not_lt.mp ha, not_lt.mp hb] at hbit

/-- Local copy of the 16×16 binary outside operator `T₁₆(y) = ∑_p y_p P_p` and shifted
operator `T̃₁₆(y) = ∑_p d₁₆(p) y_p P_p`. -/
noncomputable def c3T16 (y : Fin 64 → ℝ) : Matrix (Fin 16) (Fin 16) ℂ :=
  ∑ i : Fin 64, (y i : ℂ) • (realPauliCode (outsideLabel i)).map (Int.castRingHom ℂ)

noncomputable def c3T16Shift (y : Fin 64 → ℝ) : Matrix (Fin 16) (Fin 16) ℂ :=
  ∑ i : Fin 64, ((c3Shift16 (outsideLabel i).val : ℂ) * (y i : ℂ)) •
    (realPauliCode (outsideLabel i)).map (Int.castRingHom ℂ)

noncomputable def c3A16 (f : Fin 256 → ℤ) : Matrix (Fin 16) (Fin 16) ℂ :=
  (carrierOf f).map (Int.castRingHom ℂ)

private lemma c3T16_eq_reindex (y : Fin 64 → ℝ) :
    c3T16 y = Matrix.reindex (Equiv.ofBijective bits bits_bijective).symm
      (Equiv.ofBijective bits bits_bijective).symm
      (∑ i : Fin 64, (y i : ℂ) • pauli (codePoint (outsideLabel i))) := by
  ext a b
  simp only [c3T16, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Int.coe_castRingHom,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmem : outsideLabel i ∈ outsideCodes := by
    rw [← outside_labels_complete]; exact Finset.mem_image_of_mem _ (mem_univ i)
  have heven : bitCount4 (Nat.land (xCode (outsideLabel i)).val (zCode (outsideLabel i)).val) % 2 = 0 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2.2
  rw [realPauliCode_cast (outsideLabel i) heven a b]
  rfl

private lemma c3T16Shift_eq_reindex (y : Fin 64 → ℝ) :
    c3T16Shift y = Matrix.reindex (Equiv.ofBijective bits bits_bijective).symm
      (Equiv.ofBijective bits bits_bijective).symm
      (∑ i : Fin 64, ((c3Shift16 (outsideLabel i).val : ℂ) * (y i : ℂ)) •
        pauli (codePoint (outsideLabel i))) := by
  ext a b
  simp only [c3T16Shift, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Int.coe_castRingHom,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmem : outsideLabel i ∈ outsideCodes := by
    rw [← outside_labels_complete]; exact Finset.mem_image_of_mem _ (mem_univ i)
  have heven : bitCount4 (Nat.land (xCode (outsideLabel i)).val (zCode (outsideLabel i)).val) % 2 = 0 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2.2
  rw [realPauliCode_cast (outsideLabel i) heven a b]
  rfl

private lemma c3A16_eq_reindex (f : Fin 256 → ℤ) :
    c3A16 f = Matrix.reindex (Equiv.ofBijective bits bits_bijective).symm
      (Equiv.ofBijective bits bits_bijective).symm
      (∑ v ∈ sectionCodes, (f v : ℂ) • pauli (codePoint v)) := by
  have hsec_even : ∀ v ∈ sectionCodes,
      bitCount4 (Nat.land (xCode v).val (zCode v).val) % 2 = 0 := fun v hv =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.2
  ext a b
  simp only [c3A16, carrierOf, Matrix.map_apply, Int.coe_castRingHom, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [realPauliCode_cast v (hsec_even v hv)]
  rfl

private lemma trace_reindex_symm_eq {α β R : Type*} [Fintype α] [Fintype β] [AddCommMonoid R]
    (e : α ≃ β) (M : Matrix α α R) : (Matrix.reindex e e M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

private lemma reindex_mul_symm {α β R : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Semiring R] (e : α ≃ β) (A B : Matrix α α R) :
    Matrix.reindex e e A * Matrix.reindex e e B = Matrix.reindex e e (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun k => A (e.symm i) k * B k (e.symm j))

/-- **Exact vanishing of the geometric diagonal shift on every binary vector `y ∈ {±1}^64`:**
`∑_j ∑_i d₁₆(i ⊕ j) · |M_{i,j}|² = 0`. -/
theorem c3_shift_quad_zero (y : Fin 64 → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) :
    let M : Matrix (Fin 8) (Fin 8) ℂ := fun i j => c3T16 y (Fin.castAdd 8 i) (Fin.natAdd 8 j)
    ∑ k : Fin 8, ∑ i : Fin 8,
      (c3Shift16 (Nat.xor i.val k.val) : ℝ) * (star (M i k) * M i k).re = 0 := by
  intro M
  have htr0 : (c3T16 y * c3T16Shift y).trace = 0 := by
    rw [c3T16_eq_reindex, c3T16Shift_eq_reindex, reindex_mul_symm, trace_reindex_symm_eq]
    rw [Finset.sum_mul, Matrix.trace_sum]
    have hterm : ∀ i : Fin 64,
        (((y i : ℂ) • pauli (codePoint (outsideLabel i))) *
          ∑ j : Fin 64, ((c3Shift16 (outsideLabel j).val : ℂ) * (y j : ℂ)) •
            pauli (codePoint (outsideLabel j))).trace
        = (16 : ℂ) * (c3Shift16 (outsideLabel i).val : ℂ) := by
      intro i
      rw [Finset.mul_sum, Matrix.trace_sum, Finset.sum_eq_single i]
      · rw [Matrix.smul_mul, Matrix.mul_smul, pauli_mul_self, Matrix.trace_smul,
          Matrix.trace_smul, Matrix.trace_one]
        simp only [Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const,
          Finset.card_univ, smul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        have hy2 : (y i : ℂ) * (y i : ℂ) = 1 := by
          rcases hy i with h | h <;> rw [h] <;> norm_num
        calc (y i : ℂ) * ((c3Shift16 (outsideLabel i).val : ℂ) * (y i : ℂ) * (2 : ℂ) ^ 4)
            = ((y i : ℂ) * (y i : ℂ)) * ((16 : ℂ) * (c3Shift16 (outsideLabel i).val : ℂ)) := by norm_num; ring
          _ = 16 * (c3Shift16 (outsideLabel i).val : ℂ) := by rw [hy2, one_mul]
      · intro j _ hji
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
          trace_pauli_mul, ite_eq_right]
        · simp
        · exact fun h => hji (outside_labels_injective (codePoint_injective h)).symm
      · intro hi; exact absurd (mem_univ i) hi
    simp_rw [hterm, ← Finset.mul_sum]
    have hsumC : (∑ i : Fin 64, (c3Shift16 (outsideLabel i).val : ℂ)) = 0 := by
      exact_mod_cast c3Shift16_sum_zero_int
    rw [hsumC, mul_zero]
  have hT_herm : (c3T16 y)ᴴ = c3T16 y := by
    rw [c3T16_eq_reindex, Matrix.conjTranspose_reindex]
    congr 1; rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => by rw [Matrix.conjTranspose_smul, (pauli_isHermitian _).eq]; simp
  have hTS_herm : (c3T16Shift y)ᴴ = c3T16Shift y := by
    rw [c3T16Shift_eq_reindex, Matrix.conjTranspose_reindex]
    congr 1; rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => by
      rw [Matrix.conjTranspose_smul, (pauli_isHermitian _).eq]
      simp [star_mul']
  have hT_off : ∀ a b : Fin 16, (a.val < 8 ↔ b.val < 8) → c3T16 y a b = 0 := fun a b h => by
    simp only [c3T16, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Int.coe_castRingHom,
      smul_eq_mul]
    exact Finset.sum_eq_zero fun i _ => by rw [realPauliCode_outside_off i a b h, Int.cast_zero, mul_zero]
  have hTS_ur : ∀ i k : Fin 8,
      c3T16Shift y (Fin.castAdd 8 i) (Fin.natAdd 8 k)
        = (c3Shift16 (Nat.xor i.val k.val) : ℂ) * M i k := by
    intro i k
    simp only [M, c3T16Shift, c3T16, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
      Int.coe_castRingHom, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hnz : (Fin.castAdd 8 i).val = Nat.xor (Fin.natAdd 8 k).val (xCode (outsideLabel p)).val
    · rw [c3Shift16_mod4_eq_xor p i k hnz]; ring
    · have h0 : realPauliCode (outsideLabel p) (Fin.castAdd 8 i) (Fin.natAdd 8 k) = 0 := by
        unfold realPauliCode; exact ite_eq_right hnz
      rw [h0, Int.cast_zero, mul_zero, mul_zero, mul_zero]
  have hT_bot : ∀ i k : Fin 8, c3T16 y (Fin.natAdd 8 k) (Fin.castAdd 8 i) = star (M i k) := by
    intro i k
    have := congrFun (congrFun hT_herm (Fin.natAdd 8 k)) (Fin.castAdd 8 i)
    simpa [M, Matrix.conjTranspose_apply] using this.symm
  have hTS_bot : ∀ i k : Fin 8,
      c3T16Shift y (Fin.natAdd 8 k) (Fin.castAdd 8 i)
        = (c3Shift16 (Nat.xor i.val k.val) : ℂ) * star (M i k) := by
    intro i k
    have := congrFun (congrFun hTS_herm (Fin.natAdd 8 k)) (Fin.castAdd 8 i)
    have h1 : c3T16Shift y (Fin.natAdd 8 k) (Fin.castAdd 8 i)
        = star (c3T16Shift y (Fin.castAdd 8 i) (Fin.natAdd 8 k)) := by
      simpa [Matrix.conjTranspose_apply] using this.symm
    rw [h1, hTS_ur i k, star_mul', show star (c3Shift16 (Nat.xor i.val k.val) : ℂ)
      = (c3Shift16 (Nat.xor i.val k.val) : ℂ) by simp, mul_comm]
  have hsum16 : ∀ g : Fin 16 → ℂ,
      (∑ a : Fin 16, g a) = (∑ i : Fin 8, g (Fin.castAdd 8 i)) + (∑ k : Fin 8, g (Fin.natAdd 8 k)) := by
    intro g; rw [← Equiv.sum_comp fin16Split.symm g, Fintype.sum_sum_type]; rfl
  have htr_block : (c3T16 y * c3T16Shift y).trace
      = 2 * ∑ k : Fin 8, ∑ i : Fin 8, (c3Shift16 (Nat.xor i.val k.val) : ℂ) * (star (M i k) * M i k) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [hsum16]; simp_rw [hsum16]
    have htop0 : ∀ i : Fin 8, ∑ j : Fin 8, c3T16 y (Fin.castAdd 8 i) (Fin.castAdd 8 j) *
        c3T16Shift y (Fin.castAdd 8 j) (Fin.castAdd 8 i) = 0 := fun i =>
      Finset.sum_eq_zero fun j _ => by rw [hT_off _ _ (by simp), zero_mul]
    have hbot0 : ∀ k : Fin 8, ∑ j : Fin 8, c3T16 y (Fin.natAdd 8 k) (Fin.natAdd 8 j) *
        c3T16Shift y (Fin.natAdd 8 j) (Fin.natAdd 8 k) = 0 := fun k =>
      Finset.sum_eq_zero fun j _ => by rw [hT_off _ _ (by simp), zero_mul]
    simp_rw [htop0, hbot0, zero_add, add_zero, hT_bot, hTS_ur, hTS_bot]
    rw [Finset.sum_comm (s := univ) (t := univ) (f := fun i k =>
      c3T16 y (Fin.castAdd 8 i) (Fin.natAdd 8 k) * ((c3Shift16 (Nat.xor i.val k.val) : ℂ) * star (M i k)))]
    rw [two_mul]
    congr 1 <;>
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by dsimp only [M]; ring
  rw [htr_block] at htr0
  have hre := congrArg Complex.re htr0
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.zero_re] at hre
  have hsum_re : (∑ k : Fin 8, ∑ i : Fin 8, (c3Shift16 (Nat.xor i.val k.val) : ℂ) * (star (M i k) * M i k)).re
      = ∑ k : Fin 8, ∑ i : Fin 8, (c3Shift16 (Nat.xor i.val k.val) : ℝ) * (star (M i k) * M i k).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (c3Shift16 (Nat.xor i.val k.val) : ℂ) = ((c3Shift16 (Nat.xor i.val k.val) : ℝ) : ℂ) by
      push_cast; rfl, Complex.re_ofReal_mul]
  rw [hsum_re] at hre
  linarith

private lemma c3_outside_add_mem_section' (j i : Fin 64)
    (hne : codePoint (outsideLabel j) ≠ codePoint (outsideLabel i))
    (hcomm : symp (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) = 0) :
    codeAdd (outsideLabel j) (outsideLabel i) ∈ sectionCodes := by
  have hclosed : outNatArr.all (fun u => outNatArr.all (fun v =>
      (u == v) || (sympFast u v != 0) || isSectionFast (u ^^^ v))) = true := by
    decide +kernel
  have hp : (outsideLabel j).val ∈ outNatArr := by
    rw [← map_outsideLabel_val]; exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
  have hq : (outsideLabel i).val ∈ outNatArr := by
    rw [← map_outsideLabel_val]; exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  have hspec := List.all_eq_true.mp (List.all_eq_true.mp hclosed _ hp) _ hq
  have hnev : (outsideLabel j).val ≠ (outsideLabel i).val := fun h => hne (by rw [Fin.ext h])
  have hsymp : sympFast (outsideLabel j).val (outsideLabel i).val = 0 :=
    (symp_codePoint_eq_fast _ _).mp hcomm
  have hsec_fast : isSectionFast ((outsideLabel j).val ^^^ (outsideLabel i).val) = true := by
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hspec
    rcases hspec with (heq | hns) | hs
    · exact absurd heq hnev
    · exact absurd hsymp hns
    · exact hs
  have hlt : Nat.xor (outsideLabel j).val (outsideLabel i).val < 256 :=
    Nat.xor_lt_two_pow (n := 8) (outsideLabel j).isLt (outsideLabel i).isLt
  have hval : (codeAdd (outsideLabel j) (outsideLabel i)).val
      = (outsideLabel j).val ^^^ (outsideLabel i).val := by
    simp only [codeAdd, Nat.mod_eq_of_lt hlt]; rfl
  rw [mem_sectionCodes_iff_fast, hval]
  exact hsec_fast

private lemma c3_trace_identities_signB (y : Fin 64 → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) :
    let M : Matrix (Fin 8) (Fin 8) ℂ := fun i j => c3T16 y (Fin.castAdd 8 i) (Fin.natAdd 8 j)
    (∑ k : Fin 8, ∑ i : Fin 8, (star (M i k) * M i k).re = 512) ∧
    (16 * (∑ i : Fin 64, ∑ j : Fin 64, y i * (completionOf signB i j : ℝ) * y j)
      = (∑ k : Fin 8, ∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (c3BlockB i j : ℂ) * M j k).re
        + (∑ k : Fin 8, (c3BlockB_D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k).re) := by
  intro M
  have htrT2 : (c3T16 y * c3T16 y).trace = 1024 := by
    rw [c3T16_eq_reindex, reindex_mul_symm, trace_reindex_symm_eq, Finset.sum_mul, Matrix.trace_sum]
    have hterm : ∀ i : Fin 64,
        (((y i : ℂ) • pauli (codePoint (outsideLabel i))) *
          ∑ j : Fin 64, (y j : ℂ) • pauli (codePoint (outsideLabel j))).trace = 16 := by
      intro i
      rw [Finset.mul_sum, Matrix.trace_sum, Finset.sum_eq_single i]
      · rw [Matrix.smul_mul, Matrix.mul_smul, pauli_mul_self, Matrix.trace_smul, Matrix.trace_smul,
          Matrix.trace_one]
        simp only [Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const, Finset.card_univ, smul_eq_mul]
        rcases hy i with h | h <;> rw [h] <;> norm_num
      · intro j _ hji
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, trace_pauli_mul, ite_eq_right]
        · simp
        · exact fun h => hji (outside_labels_injective (codePoint_injective h)).symm
      · intro hi; exact absurd (mem_univ i) hi
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  have htrTAT : (c3T16 y * c3A16 signB * c3T16 y).trace
      = 16 * ∑ i : Fin 64, ∑ j : Fin 64, ((y i * (completionOf signB i j : ℝ) * y j : ℝ) : ℂ) := by
    rw [c3T16_eq_reindex, c3A16_eq_reindex, reindex_mul_symm, reindex_mul_symm, trace_reindex_symm_eq]
    let A : Matrix (Vec 4) (Vec 4) ℂ := ∑ v ∈ sectionCodes, (signB v : ℂ) • pauli (codePoint v)
    let X4 : Finset (Pt 4) := quadric 4 0
    let d4 : Pt 4 := codePoint 128
    have hX4_eq : X4 = realPoints 4 := by
      ext u; simp [X4, quadric, realPoints, qformShift, symp_comm, symp_zero_right]
    have hsec_eq : sectionCodes.image codePoint = sectionOf X4 d4 := by
      ext u
      rw [Finset.mem_image, sectionOf, Finset.mem_filter, hX4_eq]
      obtain ⟨v, rfl⟩ := codePoint_bijective.2 u
      constructor
      · rintro ⟨w, hw, heq⟩
        rw [← codePoint_injective heq]; exact (section_correct w).mp hw
      · intro h; exact ⟨v, (section_correct v).mpr h, rfl⟩
    have hout_eq : outsideCodes.image codePoint = outsideOf X4 d4 := by
      ext u
      rw [Finset.mem_image, outsideOf, Finset.mem_filter, hX4_eq]
      obtain ⟨v, rfl⟩ := codePoint_bijective.2 u
      constructor
      · rintro ⟨w, hw, heq⟩
        have h := (outside_correct w).mp hw
        rw [← codePoint_injective heq]
        exact ⟨h.1, (zmod2_cases _).resolve_left h.2⟩
      · intro h
        refine ⟨v, (outside_correct v).mpr ⟨h.1, ?_⟩, rfl⟩
        rw [h.2]; decide
    let eCode : Fin 256 ≃ Pt 4 := Equiv.ofBijective codePoint codePoint_bijective
    let σ4 : Pt 4 → ℝ := fun u => (signB (eCode.symm u) : ℝ)
    have hσ4 : ∀ v : Fin 256, σ4 (codePoint v) = (signB v : ℝ) := fun v => by
      change (signB (eCode.symm (eCode v)) : ℝ) = (signB v : ℝ)
      rw [eCode.symm_apply_apply]
    have hA_eq : A = opA (sectionOf X4 d4) σ4 := by
      unfold opA
      rw [← hsec_eq, Finset.sum_image (fun a _ b _ h => codePoint_injective h)]
      refine Finset.sum_congr rfl fun v _ => by rw [hσ4 v]; push_cast; rfl
    let T : Matrix (Vec 4) (Vec 4) ℂ := ∑ i : Fin 64, (y i : ℂ) • pauli (codePoint (outsideLabel i))
    have hT_jordan : (1 / 2 : ℂ) • (A * T + T * A)
        = ∑ j : Fin 64, (∑ i : Fin 64, ((completionOf signB j i : ℝ) : ℂ) * (y i : ℂ))
            • pauli (codePoint (outsideLabel j)) := by
      rw [hA_eq]; dsimp only [T]
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.smul_sum]
      have hterm : ∀ i : Fin 64,
          (1 / 2 : ℂ) • (opA (sectionOf X4 d4) σ4 * ((y i : ℂ) • pauli (codePoint (outsideLabel i)))
            + ((y i : ℂ) • pauli (codePoint (outsideLabel i))) * opA (sectionOf X4 d4) σ4)
          = ∑ j : Fin 64, (((completionOf signB j i : ℝ) : ℂ) * (y i : ℂ))
              • pauli (codePoint (outsideLabel j)) := by
        intro i
        have hi_mem : codePoint (outsideLabel i) ∈ outsideOf X4 d4 := by
          rw [← hout_eq, ← outside_labels_complete]
          exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (mem_univ i))
        have hJ := lemma20_jordan_action (isClosedCfg_quadric 0) d4 σ4 ⟨codePoint (outsideLabel i), hi_mem⟩
        dsimp only [jordanOp] at hJ
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_comm, hJ, Finset.smul_sum]
        have heq_O : (univ : Finset {p // p ∈ outsideOf X4 d4})
            = (univ : Finset (Fin 64)).image (fun j =>
                ⟨codePoint (outsideLabel j), by
                  rw [← hout_eq, ← outside_labels_complete]
                  exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (mem_univ j))⟩) := by
          ext ⟨u, hu⟩
          simp only [Finset.mem_univ, Finset.mem_image, true_and, true_iff]
          rw [← hout_eq, ← outside_labels_complete] at hu
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
          exact ⟨j, rfl⟩
        rw [heq_O, Finset.sum_image (fun j₁ _ j₂ _ h =>
          outside_labels_injective (codePoint_injective (congrArg Subtype.val h)))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, mul_comm (y i : ℂ)]; congr 2
        unfold completionMat completionOf
        have hcond_iff : (codePoint (outsideLabel j) ≠ codePoint (outsideLabel i) ∧
              symp (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) = 0) ↔
            (codeAdd (outsideLabel j) (outsideLabel i) ∈ sectionCodes ∧
              symp (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) = 0) := by
          constructor
          · rintro ⟨hne, hcomm⟩; exact ⟨c3_outside_add_mem_section' j i hne hcomm, hcomm⟩
          · rintro ⟨hsec, hcomm⟩
            refine ⟨fun h => ?_, hcomm⟩
            have hji : j = i := outside_labels_injective (codePoint_injective h)
            subst hji; exact isC3OutsidePair_irrefl j ((isC3OutsidePair_iff j j).mpr ⟨hsec, hcomm⟩)
        by_cases hcond : codePoint (outsideLabel j) ≠ codePoint (outsideLabel i) ∧
            symp (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) = 0
        · rw [ite_eq_left hcond, ite_eq_left (hcond_iff.mp hcond), ← codePoint_add, hσ4, Int.cast_mul,
            ← lineSign_eq_integer, codePoint_add]
          have hls : lineSign (codePoint (outsideLabel j) + codePoint (outsideLabel i))
              (codePoint (outsideLabel i))
            = lineSign (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) := by
            set pu := codePoint (outsideLabel j)
            set pv := codePoint (outsideLabel i)
            have e1 : pu + pv + pv = pu := by rw [add_assoc, pt_add_self, add_zero]
            have h1 : pauli (pu + pv) * pauli pv * pauli pu = tau (pu + pv) pv • (1 : Matrix (Vec 4) (Vec 4) ℂ) := by
              rw [pauli_mul, e1, Matrix.smul_mul, pauli_mul_self]
            have h2 : pauli (pu + pv) * pauli pv * pauli pu = tau pu pv • (1 : Matrix (Vec 4) (Vec 4) ℂ) := by
              rw [Matrix.mul_assoc, pauli_comm pu pv, hcond.2, eps_zero, one_smul,
                pauli_mul, Matrix.mul_smul, pauli_mul_self]
            have h3 : tau (pu + pv) pv = tau pu pv := by
              have h4 := congrFun (congrFun (h1.symm.trans h2) 0) 0; simpa using h4
            unfold lineSign; rw [h3]
          rw [hls, mul_comm]
        · rw [ite_eq_right hcond, ite_eq_right (fun h => hcond (hcond_iff.mpr h)), Int.cast_zero]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_smul]
    have htr_sym : (T * A * T).trace
        = (T * ((1 / 2 : ℂ) • (A * T + T * A))).trace := by
      rw [Matrix.mul_smul, mul_add, Matrix.trace_smul, Matrix.trace_add,
        Matrix.trace_mul_comm T (T * A), Matrix.mul_assoc]
      simp only [smul_eq_mul]; ring
    change (T * A * T).trace = _
    rw [htr_sym, hT_jordan]
    dsimp only [T]; rw [Finset.sum_mul, Matrix.trace_sum]
    calc (∑ i : Fin 64, (((y i : ℂ) • pauli (codePoint (outsideLabel i))) *
            ∑ j : Fin 64, (∑ k : Fin 64, ((completionOf signB j k : ℝ) : ℂ) * (y k : ℂ))
              • pauli (codePoint (outsideLabel j))).trace)
        = ∑ i : Fin 64, (16 : ℂ) * ((y i : ℂ) *
            ∑ k : Fin 64, ((completionOf signB i k : ℝ) : ℂ) * (y k : ℂ)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Matrix.trace_sum, Finset.sum_eq_single i]
          · rw [Matrix.smul_mul, Matrix.mul_smul, pauli_mul_self, Matrix.trace_smul, Matrix.trace_smul,
              Matrix.trace_one]
            simp only [Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const, Finset.card_univ, smul_eq_mul]
            norm_num; ring
          · intro j _ hji
            rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, trace_pauli_mul, ite_eq_right]
            · simp
            · exact fun h => hji (outside_labels_injective (codePoint_injective h)).symm
          · intro hi; exact absurd (mem_univ i) hi
      _ = 16 * ∑ i : Fin 64, ∑ j : Fin 64, ((y i * (completionOf signB i j : ℝ) * y j : ℝ) : ℂ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by push_cast; ring
  have hT_herm : (c3T16 y)ᴴ = c3T16 y := by
    rw [c3T16_eq_reindex, Matrix.conjTranspose_reindex]
    congr 1; rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => by rw [Matrix.conjTranspose_smul, (pauli_isHermitian _).eq]; simp
  have hT_off : ∀ a b : Fin 16, (a.val < 8 ↔ b.val < 8) → c3T16 y a b = 0 := fun a b h => by
    simp only [c3T16, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Int.coe_castRingHom, smul_eq_mul]
    exact Finset.sum_eq_zero fun i _ => by rw [realPauliCode_outside_off i a b h, Int.cast_zero, mul_zero]
  have hT_bot : ∀ i k : Fin 8, c3T16 y (Fin.natAdd 8 k) (Fin.castAdd 8 i) = star (M i k) := by
    intro i k
    have := congrFun (congrFun hT_herm (Fin.natAdd 8 k)) (Fin.castAdd 8 i)
    simpa [M, Matrix.conjTranspose_apply] using this.symm
  have hA_ul : ∀ i j : Fin 8, c3A16 signB (Fin.castAdd 8 i) (Fin.castAdd 8 j) = (c3BlockB i j : ℂ) := fun i j => by
    simp only [c3A16, Matrix.map_apply, Int.coe_castRingHom, carrierB_from_section]; rfl
  have hA_ur : ∀ i j : Fin 8, c3A16 signB (Fin.castAdd 8 i) (Fin.natAdd 8 j) = 0 := by
    have h0 : ∀ i j : Fin 8, carrierB (Fin.castAdd 8 i) (Fin.natAdd 8 j) = 0 := by decide +kernel
    intro i j; simp only [c3A16, Matrix.map_apply, Int.coe_castRingHom, carrierB_from_section, h0, Int.cast_zero]
  have hA_ll : ∀ i j : Fin 8, c3A16 signB (Fin.natAdd 8 i) (Fin.castAdd 8 j) = 0 := by
    have h0 : ∀ i j : Fin 8, carrierB (Fin.natAdd 8 i) (Fin.castAdd 8 j) = 0 := by decide +kernel
    intro i j; simp only [c3A16, Matrix.map_apply, Int.coe_castRingHom, carrierB_from_section, h0, Int.cast_zero]
  have hA_lr : ∀ i j : Fin 8, c3A16 signB (Fin.natAdd 8 i) (Fin.natAdd 8 j)
      = if i = j then (c3BlockB_D i : ℂ) else 0 := by
    have h0 : ∀ i j : Fin 8, carrierB (Fin.natAdd 8 i) (Fin.natAdd 8 j)
        = if i = j then c3BlockB_D i else 0 := by decide +kernel
    intro i j; simp only [c3A16, Matrix.map_apply, Int.coe_castRingHom, carrierB_from_section, h0]
    split_ifs <;> simp
  have hsum16 : ∀ g : Fin 16 → ℂ,
      (∑ a : Fin 16, g a) = (∑ i : Fin 8, g (Fin.castAdd 8 i)) + (∑ k : Fin 8, g (Fin.natAdd 8 k)) := by
    intro g; rw [← Equiv.sum_comp fin16Split.symm g, Fintype.sum_sum_type]; rfl
  have hT2_block : (c3T16 y * c3T16 y).trace = 2 * ∑ k : Fin 8, ∑ i : Fin 8, star (M i k) * M i k := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [hsum16]; simp_rw [hsum16]
    have htop0 : ∀ i : Fin 8, ∑ j : Fin 8, c3T16 y (Fin.castAdd 8 i) (Fin.castAdd 8 j) *
        c3T16 y (Fin.castAdd 8 j) (Fin.castAdd 8 i) = 0 := fun i =>
      Finset.sum_eq_zero fun j _ => by rw [hT_off _ _ (by simp), zero_mul]
    have hbot0 : ∀ k : Fin 8, ∑ j : Fin 8, c3T16 y (Fin.natAdd 8 k) (Fin.natAdd 8 j) *
        c3T16 y (Fin.natAdd 8 j) (Fin.natAdd 8 k) = 0 := fun k =>
      Finset.sum_eq_zero fun j _ => by rw [hT_off _ _ (by simp), zero_mul]
    simp_rw [htop0, hbot0, zero_add, add_zero, hT_bot]
    rw [Finset.sum_comm (s := univ) (t := univ) (f := fun i k =>
      c3T16 y (Fin.castAdd 8 i) (Fin.natAdd 8 k) * star (M i k)), two_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by dsimp only [M]; ring
  have hTAT_block : (c3T16 y * c3A16 signB * c3T16 y).trace
      = (∑ k : Fin 8, ∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (c3BlockB i j : ℂ) * M j k)
        + (∑ k : Fin 8, (c3BlockB_D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k) := by
    have h1' : (c3T16 y * c3A16 signB * c3T16 y).trace
        = ∑ a : Fin 16, ∑ b : Fin 16, ∑ c : Fin 16, c3T16 y a b * c3A16 signB b c * c3T16 y c a := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      trans (∑ c : Fin 16, ∑ b : Fin 16, c3T16 y a b * c3A16 signB b c * c3T16 y c a)
      · refine Finset.sum_congr rfl fun c _ => by rw [Finset.sum_mul]
      · exact Finset.sum_comm
    rw [h1', hsum16]; simp_rw [hsum16]
    have hz1 : ∀ i : Fin 8, ∑ b : Fin 8,
        ((∑ c : Fin 8, c3T16 y (Fin.castAdd 8 i) (Fin.castAdd 8 b) * c3A16 signB (Fin.castAdd 8 b) (Fin.castAdd 8 c) * c3T16 y (Fin.castAdd 8 c) (Fin.castAdd 8 i))
        + (∑ c : Fin 8, c3T16 y (Fin.castAdd 8 i) (Fin.castAdd 8 b) * c3A16 signB (Fin.castAdd 8 b) (Fin.natAdd 8 c) * c3T16 y (Fin.natAdd 8 c) (Fin.castAdd 8 i))) = 0 :=
      fun i => Finset.sum_eq_zero fun b _ => by
        rw [Finset.sum_eq_zero fun c _ => by rw [hT_off _ _ (by simp), zero_mul, zero_mul],
          Finset.sum_eq_zero fun c _ => by rw [hA_ur, mul_zero, zero_mul], add_zero]
    have hz2 : ∀ k : Fin 8, ∑ b : Fin 8,
        ((∑ c : Fin 8, c3T16 y (Fin.natAdd 8 k) (Fin.natAdd 8 b) * c3A16 signB (Fin.natAdd 8 b) (Fin.castAdd 8 c) * c3T16 y (Fin.castAdd 8 c) (Fin.natAdd 8 k))
        + (∑ c : Fin 8, c3T16 y (Fin.natAdd 8 k) (Fin.natAdd 8 b) * c3A16 signB (Fin.natAdd 8 b) (Fin.natAdd 8 c) * c3T16 y (Fin.natAdd 8 c) (Fin.natAdd 8 k))) = 0 :=
      fun k => Finset.sum_eq_zero fun b _ => by
        rw [Finset.sum_eq_zero fun c _ => by rw [hA_ll, mul_zero, zero_mul],
          Finset.sum_eq_zero fun c _ => by rw [hT_off _ _ (by simp), zero_mul, zero_mul], add_zero]
    have hD : (∑ i : Fin 8, ∑ b : Fin 8,
          ((∑ c : Fin 8, c3T16 y (Fin.castAdd 8 i) (Fin.natAdd 8 b) * c3A16 signB (Fin.natAdd 8 b) (Fin.castAdd 8 c) * c3T16 y (Fin.castAdd 8 c) (Fin.castAdd 8 i))
          + (∑ c : Fin 8, c3T16 y (Fin.castAdd 8 i) (Fin.natAdd 8 b) * c3A16 signB (Fin.natAdd 8 b) (Fin.natAdd 8 c) * c3T16 y (Fin.natAdd 8 c) (Fin.castAdd 8 i))))
        = ∑ k : Fin 8, (c3BlockB_D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k := by
      have h0 : ∀ i b : Fin 8, ∑ c : Fin 8, c3T16 y (Fin.castAdd 8 i) (Fin.natAdd 8 b) *
          c3A16 signB (Fin.natAdd 8 b) (Fin.castAdd 8 c) * c3T16 y (Fin.castAdd 8 c) (Fin.castAdd 8 i) = 0 :=
        fun i b => Finset.sum_eq_zero fun c _ => by rw [hA_ll, mul_zero, zero_mul]
      simp_rw [h0, zero_add, hA_lr]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single k]
      · simp only [↓reduceIte, hT_bot i k]; dsimp only [M]; ring
      · intro c _ hck; simp [Ne.symm hck]
      · intro hk; exact absurd (mem_univ k) hk
    have hC : (∑ k : Fin 8, ∑ i : Fin 8,
          ((∑ j : Fin 8, c3T16 y (Fin.natAdd 8 k) (Fin.castAdd 8 i) * c3A16 signB (Fin.castAdd 8 i) (Fin.castAdd 8 j) * c3T16 y (Fin.castAdd 8 j) (Fin.natAdd 8 k))
          + (∑ j : Fin 8, c3T16 y (Fin.natAdd 8 k) (Fin.castAdd 8 i) * c3A16 signB (Fin.castAdd 8 i) (Fin.natAdd 8 j) * c3T16 y (Fin.natAdd 8 j) (Fin.natAdd 8 k))))
        = ∑ k : Fin 8, ∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (c3BlockB i j : ℂ) * M j k := by
      have h0 : ∀ k i : Fin 8, ∑ j : Fin 8, c3T16 y (Fin.natAdd 8 k) (Fin.castAdd 8 i) *
          c3A16 signB (Fin.castAdd 8 i) (Fin.natAdd 8 j) * c3T16 y (Fin.natAdd 8 j) (Fin.natAdd 8 k) = 0 :=
        fun k i => Finset.sum_eq_zero fun j _ => by rw [hA_ur, mul_zero, zero_mul]
      simp_rw [h0, add_zero, hA_ul]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by rw [hT_bot i k]
    simp_rw [hz1, hz2, zero_add, add_zero]; rw [hD, hC, add_comm]
  constructor
  · rw [hT2_block] at htrT2
    have hre := congrArg Complex.re htrT2
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.re_sum] at hre
    simp only [Complex.re_sum, Complex.re_ofNat] at hre
    linarith
  · have hre := congrArg Complex.re (htrTAT.symm.trans hTAT_block)
    rw [show (16 : ℂ) = ((16 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.add_re] at hre
    have hlhs : (∑ i : Fin 64, ∑ j : Fin 64, ((y i * (completionOf signB i j : ℝ) * y j : ℝ) : ℂ)).re
        = ∑ i : Fin 64, ∑ j : Fin 64, y i * (completionOf signB i j : ℝ) * y j := by
      simp only [Complex.re_sum, Complex.ofReal_re]
    rw [hlhs] at hre; exact hre

/-- **New Theorem (Sharp QUBO SDP-Dual Lower Bound for `signB`):**
Every binary completion `y ∈ {±1}^64` of the second four-qubit C3 carrier `signB` violates
at least **330** of the 1,120 outside contexts (improving Corollary 16's spectral lower
bound from 315 to 330, the exact ceiling of the full 64-variable elliptope SDP dual
`329.85603574...`). -/
theorem corollary16_sigmaB_sdp_lower (y : Fin 64 → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) :
    330 ≤ c3ViolatedOutsideContexts signB y := by
  let M : Matrix (Fin 8) (Fin 8) ℂ := fun i j => c3T16 y (Fin.castAdd 8 i) (Fin.natAdd 8 j)
  obtain ⟨hM_norm, hTAT⟩ := c3_trace_identities_signB y hy
  have hshift0 := c3_shift_quad_zero y hy
  have hD_mod : ∀ k : Fin 8, c3BlockB_D k = c3BlockB_D ⟨k.val % 4, by omega⟩ := by decide +kernel
  have hS_mod : ∀ i k : Fin 8,
      c3Shift16 (Nat.xor i.val k.val) = c3Shift16 (Nat.xor i.val (k.val % 4)) := by decide +kernel
  have hcol_id : ∀ k : Fin 8,
      (∑ i : Fin 8, ∑ j : Fin 8,
          star (M i k) * (c3SdpBlock ⟨k.val % 4, Nat.mod_lt _ (by norm_num)⟩ i j : ℂ) * M j k).re
      = 231 * (∑ i : Fin 8, (star (M i k) * M i k).re)
        - 8 * ((∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (c3BlockB i j : ℂ) * M j k).re
               + ((c3BlockB_D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k).re)
        - ∑ i : Fin 8, (c3Shift16 (Nat.xor i.val k.val) : ℝ) * (star (M i k) * M i k).re := by
    intro k
    have hmat : ∀ i j : Fin 8,
        (c3SdpBlock ⟨k.val % 4, Nat.mod_lt _ (by norm_num)⟩ i j : ℂ)
        = (if i = j then (231 : ℂ) - 8 * (c3BlockB_D k : ℂ) - (c3Shift16 (Nat.xor i.val k.val) : ℂ) else 0)
          - 8 * (c3BlockB i j : ℂ) := by
      intro i j
      unfold c3SdpBlock
      rw [← hD_mod k, ← hS_mod i k]
      by_cases hij : i = j <;> simp [hij]
    have hC : (∑ i : Fin 8, ∑ j : Fin 8,
          star (M i k) * (c3SdpBlock ⟨k.val % 4, Nat.mod_lt _ (by norm_num)⟩ i j : ℂ) * M j k)
        = (231 : ℂ) * (∑ i : Fin 8, star (M i k) * M i k)
          - 8 * ((∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (c3BlockB i j : ℂ) * M j k)
                 + (c3BlockB_D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k)
          - ∑ i : Fin 8, (c3Shift16 (Nat.xor i.val k.val) : ℂ) * (star (M i k) * M i k) := by
      simp_rw [hmat, mul_sub, sub_mul, Finset.sum_sub_distrib]
      have hdiag : (∑ i : Fin 8, ∑ j : Fin 8,
            star (M i k) * (if i = j then (231 : ℂ) - 8 * (c3BlockB_D k : ℂ)
              - (c3Shift16 (Nat.xor i.val k.val) : ℂ) else 0) * M j k)
          = (231 : ℂ) * (∑ i : Fin 8, star (M i k) * M i k)
            - 8 * ((c3BlockB_D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k)
            - ∑ i : Fin 8, (c3Shift16 (Nat.xor i.val k.val) : ℂ) * (star (M i k) * M i k) := by
        have h1 : ∀ i : Fin 8, (∑ j : Fin 8, star (M i k) * (if i = j then (231 : ℂ)
            - 8 * (c3BlockB_D k : ℂ) - (c3Shift16 (Nat.xor i.val k.val) : ℂ) else 0) * M j k)
            = (231 : ℂ) * (star (M i k) * M i k)
              - 8 * ((c3BlockB_D k : ℂ) * (star (M i k) * M i k))
              - (c3Shift16 (Nat.xor i.val k.val) : ℂ) * (star (M i k) * M i k) := by
          intro i
          rw [Finset.sum_eq_single i]
          · simp only [↓reduceIte]; ring
          · intro j _ hji; simp [Ne.symm hji]
          · intro hi; exact absurd (mem_univ i) hi
        simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hB : (∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (8 * (c3BlockB i j : ℂ)) * M j k)
          = 8 * ∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (c3BlockB i j : ℂ) * M j k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hdiag, hB]; ring
    have hre := congrArg Complex.re hC
    simp only [Complex.sub_re, Complex.add_re, Complex.re_sum,
      show (231 : ℂ) = ((231 : ℝ) : ℂ) by norm_num,
      show (8 : ℂ) = ((8 : ℝ) : ℂ) by norm_num,
      Complex.re_ofReal_mul] at hre
    have hSre : ∀ i : Fin 8, ((c3Shift16 (Nat.xor i.val k.val) : ℂ) * (star (M i k) * M i k)).re
        = (c3Shift16 (Nat.xor i.val k.val) : ℝ) * (star (M i k) * M i k).re := fun i => by
      rw [show (c3Shift16 (Nat.xor i.val k.val) : ℂ) = ((c3Shift16 (Nat.xor i.val k.val) : ℝ) : ℂ) by
        push_cast; rfl, Complex.re_ofReal_mul]
    simp_rw [hSre] at hre
    exact hre
  have hcol_nonneg : ∀ k : Fin 8,
      0 ≤ (∑ i : Fin 8, ∑ j : Fin 8,
        star (M i k) * (c3SdpBlock ⟨k.val % 4, Nat.mod_lt _ (by norm_num)⟩ i j : ℂ) * M j k).re := by
    intro k
    by_cases hk : (fun i => M i k) = 0
    · have h0 : ∀ i : Fin 8, M i k = 0 := fun i => congrFun hk i
      simp [h0]
    · exact le_of_lt (c3SdpBlock_pos_def ⟨k.val % 4, Nat.mod_lt _ (by norm_num)⟩ (fun i => M i k) hk)
  have hex_col : ∃ k₀ : Fin 8, (fun i => M i k₀) ≠ 0 := by
    by_contra hall; push Not at hall
    have hz : ∑ k : Fin 8, ∑ i : Fin 8, (star (M i k) * M i k).re = 0 :=
      Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => by simp [congrFun (hall k) i]
    linarith
  obtain ⟨k₀, hk₀⟩ := hex_col
  have hpos : 0 < ∑ k : Fin 8, (∑ i : Fin 8, ∑ j : Fin 8,
      star (M i k) * (c3SdpBlock ⟨k.val % 4, Nat.mod_lt _ (by norm_num)⟩ i j : ℂ) * M j k).re :=
    Finset.sum_pos' (fun k _ => hcol_nonneg k)
      ⟨k₀, mem_univ k₀, c3SdpBlock_pos_def ⟨k₀.val % 4, Nat.mod_lt _ (by norm_num)⟩ (fun i => M i k₀) hk₀⟩
  simp_rw [hcol_id, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib] at hpos
  have hC_sum : ∑ k : Fin 8, (∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (c3BlockB i j : ℂ) * M j k).re
      = (∑ k : Fin 8, ∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (c3BlockB i j : ℂ) * M j k).re := by
    rw [Complex.re_sum]
  have hD_sum : ∑ k : Fin 8, ((c3BlockB_D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k).re
      = (∑ k : Fin 8, (c3BlockB_D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k).re := by
    rw [Complex.re_sum]
  rw [hC_sum, hD_sum, hM_norm, hshift0, ← hTAT] at hpos
  rw [c3_quadForm_eq signB signB_values y hy] at hpos
  have hreal : (329 : ℝ) < (c3ViolatedOutsideContexts signB y : ℝ) := by linarith
  have hnat : 329 < c3ViolatedOutsideContexts signB y := by exact_mod_cast hreal
  omega

/-- The 38 negative outside codes of the `signA` completion witness (`F = 368`). -/
def c3WitnessANegCodes : Finset (Fin 256) :=
  {8, 12, 13, 14, 24, 26, 28, 30, 40, 41, 44, 45, 56, 59, 60, 63,
   90, 93, 105, 110, 123, 125, 126, 153, 155, 157, 159, 170, 171,
   174, 175, 189, 190, 217, 219, 234, 235, 255}

def c3WitnessAInt (i : Fin 64) : ℤ :=
  if outsideLabel i ∈ c3WitnessANegCodes then -1 else 1

def c3WitnessAReal (i : Fin 64) : ℝ := (c3WitnessAInt i : ℝ)

lemma c3WitnessAReal_values (i : Fin 64) : c3WitnessAReal i = 1 ∨ c3WitnessAReal i = -1 := by
  unfold c3WitnessAReal c3WitnessAInt; split_ifs <;> simp

def signAFast (w : ℕ) : ℤ :=
  if w == 48 || w == 102 || w == 176 || w == 230 then -1 else 1

lemma signA_eq_fast : ∀ w : Fin 256, signA w = signAFast w.val := by decide +kernel

def outWithSignA : List (ℕ × ℤ) :=
  outNatArr.map fun c =>
    (c, if c == 8 || c == 12 || c == 13 || c == 14 || c == 24 || c == 26 || c == 28 || c == 30 ||
           c == 40 || c == 41 || c == 44 || c == 45 || c == 56 || c == 59 || c == 60 || c == 63 ||
           c == 90 || c == 93 || c == 105 || c == 110 || c == 123 || c == 125 || c == 126 ||
           c == 153 || c == 155 || c == 157 || c == 159 || c == 170 || c == 171 || c == 174 ||
           c == 175 || c == 189 || c == 190 || c == 217 || c == 219 || c == 234 || c == 235 ||
           c == 255 then -1 else 1)

lemma map_outsideLabel_witnessA :
    (List.finRange 64).map (fun i => ((outsideLabel i).val, c3WitnessAInt i)) = outWithSignA := by
  decide +kernel

/-- Explicit binary completion witness for `signA` violating exactly **368** outside contexts. -/
theorem corollary16_sigmaA_witness :
    c3ViolatedOutsideContexts signA c3WitnessAReal = 368 := by
  have hcomp_fast : ∀ i j : Fin 64,
      completionOf signA i j =
        if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
            (sympFast (outsideLabel i).val (outsideLabel j).val == 0)
        then signAFast ((outsideLabel i).val ^^^ (outsideLabel j).val)
              * lineSignFast (outsideLabel i).val (outsideLabel j).val
        else 0 := by
    intro i j
    have hlt : Nat.xor (outsideLabel i).val (outsideLabel j).val < 256 :=
      Nat.xor_lt_two_pow (n := 8) (outsideLabel i).isLt (outsideLabel j).isLt
    have haddv : (codeAdd (outsideLabel i) (outsideLabel j)).val
        = (outsideLabel i).val ^^^ (outsideLabel j).val := by
      simp only [codeAdd, Nat.mod_eq_of_lt hlt]; rfl
    unfold completionOf
    simp only [mem_sectionCodes_iff_fast, symp_codePoint_eq_fast, signA_eq_fast,
      integerLineSign_codePoint_eq_fast, haddv, Bool.and_eq_true, beq_iff_eq]
  have hfast : (outWithSignA.map fun p => p.2 *
      (outWithSignA.map fun q =>
        (if isSectionFast (p.1 ^^^ q.1) && (sympFast p.1 q.1 == 0)
          then signAFast (p.1 ^^^ q.1) * lineSignFast p.1 q.1 else 0) * q.2).sum).sum = 768 := by
    decide +kernel
  have hint : (∑ i : Fin 64, ∑ j : Fin 64, c3WitnessAInt i * completionOf signA i j * c3WitnessAInt j) = 768 := by
    have hrew : (∑ i : Fin 64, ∑ j : Fin 64, c3WitnessAInt i * completionOf signA i j * c3WitnessAInt j)
        = ∑ i : Fin 64, c3WitnessAInt i * ∑ j : Fin 64,
            (if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
                (sympFast (outsideLabel i).val (outsideLabel j).val == 0)
              then signAFast ((outsideLabel i).val ^^^ (outsideLabel j).val)
                    * lineSignFast (outsideLabel i).val (outsideLabel j).val
              else 0) * c3WitnessAInt j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by rw [hcomp_fast i j]; ring
    rw [hrew]
    have hlist : (∑ i : Fin 64, c3WitnessAInt i * ∑ j : Fin 64,
          (if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
              (sympFast (outsideLabel i).val (outsideLabel j).val == 0)
            then signAFast ((outsideLabel i).val ^^^ (outsideLabel j).val)
                  * lineSignFast (outsideLabel i).val (outsideLabel j).val
            else 0) * c3WitnessAInt j)
        = (outWithSignA.map fun p => p.2 *
            (outWithSignA.map fun q =>
              (if isSectionFast (p.1 ^^^ q.1) && (sympFast p.1 q.1 == 0)
                then signAFast (p.1 ^^^ q.1) * lineSignFast p.1 q.1 else 0) * q.2).sum).sum := by
      simp only [Fin.sum_univ_def]
      have h1 : ∀ p : ℕ × ℤ,
          ((List.finRange 64).map fun j =>
            (if isSectionFast (p.1 ^^^ (outsideLabel j).val) &&
                (sympFast p.1 (outsideLabel j).val == 0)
              then signAFast (p.1 ^^^ (outsideLabel j).val)
                    * lineSignFast p.1 (outsideLabel j).val
              else 0) * c3WitnessAInt j).sum
          = (outWithSignA.map fun q =>
              (if isSectionFast (p.1 ^^^ q.1) && (sympFast p.1 q.1 == 0)
                then signAFast (p.1 ^^^ q.1) * lineSignFast p.1 q.1 else 0) * q.2).sum := by
        intro p; rw [← map_outsideLabel_witnessA, List.map_map]; rfl
      have h2 : ((List.finRange 64).map fun i => c3WitnessAInt i *
            ((List.finRange 64).map fun j =>
              (if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
                  (sympFast (outsideLabel i).val (outsideLabel j).val == 0)
                then signAFast ((outsideLabel i).val ^^^ (outsideLabel j).val)
                      * lineSignFast (outsideLabel i).val (outsideLabel j).val
                else 0) * c3WitnessAInt j).sum)
          = outWithSignA.map fun p => p.2 *
              (outWithSignA.map fun q =>
                (if isSectionFast (p.1 ^^^ q.1) && (sympFast p.1 q.1 == 0)
                  then signAFast (p.1 ^^^ q.1) * lineSignFast p.1 q.1 else 0) * q.2).sum := by
        rw [← map_outsideLabel_witnessA, List.map_map]
        refine List.map_congr_left fun i _ => ?_
        dsimp only [Function.comp_apply]
        rw [h1 ((outsideLabel i).val, c3WitnessAInt i), map_outsideLabel_witnessA]
      rw [h2]
    rw [hlist, hfast]
  have hquad : (∑ i : Fin 64, ∑ j : Fin 64,
      c3WitnessAReal i * (completionOf signA i j : ℝ) * c3WitnessAReal j) = 768 := by
    have hcast : ((∑ i : Fin 64, ∑ j : Fin 64, c3WitnessAInt i * completionOf signA i j * c3WitnessAInt j : ℤ) : ℝ) = 768 := by
      rw [hint]; norm_num
    rw [← hcast]; push_cast; rfl
  have hform := c3_quadForm_eq signA signA_values c3WitnessAReal c3WitnessAReal_values
  rw [hquad] at hform
  have hreal : (c3ViolatedOutsideContexts signA c3WitnessAReal : ℝ) = 368 := by linarith
  exact_mod_cast hreal

/-- **Tightened Corollary 16 (complete two-sided kernel-certified enclosures):**
For the explicit four-qubit C3 cospectral pair `(signA, signB)`:
- `347 ≤ min_y F(signA, y) ≤ 368`
- `330 ≤ min_y F(signB, y) ≤ 344` (tightened by +15 from 315 via the exact QUBO SDP dual). -/
theorem corollary16_binary_minima_tightened :
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) → 347 ≤ c3ViolatedOutsideContexts signA y) ∧
    (∃ y₀ : Fin 64 → ℝ, (∀ i, y₀ i = 1 ∨ y₀ i = -1) ∧ c3ViolatedOutsideContexts signA y₀ = 368) ∧
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) → 330 ≤ c3ViolatedOutsideContexts signB y) ∧
    (∃ y₁ : Fin 64 → ℝ, (∀ i, y₁ i = 1 ∨ y₁ i = -1) ∧ c3ViolatedOutsideContexts signB y₁ = 344) :=
  ⟨corollary16_sigmaA_lower,
   ⟨c3WitnessAReal, c3WitnessAReal_values, corollary16_sigmaA_witness⟩,
   corollary16_sigmaB_sdp_lower,
   ⟨c3WitnessReal, c3WitnessReal_values, corollary16_sigmaB_witness⟩⟩

end TightenedCorollary16

end HoggarBound.AuditUpgrades

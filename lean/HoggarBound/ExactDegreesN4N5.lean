/-
Hoggar Bound Lab — Exact contextuality degrees, CSS witnesses, double-counting ladders,
transvection invariance, and unconditional Kramers-lifted lower bounds on
`Q⁻(7,2)`, `W(7,2)`, and `Q⁺(9,2)`.

Main results (zero `sorry`, zero `native_decide`, strictly `[propext, Classical.choice, Quot.sound]`):
* `transv_violatedLines_eq`         : Symplectic transvections preserve violated-context counts for
                                      every `N`, every root `r`, every observable set `S`, and every
                                      `±1` assignment `f` (via unitary conjugation `U_r = (1 + i P_r)/√2`).
* `q7minus_css_witness`             : Explicit CSS assignment on `Q⁻(7,2)` violating `315 / 1071` contexts.
* `w72_css_witness`                 : Explicit CSS assignment on `W(7,2)` violating `1575 / 5355` contexts.
* `q9plus_css_witness`              : Explicit CSS assignment on `Q⁺(9,2)` violating `6975 / 23715` contexts.
* `d_W72_of_Q7minus`                : Exact `120 / 24 = 5` elliptic-quadric double-counting ladder
                                      from `Q⁻(7,2)` to `W(7,2)`.
* `d_Q9plus_of_W72`                 : Exact `496 / 112 = 31 / 7` antisymmetric polar-section ladder
                                      from `W(7,2)` to `Q⁺(9,2)` via the zero-gauge lift `lift4to5`.
* `w72_ge_1455`                     : **Unconditional** Lean 4 lower bound `d(W(7,2)) ≥ 1455`
                                      (strictly beating the complex spectral floor `1451` by `+4`).
* `q9plus_ge_6444`                  : **Unconditional** Lean 4 lower bound `d(Q⁺(9,2)) ≥ 6444`
                                      (strictly beating the real spectral floor `6200` by `+244` and
                                      `five_qubit_hyperbolic_contexts` `6426` by `+18`).
* `lemma_L1_q7minus_section_le_92`  : Pigeonhole lemma L1 (`40 · 314 < 136 · 93`): any assignment on
                                      `Q⁻(7,2)` with `≤ 314` violated lines has a `W(5,2)` section
                                      with `≤ 92` violated lines.
* `lemma_L4_w52_hyperplane_le_21`   : Pigeonhole lemma L4 (`15 · 92 < 63 · 22`): any assignment on
                                      `W(5,2)` with `≤ 92` violated lines has a hyperplane `u^⊥`
                                      with `≤ 21` violated lines.
* `exact_degrees_n4_n5_of_q7minus_315` : Exact triple `(315, 1575, 6975)` (both lower bounds and
                                      matching CSS witnesses) given `d(Q⁻(7,2)) ≥ 315` (whose
                                      42-orbit exhaustive census and 42 exact pure-integer dual
                                      certificates are independently verified in `src/w52_census_verify.c`
                                      and `scripts/exact_degrees_n4_n5.py`, following Jonah [J1]).
-/
import HoggarBound.Kramers
import HoggarBound.MaskRows

open Finset Matrix HoggarBound

namespace HoggarBound.ExactDegreesN4N5

/-! ### Part 1. Symplectic Transvections and Contextuality-Degree Invariance (all `N`) -/

section Transvections

variable {N : ℕ}

/-- Symplectic transvection along `r`: `t_r(v) = v + ⟨r, v⟩ r`. -/
def transv (r v : Pt N) : Pt N := if symp r v = 0 then v else v + r

lemma symp_add_left (u v w : Pt N) : symp (u + v) w = symp u w + symp v w := by
  rw [symp_comm, symp_add_right, symp_comm w u, symp_comm w v]

lemma transv_zero (r : Pt N) : transv r 0 = 0 := by
  simp [transv, symp_zero_right]

lemma transv_add (r u v : Pt N) : transv r (u + v) = transv r u + transv r v := by
  unfold transv
  rw [symp_add_right]
  have h01 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases (symp r u) with hu | hu <;> rcases zmod2_cases (symp r v) with hv | hv
  · simp [hu, hv]
  · simp [hu, hv, h01, add_assoc]
  · simp [hu, hv, h01]; abel
  · simp [hu, hv, h01, h11]
    calc u + v = u + v + (r + r) := by rw [pt_add_self, add_zero]
      _ = u + r + (v + r) := by abel

lemma transv_involutive (r v : Pt N) : transv r (transv r v) = v := by
  unfold transv
  have h01 : (1 : ZMod 2) ≠ 0 := by decide
  rcases zmod2_cases (symp r v) with hv | hv
  · simp [hv]
  · simp only [hv, h01, ↓reduceIte, symp_add_right, symp_self, add_zero]
    rw [add_assoc, pt_add_self, add_zero]

lemma transv_injective (r : Pt N) : Function.Injective (transv r) :=
  Function.LeftInverse.injective (transv_involutive r)

lemma transv_symp (r u v : Pt N) : symp (transv r u) (transv r v) = symp u v := by
  unfold transv
  have h01 : (1 : ZMod 2) ≠ 0 := by decide
  rcases zmod2_cases (symp r u) with hu | hu <;> rcases zmod2_cases (symp r v) with hv | hv
  · simp [hu, hv]
  · simp [hu, hv, h01, symp_add_right, symp_comm u r]
  · simp [hu, hv, h01, symp_add_left]
  · simp only [h01, ↓reduceIte, symp_add_left, symp_add_right, symp_self, add_zero,
      symp_comm u r, hu, hv]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    calc symp u v + 1 + (1 + 0) = symp u v + (1 + 1) := by ring
      _ = symp u v := by rw [h11, add_zero]

lemma qform_transv_of_qform_one {r : Pt N} (hr : qform r = 1) (v : Pt N) :
    qform (transv r v) = qform v := by
  unfold transv
  have h01 : (1 : ZMod 2) ≠ 0 := by decide
  rcases zmod2_cases (symp r v) with hv | hv
  · simp [hv]
  · simp only [h01, ↓reduceIte, qform_add, hr, symp_comm v r, hv]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rw [add_assoc, h11, add_zero]

/-- Sign factor `η_r(v) ∈ {±1}` induced by conjugating `P_v` by the Clifford transvection
unitary `U_r = (1 + i P_r) / √2`. -/
noncomputable def transvSign (r v : Pt N) : ℝ :=
  if symp r v = 0 then 1 else (Complex.I * tau r v).re

lemma complex_I_mul_tau_eq {r v : Pt N} (h : symp r v = 1) :
    Complex.I * tau r v = 1 ∨ Complex.I * tau r v = -1 := by
  have hsq : (Complex.I * tau r v) * (Complex.I * tau r v) = 1 := by
    calc (Complex.I * tau r v) * (Complex.I * tau r v)
        = Complex.I ^ 2 * tau r v ^ 2 := by ring
      _ = (-1) * eps (symp r v) := by rw [Complex.I_sq, tau_sq]
      _ = 1 := by rw [h, eps_one]; ring
  exact mul_self_eq_one_iff.mp hsq

lemma transvSign_values (r v : Pt N) : transvSign r v = 1 ∨ transvSign r v = -1 := by
  unfold transvSign
  rcases zmod2_cases (symp r v) with h | h
  · simp [h]
  · have h01 : (1 : ZMod 2) ≠ 0 := by decide
    simp only [h, h01, ↓reduceIte]
    rcases complex_I_mul_tau_eq h with h1 | h1 <;> simp [h1]

lemma transvSign_cast {r v : Pt N} (h : symp r v = 1) :
    ((transvSign r v : ℝ) : ℂ) = Complex.I * tau r v := by
  unfold transvSign
  have h01 : (1 : ZMod 2) ≠ 0 := by decide
  simp only [h, h01, ↓reduceIte]
  rcases complex_I_mul_tau_eq h with h1 | h1 <;> simp [h1]

/-- Exact unitary conjugation identity (scaled by `2`):
`(1 + i P_r) P_v (1 - i P_r) = 2 η_r(v) P_{t_r(v)}`. -/
lemma transv_unitary_conj (r v : Pt N) :
    (1 + Complex.I • pauli r) * pauli v * (1 - Complex.I • pauli r) =
      (2 : ℂ) • (((transvSign r v : ℝ) : ℂ) • pauli (transv r v)) := by
  have h01 : (1 : ZMod 2) ≠ 0 := by decide
  rcases zmod2_cases (symp r v) with h | h
  · have hcomm : pauli v * pauli r = pauli r * pauli v := by
      rw [pauli_comm, h, eps_zero, one_smul]
    have hts : transvSign r v = 1 := by simp [transvSign, h]
    have htv : transv r v = v := by simp [transv, h]
    rw [hts, htv, Complex.ofReal_one, one_smul]
    calc (1 + Complex.I • pauli r) * pauli v * (1 - Complex.I • pauli r)
        = pauli v + Complex.I • (pauli r * pauli v) - Complex.I • (pauli v * pauli r)
            - (Complex.I * Complex.I) • (pauli r * (pauli v * pauli r)) := by
          simp only [add_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
            smul_smul, Matrix.mul_assoc]
          abel
      _ = pauli v + Complex.I • (pauli r * pauli v) - Complex.I • (pauli r * pauli v)
            - (-1 : ℂ) • (pauli r * (pauli r * pauli v)) := by
          rw [hcomm, Complex.I_mul_I]
      _ = pauli v + pauli v := by
          rw [← Matrix.mul_assoc, pauli_mul_self, one_mul, add_sub_cancel_right, neg_smul,
            one_smul, sub_neg_eq_add]
      _ = (2 : ℂ) • pauli v := by rw [two_smul]
  · have hanti : pauli v * pauli r = -(pauli r * pauli v) := by
      rw [pauli_comm, h, eps_one, neg_one_smul]
    have htv : transv r v = v + r := by simp [transv, h, h01]
    rw [htv, transvSign_cast h, add_comm v r]
    calc (1 + Complex.I • pauli r) * pauli v * (1 - Complex.I • pauli r)
        = pauli v + Complex.I • (pauli r * pauli v) - Complex.I • (pauli v * pauli r)
            - (Complex.I * Complex.I) • (pauli r * (pauli v * pauli r)) := by
          simp only [add_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
            smul_smul, Matrix.mul_assoc]
          abel
      _ = pauli v + Complex.I • (pauli r * pauli v) + Complex.I • (pauli r * pauli v)
            - (-1 : ℂ) • (pauli r * (-(pauli r * pauli v))) := by
          rw [hanti, smul_neg, sub_neg_eq_add, Complex.I_mul_I]
      _ = (2 : ℂ) • (Complex.I • (pauli r * pauli v)) := by
          rw [Matrix.mul_neg, ← Matrix.mul_assoc, pauli_mul_self, one_mul, neg_smul, one_smul,
            neg_neg, sub_self_add, ← two_smul ℂ]
      _ = (2 : ℂ) • ((Complex.I * tau r v) • pauli (r + v)) := by
          rw [pauli_mul, smul_smul, smul_smul, smul_smul, mul_assoc]
    where
      sub_self_add (X Y : Matrix (Vec N) (Vec N) ℂ) : X + Y + Y - X = Y + Y := by abel

/-- Fundamental sign-covariance law of a Clifford transvection on every commuting triple:
`η_r(u) η_r(v) η_r(u + v) · lineSign(t_r u, t_r v) = lineSign(u, v)`. -/
lemma transv_lineSign (r : Pt N) {u v : Pt N} (hcomm : symp u v = 0) :
    transvSign r u * transvSign r v * transvSign r (u + v) *
        lineSign (transv r u) (transv r v) = lineSign u v := by
  let W : Matrix (Vec N) (Vec N) ℂ := 1 + Complex.I • pauli r
  let W' : Matrix (Vec N) (Vec N) ℂ := 1 - Complex.I • pauli r
  have hWW' : W' * W = (2 : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ) := by
    dsimp [W, W']
    calc (1 - Complex.I • pauli r) * (1 + Complex.I • pauli r)
        = 1 + Complex.I • pauli r - Complex.I • pauli r
            - (Complex.I * Complex.I) • (pauli r * pauli r) := by
          simp only [sub_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          abel
      _ = 1 - (-1 : ℂ) • 1 := by rw [add_sub_cancel_right, Complex.I_mul_I, pauli_mul_self]
      _ = (2 : ℂ) • 1 := by rw [neg_smul, one_smul, sub_neg_eq_add, two_smul]
  have htau_eq : ∀ a b : Pt N, symp a b = 0 → tau a b = ((lineSign a b : ℝ) : ℂ) := by
    intro a b hab
    unfold lineSign
    rcases tau_eq_one_or_neg_one hab with h | h <;> simp [h]
  have hcomm' : symp (transv r u) (transv r v) = 0 := by rw [transv_symp, hcomm]
  have hprod : (W * pauli u * W') * (W * pauli v * W') =
      (2 : ℂ) • (W * (pauli u * pauli v) * W') := by
    calc (W * pauli u * W') * (W * pauli v * W')
        = W * pauli u * (W' * W) * pauli v * W' := by simp only [Matrix.mul_assoc]
      _ = W * pauli u * ((2 : ℂ) • 1) * pauli v * W' := by rw [hWW']
      _ = (2 : ℂ) • (W * (pauli u * pauli v) * W') := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one, Matrix.mul_assoc]
  have hlhs : (W * pauli u * W') * (W * pauli v * W') =
      ((4 : ℂ) * ((transvSign r u : ℝ) : ℂ) * ((transvSign r v : ℝ) : ℂ) *
        ((lineSign (transv r u) (transv r v) : ℝ) : ℂ)) • pauli (transv r (u + v)) := by
    rw [transv_unitary_conj r u, transv_unitary_conj r v, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, pauli_mul, htau_eq _ _ hcomm', ← transv_add,
      smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1; ring
  have hrhs : (2 : ℂ) • (W * (pauli u * pauli v) * W') =
      ((4 : ℂ) * ((lineSign u v : ℝ) : ℂ) * ((transvSign r (u + v) : ℝ) : ℂ)) •
        pauli (transv r (u + v)) := by
    rw [pauli_mul, htau_eq u v hcomm, Matrix.mul_smul, Matrix.smul_mul, transv_unitary_conj r (u + v),
      smul_smul, smul_smul, smul_smul]
    congr 1; ring
  have heqM := hlhs.symm.trans (hprod.trans hrhs)
  have htr := congrArg (fun M => (M * pauli (transv r (u + v))).trace) heqM
  simp only [Matrix.smul_mul, Matrix.trace_smul, trace_pauli_mul, ↓reduceIte, smul_eq_mul] at htr
  have h2N : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  have hC : ((transvSign r u : ℝ) : ℂ) * ((transvSign r v : ℝ) : ℂ) *
      ((lineSign (transv r u) (transv r v) : ℝ) : ℂ) =
      ((lineSign u v : ℝ) : ℂ) * ((transvSign r (u + v) : ℝ) : ℂ) := by
    have h1 := mul_right_cancel₀ h2N htr
    have h2 : (4 : ℂ) * (((transvSign r u : ℝ) : ℂ) * ((transvSign r v : ℝ) : ℂ) *
        ((lineSign (transv r u) (transv r v) : ℝ) : ℂ)) =
        (4 : ℂ) * (((lineSign u v : ℝ) : ℂ) * ((transvSign r (u + v) : ℝ) : ℂ)) := by
      linear_combination h1
    exact mul_left_cancel₀ h4 h2
  have hR : transvSign r u * transvSign r v * lineSign (transv r u) (transv r v) =
      lineSign u v * transvSign r (u + v) := by exact_mod_cast hC
  have hsq : transvSign r (u + v) * transvSign r (u + v) = 1 := by
    rcases transvSign_values r (u + v) with h | h <;> rw [h] <;> norm_num
  calc transvSign r u * transvSign r v * transvSign r (u + v) * lineSign (transv r u) (transv r v)
      = (transvSign r u * transvSign r v * lineSign (transv r u) (transv r v)) *
          transvSign r (u + v) := by ring
    _ = lineSign u v * (transvSign r (u + v) * transvSign r (u + v)) := by rw [hR]; ring
    _ = lineSign u v := by rw [hsq, mul_one]

/-- **Transvection invariance of violated context counts (all `N`).**
For any non-identity Pauli configuration `S` and any `±1` assignment `f` on `S`,
the transvected configuration `S.image (transv r)` admits a `±1` assignment `f'` with the
exact same number of violated contexts. -/
theorem transv_violatedLines_eq (r : Pt N) (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S)
    (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ∃ f' : Pt N → ℝ, (∀ u ∈ S.image (transv r), f' u = 1 ∨ f' u = -1) ∧
      (violatedLines (S.image (transv r)) f').card = (violatedLines S f).card := by
  let f' : Pt N → ℝ := fun x => transvSign r (transv r x) * f (transv r x)
  have hf' : ∀ x ∈ S.image (transv r), f' x = 1 ∨ f' x = -1 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    dsimp [f']
    rw [transv_involutive]
    rcases transvSign_values r u with h1 | h1 <;> rcases hf u hu with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  have h0' : (0 : Pt N) ∉ S.image (transv r) := by
    intro hm
    obtain ⟨u, hu, hzu⟩ := mem_image.mp hm
    have : u = 0 := transv_injective r (hzu.trans (transv_zero r).symm)
    exact h0 (this ▸ hu)
  have hcard_viol : (violated (S.image (transv r)) f').card = (violated S f).card := by
    refine Finset.card_bij'
      (fun p _ => (transv r p.1, transv r p.2))
      (fun p _ => (transv r p.1, transv r p.2)) ?_ ?_ ?_ ?_
    · intro p hp
      rcases p with ⟨x, y⟩
      obtain ⟨hpF, hbad⟩ := mem_filter.mp hp
      obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hpF
      obtain ⟨u, hu, rfl⟩ := mem_image.mp h1
      obtain ⟨v, hv, rfl⟩ := mem_image.mp h2
      have huvS : u + v ∈ S := by
        obtain ⟨w, hw, hweq⟩ := mem_image.mp h3
        rw [← transv_add] at hweq
        have := transv_injective r hweq
        rwa [← this]
      have hs' : symp u v = 0 := by rw [← transv_symp r u v]; exact hs
      refine mem_filter.mpr ⟨mem_flags.mpr ?_, ?_⟩
      · simpa [transv_involutive] using ⟨hu, hv, huvS, hs'⟩
      · dsimp only [transv_involutive]
        intro hgood
        rw [transv_involutive, transv_involutive] at hgood
        apply hbad
        dsimp only [f']
        rw [← transv_add, transv_involutive, transv_involutive, transv_involutive]
        have hls := transv_lineSign r hs'
        have hsq : ∀ a : Pt N, transvSign r a * transvSign r a = 1 := fun a => by
          rcases transvSign_values r a with h | h <;> rw [h] <;> norm_num
        calc transvSign r u * f u * (transvSign r v * f v) * (transvSign r (u + v) * f (u + v))
            = (transvSign r u * transvSign r v * transvSign r (u + v)) * (f u * f v * f (u + v)) := by ring
          _ = (transvSign r u * transvSign r v * transvSign r (u + v)) * lineSign u v := by rw [hgood]
          _ = (transvSign r u * transvSign r v * transvSign r (u + v)) *
                (transvSign r u * transvSign r v * transvSign r (u + v) * lineSign (transv r u) (transv r v)) := by
              rw [hls]
          _ = (transvSign r u * transvSign r u) * (transvSign r v * transvSign r v) *
                (transvSign r (u + v) * transvSign r (u + v)) * lineSign (transv r u) (transv r v) := by ring
          _ = lineSign (transv r u) (transv r v) := by rw [hsq u, hsq v, hsq (u + v)]; ring
    · intro p hp
      obtain ⟨hpF, hbad⟩ := mem_filter.mp hp
      obtain ⟨hu, hv, huv, hs⟩ := mem_flags.mp hpF
      refine mem_filter.mpr ⟨mem_flags.mpr ?_, ?_⟩
      · refine ⟨mem_image_of_mem _ hu, mem_image_of_mem _ hv, ?_, by rw [transv_symp, hs]⟩
        rw [← transv_add]; exact mem_image_of_mem _ huv
      · dsimp only [f']
        rw [← transv_add, transv_involutive, transv_involutive, transv_involutive]
        intro hgood
        apply hbad
        have hls := transv_lineSign r hs
        have hsq : ∀ a : Pt N, transvSign r a * transvSign r a = 1 := fun a => by
          rcases transvSign_values r a with h | h <;> rw [h] <;> norm_num
        calc f p.1 * f p.2 * f (p.1 + p.2)
            = (transvSign r p.1 * transvSign r p.1) * (transvSign r p.2 * transvSign r p.2) *
                (transvSign r (p.1 + p.2) * transvSign r (p.1 + p.2)) *
                (f p.1 * f p.2 * f (p.1 + p.2)) := by rw [hsq, hsq, hsq]; ring
          _ = (transvSign r p.1 * transvSign r p.2 * transvSign r (p.1 + p.2)) *
                (transvSign r p.1 * f p.1 * (transvSign r p.2 * f p.2) *
                  (transvSign r (p.1 + p.2) * f (p.1 + p.2))) := by ring
          _ = (transvSign r p.1 * transvSign r p.2 * transvSign r (p.1 + p.2)) *
                lineSign (transv r p.1) (transv r p.2) := by rw [hgood]
          _ = lineSign p.1 p.2 := hls
    · intro p _; exact Prod.ext (transv_involutive r p.1) (transv_involutive r p.2)
    · intro p _; exact Prod.ext (transv_involutive r p.1) (transv_involutive r p.2)
  refine ⟨f', hf', ?_⟩
  have h1 := card_violated_eq_six (S.image (transv r)) h0' f'
  have h2 := card_violated_eq_six S h0 f
  omega

/-- Exact character-sum count: for any `N` and any commuting pair `(u, v)` with `u, v, u + v ≠ 0`,
`8 · #{w : qform w = 1, ⟨w, u⟩ = qform u, ⟨w, v⟩ = qform v} + 4 · 2^N = 4^N`. -/
lemma card_odd_covering_flag {u v : Pt N} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u + v ≠ 0)
    (hs : symp u v = 0) :
    8 * (univ.filter fun w : Pt N => qform w = 1 ∧ symp w u = qform u ∧ symp w v = qform v).card
      + 4 * 2 ^ N = 4 ^ N := by
  have hind : ∀ w : Pt N,
      (if qform w = 1 ∧ symp w u = qform u ∧ symp w v = qform v then (1 : ℂ) else 0) =
      ((1 - eps (qform w)) * (1 + eps (symp w u + qform u)) * (1 + eps (symp w v + qform v))) / 8 := by
    intro w
    have hq : (if qform w = 1 then (1 : ℂ) else 0) = (1 - eps (qform w)) / 2 := by
      rcases zmod2_cases (qform w) with h | h <;> simp [h]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have ha : (if symp w u = qform u then (1 : ℂ) else 0) = (1 + eps (symp w u + qform u)) / 2 := by
      rcases zmod2_cases (symp w u) with h1 | h1 <;> rcases zmod2_cases (qform u) with h2 | h2 <;>
        simp [h1, h2, h11]
    have hb : (if symp w v = qform v then (1 : ℂ) else 0) = (1 + eps (symp w v + qform v)) / 2 := by
      rcases zmod2_cases (symp w v) with h1 | h1 <;> rcases zmod2_cases (qform v) with h2 | h2 <;>
        simp [h1, h2, h11]
    have hmul : (if qform w = 1 ∧ symp w u = qform u ∧ symp w v = qform v then (1 : ℂ) else 0) =
        (if qform w = 1 then (1 : ℂ) else 0) * (if symp w u = qform u then (1 : ℂ) else 0) *
          (if symp w v = qform v then (1 : ℂ) else 0) := by
      by_cases c1 : qform w = 1 <;> by_cases c2 : symp w u = qform u <;>
        by_cases c3 : symp w v = qform v <;> simp [c1, c2, c3]
    rw [hmul, hq, ha, hb]; ring
  have hsum_symp : ∀ a : Pt N, a ≠ 0 → ∑ w : Pt N, eps (symp w a) = 0 := by
    intro a ha
    have : ∀ w : Pt N, eps (symp w a) = eps (symp a w) := fun w => by rw [symp_comm]
    simp_rw [this]; exact sum_eps_symp ha
  have hsum_q : ∀ a : Pt N, ∑ w : Pt N, eps (qform w) * eps (symp w a + qform a) = (2 : ℂ) ^ N := by
    intro a
    have hrew : ∀ w : Pt N, eps (qform w) * eps (symp w a + qform a) =
        eps (qform a) * eps (qform w + symp a w) := fun w => by
      rw [symp_comm w a, eps_add, eps_add]; ring
    simp_rw [hrew, ← Finset.mul_sum, sum_eps_qform_add_symp]
    rw [← mul_assoc, eps_mul_self, one_mul]
  have hquv : qform (u + v) = qform u + qform v := by rw [qform_add, hs, add_zero]
  have hC : (((univ.filter fun w : Pt N =>
        qform w = 1 ∧ symp w u = qform u ∧ symp w v = qform v).card : ℕ) : ℂ) =
      ((4 : ℂ) ^ N - 4 * (2 : ℂ) ^ N) / 8 := by
    rw [Finset.card_filter]
    push_cast
    simp_rw [hind, ← Finset.sum_div]
    congr 1
    have hexp : ∀ w : Pt N,
        (1 - eps (qform w)) * (1 + eps (symp w u + qform u)) * (1 + eps (symp w v + qform v)) =
        1 + eps (qform u) * eps (symp w u) + eps (qform v) * eps (symp w v) +
          eps (qform u + qform v) * eps (symp w (u + v)) -
          eps (qform w) - eps (qform w) * eps (symp w u + qform u) -
          eps (qform w) * eps (symp w v + qform v) -
          eps (qform w) * eps (symp w (u + v) + qform (u + v)) := by
      intro w
      rw [hquv, symp_add_right]
      simp only [eps_add]
      ring
    simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      hsum_symp u hu, hsum_symp v hv, hsum_symp (u + v) huv, sum_eps_qform,
      hsum_q u, hsum_q v, hsum_q (u + v), Finset.sum_const, Finset.card_univ, card_pt,
      nsmul_eq_mul, mul_one]
    push_cast; ring
  have h2 : ((8 * (univ.filter fun w : Pt N =>
        qform w = 1 ∧ symp w u = qform u ∧ symp w v = qform v).card + 4 * 2 ^ N : ℕ) : ℂ) =
      ((4 ^ N : ℕ) : ℂ) := by
    push_cast; rw [hC]; ring
  exact_mod_cast h2

/-- For every `N ≥ 3` and any two distinct `w0, w` with `qform w0 = qform w = 1` and `symp w0 w = 0`,
there exists an odd point `z` anticommuting with both `w0` and `w`. -/
lemma exists_common_anticomm_odd (hN : 3 ≤ N) {w0 w : Pt N} (hw0 : qform w0 = 1)
    (hw : qform w = 1) (hne : w0 ≠ w) (hcomm : symp w0 w = 0) :
    ∃ z : Pt N, qform z = 1 ∧ symp z w0 = 1 ∧ symp z w = 1 := by
  have hw0_ne : w0 ≠ 0 := by intro h; rw [h, qform_zero] at hw0; exact absurd hw0 (by decide)
  have hw_ne : w ≠ 0 := by intro h; rw [h, qform_zero] at hw; exact absurd hw (by decide)
  have hsum_ne : w0 + w ≠ 0 := fun h => hne (pt_eq_of_add_eq_zero h)
  have hc := card_odd_covering_flag hw0_ne hw_ne hsum_ne hcomm
  rw [hw0, hw] at hc
  have h4ge : 4 * 2 ^ N < 4 ^ N := by
    have h2N : 8 ≤ 2 ^ N := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    have h4eq : 4 ^ N = 2 ^ N * 2 ^ N := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
    rw [h4eq]; nlinarith
  have hpos : 0 < (univ.filter fun z : Pt N => qform z = 1 ∧ symp z w0 = 1 ∧ symp z w = 1).card := by
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  exact ⟨z, (Finset.mem_filter.mp hz).2⟩

lemma mem_ellipticPoints {w u : Pt N} :
    u ∈ ellipticPoints N w ↔ u ≠ 0 ∧ qform u + symp w u = 0 := by
  unfold ellipticPoints
  rw [Finset.mem_filter]
  simp [qformShift]

/-- Transvection transport of `ellipticPoints N w` by an odd root `r` (`qform r = 1`). -/
lemma image_transv_ellipticPoints {r : Pt N} (hr : qform r = 1) (w : Pt N) :
    (ellipticPoints N w).image (transv r) = ellipticPoints N (transv r w) := by
  ext x
  simp only [mem_image, mem_ellipticPoints]
  constructor
  · rintro ⟨u, ⟨hu0, hqu⟩, rfl⟩
    refine ⟨fun h => hu0 (transv_injective r (h.trans (transv_zero r).symm)), ?_⟩
    rw [qform_transv_of_qform_one hr, transv_symp]; exact hqu
  · rintro ⟨hx0, hqx⟩
    refine ⟨transv r x, ⟨fun h => hx0 (by rw [← transv_involutive r x, h, transv_zero]), ?_⟩,
      transv_involutive r x⟩
    rw [qform_transv_of_qform_one hr, ← transv_symp r w (transv r x), transv_involutive]
    exact hqx

/-- Antisymmetric polar section of the hyperbolic quadric: `Q⁺(2N-1,2) ∩ w^⊥`. -/
def realPolar (N : ℕ) (w : Pt N) : Finset (Pt N) :=
  (realPoints N).filter fun u => symp w u = 0

lemma image_transv_realPolar {r : Pt N} (hr : qform r = 1) (w : Pt N) :
    (realPolar N w).image (transv r) = realPolar N (transv r w) := by
  ext x
  simp only [mem_image, realPolar, realPoints, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨u, ⟨⟨hu0, hqu⟩, hs⟩, rfl⟩
    refine ⟨⟨fun h => hu0 (transv_injective r (h.trans (transv_zero r).symm)),
      by rw [qform_transv_of_qform_one hr, hqu]⟩, by rw [transv_symp, hs]⟩
  · rintro ⟨⟨hx0, hqx⟩, hs⟩
    refine ⟨transv r x, ⟨⟨fun h => hx0 (by rw [← transv_involutive r x, h, transv_zero]),
      by rw [qform_transv_of_qform_one hr, hqx]⟩,
      by rw [← transv_symp r w (transv r x), transv_involutive, hs]⟩, transv_involutive r x⟩

/-- Any two odd points `w, w0` (`qform = 1`) for `N ≥ 3` are linked by at most two odd transvections:
so every `ellipticPoints N w` has the same minimum violated-line count as `ellipticPoints N w0`. -/
lemma ellipticPoints_min_equiv (hN : 3 ≤ N) {w0 w : Pt N} (hw0 : qform w0 = 1) (hw : qform w = 1)
    (f : Pt N → ℝ) (hf : ∀ u ∈ ellipticPoints N w, f u = 1 ∨ f u = -1) :
    ∃ f' : Pt N → ℝ, (∀ u ∈ ellipticPoints N w0, f' u = 1 ∨ f' u = -1) ∧
      (violatedLines (ellipticPoints N w0) f').card = (violatedLines (ellipticPoints N w) f).card := by
  have h0 : ∀ a : Pt N, (0 : Pt N) ∉ ellipticPoints N a := fun a => by simp [ellipticPoints]
  have hstep : ∀ (a b : Pt N), qform a = 1 → qform b = 1 → symp a b = 1 →
      ∀ g : Pt N → ℝ, (∀ u ∈ ellipticPoints N a, g u = 1 ∨ g u = -1) →
      ∃ g' : Pt N → ℝ, (∀ u ∈ ellipticPoints N b, g' u = 1 ∨ g' u = -1) ∧
        (violatedLines (ellipticPoints N b) g').card = (violatedLines (ellipticPoints N a) g).card := by
    intro a b ha hb hab g hg
    let r := a + b
    have hr : qform r = 1 := by simp [r, qform_add, ha, hb, hab, zmod2_add_self]
    have htr : transv r a = b := by
      have hsr : symp r a = 1 := by simp [r, symp_add_left, symp_self, symp_comm b a, hab]
      have h01 : (1 : ZMod 2) ≠ 0 := by decide
      simp only [transv, hsr, h01, ↓reduceIte, r]
      rw [← add_assoc, pt_add_self, zero_add]
    obtain ⟨g', hg', hcard⟩ := transv_violatedLines_eq r (ellipticPoints N a) (h0 a) g hg
    rw [image_transv_ellipticPoints hr, htr] at hg' hcard
    exact ⟨g', hg', hcard⟩
  by_cases heq : w = w0
  · subst heq; exact ⟨f, hf, rfl⟩
  · rcases zmod2_cases (symp w w0) with hs | hs
    · obtain ⟨z, hz, hzw0, hzw⟩ := exists_common_anticomm_odd hN hw0 hw (Ne.symm heq)
        (by rw [symp_comm]; exact hs)
      obtain ⟨f1, hf1, hc1⟩ := hstep w z hw hz (by rw [symp_comm]; exact hzw) f hf
      obtain ⟨f2, hf2, hc2⟩ := hstep z w0 hz hw0 hzw0 f1 hf1
      exact ⟨f2, hf2, hc2.trans hc1⟩
    · exact hstep w w0 hw hw0 hs f hf

/-- Any two antisymmetric polar sections `realPolar N w` and `realPolar N w0` (`qform = 1`, `N ≥ 3`)
have the exact same minimum violated-line count. -/
lemma realPolar_min_equiv (hN : 3 ≤ N) {w0 w : Pt N} (hw0 : qform w0 = 1) (hw : qform w = 1)
    (f : Pt N → ℝ) (hf : ∀ u ∈ realPolar N w, f u = 1 ∨ f u = -1) :
    ∃ f' : Pt N → ℝ, (∀ u ∈ realPolar N w0, f' u = 1 ∨ f' u = -1) ∧
      (violatedLines (realPolar N w0) f').card = (violatedLines (realPolar N w) f).card := by
  have h0 : ∀ a : Pt N, (0 : Pt N) ∉ realPolar N a := fun a => by simp [realPolar, realPoints]
  have hstep : ∀ (a b : Pt N), qform a = 1 → qform b = 1 → symp a b = 1 →
      ∀ g : Pt N → ℝ, (∀ u ∈ realPolar N a, g u = 1 ∨ g u = -1) →
      ∃ g' : Pt N → ℝ, (∀ u ∈ realPolar N b, g' u = 1 ∨ g' u = -1) ∧
        (violatedLines (realPolar N b) g').card = (violatedLines (realPolar N a) g).card := by
    intro a b ha hb hab g hg
    let r := a + b
    have hr : qform r = 1 := by simp [r, qform_add, ha, hb, hab, zmod2_add_self]
    have htr : transv r a = b := by
      have hsr : symp r a = 1 := by simp [r, symp_add_left, symp_self, symp_comm b a, hab]
      have h01 : (1 : ZMod 2) ≠ 0 := by decide
      simp only [transv, hsr, h01, ↓reduceIte, r]
      rw [← add_assoc, pt_add_self, zero_add]
    obtain ⟨g', hg', hcard⟩ := transv_violatedLines_eq r (realPolar N a) (h0 a) g hg
    rw [image_transv_realPolar hr, htr] at hg' hcard
    exact ⟨g', hg', hcard⟩
  by_cases heq : w = w0
  · subst heq; exact ⟨f, hf, rfl⟩
  · rcases zmod2_cases (symp w w0) with hs | hs
    · obtain ⟨z, hz, hzw0, hzw⟩ := exists_common_anticomm_odd hN hw0 hw (Ne.symm heq)
        (by rw [symp_comm]; exact hs)
      obtain ⟨f1, hf1, hc1⟩ := hstep w z hw hz (by rw [symp_comm]; exact hzw) f hf
      obtain ⟨f2, hf2, hc2⟩ := hstep z w0 hz hw0 hzw0 f1 hf1
      exact ⟨f2, hf2, hc2.trans hc1⟩
    · exact hstep w w0 hw hw0 hs f hf

end Transvections

/-! ### Part 2. Canonical `Y₀` and Exact CSS Witnesses (`315`, `1575`, `6975`) -/

/-- Canonical single-qubit `Y₀` observable on qubit `0`. -/
def Y0 (N : ℕ) (hN : 1 ≤ N) : Pt N := (Pi.single ⟨0, hN⟩ 1, Pi.single ⟨0, hN⟩ 1)

lemma qform_Y0 (N : ℕ) (hN : 1 ≤ N) : qform (Y0 N hN) = 1 := by
  simp [qform, Y0, dotProduct_single]

lemma symp_Y0_ptOfCode (N : ℕ) (hN : 1 ≤ N) (z : ℕ) :
    symp (Y0 N hN) (ptOfCode N z) = bitZ z 0 + bitZ z N := by
  simp [symp, Y0, ptOfCode, single_dotProduct, dotProduct_single]

/-- Bitmask of the 119-point elliptic quadric `Q⁻(7,2)` on four qubits. -/
def q7minusMask : ℕ := 0xc33c96690ff05aa533cc6699ff00aa553c3c6969f0f0a5a5cccc999900005554
/-- Negative-sign bitmask for the 315-violation CSS witness on `Q⁻(7,2)`. -/
def q7minusNeg  : ℕ := 0x8114022805500aa4114422985500aa54141429285050a5a44444999800000000

/-- Bitmask of the 255-point full symplectic space `W(7,2)` on four qubits. -/
def w72Mask : ℕ := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
/-- Negative-sign bitmask for the 1,575-violation CSS witness on `W(7,2)`. -/
def w72Neg  : ℕ := 0x8116033e055e0ffe117633fe55fefffe17163f3e5f5efffe7776fffefffe0000

/-- Bitmask of the 527-point hyperbolic quadric `Q⁺(9,2)` on five qubits. -/
def q9plusMask : ℕ :=
  0x69969669c33c3cc3a55a5aa50ff0f00f9966669933cccc3355aaaa55ff0000ff969669693c3cc3c35a5aa5a5f0f00f0f66669999cccc3333aaaa55550000ffff966996693cc33cc35aa55aa5f00ff00f66996699cc33cc33aa55aa5500ff00ff69696969c3c3c3c3a5a5a5a50f0f0f0f999999993333333355555555fffffffe
/-- Negative-sign bitmask for the 6,975-violation CSS witness on `Q⁺(9,2)`. -/
def q9plusNeg : ℕ :=
  0x68808000c0000002a00000040000000e880000100000003200000054000000fe80800100000003020000050400000f0e0000111000003332000055540000fffe800180000003000200050004000f000e00110010003300320055005400ff00fe0101010003030302050505040f0f0f0e11111110333333325555555400000000

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private def allUpTo (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allUpTo p n && p n

private lemma allUpTo_spec (p : ℕ → Bool) (n : ℕ) (h : allUpTo p n = true) {z : ℕ} (hz : z < n) :
    p z = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [allUpTo, Bool.and_eq_true] at h
    by_cases hzn : z < n
    · exact ih h.1 hzn
    · have : z = n := by omega
      subst this; exact h.2

private def q7minusCodeOk (z : ℕ) : Bool :=
  !q7minusMask.testBit z ||
    (decide (z ≠ 0) &&
      decide ((common z 0 z 4 4 + (if z.testBit 0 then 1 else 0) +
        (if z.testBit 4 then 1 else 0)) % 2 = 0))

private lemma q7minus_codes_ok : allUpTo q7minusCodeOk 256 = true := by decide +kernel

private lemma q7minus_card_cfg : (cfg 4 q7minusMask).card = 119 := by
  rw [card_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num)]; decide +kernel

lemma cfg_q7minus_eq : cfg 4 q7minusMask = ellipticPoints 4 (Y0 4 (by norm_num)) := by
  have hsub : cfg 4 q7minusMask ⊆ ellipticPoints 4 (Y0 4 (by norm_num)) := by
    intro u hu
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hu
    obtain ⟨hzlt, hzbit⟩ := mem_codes.mp hz
    have hok := allUpTo_spec q7minusCodeOk 256 q7minus_codes_ok hzlt
    simp only [q7minusCodeOk, hzbit, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hok
    rw [mem_ellipticPoints]
    refine ⟨fun h0 => hok.1 (ptOfCode_inj hzlt (by norm_num) (h0.trans (ptOfCode_zero 4).symm)), ?_⟩
    rw [qform, dot_eq_ycount, ycount_ptOfCode, symp_Y0_ptOfCode]
    have hb0 : bitZ z 0 = (((if z.testBit 0 then 1 else 0 : ℕ) : ZMod 2)) := by
      unfold bitZ; cases z.testBit 0 <;> simp
    have hb4 : bitZ z 4 = (((if z.testBit 4 then 1 else 0 : ℕ) : ZMod 2)) := by
      unfold bitZ; cases z.testBit 4 <;> simp
    rw [hb0, hb4, ← Nat.cast_add, ← Nat.cast_add, ← add_assoc]
    rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
    exact hok.2
  have hcardE : (ellipticPoints 4 (Y0 4 (by norm_num))).card = 119 := by
    have := card_ellipticPoints (N := 4) (qform_Y0 4 (by norm_num)); norm_num at this; omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [q7minus_card_cfg, hcardE])

private lemma w72_card_cfg : (cfg 4 w72Mask).card = 255 := by
  rw [card_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num)]; decide +kernel

lemma cfg_w72_eq : cfg 4 w72Mask = allPoints 4 := by
  have hsub : cfg 4 w72Mask ⊆ allPoints 4 := by
    intro u hu
    have h0 : (0 : Pt 4) ∉ cfg 4 w72Mask := zero_not_mem_cfg (by decide)
    exact mem_erase.mpr ⟨fun h => h0 (h ▸ hu), mem_univ _⟩
  have hcardA : (allPoints 4).card = 255 := by rw [card_allPoints]; norm_num
  exact Finset.eq_of_subset_of_card_le hsub (by rw [w72_card_cfg, hcardA])

private def q9plusCodeOk (z : ℕ) : Bool :=
  !q9plusMask.testBit z || (decide (z ≠ 0) && decide (common z 0 z 5 5 % 2 = 0))

private lemma q9plus_codes_ok : allUpTo q9plusCodeOk 1024 = true := by decide +kernel

private lemma q9plus_card_cfg : (cfg 5 q9plusMask).card = 527 := by
  rw [card_cfg_fast (b := 12) (N := 5) (by norm_num) (by norm_num)]; decide +kernel

lemma cfg_q9plus_eq : cfg 5 q9plusMask = realPoints 5 := by
  have hsub : cfg 5 q9plusMask ⊆ realPoints 5 := by
    intro u hu
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hu
    obtain ⟨hzlt, hzbit⟩ := mem_codes.mp hz
    have hok := allUpTo_spec q9plusCodeOk 1024 q9plus_codes_ok hzlt
    simp only [q9plusCodeOk, hzbit, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hok
    simp only [realPoints, mem_filter, mem_univ, true_and]
    refine ⟨fun h0 => hok.1 (ptOfCode_inj hzlt (by norm_num) (h0.trans (ptOfCode_zero 5).symm)), ?_⟩
    rw [qform, dot_eq_ycount, ycount_ptOfCode, ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
    exact hok.2
  have hcardR : (realPoints 5).card = 527 := by
    have := card_realPoints (N := 5); norm_num at this; omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [q9plus_card_cfg, hcardR])

-- Kernel evaluation of the CSS witness violation counts (16 blocks each, no `native_decide`).
private lemma q7m_vb :
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 0 = 42 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 1 = 0 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 2 = 120 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 3 = 144 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 4 = 120 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 5 = 144 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 6 = 120 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 7 = 144 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 8 = 120 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 9 = 144 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 10 = 120 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 11 = 144 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 12 = 120 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 13 = 144 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 14 = 120 ∧
    block (fastViolRow 10 4 q7minusMask q7minusNeg) 16 15 = 144 := by decide +kernel

private lemma w72_vb :
    block (fastViolRow 10 4 w72Mask w72Neg) 16 0 = 210 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 1 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 2 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 3 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 4 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 5 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 6 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 7 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 8 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 9 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 10 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 11 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 12 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 13 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 14 = 616 ∧
    block (fastViolRow 10 4 w72Mask w72Neg) 16 15 = 616 := by decide +kernel

private lemma q9p_vb_0 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 0 = 2250 := by decide +kernel
private lemma q9p_vb_1 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 1 = 2640 := by decide +kernel
private lemma q9p_vb_2 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 2 = 2640 := by decide +kernel
private lemma q9p_vb_3 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 3 = 2640 := by decide +kernel
private lemma q9p_vb_4 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 4 = 2640 := by decide +kernel
private lemma q9p_vb_5 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 5 = 2640 := by decide +kernel
private lemma q9p_vb_6 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 6 = 2640 := by decide +kernel
private lemma q9p_vb_7 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 7 = 2640 := by decide +kernel
private lemma q9p_vb_8 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 8 = 2640 := by decide +kernel
private lemma q9p_vb_9 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 9 = 2640 := by decide +kernel
private lemma q9p_vb_10 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 10 = 2640 := by decide +kernel
private lemma q9p_vb_11 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 11 = 2640 := by decide +kernel
private lemma q9p_vb_12 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 12 = 2640 := by decide +kernel
private lemma q9p_vb_13 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 13 = 2640 := by decide +kernel
private lemma q9p_vb_14 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 14 = 2640 := by decide +kernel
private lemma q9p_vb_15 : block (fastViolRow 12 5 q9plusMask q9plusNeg) 64 15 = 2640 := by decide +kernel

private lemma sgnOf_real_values (N neg : ℕ) (u : Pt N) :
    ((sgnOf N neg u : ℤ) : ℝ) = 1 ∨ ((sgnOf N neg u : ℤ) : ℝ) = -1 := by
  unfold sgnOf
  split_ifs <;> simp

/-- **Exact CSS witness on `Q⁻(7,2)`:** violates exactly `315` of the `1,071` contexts. -/
theorem q7minus_css_witness :
    ∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (violatedLines (ellipticPoints 4 (Y0 4 (by norm_num))) f).card = 315 := by
  refine ⟨fun u => ((sgnOf 4 q7minusNeg u : ℤ) : ℝ), sgnOf_real_values 4 q7minusNeg, ?_⟩
  rw [← cfg_q7minus_eq]
  have hv : (violated (cfg 4 q7minusMask) (fun u => ((sgnOf 4 q7minusNeg u : ℤ) : ℝ))).card = 6 * 315 := by
    have h := loop_blocks (fastViolRow 10 4 q7minusMask q7minusNeg) 16 16
    rcases q7m_vb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    rw [loop_sixteen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at h
    have e : (2 : ℕ) ^ (2 * 4) = 16 * 16 := by norm_num
    rw [card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num), e]
    exact h.trans (by norm_num)
  have h6 := card_violated_eq_six (cfg 4 q7minusMask) (zero_not_mem_cfg (by decide))
    (fun u => ((sgnOf 4 q7minusNeg u : ℤ) : ℝ))
  omega

/-- **Exact CSS witness on `W(7,2)`:** violates exactly `1,575` of the `5,355` contexts. -/
theorem w72_css_witness :
    ∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (violatedLines (allPoints 4) f).card = 1575 := by
  refine ⟨fun u => ((sgnOf 4 w72Neg u : ℤ) : ℝ), sgnOf_real_values 4 w72Neg, ?_⟩
  rw [← cfg_w72_eq]
  have hv : (violated (cfg 4 w72Mask) (fun u => ((sgnOf 4 w72Neg u : ℤ) : ℝ))).card = 6 * 1575 := by
    have h := loop_blocks (fastViolRow 10 4 w72Mask w72Neg) 16 16
    rcases w72_vb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    rw [loop_sixteen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at h
    have e : (2 : ℕ) ^ (2 * 4) = 16 * 16 := by norm_num
    rw [card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num), e]
    exact h.trans (by norm_num)
  have h6 := card_violated_eq_six (cfg 4 w72Mask) (zero_not_mem_cfg (by decide))
    (fun u => ((sgnOf 4 w72Neg u : ℤ) : ℝ))
  omega

/-- **Exact CSS witness on `Q⁺(9,2)`:** violates exactly `6,975` of the `23,715` contexts. -/
theorem q9plus_css_witness :
    ∃ f : Pt 5 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (violatedLines (realPoints 5) f).card = 6975 := by
  refine ⟨fun u => ((sgnOf 5 q9plusNeg u : ℤ) : ℝ), sgnOf_real_values 5 q9plusNeg, ?_⟩
  rw [← cfg_q9plus_eq]
  have hv : (violated (cfg 5 q9plusMask) (fun u => ((sgnOf 5 q9plusNeg u : ℤ) : ℝ))).card = 6 * 6975 := by
    have h := loop_blocks (fastViolRow 12 5 q9plusMask q9plusNeg) 64 16
    rw [loop_sixteen, q9p_vb_0, q9p_vb_1, q9p_vb_2, q9p_vb_3, q9p_vb_4, q9p_vb_5, q9p_vb_6,
      q9p_vb_7, q9p_vb_8, q9p_vb_9, q9p_vb_10, q9p_vb_11, q9p_vb_12, q9p_vb_13, q9p_vb_14,
      q9p_vb_15] at h
    have e : (2 : ℕ) ^ (2 * 5) = 64 * 16 := by norm_num
    rw [card_violated_cfg_fast (b := 12) (N := 5) (by norm_num) (by norm_num), e]
    exact h.trans (by norm_num)
  have h6 := card_violated_eq_six (cfg 5 q9plusMask) (zero_not_mem_cfg (by decide))
    (fun u => ((sgnOf 5 q9plusNeg u : ℤ) : ℝ))
  omega

/-! ### Part 3. Double-Counting Ladders, Zero-Gauge `W(7,2) ≃ Q⁺(9,2) ∩ Y₀^⊥`, and New Unconditional Bounds -/

/-- General flag double-counting inequality: if every flag of `T` lies in at most `c` subconfigurations
`S a` (`a ∈ I`, each `S a ⊆ T`), then `∑_{a ∈ I} #violatedLines(S a) ≤ c · #violatedLines(T)`. -/
@[nolint unusedArguments]
lemma sum_violatedLines_le_of_cover {N : ℕ} {α : Type*} [DecidableEq α]
    (T : Finset (Pt N)) (h0 : (0 : Pt N) ∉ T) (I : Finset α) (S : α → Finset (Pt N))
    (hsub : ∀ a ∈ I, S a ⊆ T) (c : ℕ)
    (hcov : ∀ p ∈ flags T, (I.filter fun a => p ∈ flags (S a)).card ≤ c)
    (f : Pt N → ℝ) :
    ∑ a ∈ I, (violatedLines (S a) f).card ≤ c * (violatedLines T f).card := by
  classical
  have h6 : 6 * ∑ a ∈ I, (violatedLines (S a) f).card = ∑ a ∈ I, (violated (S a) f).card := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    exact (card_violated_eq_six (S a) (fun h => h0 (hsub a ha h)) f).symm
  have hswap : ∑ a ∈ I, (violated (S a) f).card =
      ∑ p ∈ violated T f, (I.filter fun a => p ∈ flags (S a)).card := by
    have hfilt : ∀ a ∈ I, violated (S a) f = (violated T f).filter fun p => p ∈ flags (S a) := by
      intro a ha
      ext p
      simp only [violated, mem_filter]
      constructor
      · rintro ⟨hpS, hbad⟩
        obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hpS
        exact ⟨⟨mem_flags.mpr ⟨hsub a ha h1, hsub a ha h2, hsub a ha h3, hs⟩, hbad⟩, hpS⟩
      · rintro ⟨⟨_, hbad⟩, hpS⟩
        exact ⟨hpS, hbad⟩
    simp_rw [Finset.sum_congr rfl fun a ha => congrArg Finset.card (hfilt a ha)]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  have hbound : ∑ p ∈ violated T f, (I.filter fun a => p ∈ flags (S a)).card ≤
      c * (violated T f).card := by
    calc ∑ p ∈ violated T f, (I.filter fun a => p ∈ flags (S a)).card
        ≤ ∑ _p ∈ violated T f, c := Finset.sum_le_sum fun p hp => hcov p (mem_filter.mp hp).1
      _ = (violated T f).card * c := by rw [Finset.sum_const, smul_eq_mul]
      _ = c * (violated T f).card := Nat.mul_comm _ _
  have hT6 := card_violated_eq_six T h0 f
  rw [hT6] at hbound
  have h6le : 6 * ∑ a ∈ I, (violatedLines (S a) f).card ≤ 6 * (c * (violatedLines T f).card) := by
    calc 6 * ∑ a ∈ I, (violatedLines (S a) f).card
        = ∑ a ∈ I, (violated (S a) f).card := h6
      _ = ∑ p ∈ violated T f, (I.filter fun a => p ∈ flags (S a)).card := hswap
      _ ≤ c * (6 * (violatedLines T f).card) := hbound
      _ = 6 * (c * (violatedLines T f).card) := by ring
  omega

/-- Exact count of odd points `qform w = 1`: `2 · #{qform w = 1} + 2^N = 4^N`. -/
lemma card_qform_one (N : ℕ) :
    2 * (univ.filter fun w : Pt N => qform w = 1).card + 2 ^ N = 4 ^ N := by
  have h0 := card_qzero (N := N)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Pt N)))
    (fun w : Pt N => qform w = 0)
  have h1 : (univ.filter fun w : Pt N => ¬qform w = 0) = univ.filter fun w : Pt N => qform w = 1 := by
    ext w; simp only [mem_filter, mem_univ, true_and]
    rcases zmod2_cases (qform w) with h | h <;> simp [h]
  rw [h1, Finset.card_univ, card_pt] at hsplit
  omega

/-- **Exact `120 / 24 = 5` Double-Counting Ladder (`Q⁻(7,2) → W(7,2)`):**
Any lower bound `k` on `d(Q⁻(7,2))` lifts immediately to `5k ≤ d(W(7,2))`. -/
theorem d_W72_of_Q7minus (k : ℕ)
    (hk : ∀ g : Pt 4 → ℝ, (∀ u ∈ ellipticPoints 4 (Y0 4 (by norm_num)), g u = 1 ∨ g u = -1) →
      k ≤ (violatedLines (ellipticPoints 4 (Y0 4 (by norm_num))) g).card)
    (f : Pt 4 → ℝ) (hf : ∀ u ∈ allPoints 4, f u = 1 ∨ f u = -1) :
    5 * k ≤ (violatedLines (allPoints 4) f).card := by
  let I : Finset (Pt 4) := univ.filter fun w => qform w = 1
  have hI : I.card = 120 := by
    have := card_qform_one 4; norm_num at this; dsimp [I]; omega
  have hsub : ∀ w ∈ I, ellipticPoints 4 w ⊆ allPoints 4 := fun w _ u hu =>
    mem_erase.mpr ⟨(mem_filter.mp hu).2.1, mem_univ _⟩
  have hcov : ∀ p ∈ flags (allPoints 4), (I.filter fun w => p ∈ flags (ellipticPoints 4 w)).card ≤ 24 := by
    intro p hp
    obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hp
    have hu : p.1 ≠ 0 := (mem_erase.mp h1).1
    have hv : p.2 ≠ 0 := (mem_erase.mp h2).1
    have huv : p.1 + p.2 ≠ 0 := (mem_erase.mp h3).1
    have heq : I.filter (fun w => p ∈ flags (ellipticPoints 4 w)) =
        univ.filter fun w : Pt 4 => qform w = 1 ∧ symp w p.1 = qform p.1 ∧ symp w p.2 = qform p.2 := by
      ext w
      simp only [I, mem_filter, mem_univ, true_and, mem_flags, mem_ellipticPoints]
      constructor
      · rintro ⟨hw, ⟨_, hqu⟩, ⟨_, hqv⟩, _, _⟩
        exact ⟨hw, (zmod2_eq_of_add_eq_zero (by rw [add_comm]; exact hqu)),
          (zmod2_eq_of_add_eq_zero (by rw [add_comm]; exact hqv))⟩
      · rintro ⟨hw, hsu, hsv⟩
        refine ⟨hw, ⟨hu, by rw [hsu, zmod2_add_self]⟩, ⟨hv, by rw [hsv, zmod2_add_self]⟩,
          ⟨huv, by rw [qform_add, hs, add_zero, symp_add_right, hsu, hsv]
                   exact zmod2_add_self (qform p.1 + qform p.2)⟩, hs⟩
    rw [heq]
    have hc := card_odd_covering_flag hu hv huv hs
    norm_num at hc; omega
  have hsum := sum_violatedLines_le_of_cover (allPoints 4) (by simp [allPoints]) I
    (ellipticPoints 4) hsub 24 hcov f
  have hlow : I.card * k ≤ ∑ w ∈ I, (violatedLines (ellipticPoints 4 w) f).card := by
    calc I.card * k = ∑ _w ∈ I, k := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ w ∈ I, (violatedLines (ellipticPoints 4 w) f).card := by
        refine Finset.sum_le_sum fun w hw => ?_
        have hqw : qform w = 1 := (mem_filter.mp hw).2
        obtain ⟨g, hg, hcg⟩ := ellipticPoints_min_equiv (by norm_num) (qform_Y0 4 (by norm_num))
          hqw f (fun u hu => hf u (hsub w hw hu))
        rw [← hcg]; exact hk g hg
  rw [hI] at hlow
  omega
  where
    zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
      rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
        first | rfl | exact absurd h (by decide)

/-- Zero-gauge symplectic & sign-preserving lift `W(7,2) ↪ Q⁺(9,2) ∩ Y₀^⊥`:
places `Y₀^{q₀(u)}` on qubit 0 and `u` on qubits `1..4`. -/
def lift4to5 (u : Pt 4) : Pt 5 :=
  (Fin.cons (qform u) u.1, Fin.cons (qform u) u.2)

lemma lift4to5_injective : Function.Injective lift4to5 := by
  intro u v h
  exact Prod.ext
    (funext fun i => by simpa [lift4to5] using congrFun (congrArg Prod.fst h) i.succ)
    (funext fun i => by simpa [lift4to5] using congrFun (congrArg Prod.snd h) i.succ)

lemma lift4to5_qform (u : Pt 4) : qform (lift4to5 u) = 0 := by
  simp only [qform, lift4to5, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have hsq : qform u * qform u = qform u := by rcases zmod2_cases (qform u) with h | h <;> simp [h]
  change qform u * qform u + qform u = 0
  rw [hsq, zmod2_add_self]

lemma lift4to5_symp_Y0 (u : Pt 4) : symp (Y0 5 (by norm_num)) (lift4to5 u) = 0 := by
  simp [symp, Y0, lift4to5, single_dotProduct, dotProduct_single, zmod2_add_self]

lemma lift4to5_symp (u v : Pt 4) : symp (lift4to5 u) (lift4to5 v) = symp u v := by
  simp only [symp, lift4to5, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have h2 : qform u * qform v + qform v * qform u = 0 := by
    rw [mul_comm (qform v) (qform u), zmod2_add_self]
  calc qform u * qform v + ∑ i : Fin 4, u.2 i * v.1 i +
        (qform v * qform u + ∑ i : Fin 4, v.2 i * u.1 i)
      = (qform u * qform v + qform v * qform u) +
        (∑ i : Fin 4, u.2 i * v.1 i + ∑ i : Fin 4, v.2 i * u.1 i) := by ring
    _ = ∑ i : Fin 4, u.2 i * v.1 i + ∑ i : Fin 4, v.2 i * u.1 i := by rw [h2, zero_add]

lemma lift4to5_add {u v : Pt 4} (hs : symp u v = 0) :
    lift4to5 (u + v) = lift4to5 u + lift4to5 v := by
  have hq : qform (u + v) = qform u + qform v := by rw [qform_add, hs, add_zero]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [lift4to5, hq]

lemma ycount_lift4to5 (u : Pt 4) :
    ycount (lift4to5 u) = ycount u + if qform u = 1 then 1 else 0 := by
  unfold ycount
  rw [Finset.card_filter, Fin.sum_univ_succ, Finset.card_filter]
  simp only [lift4to5, Fin.cons_zero, Fin.cons_succ, and_self]
  ring

lemma tau_lift4to5 {u v : Pt 4} (hs : symp u v = 0) :
    tau (lift4to5 u) (lift4to5 v) = tau u v := by
  rw [tau, tau, ← lift4to5_add hs]
  have hq : qform (u + v) = qform u + qform v := by rw [qform_add, hs, add_zero]
  have hdot : (lift4to5 u).2 ⬝ᵥ (lift4to5 v).1 = qform u * qform v + u.2 ⬝ᵥ v.1 := by
    simp [lift4to5, dotProduct, Fin.sum_univ_succ]
  have hy1 := ycount_lift4to5 u
  have hy2 := ycount_lift4to5 v
  have hy3 := ycount_lift4to5 (u + v)
  rw [hy1, hy2, hy3, chi, hdot, eps_add, hq]
  rcases zmod2_cases (qform u) with hu | hu <;> rcases zmod2_cases (qform v) with hv | hv
  · simp [hu, hv, chi]
  · simp only [hu, hv, zero_add, zero_mul, eps_zero, one_mul, ↓reduceIte, chi]
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp only [h01, ↓reduceIte, add_zero]
    rw [show ycount u + (ycount v + 1) + 3 * (ycount (u + v) + 1) =
        (ycount u + ycount v + 3 * ycount (u + v)) + 4 by ring,
      pow_add, Complex.I_pow_four, mul_one]
  · simp only [hu, hv, add_zero, mul_zero, eps_zero, one_mul, ↓reduceIte, chi]
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp only [h01, ↓reduceIte, add_zero]
    rw [show ycount u + 1 + ycount v + 3 * (ycount (u + v) + 1) =
        (ycount u + ycount v + 3 * ycount (u + v)) + 4 by ring,
      pow_add, Complex.I_pow_four, mul_one]
  · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp only [hu, hv, h11, h01, mul_one, eps_one, ↓reduceIte, add_zero, chi]
    rw [show ycount u + 1 + (ycount v + 1) + 3 * ycount (u + v) =
        (ycount u + ycount v + 3 * ycount (u + v)) + 2 by ring,
      pow_add, Complex.I_sq]; ring

lemma lineSign_lift4to5 {u v : Pt 4} (hs : symp u v = 0) :
    lineSign (lift4to5 u) (lift4to5 v) = lineSign u v := by
  unfold lineSign; rw [tau_lift4to5 hs]

lemma image_lift4to5_allPoints :
    (allPoints 4).image lift4to5 = realPolar 5 (Y0 5 (by norm_num)) := by
  ext x
  simp only [mem_image, allPoints, mem_erase, mem_univ, and_true, realPolar, realPoints,
    mem_filter, true_and]
  constructor
  · rintro ⟨u, hu0, rfl⟩
    refine ⟨⟨fun h0 => hu0 (lift4to5_injective (h0.trans (by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [lift4to5, qform_zero]))),
      lift4to5_qform u⟩, lift4to5_symp_Y0 u⟩
  · rintro ⟨⟨hx0, hqx⟩, hsy⟩
    let u : Pt 4 := (fun i => x.1 i.succ, fun i => x.2 i.succ)
    have h0eq : x.1 0 = x.2 0 := by
      simp only [symp, Y0, single_dotProduct, dotProduct_single, one_mul, mul_one] at hsy
      change x.1 0 + x.2 0 = 0 at hsy
      rcases zmod2_cases (x.1 0) with h1 | h1 <;> rcases zmod2_cases (x.2 0) with h2 | h2
      · rw [h1, h2]
      · rw [h1, h2] at hsy; exact absurd hsy (by decide)
      · rw [h1, h2] at hsy; exact absurd hsy (by decide)
      · rw [h1, h2]
    have hq0 : x.2 0 = qform u := by
      simp only [qform, dotProduct, Fin.sum_univ_succ] at hqx
      rw [← h0eq] at hqx
      have hsq : x.1 0 * x.1 0 = x.1 0 := by rcases zmod2_cases (x.1 0) with h | h <;> simp [h]
      change x.1 0 * x.1 0 + qform u = 0 at hqx
      rw [hsq] at hqx
      rw [← h0eq]
      rcases zmod2_cases (x.1 0) with h1 | h1 <;> rcases zmod2_cases (qform u) with h2 | h2
      · rw [h1, h2]
      · rw [h1, h2] at hqx; exact absurd hqx (by decide)
      · rw [h1, h2] at hqx; exact absurd hqx (by decide)
      · rw [h1, h2]
    have hxu : lift4to5 u = x := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · refine Fin.cases ?_ (fun j => rfl) i
        simp [lift4to5, ← hq0, h0eq]
      · refine Fin.cases ?_ (fun j => rfl) i
        simp [lift4to5, ← hq0]
    have hu0 : u ≠ 0 := by
      intro hu; apply hx0; rw [← hxu, hu]
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [lift4to5, qform_zero]
    exact ⟨u, hu0, hxu⟩

lemma lift4to5_zero : lift4to5 0 = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [lift4to5, qform_zero]

lemma lift4to5_violatedLines_eq (S : Finset (Pt 4)) (h0 : (0 : Pt 4) ∉ S) (f : Pt 5 → ℝ) :
    (violatedLines S (f ∘ lift4to5)).card = (violatedLines (S.image lift4to5) f).card := by
  have h0_5 : (0 : Pt 5) ∉ S.image lift4to5 := by
    intro hm
    obtain ⟨u, hu, heq⟩ := mem_image.mp hm
    exact h0 (lift4to5_injective (heq.trans lift4to5_zero.symm) ▸ hu)
  have hcard : (violated S (f ∘ lift4to5)).card = (violated (S.image lift4to5) f).card := by
    refine Finset.card_bij (fun p _ => (lift4to5 p.1, lift4to5 p.2)) ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpF, hbad⟩ := mem_filter.mp hp
      obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hpF
      refine mem_filter.mpr ⟨mem_flags.mpr ⟨mem_image_of_mem _ h1, mem_image_of_mem _ h2,
        by rw [← lift4to5_add hs]; exact mem_image_of_mem _ h3, by rw [lift4to5_symp, hs]⟩, ?_⟩
      change f (lift4to5 p.1) * f (lift4to5 p.2) * f (lift4to5 p.1 + lift4to5 p.2) ≠
        lineSign (lift4to5 p.1) (lift4to5 p.2)
      rw [← lift4to5_add hs, lineSign_lift4to5 hs]
      exact hbad
    · intro p _ q _ h
      exact Prod.ext (lift4to5_injective (congrArg Prod.fst h))
        (lift4to5_injective (congrArg Prod.snd h))
    · intro q hq
      rcases q with ⟨x, y⟩
      obtain ⟨hqF, hbad⟩ := mem_filter.mp hq
      obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hqF
      obtain ⟨u, hu, rfl⟩ := mem_image.mp h1
      obtain ⟨v, hv, rfl⟩ := mem_image.mp h2
      have hs4 : symp u v = 0 := by rwa [lift4to5_symp] at hs
      have huv4 : u + v ∈ S := by
        obtain ⟨w, hw, hweq⟩ := mem_image.mp h3
        rw [← lift4to5_add hs4] at hweq
        rwa [← lift4to5_injective hweq]
      refine ⟨(u, v), mem_filter.mpr ⟨mem_flags.mpr ⟨hu, hv, huv4, hs4⟩, ?_⟩, rfl⟩
      change f (lift4to5 u) * f (lift4to5 v) * f (lift4to5 (u + v)) ≠ lineSign u v
      rw [lift4to5_add hs4, ← lineSign_lift4to5 hs4]
      exact hbad
  have h1 := card_violated_eq_six S h0 (f ∘ lift4to5)
  have h2 := card_violated_eq_six (S.image lift4to5) h0_5 f
  omega

lemma realPolar_Y0_violatedLines_eq (f : Pt 5 → ℝ) :
    (violatedLines (allPoints 4) (f ∘ lift4to5)).card =
      (violatedLines (realPolar 5 (Y0 5 (by norm_num))) f).card := by
  rw [← image_lift4to5_allPoints]
  exact lift4to5_violatedLines_eq (allPoints 4) (by simp [allPoints]) f

/-- **Exact `496 / 112` Double-Counting Ladder (`W(7,2) → Q⁺(9,2)`):**
Any lower bound `m` on `d(W(7,2))` lifts immediately to `496 m ≤ 112 · d(Q⁺(9,2))`. -/
theorem d_Q9plus_of_W72 (m : ℕ)
    (hm : ∀ g : Pt 4 → ℝ, (∀ u ∈ allPoints 4, g u = 1 ∨ g u = -1) →
      m ≤ (violatedLines (allPoints 4) g).card)
    (f : Pt 5 → ℝ) (hf : ∀ u ∈ realPoints 5, f u = 1 ∨ f u = -1) :
    496 * m ≤ 112 * (violatedLines (realPoints 5) f).card := by
  let I : Finset (Pt 5) := univ.filter fun w => qform w = 1
  have hI : I.card = 496 := by
    have := card_qform_one 5; norm_num at this; dsimp [I]; omega
  have hsub : ∀ w ∈ I, realPolar 5 w ⊆ realPoints 5 := fun w _ => filter_subset _ _
  have hcov : ∀ p ∈ flags (realPoints 5), (I.filter fun w => p ∈ flags (realPolar 5 w)).card ≤ 112 := by
    intro p hp
    obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hp
    have hu0 : p.1 ≠ 0 := (mem_filter.mp h1).2.1
    have hqu : qform p.1 = 0 := (mem_filter.mp h1).2.2
    have hv0 : p.2 ≠ 0 := (mem_filter.mp h2).2.1
    have hqv : qform p.2 = 0 := (mem_filter.mp h2).2.2
    have huv0 : p.1 + p.2 ≠ 0 := (mem_filter.mp h3).2.1
    have heq : I.filter (fun w => p ∈ flags (realPolar 5 w)) =
        univ.filter fun w : Pt 5 => qform w = 1 ∧ symp w p.1 = qform p.1 ∧ symp w p.2 = qform p.2 := by
      ext w
      simp only [I, mem_filter, mem_univ, true_and, mem_flags, realPolar, hqu, hqv]
      constructor
      · rintro ⟨hw, ⟨_, hsu⟩, ⟨_, hsv⟩, _, _⟩
        exact ⟨hw, hsu, hsv⟩
      · rintro ⟨hw, hsu, hsv⟩
        exact ⟨hw, ⟨h1, hsu⟩, ⟨h2, hsv⟩, ⟨h3, by rw [symp_add_right, hsu, hsv, add_zero]⟩, hs⟩
    rw [heq]
    have hc := card_odd_covering_flag hu0 hv0 huv0 hs
    norm_num at hc; omega
  have hsum := sum_violatedLines_le_of_cover (realPoints 5) (by simp [realPoints]) I
    (realPolar 5) hsub 112 hcov f
  have hlow : I.card * m ≤ ∑ w ∈ I, (violatedLines (realPolar 5 w) f).card := by
    calc I.card * m = ∑ _w ∈ I, m := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ w ∈ I, (violatedLines (realPolar 5 w) f).card := by
        refine Finset.sum_le_sum fun w hw => ?_
        have hqw : qform w = 1 := (mem_filter.mp hw).2
        obtain ⟨f0, hf0, hc0⟩ := realPolar_min_equiv (by norm_num) (qform_Y0 5 (by norm_num))
          hqw f (fun u hu => hf u (hsub w hw hu))
        rw [← hc0, ← realPolar_Y0_violatedLines_eq f0]
        refine hm (f0 ∘ lift4to5) fun u hu => hf0 (lift4to5 u) ?_
        rw [← image_lift4to5_allPoints]; exact mem_image_of_mem _ hu
  rw [hI] at hlow
  omega

/-- **Unconditional Lean 4 lower bound `d(W(7,2)) ≥ 1455`:**
strictly beats the complex spectral floor `1451` (`four_qubit_violated`) by `+4`,
by lifting the Kramers quaternionic floor `d(Q⁻(7,2)) ≥ 291` along the `120 / 24 = 5` ladder! -/
theorem w72_ge_1455 (f : Pt 4 → ℝ) (hf : ∀ u ∈ allPoints 4, f u = 1 ∨ f u = -1) :
    1455 ≤ (violatedLines (allPoints 4) f).card := by
  have h := d_W72_of_Q7minus 291
    (fun g hg => four_qubit_elliptic_contexts (Y0 4 (by norm_num)) (qform_Y0 4 (by norm_num)) g hg)
    f hf
  omega

/-- **Unconditional Lean 4 lower bound `d(Q⁺(9,2)) ≥ 6444`:**
strictly beats both the real spectral floor `6200` (by `+244`) and the existing Lean bound
`five_qubit_hyperbolic_contexts` `6426` (by `+18`), by lifting `w72_ge_1455` along the `496 / 112` ladder! -/
theorem q9plus_ge_6444 (f : Pt 5 → ℝ) (hf : ∀ u ∈ realPoints 5, f u = 1 ∨ f u = -1) :
    6444 ≤ (violatedLines (realPoints 5) f).card := by
  have h := d_Q9plus_of_W72 1455 w72_ge_1455 f hf
  omega

/-! ### Part 4. Pigeonhole Lemmas L1 & L4 and Exact Master Reduction `(315, 1575, 6975)` -/

/-- Exact incidence count for off-quadric sections of `Q⁻(2N-1,2)`:
for any flag `(u, v)` of `ellipticPoints N w` (`qform w = 1`),
`8 · #{d : qformShift w d = 1, ⟨d, u⟩ = 0, ⟨d, v⟩ = 0} = 4^N + 4 · 2^N`. -/
lemma card_off_elliptic_covering_flag {N : ℕ} {w u v : Pt N} (hw : qform w = 1)
    (hu : u ∈ ellipticPoints N w) (hv : v ∈ ellipticPoints N w) (huv : u + v ∈ ellipticPoints N w)
    (_hs : symp u v = 0) :
    8 * (univ.filter fun d : Pt N => qformShift w d = 1 ∧ symp d u = 0 ∧ symp d v = 0).card =
      4 ^ N + 4 * 2 ^ N := by
  have hu0 : u ≠ 0 := (mem_filter.mp hu).2.1
  have hqu : qformShift w u = 0 := (mem_filter.mp hu).2.2
  have hv0 : v ≠ 0 := (mem_filter.mp hv).2.1
  have hqv : qformShift w v = 0 := (mem_filter.mp hv).2.2
  have huv0 : u + v ≠ 0 := (mem_filter.mp huv).2.1
  have hquv : qformShift w (u + v) = 0 := (mem_filter.mp huv).2.2
  have hqw : ∀ a : Pt N, qformShift w a = 0 → qform (w + a) = 1 := by
    intro a ha
    rw [qform_add, hw]
    have : qform a + symp w a = 0 := ha
    linear_combination this
  have hsum_symp : ∀ a : Pt N, a ≠ 0 → ∑ d : Pt N, eps (symp d a) = 0 := by
    intro a ha
    have : ∀ d : Pt N, eps (symp d a) = eps (symp a d) := fun d => by rw [symp_comm]
    simp_rw [this]; exact sum_eps_symp ha
  have hsum_qs : ∀ a : Pt N, qformShift w a = 0 →
      ∑ d : Pt N, eps (qformShift w d) * eps (symp d a) = -(2 : ℂ) ^ N := by
    intro a ha
    have hrew : ∀ d : Pt N, eps (qformShift w d) * eps (symp d a) =
        eps (qform d + symp (w + a) d) := fun d => by
      rw [qformShift, ← eps_add, symp_add_left, symp_comm d a]; congr 1; ring
    simp_rw [hrew, sum_eps_qform_add_symp, hqw a ha, eps_one, neg_one_mul]
  have hsum_q0 : ∑ d : Pt N, eps (qformShift w d) = -(2 : ℂ) ^ N := by
    simp only [qformShift, sum_eps_qform_add_symp, hw, eps_one, neg_one_mul]
  have hind : ∀ d : Pt N,
      (if qformShift w d = 1 ∧ symp d u = 0 ∧ symp d v = 0 then (1 : ℂ) else 0) =
      ((1 - eps (qformShift w d)) * (1 + eps (symp d u)) * (1 + eps (symp d v))) / 8 := by
    intro d
    have h1 : (if qformShift w d = 1 then (1 : ℂ) else 0) = (1 - eps (qformShift w d)) / 2 := by
      rcases zmod2_cases (qformShift w d) with h | h <;> simp [h]
    have h2 : (if symp d u = 0 then (1 : ℂ) else 0) = (1 + eps (symp d u)) / 2 := indicator_eq _
    have h3 : (if symp d v = 0 then (1 : ℂ) else 0) = (1 + eps (symp d v)) / 2 := indicator_eq _
    have hmul : (if qformShift w d = 1 ∧ symp d u = 0 ∧ symp d v = 0 then (1 : ℂ) else 0) =
        (if qformShift w d = 1 then (1 : ℂ) else 0) * (if symp d u = 0 then (1 : ℂ) else 0) *
          (if symp d v = 0 then (1 : ℂ) else 0) := by
      by_cases c1 : qformShift w d = 1 <;> by_cases c2 : symp d u = 0 <;>
        by_cases c3 : symp d v = 0 <;> simp [c1, c2, c3]
    rw [hmul, h1, h2, h3]; ring
  have hC : (((univ.filter fun d : Pt N =>
        qformShift w d = 1 ∧ symp d u = 0 ∧ symp d v = 0).card : ℕ) : ℂ) =
      ((4 : ℂ) ^ N + 4 * (2 : ℂ) ^ N) / 8 := by
    rw [Finset.card_filter]; push_cast; simp_rw [hind, ← Finset.sum_div]; congr 1
    have hexp : ∀ d : Pt N,
        (1 - eps (qformShift w d)) * (1 + eps (symp d u)) * (1 + eps (symp d v)) =
        1 + eps (symp d u) + eps (symp d v) + eps (symp d (u + v)) -
          eps (qformShift w d) - eps (qformShift w d) * eps (symp d u) -
          eps (qformShift w d) * eps (symp d v) - eps (qformShift w d) * eps (symp d (u + v)) := by
      intro d; rw [symp_add_right, eps_add]; ring
    simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum_symp u hu0, hsum_symp v hv0,
      hsum_symp (u + v) huv0, hsum_q0, hsum_qs u hqu, hsum_qs v hqv, hsum_qs (u + v) hquv,
      Finset.sum_const, Finset.card_univ, card_pt, nsmul_eq_mul, mul_one]
    push_cast; ring
  have h2 : ((8 * (univ.filter fun d : Pt N =>
        qformShift w d = 1 ∧ symp d u = 0 ∧ symp d v = 0).card : ℕ) : ℂ) =
      ((4 ^ N + 4 * 2 ^ N : ℕ) : ℂ) := by
    push_cast; rw [hC]; ring
  exact_mod_cast h2

/-- **Lemma L1 (`Q⁻(7,2)` section pigeonhole, cf. Jonah [J1]):**
Every assignment on `Q⁻(7,2)` with `≤ 314` violated contexts has at least one off-quadric point
`d` (`136` choices, `40` per line, `40 · 314 = 12,560 < 12,648 = 136 · 93`) whose polar section
`Q⁻(7,2) ∩ d^⊥` (isomorphic to `W(5,2)`) has `≤ 92` violated contexts. -/
theorem lemma_L1_q7minus_section_le_92 (w : Pt 4) (hw : qform w = 1) (f : Pt 4 → ℝ)
    (hle : (violatedLines (ellipticPoints 4 w) f).card ≤ 314) :
    ∃ d : Pt 4, qformShift w d = 1 ∧
      (violatedLines ((ellipticPoints 4 w).filter fun u => symp d u = 0) f).card ≤ 92 := by
  let I : Finset (Pt 4) := univ.filter fun d => qformShift w d = 1
  have hI : I.card = 136 := by
    have h0 := card_qshift_zero hw
    have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Pt 4)))
      (fun d : Pt 4 => qformShift w d = 0)
    have h1 : (univ.filter fun d : Pt 4 => ¬qformShift w d = 0) = I := by
      ext d; simp only [I, mem_filter, mem_univ, true_and]
      rcases zmod2_cases (qformShift w d) with h | h <;> simp [h]
    rw [h1, Finset.card_univ, card_pt] at hsplit
    norm_num at h0 hsplit; omega
  have hcov : ∀ p ∈ flags (ellipticPoints 4 w),
      (I.filter fun d => p ∈ flags ((ellipticPoints 4 w).filter fun u => symp d u = 0)).card ≤ 40 := by
    intro p hp
    obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hp
    have heq : I.filter (fun d => p ∈ flags ((ellipticPoints 4 w).filter fun u => symp d u = 0)) =
        univ.filter fun d : Pt 4 => qformShift w d = 1 ∧ symp d p.1 = 0 ∧ symp d p.2 = 0 := by
      ext d
      simp only [I, mem_filter, mem_univ, true_and, mem_flags]
      constructor
      · rintro ⟨hd, ⟨_, hsu⟩, ⟨_, hsv⟩, _, _⟩; exact ⟨hd, hsu, hsv⟩
      · rintro ⟨hd, hsu, hsv⟩
        exact ⟨hd, ⟨h1, hsu⟩, ⟨h2, hsv⟩, ⟨h3, by rw [symp_add_right, hsu, hsv, add_zero]⟩, hs⟩
    rw [heq]
    have hc := card_off_elliptic_covering_flag hw h1 h2 h3 hs
    norm_num at hc; omega
  have hsum := sum_violatedLines_le_of_cover (ellipticPoints 4 w) (by simp [ellipticPoints]) I
    (fun d => (ellipticPoints 4 w).filter fun u => symp d u = 0)
    (fun _ _ => filter_subset _ _) 40 hcov f
  by_contra hall
  push Not at hall
  have hlow : I.card * 93 ≤ ∑ d ∈ I,
      (violatedLines ((ellipticPoints 4 w).filter fun u => symp d u = 0) f).card := by
    calc I.card * 93 = ∑ _d ∈ I, 93 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ d ∈ I, (violatedLines ((ellipticPoints 4 w).filter fun u => symp d u = 0) f).card :=
        Finset.sum_le_sum fun d hd => hall d (mem_filter.mp hd).2
  rw [hI] at hlow
  omega

/-- Exact count of points commuting with two distinct nonzero points `a, b` (`a + b ≠ 0`):
`4 · #{u : ⟨u, a⟩ = 0, ⟨u, b⟩ = 0} = 4^N`. -/
lemma card_commuting_two {N : ℕ} {a b : Pt N} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    4 * (univ.filter fun u : Pt N => symp u a = 0 ∧ symp u b = 0).card = 4 ^ N := by
  have hsum_symp : ∀ x : Pt N, x ≠ 0 → ∑ u : Pt N, eps (symp u x) = 0 := by
    intro x hx
    have : ∀ u : Pt N, eps (symp u x) = eps (symp x u) := fun u => by rw [symp_comm]
    simp_rw [this]; exact sum_eps_symp hx
  have hind : ∀ u : Pt N, (if symp u a = 0 ∧ symp u b = 0 then (1 : ℂ) else 0) =
      (1 + eps (symp u a) + eps (symp u b) + eps (symp u (a + b))) / 4 := by
    intro u
    have hmul : (if symp u a = 0 ∧ symp u b = 0 then (1 : ℂ) else 0) =
        (if symp u a = 0 then (1 : ℂ) else 0) * (if symp u b = 0 then (1 : ℂ) else 0) := by
      by_cases c1 : symp u a = 0 <;> by_cases c2 : symp u b = 0 <;> simp [c1, c2]
    rw [hmul, indicator_eq, indicator_eq, symp_add_right, eps_add]; ring
  have hC : (((univ.filter fun u : Pt N => symp u a = 0 ∧ symp u b = 0).card : ℕ) : ℂ) =
      (4 : ℂ) ^ N / 4 := by
    rw [Finset.card_filter]; push_cast
    simp_rw [hind, ← Finset.sum_div, Finset.sum_add_distrib, hsum_symp a ha, hsum_symp b hb,
      hsum_symp (a + b) hab, Finset.sum_const, Finset.card_univ, card_pt, nsmul_eq_mul, mul_one]
    push_cast; ring
  have h2 : ((4 * (univ.filter fun u : Pt N => symp u a = 0 ∧ symp u b = 0).card : ℕ) : ℂ) =
      ((4 ^ N : ℕ) : ℂ) := by push_cast; rw [hC]; ring
  exact_mod_cast h2

/-- **Lemma L4 (`W(5,2)` hyperplane pigeonhole, cf. Jonah [J1]):**
Every assignment on `W(5,2)` with `≤ 92` violated contexts has at least one hyperplane `u^⊥`
(`63` hyperplanes, `15` per line, `15 · 92 = 1,380 < 1,386 = 63 · 22`) with `≤ 21` violated contexts. -/
theorem lemma_L4_w52_hyperplane_le_21 (f : Pt 3 → ℝ)
    (hle : (violatedLines (allPoints 3) f).card ≤ 92) :
    ∃ u ∈ allPoints 3,
      (violatedLines ((allPoints 3).filter fun v => symp u v = 0) f).card ≤ 21 := by
  have hI : (allPoints 3).card = 63 := by rw [card_allPoints]; norm_num
  have hcov : ∀ p ∈ flags (allPoints 3),
      ((allPoints 3).filter fun u => p ∈ flags ((allPoints 3).filter fun v => symp u v = 0)).card ≤ 15 := by
    intro p hp
    obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hp
    have ha : p.1 ≠ 0 := (mem_erase.mp h1).1
    have hb : p.2 ≠ 0 := (mem_erase.mp h2).1
    have hab : p.1 + p.2 ≠ 0 := (mem_erase.mp h3).1
    have heq : (allPoints 3).filter (fun u => p ∈ flags ((allPoints 3).filter fun v => symp u v = 0)) =
        (univ.filter fun u : Pt 3 => symp u p.1 = 0 ∧ symp u p.2 = 0).erase 0 := by
      ext u
      simp only [allPoints, mem_filter, mem_erase, mem_univ, and_true, true_and, mem_flags]
      constructor
      · rintro ⟨hu0, ⟨_, hsu⟩, ⟨_, hsv⟩, _, _⟩; exact ⟨hu0, hsu, hsv⟩
      · rintro ⟨hu0, hsu, hsv⟩
        exact ⟨hu0, ⟨ha, hsu⟩, ⟨hb, hsv⟩, ⟨hab, by rw [symp_add_right, hsu, hsv, add_zero]⟩, hs⟩
    rw [heq, Finset.card_erase_of_mem (by simp [symp_comm, symp_zero_right])]
    have hc := card_commuting_two ha hb hab
    norm_num at hc; omega
  have hsum := sum_violatedLines_le_of_cover (allPoints 3) (by simp [allPoints]) (allPoints 3)
    (fun u => (allPoints 3).filter fun v => symp u v = 0)
    (fun _ _ => filter_subset _ _) 15 hcov f
  by_contra hall
  push Not at hall
  have hlow : (allPoints 3).card * 22 ≤ ∑ u ∈ allPoints 3,
      (violatedLines ((allPoints 3).filter fun v => symp u v = 0) f).card := by
    calc (allPoints 3).card * 22 = ∑ _u ∈ allPoints 3, 22 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ u ∈ allPoints 3, (violatedLines ((allPoints 3).filter fun v => symp u v = 0) f).card :=
        Finset.sum_le_sum fun u hu => hall u hu
  rw [hI] at hlow
  omega

/-- **Exact Degrees Master Theorem (`Q⁻(7,2) = 315`, `W(7,2) = 1575`, `Q⁺(9,2) = 6975`):**
Combining the `120 / 24` and `496 / 112` double-counting ladders with the three kernel-verified
CSS witnesses, the single lower bound `d(Q⁻(7,2)) ≥ 315` (verified independently across all 42
`Sp(6,2)` orbits via exact pure-integer certificates in `src/w52_census_verify.c` and
`scripts/exact_degrees_n4_n5.py`, following Jonah [J1]) determines all three exact contextuality
degrees simultaneously. -/
theorem exact_degrees_n4_n5_of_q7minus_315
    (hq7 : ∀ f : Pt 4 → ℝ, (∀ u ∈ ellipticPoints 4 (Y0 4 (by norm_num)), f u = 1 ∨ f u = -1) →
      315 ≤ (violatedLines (ellipticPoints 4 (Y0 4 (by norm_num))) f).card) :
    ((∀ f : Pt 4 → ℝ, (∀ u ∈ ellipticPoints 4 (Y0 4 (by norm_num)), f u = 1 ∨ f u = -1) →
        315 ≤ (violatedLines (ellipticPoints 4 (Y0 4 (by norm_num))) f).card) ∧
      (∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
        (violatedLines (ellipticPoints 4 (Y0 4 (by norm_num))) f).card = 315)) ∧
    ((∀ f : Pt 4 → ℝ, (∀ u ∈ allPoints 4, f u = 1 ∨ f u = -1) →
        1575 ≤ (violatedLines (allPoints 4) f).card) ∧
      (∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
        (violatedLines (allPoints 4) f).card = 1575)) ∧
    ((∀ f : Pt 5 → ℝ, (∀ u ∈ realPoints 5, f u = 1 ∨ f u = -1) →
        6975 ≤ (violatedLines (realPoints 5) f).card) ∧
      (∃ f : Pt 5 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
        (violatedLines (realPoints 5) f).card = 6975)) := by
  have hw72 : ∀ f : Pt 4 → ℝ, (∀ u ∈ allPoints 4, f u = 1 ∨ f u = -1) →
      1575 ≤ (violatedLines (allPoints 4) f).card := fun f hf => by
    have h := d_W72_of_Q7minus 315 hq7 f hf; omega
  have hq9p : ∀ f : Pt 5 → ℝ, (∀ u ∈ realPoints 5, f u = 1 ∨ f u = -1) →
      6975 ≤ (violatedLines (realPoints 5) f).card := fun f hf => by
    have h := d_Q9plus_of_W72 1575 hw72 f hf; omega
  exact ⟨⟨hq7, q7minus_css_witness⟩, ⟨hw72, w72_css_witness⟩, ⟨hq9p, q9plus_css_witness⟩⟩

end HoggarBound.ExactDegreesN4N5

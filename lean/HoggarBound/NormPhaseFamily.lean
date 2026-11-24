/-
Infinite Family of Non-Closed, Contextual, Floor-Saturating Flat Phase States |Ψ_{3m}⟩ (v1.8.0)

Resolves the Section 12 open problem ("an infinite family of non-closed configurations that
attain the floor") completely and unconditionally inside Lean 4's kernel for EVERY `m ≥ 1`
(`N = 3m` qubits, `q = 2^m`, `D = 2^{3m} = q^3`):

For `F = GaloisField 2 m` (`|F| = q = 2^m`), define the pure-CCZ real phase state on `N = 3m`
qubits (identifying `Vec (3m) ≃ₗ[ZMod 2] (Fin 3 → F)`):

    |Ψ_{3m}⟩ = 2^{-3m/2} ∑_{x ∈ F³} (-1)^{Tr_{F/F₂}(x₀ x₁ x₂)} |x⟩.

Main kernel-checked theorems (for EVERY `m ≥ 1`, no `sorry`, strictly standard axioms):
  * `detPhase_isFlatState`              : `|Ψ_{3m}⟩` is a unit vector flat on `detSupport` with
                                          modulus `1/q = 2^{-m}` (constant trilinear rank `r = 2m`).
  * `detSupport_card`                   : `|S_{3m}| = (q³ - 1) q²`.
  * `detSupport_not_closed`             : `S_{3m}` is strictly non-closed for every `m ≥ 1`.
  * `detSupport_flags_card`             : `|flags S_{3m}| = (q³ - 1) q⁴ (q² + q - 3)`.
  * `infinite_nonclosed_saturated_family` : for ALL `m ≥ 1`, exact contextuality degree
                                          `d(S_{3m}) = (q³ - 1) q³ (q - 1) (q - 2) / 12`
                                          attaining the spectral floor, and strictly positive
                                          for every `m ≥ 2`.
-/

import HoggarBound.SaturationTheory
import HoggarBound.IndependentContexts
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace

open Finset Matrix BigOperators

namespace HoggarBound.NormPhaseFamily

/-! ### Part 1. Characteristic-2 Finite Field Trace and Frobenius Inverse -/

/-- The `F → ZMod 2` field trace. -/
@[nolint unusedArguments]
noncomputable abbrev trF (F : Type*) [Field F] [Fintype F] [Algebra (ZMod 2) F] :
    F →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) F

section Char2Basic

variable {F : Type*} [Field F] [CharP F 2]

lemma char2_add_self (x : F) : x + x = 0 := CharTwo.add_self_eq_zero x

lemma char2_two : (2 : F) = 0 := CharTwo.two_eq_zero

lemma char2_add_sq (x y : F) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ring_nf; simp [h2]

lemma char2_eq_of_add_eq_zero {u v : F} (h : u + v = 0) : u = v := by
  calc u = u + (v + v) := by rw [char2_add_self, add_zero]
    _ = (u + v) + v := by ring
    _ = v := by rw [h, zero_add]

end Char2Basic

section FiniteFieldChar2

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] [Algebra (ZMod 2) F]

omit [DecidableEq F] in
/-- In characteristic 2, the field trace satisfies `Tr(x²) = Tr(x)` because Frobenius is a
`ZMod 2`-algebra automorphism of `F`. -/
lemma trF_sq (x : F) : trF F (x ^ 2) = trF F x := by
  let φHom : F →ₐ[ZMod 2] F :=
    { toFun := fun a => a ^ 2
      map_one' := one_pow 2
      map_mul' := fun a b => mul_pow a b 2
      map_zero' := zero_pow (by norm_num)
      map_add' := fun a b => char2_add_sq a b
      commutes' := fun r => by
        rcases zmod2_cases r with rfl | rfl <;> simp }
  have hinj : Function.Injective φHom := by
    intro a b hab
    change a ^ 2 = b ^ 2 at hab
    have h0 : (a + b) ^ 2 = 0 := by rw [char2_add_sq, hab, char2_add_self]
    exact char2_eq_of_add_eq_zero (sq_eq_zero_iff.mp h0)
  let φ : F ≃ₐ[ZMod 2] F := AlgEquiv.ofBijective φHom (Finite.injective_iff_bijective.mp hinj)
  have hconj : Algebra.lmul (ZMod 2) F (φ x)
      = φ.toLinearEquiv.toLinearMap ∘ₗ Algebra.lmul (ZMod 2) F x ∘ₗ
          φ.symm.toLinearEquiv.toLinearMap := by
    ext y
    change φ x * y = φ (x * φ.symm y)
    rw [map_mul, AlgEquiv.apply_symm_apply]
  change LinearMap.trace (ZMod 2) F (Algebra.lmul (ZMod 2) F (φ x)) =
    LinearMap.trace (ZMod 2) F (Algebra.lmul (ZMod 2) F x)
  rw [hconj]
  exact LinearMap.trace_conj' (Algebra.lmul (ZMod 2) F x) φ.toLinearEquiv

/-- Nondegeneracy of the `ZMod 2`-trace on any finite field of characteristic 2. -/
lemma trF_nondeg {a : F} (ha : a ≠ 0) : ∃ b : F, trF F (a * b) = 1 := by
  have hrc : ringChar F = 2 := ringChar.eq F 2
  have hne : ∃ b : F, trF F (a * b) ≠ 0 := by
    let : CharP F (ringChar F) := ringChar.charP F
    have : Fact (Nat.Prime (ringChar F)) := ⟨by rw [hrc]; exact Nat.prime_two⟩
    let eR : ZMod (ringChar F) ≃+* ZMod 2 := ZMod.ringEquivCongr hrc
    let : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
    obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate F ha
    refine ⟨b, ?_⟩
    have halg : ∀ (r : ZMod (ringChar F)) (y : F),
        r • y = (eR r) • y := by
      intro r y
      rw [Algebra.smul_def, Algebra.smul_def]
      congr 1
      have h1 : (algebraMap (ZMod (ringChar F)) F) = (algebraMap (ZMod 2) F).comp eR.toRingHom := by
        apply Subsingleton.elim
      rw [h1]; rfl
    have htr_eq : eR (Algebra.trace (ZMod (ringChar F)) F (a * b)) = trF F (a * b) := by
      let B := Module.Basis.ofVectorSpace (ZMod (ringChar F)) F
      let : Fintype (Module.Basis.ofVectorSpaceIndex (ZMod (ringChar F)) F) := Fintype.ofFinite _
      let B2 : Module.Basis (Module.Basis.ofVectorSpaceIndex (ZMod (ringChar F)) F) (ZMod 2) F :=
        Module.Basis.mk
          (by
            rw [Fintype.linearIndependent_iff]
            intro g hg i
            have hg' : ∑ j, (eR.symm (g j)) • B j = 0 := by
              convert hg using 1
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [halg, eR.apply_symm_apply]
            have h0 := (Fintype.linearIndependent_iff.mp B.linearIndependent) (fun j => eR.symm (g j)) hg' i
            exact eR.symm.injective (by simpa using h0))
          (by
            intro y _
            rw [← B.sum_repr y]
            refine Submodule.sum_mem _ fun j _ => ?_
            rw [halg]
            exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
      rw [Algebra.trace_eq_matrix_trace B, Algebra.trace_eq_matrix_trace B2]
      simp only [Matrix.trace, Matrix.diag_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hB2 : ∀ j, B2 j = B j := fun j => Module.Basis.mk_apply _ _ j
      have hrepr : ∀ y : F, B2.repr y i = eR (B.repr y i) := by
        intro y
        have hsum : ∑ j, (eR (B.repr y j)) • B2 j = y := by
          simp_rw [hB2, ← halg]
          exact B.sum_repr y
        have := congrArg (fun z => B2.repr z i) hsum
        rw [map_sum, Finsupp.finsetSum_apply] at this
        simp only [LinearEquiv.map_smul, B2.repr_self, Finsupp.smul_apply,
          Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
        exact this.symm
      rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hB2 i, hrepr]
    intro h0
    apply hb
    exact eR.injective (by rw [htr_eq, h0, map_zero])
  obtain ⟨b, hb⟩ := hne
  exact ⟨b, (zmod2_cases (trF F (a * b))).resolve_left hb⟩

/-- Exact character sum over `F`: `∑_{x ∈ F} (-1)^{Tr(a x)} = |F|` if `a = 0`, else `0`. -/
lemma sum_eps_trF (a : F) :
    (∑ x : F, eps (trF F (a * x))) = if a = 0 then (Fintype.card F : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨b, hb⟩ := trF_nondeg h
    have hb0 : b ≠ 0 := by intro h0; subst h0; simp at hb
    refine Finset.sum_ninvolution (fun x => x + b) ?_ ?_ ?_ ?_
    · intro x
      rw [mul_add, map_add, eps_add, hb, eps_one]; ring
    · intro x _ hx
      exact hb0 (char2_eq_of_add_eq_zero (by
        calc b + 0 = (x + b) + x := by rw [add_zero, add_comm x b, add_assoc, char2_add_self, add_zero]
          _ = x + x := by rw [hx]
          _ = 0 := char2_add_self x))
    · intro x; exact mem_univ _
    · intro x; rw [add_assoc, char2_add_self, add_zero]

/-- Square root map `x ↦ x^{2^{m-1}}` when `|F| = 2^m` (`m ≥ 1`). -/
def sqrtF (m : ℕ) (x : F) : F := x ^ (2 ^ (m - 1))

omit [DecidableEq F] [CharP F 2] [Algebra (ZMod 2) F] in
lemma sqrtF_sq {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card F = 2 ^ m) (x : F) :
    (sqrtF m x) ^ 2 = x := by
  unfold sqrtF
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hm, ← hcard]
  exact FiniteField.pow_card x

omit [DecidableEq F] [CharP F 2] [Algebra (ZMod 2) F] in
lemma sq_sqrtF {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card F = 2 ^ m) (x : F) :
    sqrtF m (x ^ 2) = x := by
  unfold sqrtF
  rw [← pow_mul, mul_comm, ← pow_succ, Nat.sub_add_cancel hm, ← hcard]
  exact FiniteField.pow_card x

omit [DecidableEq F] [Algebra (ZMod 2) F] in
lemma sqrtF_add {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card F = 2 ^ m) (x y : F) :
    sqrtF m (x + y) = sqrtF m x + sqrtF m y := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h : (sqrtF m (x + y) + (sqrtF m x + sqrtF m y)) ^ 2 = 0 := by
    rw [char2_add_sq, char2_add_sq, sqrtF_sq hm hcard, sqrtF_sq hm hcard, sqrtF_sq hm hcard]
    ring_nf; simp [h2]
  exact char2_eq_of_add_eq_zero (sq_eq_zero_iff.mp h)

omit [Fintype F] [DecidableEq F] [CharP F 2] [Algebra (ZMod 2) F] in
lemma sqrtF_mul {m : ℕ} (x y : F) : sqrtF m (x * y) = sqrtF m x * sqrtF m y :=
  mul_pow x y (2 ^ (m - 1))

omit [DecidableEq F] in
lemma trF_sqrtF {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card F = 2 ^ m) (x : F) :
    trF F (sqrtF m x) = trF F x := by
  rw [← trF_sq (sqrtF m x), sqrtF_sq hm hcard]

/-! ### Part 2. The Determinant Cubic Form on `F³` and Exact Character Sum -/

/-- Cubic monomial `x₀ x₁ x₂` on `F³`. -/
def detP (x : Fin 3 → F) : F := x 0 * x 1 * x 2
/-- Standard dot product `a₀ b₀ + a₁ b₁ + a₂ b₂` on `F³`. -/
def dotF (a b : Fin 3 → F) : F := a 0 * b 0 + a 1 * b 1 + a 2 * b 2
/-- Quadratic directional derivative of `detP` along `a`. -/
def detQ (a x : Fin 3 → F) : F := a 0 * x 1 * x 2 + a 1 * x 0 * x 2 + a 2 * x 0 * x 1
/-- Linear second derivative of `detP` along `a`. -/
def detL (a x : Fin 3 → F) : F := a 1 * a 2 * x 0 + a 0 * a 2 * x 1 + a 0 * a 1 * x 2
/-- Alternating trilinear polarization of `detP`. -/
def detT (a x y : Fin 3 → F) : F :=
  a 0 * x 1 * y 2 + a 0 * x 2 * y 1 + a 1 * x 0 * y 2 +
  a 1 * x 2 * y 0 + a 2 * x 0 * y 1 + a 2 * x 1 * y 0

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
lemma detP_add (x a : Fin 3 → F) :
    detP (x + a) + detP x = detP a + detQ a x + detL a x := by
  unfold detP detQ detL; simp only [Pi.add_apply]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ring_nf; simp [h2]

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
lemma detP_second_diff (a x y : Fin 3 → F) :
    detP (x + y + a) + detP (x + y) + (detP (x + a) + detP x) =
      detQ a y + detL a y + detT a x y := by
  rw [detP_add (x + y) a, detP_add x a]
  unfold detQ detL detT; simp only [Pi.add_apply]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ring_nf; simp [h2]

omit [Fintype F] [DecidableEq F] [CharP F 2] [Algebra (ZMod 2) F] in
lemma detT_eq_dotF_cross (a x y : Fin 3 → F) :
    detT a x y = dotF x ![a 1 * y 2 + a 2 * y 1, a 2 * y 0 + a 0 * y 2, a 0 * y 1 + a 1 * y 0] := by
  unfold detT dotF; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
/-- **Constant trilinear rank `2m`:** for every nonzero `a ∈ F³`, the radical of
`(x, y) ↦ Tr(det[a, x, y])` is precisely the 1-dimensional `F`-line `F · a`. -/
lemma detT_radical_iff {a : Fin 3 → F} (ha : a ≠ 0) (y : Fin 3 → F) :
    (![a 1 * y 2 + a 2 * y 1, a 2 * y 0 + a 0 * y 2, a 0 * y 1 + a 1 * y 0] = (0 : Fin 3 → F)) ↔
      ∃ t : F, y = t • a := by
  constructor
  · intro h0
    have e0 : a 1 * y 2 + a 2 * y 1 = 0 := congrFun h0 0
    have e1 : a 2 * y 0 + a 0 * y 2 = 0 := congrFun h0 1
    have e2 : a 0 * y 1 + a 1 * y 0 = 0 := congrFun h0 2
    have hneq : a 0 ≠ 0 ∨ a 1 ≠ 0 ∨ a 2 ≠ 0 := by
      by_contra hall; push Not at hall
      exact ha (funext fun i => by fin_cases i <;> tauto)
    rcases hneq with h0' | h1' | h2'
    · refine ⟨y 0 / a 0, funext fun i => ?_⟩
      fin_cases i
      · change y 0 = y 0 / a 0 * a 0; rw [div_mul_cancel₀ _ h0']
      · change y 1 = y 0 / a 0 * a 1
        have h := char2_eq_of_add_eq_zero e2
        rw [div_mul_eq_mul_div, mul_comm (y 0), ← h, mul_div_cancel_left₀ _ h0']
      · change y 2 = y 0 / a 0 * a 2
        have h := (char2_eq_of_add_eq_zero e1).symm
        rw [div_mul_eq_mul_div, mul_comm (y 0), ← h, mul_div_cancel_left₀ _ h0']
    · refine ⟨y 1 / a 1, funext fun i => ?_⟩
      fin_cases i
      · change y 0 = y 1 / a 1 * a 0
        have h := (char2_eq_of_add_eq_zero e2).symm
        rw [div_mul_eq_mul_div, mul_comm (y 1), ← h, mul_div_cancel_left₀ _ h1']
      · change y 1 = y 1 / a 1 * a 1; rw [div_mul_cancel₀ _ h1']
      · change y 2 = y 1 / a 1 * a 2
        have h := char2_eq_of_add_eq_zero e0
        rw [div_mul_eq_mul_div, mul_comm (y 1), ← h, mul_div_cancel_left₀ _ h1']
    · refine ⟨y 2 / a 2, funext fun i => ?_⟩
      fin_cases i
      · change y 0 = y 2 / a 2 * a 0
        have h := char2_eq_of_add_eq_zero e1
        rw [div_mul_eq_mul_div, mul_comm (y 2), ← h, mul_div_cancel_left₀ _ h2']
      · change y 1 = y 2 / a 2 * a 1
        have h := (char2_eq_of_add_eq_zero e0).symm
        rw [div_mul_eq_mul_div, mul_comm (y 2), ← h, mul_div_cancel_left₀ _ h2']
      · change y 2 = y 2 / a 2 * a 2; rw [div_mul_cancel₀ _ h2']
  · rintro ⟨t, rfl⟩
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    funext i
    fin_cases i
    · change a 1 * (t * a 2) + a 2 * (t * a 1) = 0; ring_nf; simp [h2]
    · change a 2 * (t * a 0) + a 0 * (t * a 2) = 0; ring_nf; simp [h2]
    · change a 0 * (t * a 1) + a 1 * (t * a 0) = 0; ring_nf; simp [h2]

lemma sum_eps_dotF (v : Fin 3 → F) :
    (∑ x : Fin 3 → F, eps (trF F (dotF x v))) =
      if v = 0 then (Fintype.card F : ℂ) ^ 3 else 0 := by
  have hprod : (∑ x : Fin 3 → F, eps (trF F (dotF x v))) =
      (∑ x0 : F, eps (trF F (v 0 * x0))) *
      (∑ x1 : F, eps (trF F (v 1 * x1))) *
      (∑ x2 : F, eps (trF F (v 2 * x2))) := by
    let e3 : (Fin 3 → F) ≃ F × (F × F) :=
      { toFun := fun x => (x 0, (x 1, x 2))
        invFun := fun ⟨a, b, c⟩ => ![a, b, c]
        left_inv := fun x => funext fun i => by fin_cases i <;> rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    rw [Fintype.sum_equiv e3 _ (fun p =>
      eps (trF F (v 0 * p.1)) * (eps (trF F (v 1 * p.2.1)) * eps (trF F (v 2 * p.2.2)))) ?_]
    · rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    · intro x
      simp only [e3, Equiv.coe_fn_mk, dotF, map_add, eps_add]
      rw [mul_comm (x 0) (v 0), mul_comm (x 1) (v 1), mul_comm (x 2) (v 2), mul_assoc]
  rw [hprod, sum_eps_trF, sum_eps_trF, sum_eps_trF]
  by_cases hv : v = 0
  · subst hv; simp; ring
  · rw [ite_eq_right hv]
    have hex : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
      by_contra h; push Not at h
      exact hv (funext fun i => by fin_cases i <;> tauto)
    rcases hex with h | h | h <;> simp [h]

/-- Exact squared modulus of the Walsh–Hadamard sum for `detP` over `F³` (`|F| = 2^m`, `m ≥ 1`). -/
theorem detP_charSum_sq {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card F = 2 ^ m)
    (a b : Fin 3 → F) :
    (∑ x : Fin 3 → F, eps (trF F (detP (x + a) + detP x + dotF b x))) ^ 2 =
      if a = 0 then (if b = 0 then (Fintype.card F : ℂ) ^ 6 else 0)
      else if dotF a b = detP a + sqrtF m (detP a) then (Fintype.card F : ℂ) ^ 4 else 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_cases ha : a = 0
  · subst ha
    simp only [add_zero, char2_add_self, zero_add, ↓reduceIte]
    have hdot : ∀ x : Fin 3 → F, dotF b x = dotF x b := fun x => by unfold dotF; ring
    simp_rw [hdot]
    rw [sum_eps_dotF b]
    split_ifs <;> ring
  · simp only [ha, ↓reduceIte]
    have hsq : (∑ x : Fin 3 → F, eps (trF F (detP (x + a) + detP x + dotF b x))) ^ 2 =
        ∑ y : Fin 3 → F,
          eps (trF F (detQ a y + detL a y + dotF b y)) *
          ∑ x : Fin 3 → F, eps (trF F (detT a x y)) := by
      rw [sq, Finset.sum_mul]
      have hsub : ∀ x : Fin 3 → F,
          eps (trF F (detP (x + a) + detP x + dotF b x)) *
            ∑ z : Fin 3 → F, eps (trF F (detP (z + a) + detP z + dotF b z)) =
          ∑ y : Fin 3 → F,
            eps (trF F (detQ a y + detL a y + dotF b y)) * eps (trF F (detT a x y)) := by
        intro x
        rw [Finset.mul_sum]
        refine Fintype.sum_equiv (Equiv.addLeft x).symm _ _ fun z => ?_
        have hzy : x + (Equiv.addLeft x).symm z = z := (Equiv.addLeft x).apply_symm_apply z
        set y := (Equiv.addLeft x).symm z
        have hz_eq : z = x + y := hzy.symm
        rw [hz_eq, ← eps_add, ← map_add, ← eps_add, ← map_add]
        congr 2
        have hd := detP_second_diff a x y
        have hdot : dotF b (x + y) = dotF b x + dotF b y := by unfold dotF; simp; ring
        rw [hdot]
        calc detP (x + a) + detP x + dotF b x + (detP (x + y + a) + detP (x + y) + (dotF b x + dotF b y))
            = (detP (x + y + a) + detP (x + y) + (detP (x + a) + detP x)) + (dotF b x + dotF b x) + dotF b y := by ring
          _ = (detQ a y + detL a y + detT a x y) + 0 + dotF b y := by rw [hd, char2_add_self]
          _ = detQ a y + detL a y + dotF b y + detT a x y := by ring
      simp_rw [hsub]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => by rw [← Finset.mul_sum]
    rw [hsq]
    have hinner : ∀ y : Fin 3 → F,
        (∑ x : Fin 3 → F, eps (trF F (detT a x y))) =
          if ∃ t : F, y = t • a then (Fintype.card F : ℂ) ^ 3 else 0 := by
      intro y
      simp_rw [detT_eq_dotF_cross]
      rw [sum_eps_dotF]
      simp only [detT_radical_iff ha]
    simp_rw [hinner]
    have hline : (∑ y : Fin 3 → F,
          eps (trF F (detQ a y + detL a y + dotF b y)) *
            (if ∃ t : F, y = t • a then (Fintype.card F : ℂ) ^ 3 else 0)) =
        (Fintype.card F : ℂ) ^ 3 *
          ∑ t : F, eps (trF F ((dotF a b + detP a + sqrtF m (detP a)) * t)) := by
      have hinj : Function.Injective (fun t : F => t • a) := by
        intro t1 t2 ht
        have hex : ∃ i : Fin 3, a i ≠ 0 := by
          by_contra hall; push Not at hall; exact ha (funext hall)
        obtain ⟨i, hi⟩ := hex
        exact mul_right_cancel₀ hi (congrFun ht i)
      rw [Finset.mul_sum]
      rw [← Finset.sum_filter_add_sum_filter_not (s := univ) (p := fun y : Fin 3 → F => ∃ t : F, y = t • a)]
      have hzero : ∑ y ∈ univ.filter (fun y : Fin 3 → F => ¬∃ t : F, y = t • a),
            eps (trF F (detQ a y + detL a y + dotF b y)) *
              (if ∃ t : F, y = t • a then (Fintype.card F : ℂ) ^ 3 else 0) = 0 :=
        Finset.sum_eq_zero fun y hy => by simp [(Finset.mem_filter.mp hy).2]
      rw [hzero, add_zero]
      have hfilt : univ.filter (fun y : Fin 3 → F => ∃ t : F, y = t • a) =
          univ.image (fun t : F => t • a) := by
        ext y; simp [eq_comm]
      rw [hfilt, Finset.sum_image (fun t1 _ t2 _ h => hinj h)]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [ite_eq_left ⟨t, rfl⟩, mul_comm]
      congr 2
      have h3 : (3 : F) = 1 := by
        calc (3 : F) = 2 + 1 := by norm_num
          _ = 1 := by rw [h2, zero_add]
      have hQ : detQ a (t • a) = t ^ 2 * detP a := by
        unfold detQ detP; simp only [Pi.smul_apply, smul_eq_mul]; ring_nf; simp [h3]
      have hL : detL a (t • a) = t * detP a := by
        unfold detL detP; simp only [Pi.smul_apply, smul_eq_mul]; ring_nf; simp [h3]
      have hD : dotF b (t • a) = t * dotF a b := by
        unfold dotF; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [hQ, hL, hD, map_add, map_add]
      have hsqtr : trF F (t ^ 2 * detP a) = trF F (sqrtF m (detP a) * t) := by
        have heq : t ^ 2 * detP a = (sqrtF m (detP a) * t) ^ 2 := by
          rw [mul_pow, sqrtF_sq hm hcard]; ring
        rw [heq, trF_sq]
      rw [hsqtr, ← map_add, ← map_add]
      congr 1; ring
    rw [hline, sum_eps_trF]
    have heq_cond : (dotF a b + detP a + sqrtF m (detP a) = 0) ↔
        (dotF a b = detP a + sqrtF m (detP a)) := by
      constructor
      · intro h
        exact char2_eq_of_add_eq_zero (by rw [← add_assoc]; exact h)
      · intro h; rw [h]; ring_nf; simp [h2]
    simp only [heq_cond]
    split_ifs <;> ring

/-! ### Part 3. Pure Algebraic Support `S_F` and Exact Flag Counts -/

/-- The algebraic Pauli support in `F³ × F³` coordinates:
`S_F = {(a, b) ∈ F³ × F³ : a ≠ 0 ∧ dotF a b = P(a) + sqrtF m (P(a))}`. -/
def algSupport (m : ℕ) : Finset ((Fin 3 → F) × (Fin 3 → F)) :=
  univ.filter fun p => p.1 ≠ 0 ∧ dotF p.1 p.2 = detP p.1 + sqrtF m (detP p.1)

omit [Algebra (ZMod 2) F] in
lemma card_hyperplane_F3 {a : Fin 3 → F} (ha : a ≠ 0) (c : F) :
    (univ.filter fun b : Fin 3 → F => dotF a b = c).card = Fintype.card F ^ 2 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hex : a 0 ≠ 0 ∨ a 1 ≠ 0 ∨ a 2 ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext fun i => by fin_cases i <;> tauto)
  have hbij : ∀ (f : F × F → (Fin 3 → F)),
      Function.Injective f →
      (∀ p, dotF a (f p) = c) →
      (∀ b, dotF a b = c → ∃ p, f p = b) →
      (univ.filter fun b : Fin 3 → F => dotF a b = c).card = Fintype.card F ^ 2 := by
    intro f hinj hmem hsurj
    have heq : univ.filter (fun b : Fin 3 → F => dotF a b = c) = univ.image f := by
      ext b; simp only [mem_filter, mem_univ, true_and, mem_image]
      exact ⟨hsurj b, fun ⟨p, hp⟩ => hp ▸ hmem p⟩
    rw [heq, card_image_of_injective _ hinj, card_univ, Fintype.card_prod, sq]
  rcases hex with h0 | h1 | h2'
  · refine hbij (fun ⟨b1, b2⟩ => ![(c + a 1 * b1 + a 2 * b2) / a 0, b1, b2]) ?_ ?_ ?_
    · rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h; exact Prod.ext (congrFun h 1) (congrFun h 2)
    · rintro ⟨b1, b2⟩
      unfold dotF; dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [mul_div_cancel₀ _ h0]; ring_nf; simp [h2]
    · intro b hb
      refine ⟨(b 1, b 2), funext fun i => ?_⟩
      fin_cases i
      · change (c + a 1 * b 1 + a 2 * b 2) / a 0 = b 0
        rw [← hb]; unfold dotF; field_simp [h0]; ring_nf; simp [h2]
      · rfl
      · rfl
  · refine hbij (fun ⟨b0, b2⟩ => ![b0, (c + a 0 * b0 + a 2 * b2) / a 1, b2]) ?_ ?_ ?_
    · rintro ⟨x0, x2⟩ ⟨y0, y2⟩ h; exact Prod.ext (congrFun h 0) (congrFun h 2)
    · rintro ⟨b0, b2⟩
      unfold dotF; dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [mul_div_cancel₀ _ h1]; ring_nf; simp [h2]
    · intro b hb
      refine ⟨(b 0, b 2), funext fun i => ?_⟩
      fin_cases i
      · rfl
      · change (c + a 0 * b 0 + a 2 * b 2) / a 1 = b 1
        rw [← hb]; unfold dotF; field_simp [h1]; ring_nf; simp [h2]
      · rfl
  · refine hbij (fun ⟨b0, b1⟩ => ![b0, b1, (c + a 0 * b0 + a 1 * b1) / a 2]) ?_ ?_ ?_
    · rintro ⟨x0, x1⟩ ⟨y0, y1⟩ h; exact Prod.ext (congrFun h 0) (congrFun h 1)
    · rintro ⟨b0, b1⟩
      unfold dotF; dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [mul_div_cancel₀ _ h2']; ring_nf; simp [h2]
    · intro b hb
      refine ⟨(b 0, b 1), funext fun i => ?_⟩
      fin_cases i
      · rfl
      · rfl
      · change (c + a 0 * b 0 + a 1 * b 1) / a 2 = b 2
        rw [← hb]; unfold dotF; field_simp [h2']; ring_nf; simp [h2]

omit [Algebra (ZMod 2) F] in
lemma card_two_hyperplanes_F3 {a a' : Fin 3 → F}
    (hind : ∀ t : F, a' ≠ t • a) (ha : a ≠ 0) (c1 c2 : F) :
    (univ.filter fun b : Fin 3 → F => dotF a b = c1 ∧ dotF a' b = c2).card = Fintype.card F := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet : a 0 * a' 1 + a 1 * a' 0 ≠ 0 ∨ a 0 * a' 2 + a 2 * a' 0 ≠ 0 ∨ a 1 * a' 2 + a 2 * a' 1 ≠ 0 := by
    by_contra h; push Not at h
    have h0 : ![a 1 * a' 2 + a 2 * a' 1, a 2 * a' 0 + a 0 * a' 2, a 0 * a' 1 + a 1 * a' 0] = 0 := by
      funext i; fin_cases i
      · change a 1 * a' 2 + a 2 * a' 1 = 0; exact h.2.2
      · change a 2 * a' 0 + a 0 * a' 2 = 0; rw [add_comm]; exact h.2.1
      · change a 0 * a' 1 + a 1 * a' 0 = 0; exact h.1
    obtain ⟨t, ht⟩ := (detT_radical_iff ha a').mp h0
    exact hind t ht
  have hsolve : ∀ (f : F → (Fin 3 → F)),
      Function.Injective f →
      (∀ z, dotF a (f z) = c1 ∧ dotF a' (f z) = c2) →
      (∀ b, dotF a b = c1 ∧ dotF a' b = c2 → ∃ z, f z = b) →
      (univ.filter fun b : Fin 3 → F => dotF a b = c1 ∧ dotF a' b = c2).card = Fintype.card F := by
    intro f hinj hmem hsurj
    have heq : univ.filter (fun b : Fin 3 → F => dotF a b = c1 ∧ dotF a' b = c2) = univ.image f := by
      ext b; simp only [mem_filter, mem_univ, true_and, mem_image]
      exact ⟨hsurj b, fun ⟨z, hz⟩ => hz ▸ hmem z⟩
    rw [heq, card_image_of_injective _ hinj, card_univ]
  rcases hdet with hd01 | hd02 | hd12
  · set Δ := a 0 * a' 1 + a 1 * a' 0
    refine hsolve (fun z => ![((c1 + a 2 * z) * a' 1 + (c2 + a' 2 * z) * a 1) / Δ,
                              ((c1 + a 2 * z) * a' 0 + (c2 + a' 2 * z) * a 0) / Δ, z]) ?_ ?_ ?_
    · intro z1 z2 h; exact congrFun h 2
    · intro z
      unfold dotF; dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      constructor <;> (field_simp [hd01]; dsimp [Δ]; ring_nf; simp [h2])
    · intro b ⟨hb1, hb2⟩
      refine ⟨b 2, funext fun i => ?_⟩
      unfold dotF at hb1 hb2
      fin_cases i
      · change ((c1 + a 2 * b 2) * a' 1 + (c2 + a' 2 * b 2) * a 1) / Δ = b 0
        rw [← hb1, ← hb2]; field_simp [hd01]; dsimp [Δ]; ring_nf; simp [h2]
      · change ((c1 + a 2 * b 2) * a' 0 + (c2 + a' 2 * b 2) * a 0) / Δ = b 1
        rw [← hb1, ← hb2]; field_simp [hd01]; dsimp [Δ]; ring_nf; simp [h2]
      · rfl
  · set Δ := a 0 * a' 2 + a 2 * a' 0
    refine hsolve (fun z => ![((c1 + a 1 * z) * a' 2 + (c2 + a' 1 * z) * a 2) / Δ, z,
                              ((c1 + a 1 * z) * a' 0 + (c2 + a' 1 * z) * a 0) / Δ]) ?_ ?_ ?_
    · intro z1 z2 h; exact congrFun h 1
    · intro z
      unfold dotF; dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      constructor <;> (field_simp [hd02]; dsimp [Δ]; ring_nf; simp [h2])
    · intro b ⟨hb1, hb2⟩
      refine ⟨b 1, funext fun i => ?_⟩
      unfold dotF at hb1 hb2
      fin_cases i
      · change ((c1 + a 1 * b 1) * a' 2 + (c2 + a' 1 * b 1) * a 2) / Δ = b 0
        rw [← hb1, ← hb2]; field_simp [hd02]; dsimp [Δ]; ring_nf; simp [h2]
      · rfl
      · change ((c1 + a 1 * b 1) * a' 0 + (c2 + a' 1 * b 1) * a 0) / Δ = b 2
        rw [← hb1, ← hb2]; field_simp [hd02]; dsimp [Δ]; ring_nf; simp [h2]
  · set Δ := a 1 * a' 2 + a 2 * a' 1
    refine hsolve (fun z => ![z, ((c1 + a 0 * z) * a' 2 + (c2 + a' 0 * z) * a 2) / Δ,
                              ((c1 + a 0 * z) * a' 1 + (c2 + a' 0 * z) * a 1) / Δ]) ?_ ?_ ?_
    · intro z1 z2 h; exact congrFun h 0
    · intro z
      unfold dotF; dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      constructor <;> (field_simp [hd12]; dsimp [Δ]; ring_nf; simp [h2])
    · intro b ⟨hb1, hb2⟩
      refine ⟨b 0, funext fun i => ?_⟩
      unfold dotF at hb1 hb2
      fin_cases i
      · rfl
      · change ((c1 + a 0 * b 0) * a' 2 + (c2 + a' 0 * b 0) * a 2) / Δ = b 1
        rw [← hb1, ← hb2]; field_simp [hd12]; dsimp [Δ]; ring_nf; simp [h2]
      · change ((c1 + a 0 * b 0) * a' 1 + (c2 + a' 0 * b 0) * a 1) / Δ = b 2
        rw [← hb1, ← hb2]; field_simp [hd12]; dsimp [Δ]; ring_nf; simp [h2]

omit [Algebra (ZMod 2) F] in
lemma card_algSupport (m : ℕ) :
    (algSupport (F := F) m).card = (Fintype.card F ^ 3 - 1) * Fintype.card F ^ 2 := by
  have h1 : (algSupport (F := F) m).card =
      ∑ a ∈ (univ : Finset (Fin 3 → F)).erase 0,
        (univ.filter fun b : Fin 3 → F => dotF a b = detP a + sqrtF m (detP a)).card := by
    rw [algSupport, Finset.card_filter, Fintype.sum_prod_type]
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : Fin 3 → F))]
    have hz : ∑ b : Fin 3 → F,
        (if (0 : Fin 3 → F) ≠ 0 ∧ dotF 0 b = detP 0 + sqrtF m (detP 0) then 1 else 0) = 0 := by simp
    rw [hz, zero_add]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun b _ => by simp [ha0]
  rw [h1]
  have hcon : ∀ a ∈ (univ : Finset (Fin 3 → F)).erase 0,
      (univ.filter fun b : Fin 3 → F => dotF a b = detP a + sqrtF m (detP a)).card =
        Fintype.card F ^ 2 := fun a ha => card_hyperplane_F3 (Finset.ne_of_mem_erase ha) _
  rw [Finset.sum_congr rfl hcon, Finset.sum_const, Finset.card_erase_of_mem (mem_univ _),
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

/-- Exact vertex-regular flag degree of every point `(a, b) ∈ algSupport m`:
`q⁴ + q³ - 3 q²` (`q = |F|`). -/
lemma algSupport_point_flag_deg {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card F = 2 ^ m)
    {a b : Fin 3 → F} (hab : (a, b) ∈ algSupport (F := F) m) :
    ((algSupport (F := F) m).filter fun p =>
      p ≠ (a, b) ∧ (a + p.1, b + p.2) ∈ algSupport (F := F) m ∧
      trF F (dotF a p.2 + dotF p.1 b) = 0).card =
      Fintype.card F ^ 4 + Fintype.card F ^ 3 - 3 * Fintype.card F ^ 2 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [algSupport, mem_filter, mem_univ, true_and] at hab
  rcases hab with ⟨ha0, hab_eq⟩
  set q := Fintype.card F with hq
  have hq2 : 2 ≤ q := by
    rw [hcard]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hauto_comm : ∀ a' b' : Fin 3 → F,
      dotF a' b' = detP a' + sqrtF m (detP a') →
      dotF (a + a') (b + b') = detP (a + a') + sqrtF m (detP (a + a')) →
      trF F (dotF a b' + dotF a' b) = 0 := by
    intro a' b' h1 h2'
    have hexp : dotF (a + a') (b + b') = dotF a b + dotF a' b' + (dotF a b' + dotF a' b) := by
      unfold dotF; simp only [Pi.add_apply]; ring
    set Δ := detP (a + a') + detP a + detP a'
    have hdiff : dotF a b' + dotF a' b = Δ + sqrtF m Δ := by
      have hsΔ : sqrtF m Δ = sqrtF m (detP (a + a')) + sqrtF m (detP a) + sqrtF m (detP a') := by
        dsimp [Δ]; rw [sqrtF_add hm hcard, sqrtF_add hm hcard]
      rw [hexp, hab_eq, h1] at h2'
      apply char2_eq_of_add_eq_zero
      rw [hsΔ]; dsimp [Δ]
      have : (dotF a b' + dotF a' b) +
          (detP (a + a') + detP a + detP a' + (sqrtF m (detP (a + a')) + sqrtF m (detP a) + sqrtF m (detP a'))) =
          ((detP a + sqrtF m (detP a) + (detP a' + sqrtF m (detP a')) + (dotF a b' + dotF a' b)) +
           (detP (a + a') + sqrtF m (detP (a + a')))) := by
        ring_nf
      rw [this, h2', char2_add_self]
    rw [hdiff, map_add, trF_sqrtF hm hcard, zmod2_add_self]
  have hsum : ((algSupport (F := F) m).filter fun p =>
      p ≠ (a, b) ∧ (a + p.1, b + p.2) ∈ algSupport (F := F) m ∧
      trF F (dotF a p.2 + dotF p.1 b) = 0).card =
      ∑ a' ∈ (univ.erase (0 : Fin 3 → F)).erase a,
        (univ.filter fun b' : Fin 3 → F =>
          dotF a' b' = detP a' + sqrtF m (detP a') ∧
          dotF a b' + dotF a' b = (detP (a + a') + detP a + detP a') +
            sqrtF m (detP (a + a') + detP a + detP a')).card := by
    rw [Finset.card_filter, algSupport, Finset.sum_filter, Fintype.sum_prod_type]
    have hsplit_a : ∀ a' : Fin 3 → F,
        (∑ b' : Fin 3 → F,
          if (a' ≠ 0 ∧ dotF a' b' = detP a' + sqrtF m (detP a')) then
            if (a', b') ≠ (a, b) ∧ (a + a' ≠ 0 ∧ dotF (a + a') (b + b') = detP (a + a') + sqrtF m (detP (a + a'))) ∧
               trF F (dotF a b' + dotF a' b) = 0 then 1 else 0
          else 0) =
        if a' ∈ (univ.erase (0 : Fin 3 → F)).erase a then
          (univ.filter fun b' : Fin 3 → F =>
            dotF a' b' = detP a' + sqrtF m (detP a') ∧
            dotF a b' + dotF a' b = (detP (a + a') + detP a + detP a') +
              sqrtF m (detP (a + a') + detP a + detP a')).card
        else 0 := by
      intro a'
      by_cases hm' : a' ∈ (univ.erase (0 : Fin 3 → F)).erase a
      · rw [ite_eq_left hm', Finset.card_filter]
        have ha'0 : a' ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hm')
        have ha'a : a' ≠ a := Finset.ne_of_mem_erase hm'
        have haa'0 : a + a' ≠ 0 := fun h => ha'a (funext fun i => (char2_eq_of_add_eq_zero (congrFun h i)).symm)
        refine Finset.sum_congr rfl fun b' _ => ?_
        have hiff : (dotF a' b' = detP a' + sqrtF m (detP a') ∧
            dotF (a + a') (b + b') = detP (a + a') + sqrtF m (detP (a + a'))) ↔
            (dotF a' b' = detP a' + sqrtF m (detP a') ∧
            dotF a b' + dotF a' b = (detP (a + a') + detP a + detP a') +
              sqrtF m (detP (a + a') + detP a + detP a')) := by
          have hexp : dotF (a + a') (b + b') = dotF a b + dotF a' b' + (dotF a b' + dotF a' b) := by
            unfold dotF; simp only [Pi.add_apply]; ring
          have hsr : sqrtF m (detP (a + a') + detP a + detP a') =
              sqrtF m (detP (a + a')) + sqrtF m (detP a) + sqrtF m (detP a') := by
            rw [sqrtF_add hm hcard, sqrtF_add hm hcard]
          constructor
          · rintro ⟨h1, h2'⟩
            refine ⟨h1, ?_⟩
            rw [hexp, hab_eq, h1] at h2'
            apply char2_eq_of_add_eq_zero; rw [hsr]
            have : dotF a b' + dotF a' b +
                (detP (a + a') + detP a + detP a' + (sqrtF m (detP (a + a')) + sqrtF m (detP a) + sqrtF m (detP a'))) =
                (detP a + sqrtF m (detP a) + (detP a' + sqrtF m (detP a')) + (dotF a b' + dotF a' b)) +
                (detP (a + a') + sqrtF m (detP (a + a'))) := by ring_nf
            rw [this, h2', char2_add_self]
          · rintro ⟨h1, h2'⟩
            refine ⟨h1, ?_⟩
            rw [hexp, hab_eq, h1, h2', hsr]; ring_nf; simp [h2]
        by_cases h1 : dotF a' b' = detP a' + sqrtF m (detP a') ∧
            dotF a b' + dotF a' b = (detP (a + a') + detP a + detP a') +
              sqrtF m (detP (a + a') + detP a + detP a')
        · have h2' := hiff.mpr h1
          have hcomm := hauto_comm a' b' h2'.1 h2'.2
          have hne : (a', b') ≠ (a, b) := fun h => ha'a (congrArg Prod.fst h)
          rw [ite_eq_left ⟨ha'0, h2'.1⟩, ite_eq_left ⟨hne, ⟨haa'0, h2'.2⟩, hcomm⟩, ite_eq_left h1]
        · have h2' : ¬(dotF a' b' = detP a' + sqrtF m (detP a') ∧
              dotF (a + a') (b + b') = detP (a + a') + sqrtF m (detP (a + a'))) := mt hiff.mp h1
          simp only [h1, ↓reduceIte]
          by_cases h1a : dotF a' b' = detP a' + sqrtF m (detP a')
          · have h2b : ¬(dotF (a + a') (b + b') = detP (a + a') + sqrtF m (detP (a + a'))) :=
              fun hb' => h2' ⟨h1a, hb'⟩
            simp [ha'0, h1a, h2b]
          · simp [h1a]
      · rw [ite_eq_right hm']
        simp only [mem_erase, mem_univ, and_true, not_and, not_not] at hm'
        refine Finset.sum_eq_zero fun b' _ => ?_
        by_cases ha'a : a' = a
        · subst ha'a
          have h0 : a' + a' = (0 : Fin 3 → F) := funext fun i => char2_add_self (a' i)
          simp [h0]
        · have ha'0 : a' = 0 := hm' ha'a; subst ha'0; simp
    simp only [mem_filter, mem_univ, true_and]
    simp_rw [hsplit_a]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsum]
  set U := (univ.erase (0 : Fin 3 → F)).erase a
  rw [← Finset.sum_filter_add_sum_filter_not (s := U) (p := fun a' : Fin 3 → F => ∃ t : F, a' = t • a)]
  have hcol : ∀ a' ∈ U.filter (fun a' : Fin 3 → F => ∃ t : F, a' = t • a),
      (univ.filter fun b' : Fin 3 → F =>
        dotF a' b' = detP a' + sqrtF m (detP a') ∧
        dotF a b' + dotF a' b = (detP (a + a') + detP a + detP a') +
          sqrtF m (detP (a + a') + detP a + detP a')).card = q ^ 2 := by
    intro a' ha'
    obtain ⟨t, rfl⟩ := (Finset.mem_filter.mp ha').2
    have hPta : detP (t • a) = t ^ 3 * detP a := by
      unfold detP; simp only [Pi.smul_apply, smul_eq_mul]; ring
    have hP1ta : detP (a + t • a) = (1 + t) ^ 3 * detP a := by
      unfold detP; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hΔ : detP (a + t • a) + detP a + detP (t • a) = (t ^ 2 + t) * detP a := by
      have h3 : (3 : F) = 1 := by calc (3 : F) = 2 + 1 := by norm_num
        _ = 1 := by rw [h2, zero_add]
      rw [hP1ta, hPta]; ring_nf; simp [h2, h3]
    have hdot_ta : ∀ v : Fin 3 → F, dotF (t • a) v = t * dotF a v := fun v => by
      unfold dotF; simp only [Pi.smul_apply, smul_eq_mul]; ring
    have hkey : t * (t * (detP a + sqrtF m (detP a)) + ((t ^ 2 + t) * detP a + sqrtF m ((t ^ 2 + t) * detP a))) =
        t ^ 3 * detP a + sqrtF m (t ^ 3 * detP a) := by
      rw [sqrtF_mul, sqrtF_add hm hcard, sq_sqrtF hm hcard, sqrtF_mul]
      have hst3 : sqrtF m (t ^ 3) = t * sqrtF m t := by
        have : t ^ 3 = t ^ 2 * t := by ring
        rw [this, sqrtF_mul, sq_sqrtF hm hcard]
      rw [hst3]; ring_nf; simp [h2]
    have heq_set : (univ.filter fun b' : Fin 3 → F =>
        dotF (t • a) b' = detP (t • a) + sqrtF m (detP (t • a)) ∧
        dotF a b' + dotF (t • a) b = (detP (a + t • a) + detP a + detP (t • a)) +
          sqrtF m (detP (a + t • a) + detP a + detP (t • a))) =
        univ.filter fun b' : Fin 3 → F =>
          dotF a b' = t * (detP a + sqrtF m (detP a)) +
            ((t ^ 2 + t) * detP a + sqrtF m ((t ^ 2 + t) * detP a)) := by
      ext b'
      simp only [mem_filter, mem_univ, true_and]
      rw [hΔ]
      simp only [hdot_ta, hPta, hab_eq]
      constructor
      · rintro ⟨_, h2'⟩
        apply char2_eq_of_add_eq_zero
        have : dotF a b' + (t * (detP a + sqrtF m (detP a)) + ((t ^ 2 + t) * detP a + sqrtF m ((t ^ 2 + t) * detP a))) =
            (dotF a b' + t * (detP a + sqrtF m (detP a))) + ((t ^ 2 + t) * detP a + sqrtF m ((t ^ 2 + t) * detP a)) := by ring
        rw [this, h2', char2_add_self]
      · intro hb'
        refine ⟨by rw [hb', hkey], by
          rw [hb', add_comm (t * (detP a + sqrtF m (detP a))), add_assoc, char2_add_self, add_zero]⟩
    rw [heq_set]
    exact card_hyperplane_F3 ha0 _
  have hncol : ∀ a' ∈ U.filter (fun a' : Fin 3 → F => ¬∃ t : F, a' = t • a),
      (univ.filter fun b' : Fin 3 → F =>
        dotF a' b' = detP a' + sqrtF m (detP a') ∧
        dotF a b' + dotF a' b = (detP (a + a') + detP a + detP a') +
          sqrtF m (detP (a + a') + detP a + detP a')).card = q := by
    intro a' ha'
    have hind : ∀ t : F, a' ≠ t • a := by
      have h := (Finset.mem_filter.mp ha').2; push Not at h; exact h
    have heq_set : (univ.filter fun b' : Fin 3 → F =>
        dotF a' b' = detP a' + sqrtF m (detP a') ∧
        dotF a b' + dotF a' b = (detP (a + a') + detP a + detP a') +
          sqrtF m (detP (a + a') + detP a + detP a')) =
        univ.filter fun b' : Fin 3 → F =>
          dotF a b' = dotF a' b + (detP (a + a') + detP a + detP a') +
            sqrtF m (detP (a + a') + detP a + detP a') ∧
          dotF a' b' = detP a' + sqrtF m (detP a') := by
      ext b'; simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2'⟩
        refine ⟨?_, h1⟩
        apply char2_eq_of_add_eq_zero
        have : dotF a b' + (dotF a' b + (detP (a + a') + detP a + detP a') + sqrtF m (detP (a + a') + detP a + detP a')) =
            (dotF a b' + dotF a' b) + ((detP (a + a') + detP a + detP a') + sqrtF m (detP (a + a') + detP a + detP a')) := by ring
        rw [this, h2', char2_add_self]
      · rintro ⟨h2', h1⟩
        refine ⟨h1, by rw [h2']; ring_nf; simp [h2]⟩
    rw [heq_set]
    exact card_two_hyperplanes_F3 hind ha0 _ _
  have hcol_card : (U.filter fun a' : Fin 3 → F => ∃ t : F, a' = t • a).card = q - 2 := by
    have hinj : Function.Injective (fun t : F => t • a) := by
      intro t1 t2 ht
      have hex : ∃ i : Fin 3, a i ≠ 0 := by
        by_contra hall; push Not at hall; exact ha0 (funext hall)
      obtain ⟨i, hi⟩ := hex
      exact mul_right_cancel₀ hi (congrFun ht i)
    have hset : U.filter (fun a' : Fin 3 → F => ∃ t : F, a' = t • a) =
        ((univ.erase (0 : F)).erase 1).image (fun t : F => t • a) := by
      ext a'
      simp only [U, mem_filter, mem_erase, mem_univ, and_true, mem_image]
      constructor
      · rintro ⟨⟨ha'a, ha'0⟩, ⟨t, rfl⟩⟩
        refine ⟨t, ⟨fun h1 => ha'a (by rw [h1, one_smul]), fun h0 => ha'0 (by rw [h0, zero_smul])⟩, rfl⟩
      · rintro ⟨t, ⟨ht1, ht0⟩, rfl⟩
        refine ⟨⟨fun h => ht1 (hinj (by simpa using h)), fun h => ht0 (hinj (by simpa using h))⟩, ⟨t, rfl⟩⟩
    rw [hset, card_image_of_injective _ hinj,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨one_ne_zero, mem_univ _⟩),
      Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, ← hq]
    omega
  have hU_card : U.card = q ^ 3 - 2 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ha0, mem_univ _⟩),
      Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ← hq]
    omega
  have hq2_le_q3 : 2 ≤ q ^ 3 := by
    have : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
    omega
  have hq_le_q3 : q ≤ q ^ 3 := by
    calc q = q * 1 := (mul_one q).symm
      _ ≤ q * q ^ 2 := Nat.mul_le_mul_left q (by nlinarith)
      _ = q ^ 3 := by ring
  have hncol_card : (U.filter fun a' : Fin 3 → F => ¬∃ t : F, a' = t • a).card = q ^ 3 - q := by
    have hs := Finset.card_filter_add_card_filter_not (s := U) (fun a' : Fin 3 → F => ∃ t : F, a' = t • a)
    rw [hU_card, hcol_card] at hs
    omega
  rw [Finset.sum_congr rfl hcol, Finset.sum_congr rfl hncol, Finset.sum_const, Finset.sum_const,
    hcol_card, hncol_card, smul_eq_mul, smul_eq_mul]
  have h3q2 : 3 * q ^ 2 ≤ q ^ 4 + q ^ 3 := by
    have h4 : 4 * q ^ 2 ≤ q ^ 4 := by
      calc 4 * q ^ 2 = 2 ^ 2 * q ^ 2 := by norm_num
        _ ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hq2 2)
        _ = q ^ 4 := by ring
    omega
  zify [hq2, hq_le_q3, h3q2]
  ring

end FiniteFieldChar2

/-! ### Part 4. Embedding into `N = 3m` Qubits and Master Infinite-Family Theorem -/

/-- Existence of a `ZMod 2`-linear isomorphism `Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → GaloisField 2 m)`
for every `m ≥ 1`. -/
lemma exists_linearEquiv_galoisField3 (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → GaloisField 2 m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype (GaloisField 2 m) := Fintype.ofFinite (GaloisField 2 m)
  have hm0 : m ≠ 0 := by omega
  have hcardF : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 m hm0
  have hfinF : Module.finrank (ZMod 2) (GaloisField 2 m) = m := by
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := GaloisField 2 m)
    rw [ZMod.card, hcardF] at hc
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hc.symm
  have hfin1 : Module.finrank (ZMod 2) (Vec (3 * m)) = 3 * m := by
    simp [Vec]
  have hfin2 : Module.finrank (ZMod 2) (Fin 3 → GaloisField 2 m) = 3 * m := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hfinF]
  exact ⟨LinearEquiv.ofFinrankEq _ _ (hfin1.trans hfin2.symm)⟩

/-- Trace-dual linear isomorphism `eDual : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F)` satisfying
`c ⬝ᵥ x = trF F (dotF (e x) (eDual c))` for all `c, x : Vec (3 * m)`. -/
noncomputable def traceDualEquiv {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F)) :
    Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F) := by
  let fwd : (Fin 3 → F) →ₗ[ZMod 2] Vec (3 * m) :=
    { toFun := fun b i => trF F (dotF (e (Pi.single i 1)) b)
      map_add' := fun b1 b2 => by
        funext i
        have h : dotF (e (Pi.single i 1)) (b1 + b2) =
            dotF (e (Pi.single i 1)) b1 + dotF (e (Pi.single i 1)) b2 := by
          unfold dotF; simp; ring
        rw [h, map_add]; rfl
      map_smul' := fun r b => by
        funext i
        rcases zmod2_cases r with rfl | rfl <;> simp [dotF] }
  have hinj : Function.Injective fwd := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    have hex : b 0 ≠ 0 ∨ b 1 ≠ 0 ∨ b 2 ≠ 0 := by
      by_contra h; push Not at h; exact hb0 (funext fun i => by fin_cases i <;> tauto)
    have hy : ∃ y : Fin 3 → F, trF F (dotF y b) = 1 := by
      rcases hex with h0 | h1 | h2
      · obtain ⟨u, hu⟩ := trF_nondeg h0
        exact ⟨![u, 0, 0], by unfold dotF; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zero_mul, add_zero]; rw [mul_comm]; exact hu⟩
      · obtain ⟨u, hu⟩ := trF_nondeg h1
        exact ⟨![0, u, 0], by unfold dotF; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zero_mul, zero_add, add_zero]; rw [mul_comm]; exact hu⟩
      · obtain ⟨u, hu⟩ := trF_nondeg h2
        exact ⟨![0, 0, u], by unfold dotF; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zero_mul, zero_add]; rw [mul_comm]; exact hu⟩
    obtain ⟨y, hy1⟩ := hy
    set x : Vec (3 * m) := e.symm y
    have hdot0 : trF F (dotF (e x) b) = 0 := by
      have hx : x = ∑ i : Fin (3 * m), x i • Pi.single i (1 : ZMod 2) := by
        funext j; simp [Finset.sum_apply, Pi.single_apply]
      have hlin : ∀ (s : Finset (Fin (3 * m))) (g : Fin (3 * m) → (Fin 3 → F)),
          trF F (dotF (∑ i ∈ s, g i) b) = ∑ i ∈ s, trF F (dotF (g i) b) := by
        intro s g
        induction s using Finset.cons_induction with
        | empty => simp [dotF]
        | cons a s' has ih =>
          rw [Finset.sum_cons, Finset.sum_cons, ← ih, ← map_add]
          congr 1; unfold dotF; simp; ring
      conv_lhs => rw [hx, map_sum, hlin]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases zmod2_cases (x i) with hxi | hxi
      · simp [hxi, dotF]
      · rw [hxi, one_smul]
        exact congrFun hb i
    rw [e.apply_symm_apply, hy1] at hdot0
    exact one_ne_zero hdot0
  have hbij : Function.Bijective fwd := by
    have hcard : Fintype.card (Fin 3 → F) = Fintype.card (Vec (3 * m)) :=
      (Fintype.card_congr e.toEquiv).symm
    exact (Fintype.bijective_iff_injective_and_card fwd).mpr ⟨hinj, hcard⟩
  exact (LinearEquiv.ofBijective fwd hbij).symm

lemma traceDualEquiv_spec {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F))
    (c x : Vec (3 * m)) :
    c ⬝ᵥ x = trF F (dotF (e x) (traceDualEquiv e c)) := by
  set b := traceDualEquiv e c
  have hcb : ∀ i : Fin (3 * m), c i = trF F (dotF (e (Pi.single i 1)) b) := by
    intro i
    have happ : (traceDualEquiv e).symm b = c := (traceDualEquiv e).symm_apply_apply c
    rw [← happ]; rfl
  have hx : x = ∑ i : Fin (3 * m), x i • Pi.single i (1 : ZMod 2) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have hlin : ∀ (s : Finset (Fin (3 * m))) (g : Fin (3 * m) → (Fin 3 → F)),
      trF F (dotF (∑ i ∈ s, g i) b) = ∑ i ∈ s, trF F (dotF (g i) b) := by
    intro s g
    induction s using Finset.cons_induction with
    | empty => simp [dotF]
    | cons a s' has ih =>
      rw [Finset.sum_cons, Finset.sum_cons, ← ih, ← map_add]
      congr 1; unfold dotF; simp; ring
  conv_rhs => rw [hx, map_sum, hlin]
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases zmod2_cases (x i) with hxi | hxi
  · simp [hxi, dotF]
  · rw [hxi, one_smul, mul_one, hcb i]

/-- Pauli-label equivalence `(a, c) ↦ (e a, traceDualEquiv e c)` from `Pt (3 * m)` to `F³ × F³`. -/
noncomputable def ptEquiv {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F)) :
    Pt (3 * m) ≃ (Fin 3 → F) × (Fin 3 → F) :=
  e.toEquiv.prodCongr (traceDualEquiv e).toEquiv

/-- The pure-CCZ determinant flat phase state `|Ψ_{3m}⟩` on `3m` qubits. -/
@[nolint unusedArguments]
noncomputable def detPhaseState {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F)) :
    Vec (3 * m) → ℂ :=
  fun x => ((Real.sqrt ((2 : ℝ) ^ (3 * m)))⁻¹ : ℝ) * eps (trF F (detP (e x)))

/-- The Pauli support `S_{3m} ⊆ Pt (3 * m)` of `|Ψ_{3m}⟩`. -/
noncomputable def detSupport {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F)) :
    Finset (Pt (3 * m)) :=
  (algSupport (F := F) m).map (ptEquiv e).symm.toEmbedding

/-- The optimal sign assignment `f(v) = sign(⟨Ψ_{3m} | P_v | Ψ_{3m}⟩)`. -/
noncomputable def detSigns {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F)) :
    Pt (3 * m) → ℝ :=
  fun v => if 0 ≤ ((star (detPhaseState e)) ⬝ᵥ (pauli v *ᵥ detPhaseState e)).re then 1 else -1

lemma detSigns_values {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F))
    (v : Pt (3 * m)) : detSigns e v = 1 ∨ detSigns e v = -1 := by
  unfold detSigns; split_ifs <;> simp

lemma detSupport_zero_notMem {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F)) :
    (0 : Pt (3 * m)) ∉ detSupport e := by
  simp only [detSupport, mem_map, Equiv.coe_toEmbedding, algSupport, mem_filter, mem_univ, true_and]
  rintro ⟨⟨a, b⟩, ⟨ha, _⟩, hab⟩
  have h1 : a = 0 := by
    have := congrArg (fun p => (ptEquiv e p).1) hab
    simpa [ptEquiv] using this
  exact ha h1

lemma detSupport_card {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (hcard : Fintype.card F = 2 ^ m)
    (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F)) :
    (detSupport e).card = ((2 ^ m) ^ 3 - 1) * (2 ^ m) ^ 2 := by
  rw [detSupport, Finset.card_map, card_algSupport, hcard]

/-- `|Ψ_{3m}⟩` is a unit vector flat on `detSupport e` with modulus `1 / 2^m`. -/
theorem detPhase_isFlatState {m : ℕ} (hm : 1 ≤ m) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (hcard : Fintype.card F = 2 ^ m)
    (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F)) :
    IsFlatState (detSupport e) (detSigns e) (detPhaseState e) := by
  set D : ℝ := (2 : ℝ) ^ (3 * m) with hD
  have hDpos : (0 : ℝ) < D := by positivity
  have hqpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hD_q3 : D = ((2 : ℝ) ^ m) ^ 3 := by rw [hD, ← pow_mul, mul_comm]
  -- 1. Unit norm
  have hnorm : ∑ x : Vec (3 * m), Complex.normSq (detPhaseState e x) = 1 := by
    have hterm : ∀ x : Vec (3 * m), Complex.normSq (detPhaseState e x) = D⁻¹ := by
      intro x
      unfold detPhaseState
      rw [Complex.normSq_mul, Complex.normSq_ofReal]
      have heps : Complex.normSq (eps (trF F (detP (e x)))) = 1 := by
        rcases zmod2_cases (trF F (detP (e x))) with h | h <;> simp [h]
      rw [heps, mul_one, ← mul_inv, Real.mul_self_sqrt (le_of_lt hDpos)]
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      ZMod.card, nsmul_eq_mul]
    have hcast : ((2 ^ (3 * m) : ℕ) : ℝ) = D := by push_cast [hD]; rfl
    rw [hcast, mul_inv_cancel₀ (ne_of_gt hDpos)]
  -- 2. Exact formula for `⟨ψ | P_v | ψ⟩` with `y` as outer sum
  have hexp_val : ∀ v : Pt (3 * m),
      (star (detPhaseState e)) ⬝ᵥ (pauli v *ᵥ detPhaseState e) =
        Complex.I ^ (ycount v) * ((D : ℂ)⁻¹) *
        ∑ y : Fin 3 → F, eps (trF F (detP (y + e v.1) + detP y + dotF (traceDualEquiv e v.2) y)) := by
    intro v
    simp only [dotProduct, mulVec, Pi.star_apply, pauli, Matrix.smul_apply, smul_eq_mul, weyl,
      mul_ite, mul_zero, ite_mul, zero_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hcol : ∀ y : Vec (3 * m),
        (∑ x : Vec (3 * m),
          if x = y + v.1 then star (detPhaseState e x) * (Complex.I ^ ycount v * chi v.2 y * detPhaseState e y) else 0) =
        Complex.I ^ ycount v * ((D : ℂ)⁻¹) *
          eps (trF F (detP (e y + e v.1) + detP (e y) + dotF (traceDualEquiv e v.2) (e y))) := by
      intro y
      rw [Finset.sum_eq_single (y + v.1)]
      · rw [ite_eq_left rfl]
        unfold detPhaseState
        have hstar : star (((Real.sqrt D)⁻¹ : ℝ) * eps (trF F (detP (e (y + v.1))))) =
            ((Real.sqrt D)⁻¹ : ℝ) * eps (trF F (detP (e (y + v.1)))) := by
          rw [star_mul', star_eps, Complex.star_def, Complex.conj_ofReal, mul_comm]
        rw [hstar]
        have hsqinv : (((Real.sqrt D)⁻¹ : ℝ) : ℂ) * (((Real.sqrt D)⁻¹ : ℝ) : ℂ) = (D : ℂ)⁻¹ := by
          rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (le_of_lt hDpos), Complex.ofReal_inv]
        have hchi : chi v.2 y = eps (trF F (dotF (traceDualEquiv e v.2) (e y))) := by
          unfold chi
          rw [traceDualEquiv_spec e v.2 y]
          congr 2; unfold dotF; ring
        rw [hchi, map_add]
        have heps3 : eps (trF F (detP (e y + e v.1))) * eps (trF F (dotF (traceDualEquiv e v.2) (e y))) *
            eps (trF F (detP (e y))) =
            eps (trF F (detP (e y + e v.1) + detP (e y) + dotF (traceDualEquiv e v.2) (e y))) := by
          rw [map_add, map_add, eps_add, eps_add]; ring
        calc (((Real.sqrt D)⁻¹ : ℝ) : ℂ) * eps (trF F (detP (e y + e v.1))) *
              (Complex.I ^ ycount v * eps (trF F (dotF (traceDualEquiv e v.2) (e y))) *
                ((((Real.sqrt D)⁻¹ : ℝ) : ℂ) * eps (trF F (detP (e y)))))
            = Complex.I ^ ycount v *
              ((((Real.sqrt D)⁻¹ : ℝ) : ℂ) * (((Real.sqrt D)⁻¹ : ℝ) : ℂ)) *
              (eps (trF F (detP (e y + e v.1))) * eps (trF F (dotF (traceDualEquiv e v.2) (e y))) *
                eps (trF F (detP (e y)))) := by ring
          _ = Complex.I ^ ycount v * (D : ℂ)⁻¹ *
              eps (trF F (detP (e y + e v.1) + detP (e y) + dotF (traceDualEquiv e v.2) (e y))) := by
            rw [hsqinv, heps3]
      · intro x _ hx; rw [ite_eq_right hx]
      · intro hy'; exact absurd (mem_univ _) hy'
    simp_rw [hcol, ← Finset.mul_sum]
    congr 1
    exact Fintype.sum_equiv e.toEquiv _ _ fun y => rfl
  -- 3. `⟨ψ | P_v | ψ⟩` is real because `pauli v` is Hermitian
  have hexp_real : ∀ v : Pt (3 * m),
      (star (detPhaseState e)) ⬝ᵥ (pauli v *ᵥ detPhaseState e) =
        (((star (detPhaseState e) ⬝ᵥ (pauli v *ᵥ detPhaseState e)).re : ℝ) : ℂ) := by
    intro v
    have hH := pauli_isHermitian v
    have hconj : star ((star (detPhaseState e)) ⬝ᵥ (pauli v *ᵥ detPhaseState e)) =
        (star (detPhaseState e)) ⬝ᵥ (pauli v *ᵥ detPhaseState e) := by
      simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, star_sum, star_mul']
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      have hij : star (pauli v i j) = pauli v j i := by
        have := congrFun (congrFun hH.eq j) i
        simpa [Matrix.conjTranspose_apply] using this
      rw [star_star, hij]; ring
    exact (Complex.conj_eq_iff_re.mp hconj).symm
  -- 4. Compute exact modulus `√((D - 1) / |S|) = 1 / 2^m`
  have hsqrt_mod : Real.sqrt (((2 : ℝ) ^ (3 * m) - 1) / ((detSupport e).card : ℝ)) = ((2 : ℝ) ^ m)⁻¹ := by
    rw [detSupport_card hcard e]
    have hq3_ge : 1 ≤ (2 ^ m) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    have hq2R : (2 : ℝ) ≤ (2 : ℝ) ^ m := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have hq3_ne : ((2 : ℝ) ^ m) ^ 3 - 1 ≠ 0 := by
      have : (2 : ℝ) ^ 3 ≤ ((2 : ℝ) ^ m) ^ 3 := pow_le_pow_left₀ (by norm_num) hq2R 3
      linarith
    have hcardR : ((((2 ^ m) ^ 3 - 1) * (2 ^ m) ^ 2 : ℕ) : ℝ) =
        (((2 : ℝ) ^ m) ^ 3 - 1) * ((2 : ℝ) ^ m) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_sub hq3_ge]; push_cast; rfl
    rw [hcardR, ← hD, hD_q3]
    have hdiv : (((2 : ℝ) ^ m) ^ 3 - 1) / ((((2 : ℝ) ^ m) ^ 3 - 1) * ((2 : ℝ) ^ m) ^ 2) =
        (((2 : ℝ) ^ m)⁻¹) ^ 2 := by
      field_simp [hq3_ne, ne_of_gt hqpos]
    rw [hdiv, Real.sqrt_sq (le_of_lt (inv_pos.mpr hqpos))]
  -- 5. Assemble `IsFlatState`
  refine ⟨hnorm, ?_, ?_⟩
  · intro v hv
    have hv_alg : (e v.1, traceDualEquiv e v.2) ∈ algSupport (F := F) m := by
      simp only [detSupport, mem_map, Equiv.coe_toEmbedding] at hv
      rcases hv with ⟨p, hp, rfl⟩
      simpa [ptEquiv] using hp
    simp only [algSupport, mem_filter, mem_univ, true_and] at hv_alg
    rcases hv_alg with ⟨ha0, hdot_eq⟩
    have heven : Even (ycount v) := by
      have htr0 : v.2 ⬝ᵥ v.1 = 0 := by
        rw [traceDualEquiv_spec e v.2 v.1, hdot_eq, map_add, trF_sqrtF hm hcard, zmod2_add_self]
      have hcast : ((ycount v : ℕ) : ZMod 2) = 0 := by
        rw [← dot_eq_ycount, htr0]
      exact Nat.even_iff.mpr (by
        have h2d : 2 ∣ ycount v := (ZMod.natCast_eq_zero_iff (ycount v) 2).mp hcast
        exact Nat.mod_eq_zero_of_dvd h2d)
    have hI2 : Complex.I ^ (2 * ycount v) = 1 := by
      obtain ⟨k, hk⟩ := heven
      rw [hk, show 2 * (k + k) = 4 * k by ring, pow_mul, Complex.I_pow_four, one_pow]
    have hsq := congrArg (fun z : ℂ => z ^ 2) (hexp_val v)
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm (ycount v) 2, hI2, one_mul,
        detP_charSum_sq hm hcard (e v.1) (traceDualEquiv e v.2),
        ite_eq_right ha0, ite_eq_left hdot_eq, hcard] at hsq
    have hq_neC : ((2 : ℂ) ^ m) ≠ 0 := pow_ne_zero m (by norm_num)
    have hDC : (D : ℂ) = ((2 : ℂ) ^ m) ^ 3 := by push_cast [hD_q3]; rfl
    have hrhs : ((D : ℂ)⁻¹) ^ 2 * (((2 ^ m : ℕ) : ℂ) ^ 4) = (((((2 : ℝ) ^ m)⁻¹ : ℝ) : ℂ)) ^ 2 := by
      rw [hDC]; push_cast; field_simp [hq_neC]
    rw [hrhs] at hsq
    have hre_sq : ((star (detPhaseState e) ⬝ᵥ (pauli v *ᵥ detPhaseState e)).re) ^ 2 =
        (((2 : ℝ) ^ m)⁻¹) ^ 2 := by
      have h1 := hexp_real v
      rw [h1] at hsq
      exact_mod_cast hsq
    have hre_eq : (star (detPhaseState e) ⬝ᵥ (pauli v *ᵥ detPhaseState e)).re =
        detSigns e v * ((2 : ℝ) ^ m)⁻¹ := by
      unfold detSigns
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hre_sq with hpos' | hneg'
      · have hge : 0 ≤ (star (detPhaseState e) ⬝ᵥ (pauli v *ᵥ detPhaseState e)).re := by
          rw [hpos']; positivity
        rw [ite_eq_left hge, one_mul, hpos']
      · have hlt : ¬(0 ≤ (star (detPhaseState e) ⬝ᵥ (pauli v *ᵥ detPhaseState e)).re) := by
          rw [hneg']; have : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := inv_pos.mpr hqpos; linarith
        rw [ite_eq_right hlt, neg_one_mul, hneg']
    rw [hexp_real v, hsqrt_mod, hre_eq]
  · intro v hv0 hv_not
    have hv_alg_not : (e v.1, traceDualEquiv e v.2) ∉ algSupport (F := F) m := by
      intro hmem; apply hv_not
      exact Finset.mem_map.mpr ⟨(e v.1, traceDualEquiv e v.2), hmem, by simp [ptEquiv]⟩
    have hv_pt0 : (e v.1, traceDualEquiv e v.2) ≠ (0, 0) := by
      intro h; apply hv0
      exact Prod.ext
        (e.injective (by simpa using congrArg Prod.fst h))
        ((traceDualEquiv e).injective (by simpa using congrArg Prod.snd h))
    have hsq := congrArg (fun z : ℂ => z ^ 2) (hexp_val v)
    rw [mul_pow, mul_pow, detP_charSum_sq hm hcard (e v.1) (traceDualEquiv e v.2)] at hsq
    have hzero : (if e v.1 = 0 then if traceDualEquiv e v.2 = 0 then (Fintype.card F : ℂ) ^ 6 else 0
        else if dotF (e v.1) (traceDualEquiv e v.2) = detP (e v.1) + sqrtF m (detP (e v.1))
        then (Fintype.card F : ℂ) ^ 4 else 0) = 0 := by
      by_cases ha : e v.1 = 0
      · rw [ite_eq_left ha]
        have hb : traceDualEquiv e v.2 ≠ 0 := fun hb => hv_pt0 (Prod.ext ha hb)
        rw [ite_eq_right hb]
      · rw [ite_eq_right ha]
        have hndot : dotF (e v.1) (traceDualEquiv e v.2) ≠ detP (e v.1) + sqrtF m (detP (e v.1)) := by
          intro hdot; apply hv_alg_not
          simp only [algSupport, mem_filter, mem_univ, true_and]
          exact ⟨ha, hdot⟩
        rw [ite_eq_right hndot]
    rw [hzero, mul_zero] at hsq
    exact sq_eq_zero_iff.mp hsq

/-- Symplectic pairing in `ptEquiv` coordinates equals `trF F (dotF a b' + dotF a' b)`. -/
lemma symp_eq_trF_dotF {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F))
    (u v : Pt (3 * m)) :
    symp u v = trF F (dotF (e u.1) (traceDualEquiv e v.2) + dotF (e v.1) (traceDualEquiv e u.2)) := by
  unfold symp
  rw [traceDualEquiv_spec e u.2 v.1, traceDualEquiv_spec e v.2 u.1, map_add, add_comm]

/-- **Strict non-closure for ALL `m ≥ 1`:** `detSupport e` always contains two distinct
commuting observables whose sum is NOT in `detSupport e`. -/
theorem detSupport_not_closed {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F)) :
    ∃ u ∈ detSupport e, ∃ v ∈ detSupport e, u ≠ v ∧ symp u v = 0 ∧ u + v ∉ detSupport e := by
  let a : Fin 3 → F := ![1, 0, 0]
  let b1 : Fin 3 → F := ![0, 0, 0]
  let b2 : Fin 3 → F := ![0, 1, 0]
  have ha0 : a ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  have hPa : detP a = 0 := by unfold detP; simp [a]
  have hs0 : sqrtF m (0 : F) = 0 := by unfold sqrtF; exact zero_pow (pow_ne_zero _ (by norm_num))
  have hm1 : (a, b1) ∈ algSupport (F := F) m := by
    simp only [algSupport, mem_filter, mem_univ, true_and, hPa, hs0, add_zero]
    exact ⟨ha0, by unfold dotF; simp [a, b1]⟩
  have hm2 : (a, b2) ∈ algSupport (F := F) m := by
    simp only [algSupport, mem_filter, mem_univ, true_and, hPa, hs0, add_zero]
    exact ⟨ha0, by unfold dotF; simp [a, b2]⟩
  let u := (ptEquiv e).symm (a, b1)
  let v := (ptEquiv e).symm (a, b2)
  have hu : u ∈ detSupport e := Finset.mem_map.mpr ⟨(a, b1), hm1, rfl⟩
  have hv : v ∈ detSupport e := Finset.mem_map.mpr ⟨(a, b2), hm2, rfl⟩
  have huv : u ≠ v := by
    intro h
    have h2 : (a, b1) = (a, b2) := (ptEquiv e).symm.injective h
    exact one_ne_zero (congrFun (congrArg Prod.snd h2).symm 1)
  have he1 : e u.1 = a := by simp [u, ptEquiv]
  have he2 : e v.1 = a := by simp [v, ptEquiv]
  have hd1 : traceDualEquiv e u.2 = b1 := by simp [u, ptEquiv]
  have hd2 : traceDualEquiv e v.2 = b2 := by simp [v, ptEquiv]
  have hcomm : symp u v = 0 := by
    rw [symp_eq_trF_dotF e, he1, he2, hd1, hd2]
    have h0 : dotF a b2 + dotF a b1 = 0 := by unfold dotF; simp [a, b1, b2]
    rw [h0, map_zero (trF F)]
  have hnot : u + v ∉ detSupport e := by
    intro hmem
    simp only [detSupport, mem_map, Equiv.coe_toEmbedding, algSupport, mem_filter, mem_univ, true_and] at hmem
    rcases hmem with ⟨⟨a', b'⟩, ⟨ha'0, _⟩, heq⟩
    have hf : a' = e (u + v).1 := by
      have := congrArg (fun p => (ptEquiv e p).1) heq
      simpa [ptEquiv] using this
    have haa : a + a = (0 : Fin 3 → F) := funext fun i => char2_add_self (a i)
    rw [Prod.fst_add, map_add, he1, he2, haa] at hf
    exact ha'0 hf
  exact ⟨u, hu, v, hv, huv, hcomm, hnot⟩

lemma ptEquiv_add {m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F))
    (u v : Pt (3 * m)) :
    ptEquiv e (u + v) = ((ptEquiv e u).1 + (ptEquiv e v).1, (ptEquiv e u).2 + (ptEquiv e v).2) :=
  Prod.ext (e.map_add u.1 v.1) ((traceDualEquiv e).map_add u.2 v.2)

/-- Exact flag count of `detSupport e` for EVERY `m ≥ 1` (`q = 2^m`):
`|flags S_{3m}| = (q³ - 1) q⁴ (q² + q - 3)`. -/
theorem detSupport_flags_card {m : ℕ} (hm : 1 ≤ m) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] [Algebra (ZMod 2) F] (hcard : Fintype.card F = 2 ^ m)
    (e : Vec (3 * m) ≃ₗ[ZMod 2] (Fin 3 → F)) :
    (flags (detSupport e)).card = ((2 ^ m) ^ 3 - 1) * (2 ^ m) ^ 4 * ((2 ^ m) ^ 2 + 2 ^ m - 3) := by
  set q := 2 ^ m with hq
  have hq2 : 2 ≤ q := by
    dsimp [q]; calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hfib : (flags (detSupport e)).card =
      ∑ u ∈ detSupport e,
        ((detSupport e).filter fun v => v ≠ u ∧ u + v ∈ detSupport e ∧ symp u v = 0).card := by
    unfold flags
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    dsimp only
    have hiff : (u + v ∈ detSupport e ∧ symp u v = 0) ↔
        (v ≠ u ∧ u + v ∈ detSupport e ∧ symp u v = 0) := by
      constructor
      · rintro ⟨huv, hs⟩
        refine ⟨fun h => ?_, huv, hs⟩
        subst h
        rw [pt_add_self] at huv
        exact detSupport_zero_notMem e huv
      · rintro ⟨_, huv, hs⟩; exact ⟨huv, hs⟩
    by_cases h : u + v ∈ detSupport e ∧ symp u v = 0
    · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
    · rw [ite_eq_right h, ite_eq_right (mt hiff.mpr h)]
  rw [hfib]
  have hmem_iff : ∀ x : Pt (3 * m), x ∈ detSupport e ↔ ptEquiv e x ∈ algSupport (F := F) m := by
    intro x
    simp only [detSupport, mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨p, hp, rfl⟩; simpa using hp
    · intro hx; exact ⟨ptEquiv e x, hx, by simp⟩
  have hdeg : ∀ u ∈ detSupport e,
      ((detSupport e).filter fun v => v ≠ u ∧ u + v ∈ detSupport e ∧ symp u v = 0).card =
        q ^ 4 + q ^ 3 - 3 * q ^ 2 := by
    intro u hu
    have hu_alg : ptEquiv e u ∈ algSupport (F := F) m := (hmem_iff u).mp hu
    have hbij : ((detSupport e).filter fun v => v ≠ u ∧ u + v ∈ detSupport e ∧ symp u v = 0).card =
        ((algSupport (F := F) m).filter fun p =>
          p ≠ ptEquiv e u ∧ ((ptEquiv e u).1 + p.1, (ptEquiv e u).2 + p.2) ∈ algSupport (F := F) m ∧
          trF F (dotF (ptEquiv e u).1 p.2 + dotF p.1 (ptEquiv e u).2) = 0).card := by
      refine Finset.card_bij (fun v _ => ptEquiv e v) ?_ ?_ ?_
      · intro v hv
        simp only [mem_filter] at hv ⊢
        rcases hv with ⟨hvS, hvu, huvS, hcomm⟩
        refine ⟨(hmem_iff v).mp hvS, fun h => hvu ((ptEquiv e).injective h), ?_, ?_⟩
        · rw [← ptEquiv_add]; exact (hmem_iff (u + v)).mp huvS
        · rw [symp_eq_trF_dotF e u v] at hcomm; exact hcomm
      · intro v1 _ v2 _ h; exact (ptEquiv e).injective h
      · intro p hp
        simp only [mem_filter] at hp
        rcases hp with ⟨hpS, hpu, hupS, htr⟩
        refine ⟨(ptEquiv e).symm p, ?_, (ptEquiv e).apply_symm_apply p⟩
        simp only [mem_filter]
        refine ⟨(hmem_iff _).mpr (by simpa using hpS),
          fun h => hpu (by rw [← (ptEquiv e).apply_symm_apply p, h]), ?_, ?_⟩
        · rw [hmem_iff, ptEquiv_add, (ptEquiv e).apply_symm_apply p]; exact hupS
        · rw [symp_eq_trF_dotF e u ((ptEquiv e).symm p)]
          have hp1 : e ((ptEquiv e).symm p).1 = p.1 := congrArg Prod.fst ((ptEquiv e).apply_symm_apply p)
          have hp2 : traceDualEquiv e ((ptEquiv e).symm p).2 = p.2 := congrArg Prod.snd ((ptEquiv e).apply_symm_apply p)
          rw [hp1, hp2]; exact htr
    rw [hbij]
    have hdeg_pt := algSupport_point_flag_deg (a := (ptEquiv e u).1) (b := (ptEquiv e u).2) hm hcard hu_alg
    rw [hdeg_pt, hcard]
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, detSupport_card hcard e, smul_eq_mul]
  have h1 : 3 ≤ q ^ 2 + q := by nlinarith
  have h2 : 3 * q ^ 2 ≤ q ^ 4 + q ^ 3 := by
    have : 4 * q ^ 2 ≤ q ^ 4 := by
      calc 4 * q ^ 2 = 2 ^ 2 * q ^ 2 := by norm_num
        _ ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hq2 2)
        _ = q ^ 4 := by ring
    omega
  rw [← hq]
  zify [h1, h2]
  ring

/-- **Main Theorem (Infinite Non-Closed Contextual Flat-State Family, all `m ≥ 1`).** -/
theorem infinite_nonclosed_saturated_family (m : ℕ) (hm : 1 ≤ m) :
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
  classical
  intro q
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by omega
  let F := GaloisField 2 m
  let : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = q := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 m hm0
  obtain ⟨e⟩ := exists_linearEquiv_galoisField3 m hm
  let S := detSupport e
  have h0 : (0 : Pt (3 * m)) ∉ S := detSupport_zero_notMem e
  have hS_card : S.card = (q ^ 3 - 1) * q ^ 2 := detSupport_card hcard e
  have hq2 : 2 ≤ q := by
    dsimp [q]; calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hq3_ge8 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
  have hne : S.Nonempty := Finset.card_pos.mp (by
    rw [hS_card]; exact mul_pos (by omega) (by positivity))
  have hflags : (flags S).card = (q ^ 3 - 1) * q ^ 4 * (q ^ 2 + q - 3) :=
    detSupport_flags_card hm hcard e
  have hctx : 6 * (contexts S).card = (q ^ 3 - 1) * q ^ 4 * (q ^ 2 + q - 3) := by
    rw [← card_flags_eq_six_contexts S h0, hflags]
  have hD_eq : (2 : ℝ) ^ (3 * m) = (q : ℝ) ^ 3 := by
    dsimp [q]
    rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm]
  have hsqrt_val : Real.sqrt (((2 : ℝ) ^ (3 * m) - 1) * (S.card : ℝ)) =
      (((q : ℝ) ^ 3 - 1) * (q : ℝ)) := by
    rw [hD_eq, hS_card]
    have hq3_ge : 1 ≤ q ^ 3 := by omega
    have hcast : ((((q ^ 3 - 1) * q ^ 2 : ℕ) : ℝ)) = ((q : ℝ) ^ 3 - 1) * (q : ℝ) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_sub hq3_ge]; push_cast; rfl
    rw [hcast]
    have hrew : ((q : ℝ) ^ 3 - 1) * (((q : ℝ) ^ 3 - 1) * (q : ℝ) ^ 2) =
        (((q : ℝ) ^ 3 - 1) * (q : ℝ)) ^ 2 := by ring
    have hnn : (0 : ℝ) ≤ ((q : ℝ) ^ 3 - 1) * (q : ℝ) := by
      have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
      have hq3R : (8 : ℝ) ≤ (q : ℝ) ^ 3 := by exact_mod_cast hq3_ge8
      nlinarith
    rw [hrew, Real.sqrt_sq hnn]
  have hfloor_rhs : ((2 : ℝ) ^ (3 * m) - 2) * (S.card : ℝ) *
      Real.sqrt (((2 : ℝ) ^ (3 * m) - 1) * (S.card : ℝ)) =
      ((2 : ℝ) ^ (3 * m) - 1) * ((((q ^ 3 - 1) * (q ^ 3 - 2) * q ^ 3 : ℕ) : ℝ)) := by
    rw [hsqrt_val, hD_eq, hS_card]
    have hq3_ge2 : 2 ≤ q ^ 3 := by omega
    have hq3_ge1 : 1 ≤ q ^ 3 := by omega
    have h1 : (((q ^ 3 - 1) * (q ^ 3 - 2) * q ^ 3 : ℕ) : ℝ) =
        ((q : ℝ) ^ 3 - 1) * ((q : ℝ) ^ 3 - 2) * (q : ℝ) ^ 3 := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq3_ge1, Nat.cast_sub hq3_ge2]
      push_cast; rfl
    have h2 : ((((q ^ 3 - 1) * q ^ 2 : ℕ) : ℝ)) = ((q : ℝ) ^ 3 - 1) * (q : ℝ) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_sub hq3_ge1]; push_cast; rfl
    rw [h1, h2]; ring
  have hDm1_pos : (0 : ℝ) < (2 : ℝ) ^ (3 * m) - 1 := by
    rw [hD_eq]
    have hq3R : (8 : ℝ) ≤ (q : ℝ) ^ 3 := by exact_mod_cast hq3_ge8
    linarith
  have halg_diff : (flags S).card =
      (q ^ 3 - 1) * (q ^ 3 - 2) * q ^ 3 + (q ^ 3 - 1) * q ^ 3 * (q - 1) * (q - 2) := by
    rw [hflags]
    have h1 : 3 ≤ q ^ 2 + q := by nlinarith
    have h2 : 2 ≤ q ^ 3 := by omega
    have h3 : 1 ≤ q ^ 3 := by omega
    have h4 : 1 ≤ q := by omega
    zify [h1, h2, h3, h4, hq2]
    ring
  refine ⟨S, h0, hS_card, detSupport_not_closed e, hctx, ?_, ?_⟩
  · intro f hf
    have hhb := hoggar_bound (N := 3 * m) (by omega) S h0 f hf
    rw [hfloor_rhs] at hhb
    have hbeta_le : beta6 S f ≤ (((q ^ 3 - 1) * (q ^ 3 - 2) * q ^ 3 : ℕ) : ℝ) :=
      le_of_mul_le_mul_left hhb hDm1_pos
    rw [beta6_eq_card S f hf, card_violated_eq_six S h0 f] at hbeta_le
    have hnat : (flags S).card ≤ (q ^ 3 - 1) * (q ^ 3 - 2) * q ^ 3 + 12 * (violatedLines S f).card := by
      have : ((flags S).card : ℝ) ≤
          (((q ^ 3 - 1) * (q ^ 3 - 2) * q ^ 3 + 12 * (violatedLines S f).card : ℕ) : ℝ) := by
        push_cast at hbeta_le ⊢; linarith
      exact_mod_cast this
    omega
  · refine ⟨detSigns e, detSigns_values e, ?_⟩
    have hflat := detPhase_isFlatState hm hcard e
    have htfae := saturation_tfae (N := 3 * m) (by omega) S h0 hne (detSigns e)
      (fun u _ => detSigns_values e u)
    have h41 : (∃ ψ, IsFlatState S (detSigns e) ψ) ↔
        ((2 : ℝ) ^ (3 * m) - 1) * beta6 S (detSigns e) =
          ((2 : ℝ) ^ (3 * m) - 2) * (S.card : ℝ) *
            Real.sqrt (((2 : ℝ) ^ (3 * m) - 1) * (S.card : ℝ)) :=
      htfae.out 4 1
    have hsat := h41.mp ⟨detPhaseState e, hflat⟩
    rw [hfloor_rhs] at hsat
    have hbeta_eq : beta6 S (detSigns e) = (((q ^ 3 - 1) * (q ^ 3 - 2) * q ^ 3 : ℕ) : ℝ) :=
      mul_left_cancel₀ (ne_of_gt hDm1_pos) hsat
    rw [beta6_eq_card S (detSigns e) (fun u _ => detSigns_values e u),
        card_violated_eq_six S h0 (detSigns e)] at hbeta_eq
    have hnat : (flags S).card =
        (q ^ 3 - 1) * (q ^ 3 - 2) * q ^ 3 + 12 * (violatedLines S (detSigns e)).card := by
      have : ((flags S).card : ℝ) =
          (((q ^ 3 - 1) * (q ^ 3 - 2) * q ^ 3 + 12 * (violatedLines S (detSigns e)).card : ℕ) : ℝ) := by
        push_cast at hbeta_eq ⊢; linarith
      exact_mod_cast this
    omega

/-- **Corollary:** For every `m ≥ 2` (`N = 6, 9, 12, ...`), the degree `d_m` is strictly positive
(every member for `m ≥ 2` is strictly contextual, non-closed, and saturates the spectral floor). -/
theorem infinite_nonclosed_family_contextual (m : ℕ) (hm : 2 ≤ m) :
    0 < ((2 ^ m) ^ 3 - 1) * (2 ^ m) ^ 3 * (2 ^ m - 1) * (2 ^ m - 2) := by
  have hq : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hq3 : 64 ≤ (2 ^ m) ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ (2 ^ m) ^ 3 := Nat.pow_le_pow_left hq 3
  have h1 : 0 < (2 ^ m) ^ 3 - 1 := by omega
  have h2 : 0 < (2 ^ m) ^ 3 := by positivity
  have h3 : 0 < 2 ^ m - 1 := by omega
  have h4 : 0 < 2 ^ m - 2 := by omega
  positivity

end HoggarBound.NormPhaseFamily

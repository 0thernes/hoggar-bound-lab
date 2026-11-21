/-
Hoggar Bound Lab — Core machinery for Jonah's Conjecture E (all nine vertex cases, all `N ≥ 4`).

This module formalizes:
1. Lemma 20 (`lemma20_jordan_action`): for any closed Pauli configuration `X` and hyperplane `d⊥`,
   Jordan multiplication `Ψ_σ(T) = (A_σ T + T A_σ) / 2` acts on `span{P_p : p ∈ O}` with matrix
   `completionMat X d σ` (defined literally from `HoggarBound.lineSign`).
2. Universal cubic-trace theorem (`trace_completion_cube_universal`):
      `8 · 2^N · tr(Λ_σ³) = 2 |O| · tr(A_σ³) + 6 ∑_{s ∈ H} σ(s) · c_O(s) · tr(A_σ² P_s)`,
   where `c_O(s) = ∑_{p ∈ O} (-1)^{⟨s, p⟩}` is an explicit character sum on `O`.
   This eigenvalue-free identity unifies the cubic-trace calculation across all nine vertex cases
   of Jonah's classification (C1, C3, C5, C6, C8, C11, C12, C14, C15).
3. Lemma 21 (`lemma21_trace_cube_sylvester`, `lemma21_trace_cube_symm`): exact cubic trace
   formulas for `M ↦ (C M + M D) / 2` on all matrices and on symmetric / skew-symmetric matrices.
4. Corollary 18 (`cone_lift_strict_law_fails`): Jonah's cone lift (Lemma D (D2)).
5. Complex block-splitting charpoly lemma (`charpoly_block_split`) and the uniform `g ≥ 2` graph
   character sums (real, imaginary, and diagonal).
-/
import HoggarBound.Kramers
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Block

open Finset Matrix
open scoped Kronecker

namespace HoggarBound.ConjectureE

/-! ### Part 1. Closed configurations, sections, completion matrix, and Lemma 20 -/

section Lemma20

variable {N : ℕ}

/-- A configuration `X` is closed under commuting products of distinct points and excludes `0`. -/
def IsClosedCfg (X : Finset (Pt N)) : Prop :=
  (0 : Pt N) ∉ X ∧ ∀ u ∈ X, ∀ v ∈ X, u ≠ v → symp u v = 0 → u + v ∈ X

/-- Hyperplane section `H = X ∩ d⊥`. -/
def sectionOf (X : Finset (Pt N)) (d : Pt N) : Finset (Pt N) :=
  X.filter fun v => symp v d = 0

/-- Outside set `O = X \ H = {p ∈ X : ⟨p, d⟩ = 1}`. -/
def outsideOf (X : Finset (Pt N)) (d : Pt N) : Finset (Pt N) :=
  X.filter fun v => symp v d = 1

/-- The real symmetric completion matrix `Λ_σ` indexed by `O`, defined directly from
`HoggarBound.lineSign` and `symp`. -/
noncomputable def completionMat (X : Finset (Pt N)) (d : Pt N) (σ : Pt N → ℝ) :
    Matrix {p // p ∈ outsideOf X d} {p // p ∈ outsideOf X d} ℝ :=
  fun q p => if q.1 ≠ p.1 ∧ symp q.1 p.1 = 0
    then lineSign (q.1 + p.1) p.1 * σ (q.1 + p.1) else 0

/-- Jordan multiplication `Ψ_A(T) = (A T + T A) / 2`. -/
noncomputable def jordanOp (A T : Matrix (Vec N) (Vec N) ℂ) : Matrix (Vec N) (Vec N) ℂ :=
  ((1 / 2 : ℂ)) • (A * T + T * A)

lemma symp_add_self_right (u v : Pt N) : symp (u + v) v = symp u v := by
  rw [symp_comm, symp_add_right, symp_self, add_zero, symp_comm]

lemma tau_add_comm' (u v : Pt N) (h : symp u v = 0) : tau (u + v) v = tau (u + v) u := by
  have e1 : u + v + v = u := by rw [add_assoc, pt_add_self, add_zero]
  have e2 : u + v + u = v := by rw [add_comm u v, add_assoc, pt_add_self, add_zero]
  have h1 : pauli (u + v) * pauli v * pauli u = tau (u + v) v • (1 : Matrix (Vec N) (Vec N) ℂ) := by
    rw [pauli_mul, e1, Matrix.smul_mul, pauli_mul_self]
  have h2 : pauli (u + v) * pauli u * pauli v = tau (u + v) u • (1 : Matrix (Vec N) (Vec N) ℂ) := by
    rw [pauli_mul, e2, Matrix.smul_mul, pauli_mul_self]
  have hc : pauli v * pauli u = pauli u * pauli v := by
    rw [pauli_comm, h, eps_zero, one_smul]
  have h3 : tau (u + v) v • (1 : Matrix (Vec N) (Vec N) ℂ) = tau (u + v) u • 1 := by
    rw [← h1, ← h2, Matrix.mul_assoc, hc, ← Matrix.mul_assoc]
  have h4 := congrFun (congrFun h3 0) 0
  simpa using h4

/-- `completionMat` is symmetric. -/
theorem completionMat_transpose (X : Finset (Pt N)) (d : Pt N) (σ : Pt N → ℝ) :
    (completionMat X d σ)ᵀ = completionMat X d σ := by
  ext p q
  simp only [Matrix.transpose_apply, completionMat]
  by_cases h : p.1 ≠ q.1 ∧ symp p.1 q.1 = 0
  · have h' : q.1 ≠ p.1 ∧ symp q.1 p.1 = 0 :=
      ⟨fun e => h.1 e.symm, by rw [symp_comm]; exact h.2⟩
    rw [ite_eq_left h, ite_eq_left h', add_comm q.1 p.1]
    congr 1
    unfold lineSign
    rw [tau_add_comm' p.1 q.1 h.2]
  · have h' : ¬ (q.1 ≠ p.1 ∧ symp q.1 p.1 = 0) :=
      fun hh => h ⟨fun e => hh.1 e.symm, by rw [symp_comm]; exact hh.2⟩
    rw [ite_eq_right h, ite_eq_right h']

/-- **Lemma 20 (Restriction).** For any closed configuration `X` and point `d`,
Jordan multiplication by `A_σ = ∑_{s ∈ H} σ(s) P_s` maps `span{P_p : p ∈ O}` into itself
with matrix `completionMat X d σ`. -/
theorem lemma20_jordan_action {X : Finset (Pt N)} (hX : IsClosedCfg X) (d : Pt N)
    (σ : Pt N → ℝ) (p : {p // p ∈ outsideOf X d}) :
    jordanOp (opA (sectionOf X d) σ) (pauli p.1)
      = ∑ q : {q // q ∈ outsideOf X d},
          ((completionMat X d σ q p : ℝ) : ℂ) • pauli q.1 := by
  classical
  have hpX : p.1 ∈ X := (Finset.mem_filter.mp p.2).1
  have hpd : symp p.1 d = 1 := (Finset.mem_filter.mp p.2).2
  unfold jordanOp opA
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
  -- Simplify each summand `s ∈ sectionOf X d`.
  have hterm : ∀ s ∈ sectionOf X d,
      (1 / 2 : ℂ) • ((((σ s : ℝ) : ℂ) • pauli s) * pauli p.1
        + pauli p.1 * (((σ s : ℝ) : ℂ) • pauli s))
      = if symp s p.1 = 0 then (((lineSign s p.1 * σ s : ℝ) : ℂ)) • pauli (s + p.1) else 0 := by
    intro s _
    rw [Matrix.smul_mul, Matrix.mul_smul, pauli_comm s p.1]
    by_cases hsp : symp s p.1 = 0
    · rw [ite_eq_left hsp, hsp, eps_zero, one_smul, pauli_mul, tau_eq_lineSign hsp, smul_smul,
        ← two_smul ℂ, smul_smul, smul_smul]
      congr 1
      push_cast; ring
    · have hsp1 : symp s p.1 = 1 := (zmod2_cases _).resolve_left hsp
      rw [ite_eq_right hsp, hsp1, eps_one, neg_one_smul, smul_neg, add_neg_cancel, smul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  -- Clean bijection `s ↦ s + p.1` between `H_p` and `O_p`.
  rw [show (∑ q : {q // q ∈ outsideOf X d}, ((completionMat X d σ q p : ℝ) : ℂ) • pauli q.1)
      = ∑ q ∈ (outsideOf X d).filter (fun q => q ≠ p.1 ∧ symp q p.1 = 0),
          ((lineSign (q + p.1) p.1 * σ (q + p.1) : ℝ) : ℂ) • pauli q by
    have h1 : (∑ q : {q // q ∈ outsideOf X d}, ((completionMat X d σ q p : ℝ) : ℂ) • pauli q.1)
        = ∑ q ∈ outsideOf X d, if q ≠ p.1 ∧ symp q p.1 = 0
            then ((lineSign (q + p.1) p.1 * σ (q + p.1) : ℝ) : ℂ) • pauli q else 0 := by
      rw [← Finset.sum_attach (outsideOf X d)]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [completionMat]
      split_ifs <;> simp
    rw [h1, Finset.sum_filter]]
  refine Finset.sum_nbij' (fun s => s + p.1) (fun q => q + p.1) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    obtain ⟨hsH, hsp⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsX, hsd⟩ := Finset.mem_filter.mp hsH
    have hsne : s ≠ p.1 := fun h => by rw [h, hpd] at hsd; exact absurd hsd (by decide)
    have hspX : s + p.1 ∈ X := hX.2 s hsX p.1 hpX hsne hsp
    have hspd : symp (s + p.1) d = 1 := by
      rw [symp_comm, symp_add_right, symp_comm d s, hsd, symp_comm d p.1, hpd, zero_add]
    have hne : s + p.1 ≠ p.1 := by
      intro h
      apply hX.1
      have : s = 0 := by
        calc s = (s + p.1) + p.1 := by rw [add_assoc, pt_add_self, add_zero]
          _ = p.1 + p.1 := by rw [h]
          _ = 0 := pt_add_self p.1
      rwa [← this]
    have hsymp : symp (s + p.1) p.1 = 0 := by rw [symp_add_self_right, hsp]
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hspX, hspd⟩, hne, hsymp⟩
  · intro q hq
    obtain ⟨hqO, hqne, hqp⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqX, hqd⟩ := Finset.mem_filter.mp hqO
    have hqpX : q + p.1 ∈ X := hX.2 q hqX p.1 hpX hqne hqp
    have hqpd : symp (q + p.1) d = 0 := by
      rw [symp_comm, symp_add_right, symp_comm d q, hqd, symp_comm d p.1, hpd]; decide
    have hsymp : symp (q + p.1) p.1 = 0 := by rw [symp_add_self_right, hqp]
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hqpX, hqpd⟩, hsymp⟩
  · intro s _; show s + p.1 + p.1 = s; rw [add_assoc, pt_add_self, add_zero]
  · intro q _; show q + p.1 + p.1 = q; rw [add_assoc, pt_add_self, add_zero]
  · intro s _
    have hadd : s + p.1 + p.1 = s := by rw [add_assoc, pt_add_self, add_zero]
    rw [hadd]

/-- Iterated Jordan action: `Ψ^k(P_p) = ∑_q (Λ^k)_{qp} P_q`. -/
lemma lemma20_jordan_pow {X : Finset (Pt N)} (hX : IsClosedCfg X) (d : Pt N)
    (σ : Pt N → ℝ) (k : ℕ) (p : {p // p ∈ outsideOf X d}) :
    (jordanOp (opA (sectionOf X d) σ))^[k] (pauli p.1)
      = ∑ q : {q // q ∈ outsideOf X d},
          (((completionMat X d σ ^ k) q p : ℝ) : ℂ) • pauli q.1 := by
  induction k generalizing p with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero, Matrix.one_apply]
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hqp; simp [hqp]
    · intro h; exact absurd (mem_univ _) h
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold jordanOp
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.smul_sum]
    have hstep : ∀ r : {r // r ∈ outsideOf X d},
        (1 / 2 : ℂ) • (opA (sectionOf X d) σ * ((((completionMat X d σ ^ k) r p : ℝ) : ℂ) • pauli r.1)
          + ((((completionMat X d σ ^ k) r p : ℝ) : ℂ) • pauli r.1) * opA (sectionOf X d) σ)
        = ((((completionMat X d σ ^ k) r p : ℝ) : ℂ)) •
            ∑ q : {q // q ∈ outsideOf X d}, ((completionMat X d σ q r : ℝ) : ℂ) • pauli q.1 := by
      intro r
      rw [← lemma20_jordan_action hX d σ r]
      unfold jordanOp
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_comm]
    simp_rw [hstep, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [pow_succ', Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    push_cast; ring

/-- Power-trace formula: `2^N · tr(Λ_σ^k) = ∑_{p ∈ O} tr(P_p · Ψ_σ^[k](P_p))`. -/
theorem trace_completion_pow_eq {X : Finset (Pt N)} (hX : IsClosedCfg X) (d : Pt N)
    (σ : Pt N → ℝ) (k : ℕ) :
    (2 : ℂ) ^ N * (((completionMat X d σ ^ k).trace : ℝ) : ℂ)
      = ∑ p ∈ outsideOf X d,
          (pauli p * (jordanOp (opA (sectionOf X d) σ))^[k] (pauli p)).trace := by
  rw [Matrix.trace, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_attach (outsideOf X d)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [lemma20_jordan_pow hX d σ k p, Finset.mul_sum, Matrix.trace_sum]
  rw [Finset.sum_eq_single p]
  · rw [Matrix.mul_smul, Matrix.trace_smul, trace_pauli_mul, ite_eq_left rfl, smul_eq_mul,
      Matrix.diag_apply, mul_comm]
  · intro q _ hqp
    have hne : p.1 ≠ q.1 := fun h => hqp (Subtype.ext h).symm
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_pauli_mul, ite_eq_right hne, smul_zero]
  · intro h; exact absurd (mem_univ _) h

/-- Character sum of `s` over `O`: `c_O(s) = ∑_{p ∈ O} (-1)^{⟨s, p⟩}`. -/
def charSumOut (O : Finset (Pt N)) (s : Pt N) : ℂ :=
  ∑ p ∈ O, eps (symp s p)

/-- **Universal Cubic-Trace Identity** for ANY closed Pauli configuration `X` and point `d`:
`8 · 2^N · tr(Λ_σ³) = 2 |O| · tr(A_σ³) + 6 ∑_{s ∈ H} σ(s) · c_O(s) · tr(A_σ² P_s)`. -/
theorem trace_completion_cube_universal {X : Finset (Pt N)} (hX : IsClosedCfg X) (d : Pt N)
    (σ : Pt N → ℝ) :
    8 * (2 : ℂ) ^ N * (((completionMat X d σ ^ 3).trace : ℝ) : ℂ)
      = 2 * ((outsideOf X d).card : ℂ) * (opA (sectionOf X d) σ ^ 3).trace
        + 6 * ∑ s ∈ sectionOf X d, ((σ s : ℝ) : ℂ) * charSumOut (outsideOf X d) s
            * (opA (sectionOf X d) σ ^ 2 * pauli s).trace := by
  set A := opA (sectionOf X d) σ
  have hpow := trace_completion_pow_eq hX d σ 3
  -- Expand `8 · tr(P_p · Ψ^[3](P_p)) = 2 tr(A³) + 6 tr(A² P_p A P_p)`.
  have hstep : ∀ p : Pt N,
      8 * (pauli p * (jordanOp A)^[3] (pauli p)).trace
        = 2 * (A ^ 3).trace + 6 * (A ^ 2 * (pauli p * A * pauli p)).trace := by
    intro p
    have h3 : (jordanOp A)^[3] (pauli p)
        = (1 / 8 : ℂ) • (A ^ 3 * pauli p + (3 : ℂ) • (A ^ 2 * pauli p * A)
            + (3 : ℂ) • (A * pauli p * A ^ 2) + pauli p * A ^ 3) := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, jordanOp]
      simp only [Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, smul_add, smul_smul,
        Matrix.mul_assoc]
      ext x y
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, pow_succ, pow_zero, one_mul,
        Matrix.mul_assoc]
      ring
    rw [h3, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [show 8 * ((1 / 8 : ℂ) * _) = _ by ring]
    simp only [mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have ht1 : (pauli p * (A ^ 3 * pauli p)).trace = (A ^ 3).trace := by
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc, pauli_mul_self, mul_one]
    have ht4 : (pauli p * (pauli p * A ^ 3)).trace = (A ^ 3).trace := by
      rw [← Matrix.mul_assoc, pauli_mul_self, one_mul]
    have ht2 : (pauli p * (A ^ 2 * pauli p * A)).trace
        = (A ^ 2 * (pauli p * A * pauli p)).trace := by
      calc (pauli p * (A ^ 2 * pauli p * A)).trace
          = (A ^ 2 * pauli p * A * pauli p).trace := Matrix.trace_mul_comm _ _
        _ = (A ^ 2 * (pauli p * A * pauli p)).trace := by simp only [Matrix.mul_assoc]
    have ht3 : (pauli p * (A * pauli p * A ^ 2)).trace
        = (A ^ 2 * (pauli p * A * pauli p)).trace := by
      calc (pauli p * (A * pauli p * A ^ 2)).trace
          = (pauli p * A * pauli p * A ^ 2).trace := by simp only [Matrix.mul_assoc]
        _ = (A ^ 2 * (pauli p * A * pauli p)).trace := Matrix.trace_mul_comm _ _
    rw [ht1, ht2, ht3, ht4]
    ring
  have hmul : 8 * (2 : ℂ) ^ N * (((completionMat X d σ ^ 3).trace : ℝ) : ℂ)
      = ∑ p ∈ outsideOf X d, 8 * (pauli p * (jordanOp A)^[3] (pauli p)).trace := by
    rw [mul_assoc, hpow, Finset.mul_sum]
  rw [hmul, Finset.sum_congr rfl (fun p _ => hstep p), Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum]
  have h1 : ((outsideOf X d).card : ℂ) * (2 * (A ^ 3).trace) = 2 * ((outsideOf X d).card : ℂ) * (A ^ 3).trace := by
    ring
  rw [h1]
  congr 1
  congr 1
  -- Expand `∑_{p ∈ O} tr(A² P_p A P_p) = ∑_{s ∈ H} σ(s) · c_O(s) · tr(A² P_s)`.
  have hconj : ∀ p : Pt N,
      pauli p * A * pauli p = ∑ s ∈ sectionOf X d, (((σ s : ℝ) : ℂ) * eps (symp s p)) • pauli s := by
    intro p
    dsimp only [A, opA]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, pauli_comm s p, Matrix.smul_mul, Matrix.mul_assoc,
      pauli_mul_self, mul_one, smul_smul, mul_comm]
  simp_rw [hconj, Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold charSumOut
  rw [Finset.mul_sum, Finset.sum_mul]

/-- Explicit formula for `tr(A_σ² P_z)` when `z ∈ H` commutes with all of `H`. -/
theorem trace_opA_sq_mul_central {H : Finset (Pt N)} (σ : Pt N → ℝ) {z : Pt N}
    (_hz : z ≠ 0) (_hcomm : ∀ u ∈ H, symp u z = 0) :
    (opA H σ ^ 2 * pauli z).trace
      = (2 : ℂ) ^ N * ∑ u ∈ H.filter (fun u => u + z ∈ H),
          ((σ u : ℝ) : ℂ) * ((σ (u + z) : ℝ) : ℂ) * tau u (u + z) := by
  classical
  rw [pow_two, opA_mul_opA, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_mul, Matrix.trace_sum]
  have hinner : ∀ v ∈ H,
      ((((σ u : ℝ) : ℂ) * ((σ v : ℝ) : ℂ) * tau u v) • pauli (u + v) * pauli z).trace
        = if v = u + z then (2 : ℂ) ^ N * (((σ u : ℝ) : ℂ) * ((σ (u + z) : ℝ) : ℂ) * tau u (u + z)) else 0 := by
    intro v _
    rw [Matrix.smul_mul, Matrix.trace_smul, trace_pauli_mul, smul_eq_mul]
    have hiff : u + v = z ↔ v = u + z := by
      constructor
      · intro h
        calc v = (u + u) + v := by rw [pt_add_self, zero_add]
          _ = u + (u + v) := by abel
          _ = u + z := by rw [h]
      · intro h; rw [h, ← add_assoc, pt_add_self, zero_add]
    by_cases hv : v = u + z
    · rw [ite_eq_left (hiff.mpr hv), ite_eq_left hv, hv]; ring
    · rw [ite_eq_right (fun h => hv (hiff.mp h)), ite_eq_right hv, mul_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']

end Lemma20

/-! ### Part 2. Characteristic polynomial determines power traces for Hermitian matrices -/

section SpectralTraces

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma trace_pow_eq_charpoly_roots_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = (A.charpoly.roots.map (· ^ k)).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, trace_pow_eq_sum_eigenvalues_pow hA k]
  rfl

theorem trace_pow_eq_of_charpoly_eq_complex {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) (k : ℕ) :
    (A ^ k).trace = (B ^ k).trace := by
  rw [trace_pow_eq_charpoly_roots_sum hA k, trace_pow_eq_charpoly_roots_sum hB k, h]

theorem trace_pow_eq_of_charpoly_eq_real {A B : Matrix n n ℝ}
    (hA : Aᵀ = A) (hB : Bᵀ = B) (h : A.charpoly = B.charpoly) (k : ℕ) :
    (A ^ k).trace = (B ^ k).trace := by
  set AC : Matrix n n ℂ := A.map Complex.ofRealHom
  set BC : Matrix n n ℂ := B.map Complex.ofRealHom
  have hAC : AC.IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j
    simp only [AC, Matrix.conjTranspose_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe,
      Complex.star_def, Complex.conj_ofReal]
    exact congrArg (fun r : ℝ => (r : ℂ)) (congrFun (congrFun hA i) j)
  have hBC : BC.IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j
    simp only [BC, Matrix.conjTranspose_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe,
      Complex.star_def, Complex.conj_ofReal]
    exact congrArg (fun r : ℝ => (r : ℂ)) (congrFun (congrFun hB i) j)
  have hcp : AC.charpoly = BC.charpoly := by
    dsimp [AC, BC]
    rw [Matrix.charpoly_map A Complex.ofRealHom, Matrix.charpoly_map B Complex.ofRealHom, h]
  have htr := trace_pow_eq_of_charpoly_eq_complex hAC hBC hcp k
  have hpowC : ∀ (M : Matrix n n ℝ) (j : ℕ),
      ((M.map Complex.ofRealHom) ^ j).trace = ((M ^ j).trace : ℂ) := by
    intro M j
    have hm : (M.map Complex.ofRealHom) ^ j = (M ^ j).map Complex.ofRealHom := by
      induction j with
      | zero => simp [Matrix.map_one]
      | succ j ih => rw [pow_succ, pow_succ, ih, ← Matrix.map_mul]
    rw [hm]
    simp [Matrix.trace, Complex.ofReal_sum]
  rw [hpowC A k, hpowC B k] at htr
  exact Complex.ofReal_injective htr

end SpectralTraces

/-! ### Part 3. Lemma 21 (Jordan multiplication trace formulas) -/

section Lemma21

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix of `M ↦ (1/2)(C M + M D)` on `Matrix ι ι ℂ` in the standard basis. -/
noncomputable def jordanSylvester (C D : Matrix ι ι ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  (1 / 2 : ℂ) • (C ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ Dᵀ)

/-- Transpose operator `T : M ↦ Mᵀ` as a matrix on `ι × ι`. -/
def transposeMat : Matrix (ι × ι) (ι × ι) ℂ :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- **Lemma 21(a) (Trace-cube formula).** For any `k × k` complex matrices `C, D`:
`tr(Φ³) = (1/8)(k tr C³ + 3 tr C² tr D + 3 tr C tr D² + k tr D³)`. -/
theorem lemma21_trace_cube_sylvester (C D : Matrix ι ι ℂ) :
    (jordanSylvester C D ^ 3).trace
      = (1 / 8 : ℂ) * ((Fintype.card ι : ℂ) * (C ^ 3).trace
          + 3 * (C ^ 2).trace * D.trace
          + 3 * C.trace * (D ^ 2).trace
          + (Fintype.card ι : ℂ) * (D ^ 3).trace) := by
  have h2 : (Dᵀ * Dᵀ).trace = (D * D).trace := by rw [← transpose_mul, trace_transpose]
  have h3 : (Dᵀ * (Dᵀ * Dᵀ)).trace = (D * (D * D)).trace := by
    rw [← transpose_mul, ← transpose_mul, trace_transpose, mul_assoc]
  unfold jordanSylvester
  rw [smul_pow, Matrix.trace_smul, smul_eq_mul,
    pow_three (C ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ Dᵀ)]
  simp only [mul_add, add_mul, ← mul_kronecker_mul, mul_one, one_mul, trace_add, trace_kronecker,
    trace_one, trace_transpose, h2, h3]
  rw [pow_three C, pow_two C, pow_three D, pow_two D]
  ring

lemma trace_kronecker_mul_transposeMat (A B : Matrix ι ι ℂ) :
    ((A ⊗ₖ B) * transposeMat).trace = (A * B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, kroneckerMap_apply, transposeMat,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi; simp [hbi]
    · intro h; exact absurd (mem_univ _) h
  · intro a _ haj
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [haj]
  · intro h; exact absurd (mem_univ _) h

/-- **Lemma 21(b) (Symmetric / skew-symmetric trace-cube formula).**
For `Φ(M) = (1/2)(C M + M Cᵀ)` and projection `P_η(M) = (1/2)(M + η Mᵀ)` (`η ∈ {±1}`),
`2 · tr_ℂ(Φ³ ∘ P_η) = (1/4)((k + 4η) tr C³ + 3 tr C · tr C²)`. -/
theorem lemma21_trace_cube_symm (C : Matrix ι ι ℂ) (η : ℂ) :
    2 * ((jordanSylvester C Cᵀ ^ 3) * ((1 / 2 : ℂ) • (1 + η • transposeMat))).trace
      = (1 / 4 : ℂ) * (((Fintype.card ι : ℂ) + 4 * η) * (C ^ 3).trace
          + 3 * C.trace * (C ^ 2).trace) := by
  have hT : ((jordanSylvester C Cᵀ ^ 3) * transposeMat).trace = (C ^ 3).trace := by
    have h2 : (Cᵀᵀ) = C := transpose_transpose C
    unfold jordanSylvester
    rw [h2, smul_pow, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      pow_three (C ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ C)]
    simp only [mul_add, add_mul, ← mul_kronecker_mul, mul_one, one_mul, trace_add,
      trace_kronecker_mul_transposeMat]
    rw [pow_three C, Matrix.mul_assoc]
    ring
  rw [Matrix.mul_smul, Matrix.trace_smul, mul_add, Matrix.trace_add, mul_one,
    Matrix.mul_smul, Matrix.trace_smul, lemma21_trace_cube_sylvester, hT,
    show (Cᵀ ^ 3).trace = (C ^ 3).trace by rw [← transpose_pow, trace_transpose],
    show (Cᵀ ^ 2).trace = (C ^ 2).trace by rw [← transpose_pow, trace_transpose],
    trace_transpose]
  simp only [smul_eq_mul]
  ring

end Lemma21

/-! ### Part 4. Complex block-splitting charpoly lemma -/

section BlockSplit

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma charmatrix_neg_one_add_complex (B : Matrix ι ι ℂ) :
    charmatrix (-1 + B) = charmatrix (-1 : Matrix ι ι ℂ) - (Polynomial.C : ℂ →+* ℂ[X]).mapMatrix B := by
  simp only [charmatrix, map_add]
  abel

lemma charmatrix_neg_one_commute_complex (M : Matrix ι ι ℂ[X]) :
    M * charmatrix (-1 : Matrix ι ι ℂ) = charmatrix (-1 : Matrix ι ι ℂ) * M := by
  have h1 : charmatrix (-1 : Matrix ι ι ℂ) = Matrix.scalar ι (X : ℂ[X]) + 1 := by
    simp only [charmatrix, map_neg, map_one, sub_neg_eq_add]
  rw [h1]
  exact (((Matrix.scalar_commute (X : ℂ[X]) (fun _ => Commute.all _ _) M).add_left
    (Commute.one_left M)).eq).symm

/-- If `B₁ * B₂ = 0`, then moving `B₂` from the upper-left block `-1 + B₁ + B₂` to the lower-right
block `-1` preserves the characteristic polynomial of the block-diagonal matrix. -/
theorem charpoly_block_split (B₁ B₂ : Matrix ι ι ℂ) (h12 : B₁ * B₂ = 0) :
    (fromBlocks (-1 + (B₁ + B₂)) 0 0 (-1 : Matrix ι ι ℂ)).charpoly
      = (fromBlocks (-1 + B₁) 0 0 (-1 + B₂)).charpoly := by
  have hφ : (Polynomial.C : ℂ →+* ℂ[X]).mapMatrix B₁ * (Polynomial.C : ℂ →+* ℂ[X]).mapMatrix B₂ = 0 := by
    rw [← map_mul, h12, map_zero]
  have key : charmatrix (-1 + B₁) * charmatrix (-1 + B₂)
      = charmatrix (-1 : Matrix ι ι ℂ) * charmatrix (-1 + (B₁ + B₂)) := by
    rw [charmatrix_neg_one_add_complex, charmatrix_neg_one_add_complex, charmatrix_neg_one_add_complex,
      map_add, sub_mul, mul_sub, mul_sub,
      charmatrix_neg_one_commute_complex ((Polynomial.C : ℂ →+* ℂ[X]).mapMatrix B₁),
      hφ, mul_sub, mul_add]
    abel
  rw [charpoly_fromBlocks_zero₁₂, charpoly_fromBlocks_zero₁₂]
  simp only [charpoly]
  rw [mul_comm, ← det_mul, ← key, det_mul]

/-- Moving a block in a 4-block matrix `C ⊕ Cᵀ ⊕ D ⊕ Dᵀ` preserves the characteristic polynomial. -/
theorem charpoly_four_block_split (B₁ B₂ : Matrix ι ι ℂ) (h12 : B₁ * B₂ = 0) :
    (fromBlocks (fromBlocks (-1 + (B₁ + B₂)) 0 0 (-1 + (B₁ + B₂))ᵀ) 0 0
        (fromBlocks (-1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix ι ι ℂ)ᵀ)).charpoly
      = (fromBlocks (fromBlocks (-1 + B₁) 0 0 (-1 + B₁)ᵀ) 0 0
          (fromBlocks (-1 + B₂) 0 0 (-1 + B₂)ᵀ)).charpoly := by
  have h2 := charpoly_block_split B₁ B₂ h12
  rw [charpoly_fromBlocks_zero₁₂, charpoly_fromBlocks_zero₁₂] at h2
  simp only [charpoly_fromBlocks_zero₁₂, Matrix.charpoly_transpose]
  calc (-1 + (B₁ + B₂)).charpoly * (-1 + (B₁ + B₂)).charpoly * ((-1 : Matrix ι ι ℂ).charpoly * (-1 : Matrix ι ι ℂ).charpoly)
      = ((-1 + (B₁ + B₂)).charpoly * (-1 : Matrix ι ι ℂ).charpoly) ^ 2 := by ring
    _ = ((-1 + B₁).charpoly * (-1 + B₂).charpoly) ^ 2 := by rw [h2]
    _ = (-1 + B₁).charpoly * (-1 + B₁).charpoly * ((-1 + B₂).charpoly * (-1 + B₂).charpoly) := by ring

end BlockSplit

/-! ### Part 5. Uniform `g ≥ 2` graph character sums (real, imaginary, diagonal) -/

section GraphSums

/-- Basis vector `e_0` in `Vec g` (`g ≥ 2`). -/
def gv1 {g : ℕ} (hg : 2 ≤ g) : Vec g := Pi.single ⟨0, by omega⟩ 1

/-- Basis vector `e_1` in `Vec g` (`g ≥ 2`). -/
def gv2 {g : ℕ} (hg : 2 ≤ g) : Vec g := Pi.single ⟨1, by omega⟩ 1

/-- Vector `e_0 + e_1` in `Vec g` (`g ≥ 2`). -/
def gv3 {g : ℕ} (hg : 2 ≤ g) : Vec g := gv1 hg + gv2 hg

/-- Uniform graph vertex assignment `u_a` for every `a : Vec g` (`g ≥ 2`):
the triangle `{0, e_0, e_0 + e_1}` is a connected component disjoint from `t = e_1` and from
every other edge `{e_1, e_1 + a}`. -/
def uEdge {g : ℕ} (hg : 2 ≤ g) (a : Vec g) : Vec g :=
  if a = gv1 hg then 0
  else if a = gv2 hg then gv1 hg
  else if a = gv3 hg then 0
  else gv2 hg

/-- The three moved directions forming the triangle component `{0, e_0, e_0 + e_1}`. -/
def isMovedDir {g : ℕ} (hg : 2 ≤ g) (a : Vec g) : Prop :=
  a = gv1 hg ∨ a = gv2 hg ∨ a = gv3 hg

instance {g : ℕ} (hg : 2 ≤ g) (a : Vec g) : Decidable (isMovedDir hg a) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Vertices of the triangle component: `{0, e_0, e_0 + e_1}`. -/
def inTriVert {g : ℕ} (hg : 2 ≤ g) (x : Vec g) : Prop :=
  x = 0 ∨ x = gv1 hg ∨ x = gv3 hg

lemma gv_ne_01 {g : ℕ} (hg : 2 ≤ g) : gv1 hg ≠ 0 := by
  intro h; have := congrFun h ⟨0, by omega⟩; simp [gv1] at this

lemma gv_ne_02 {g : ℕ} (hg : 2 ≤ g) : gv2 hg ≠ 0 := by
  intro h; have := congrFun h ⟨1, by omega⟩; simp [gv2] at this

lemma gv_ne_03 {g : ℕ} (hg : 2 ≤ g) : gv3 hg ≠ 0 := by
  intro h; have := congrFun h ⟨0, by omega⟩
  have h01 : (⟨0, by omega⟩ : Fin g) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  simp [gv3, gv1, gv2, h01] at this

lemma gv_ne_12 {g : ℕ} (hg : 2 ≤ g) : gv1 hg ≠ gv2 hg := by
  intro h; have := congrFun h ⟨0, by omega⟩
  have h01 : (⟨0, by omega⟩ : Fin g) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  simp [gv1, gv2, h01] at this

lemma gv_ne_13 {g : ℕ} (hg : 2 ≤ g) : gv1 hg ≠ gv3 hg := by
  intro h; have := congrFun h ⟨1, by omega⟩
  have h10 : (⟨1, by omega⟩ : Fin g) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  simp [gv3, gv1, gv2, h10] at this

lemma gv_ne_23 {g : ℕ} (hg : 2 ≤ g) : gv2 hg ≠ gv3 hg := by
  intro h; have := congrFun h ⟨0, by omega⟩
  have h01 : (⟨0, by omega⟩ : Fin g) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  simp [gv3, gv1, gv2, h01] at this

lemma not_inTriVert_gv2 {g : ℕ} (hg : 2 ≤ g) : ¬ inTriVert hg (gv2 hg) := by
  rintro (h | h | h)
  · exact gv_ne_02 hg h
  · exact gv_ne_12 hg h.symm
  · exact gv_ne_23 hg h

lemma uEdge_inTriVert_of_moved {g : ℕ} (hg : 2 ≤ g) {a : Vec g} (ha : isMovedDir hg a) :
    inTriVert hg (uEdge hg a) ∧ inTriVert hg (uEdge hg a + a) := by
  rcases ha with rfl | rfl | rfl
  · simp [uEdge, inTriVert]
  · simp [uEdge, (gv_ne_12 hg).symm, gv3, inTriVert]
  · simp [uEdge, (gv_ne_13 hg).symm, (gv_ne_23 hg).symm, inTriVert]

lemma uEdge_not_inTriVert_of_unmoved {g : ℕ} (hg : 2 ≤ g) {a : Vec g}
    (ha : ¬ isMovedDir hg a) :
    ¬ inTriVert hg (uEdge hg a) ∧ ¬ inTriVert hg (uEdge hg a + a) := by
  have h1 : a ≠ gv1 hg := fun h => ha (Or.inl h)
  have h2 : a ≠ gv2 hg := fun h => ha (Or.inr (Or.inl h))
  have h3 : a ≠ gv3 hg := fun h => ha (Or.inr (Or.inr h))
  have hu : uEdge hg a = gv2 hg := by simp [uEdge, h1, h2, h3]
  rw [hu]
  refine ⟨not_inTriVert_gv2 hg, ?_⟩
  rintro (h | h | h)
  · apply h2
    calc a = (gv2 hg + gv2 hg) + a := by rw [vec_add_self, zero_add]
      _ = gv2 hg + (gv2 hg + a) := by abel
      _ = gv2 hg := by rw [h, add_zero]
  · apply h3
    calc a = (gv2 hg + gv2 hg) + a := by rw [vec_add_self, zero_add]
      _ = gv2 hg + (gv2 hg + a) := by abel
      _ = gv2 hg + gv1 hg := by rw [h]
      _ = gv3 hg := by rw [gv3, add_comm]
  · apply h1
    calc a = (gv2 hg + gv2 hg) + a := by rw [vec_add_self, zero_add]
      _ = gv2 hg + (gv2 hg + a) := by abel
      _ = gv2 hg + (gv1 hg + gv2 hg) := by rw [h, gv3]
      _ = gv1 hg + (gv2 hg + gv2 hg) := by abel
      _ = gv1 hg := by rw [vec_add_self, add_zero]

/-- Real edge matrix `E(u, a) = |u+a⟩⟨u| + |u⟩⟨u+a|`. -/
def edgeReal {g : ℕ} (u a : Vec g) : Matrix (Vec g) (Vec g) ℂ :=
  fun x y => (if x = u + a ∧ y = u then 1 else 0) + (if x = u ∧ y = u + a then 1 else 0)

/-- Antisymmetric edge matrix `J(u, a) = |u+a⟩⟨u| - |u⟩⟨u+a|`. -/
def edgeImag {g : ℕ} (u a : Vec g) : Matrix (Vec g) (Vec g) ℂ :=
  fun x y => (if x = u + a ∧ y = u then 1 else 0) - (if x = u ∧ y = u + a then 1 else 0)

/-- Rank-one projector `|t⟩⟨t|`. -/
def diagProj {g : ℕ} (t : Vec g) : Matrix (Vec g) (Vec g) ℂ :=
  fun x y => if x = t ∧ y = t then 1 else 0

/-- Graph sign for even `ycount(a, c)` (real Pauli `P_{a, c}`). -/
def signEven {g : ℕ} (u a c : Vec g) : ℝ :=
  (-1 : ℝ) ^ (ZMod.val (c ⬝ᵥ u) + ycount (a, c) / 2)

/-- Graph sign for odd `ycount(a, c)` (imaginary Pauli `P_{a, c}`). -/
def signOdd {g : ℕ} (u a c : Vec g) : ℝ :=
  (-1 : ℝ) ^ (ZMod.val (c ⬝ᵥ u) + (ycount (a, c) - 1) / 2)

lemma signEven_eq_one_or {g : ℕ} (u a c : Vec g) : signEven u a c = 1 ∨ signEven u a c = -1 :=
  neg_one_pow_eq_or ℝ _

lemma signOdd_eq_one_or {g : ℕ} (u a c : Vec g) : signOdd u a c = 1 ∨ signOdd u a c = -1 :=
  neg_one_pow_eq_or ℝ _

lemma eps_eq_neg_one_pow_val (z : ZMod 2) : eps z = (-1 : ℂ) ^ (ZMod.val z) := by
  rcases zmod2_cases z with rfl | rfl
  · simp
  · have hv : ZMod.val (1 : ZMod 2) = 1 := rfl
    simp [hv]

lemma signEven_smul_pauli {g : ℕ} (u a c : Vec g) (hq : qform (a, c) = 0) :
    ((signEven u a c : ℝ) : ℂ) • pauli (a, c) = chi c u • weyl (a, c) := by
  rw [pauli, smul_smul]
  congr 1
  have heven : 2 ∣ ycount (a, c) := by
    have h0 : ((ycount (a, c) : ℕ) : ZMod 2) = 0 := by rw [← dot_eq_ycount]; exact hq
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  obtain ⟨k, hk⟩ := heven
  have hdiv : ycount (a, c) / 2 = k := by omega
  unfold signEven chi
  rw [hdiv, hk, eps_eq_neg_one_pow_val]
  push_cast
  rw [pow_add, pow_mul, Complex.I_sq]
  have hsq : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by rw [← mul_pow]; simp
  linear_combination (-1 : ℂ) ^ ZMod.val (c ⬝ᵥ u) * hsq

lemma signOdd_smul_pauli {g : ℕ} (u a c : Vec g) (hq : qform (a, c) = 1) :
    ((signOdd u a c : ℝ) : ℂ) • pauli (a, c) = (Complex.I * chi c u) • weyl (a, c) := by
  rw [pauli, smul_smul]
  congr 1
  have hodd : ycount (a, c) % 2 = 1 := by
    have h1 : ((ycount (a, c) : ℕ) : ZMod 2) = 1 := by rw [← dot_eq_ycount]; exact hq
    have hmod : ((ycount (a, c) : ℕ) : ZMod 2).val = ycount (a, c) % 2 :=
      ZMod.val_natCast (n := 2) (ycount (a, c))
    have hv : (1 : ZMod 2).val = 1 := rfl
    rw [h1, hv] at hmod
    exact hmod.symm
  set k := (ycount (a, c) - 1) / 2 with hkdef
  have hk : ycount (a, c) = 2 * k + 1 := by omega
  unfold signOdd chi
  rw [← hkdef, hk, eps_eq_neg_one_pow_val]
  push_cast
  rw [pow_add, pow_succ, pow_mul, Complex.I_sq]
  have hsq : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by rw [← mul_pow]; simp
  linear_combination Complex.I * (-1 : ℂ) ^ ZMod.val (c ⬝ᵥ u) * hsq

lemma sum_chi_eq {g : ℕ} (v : Vec g) :
    ∑ c : Vec g, chi c v = if v = 0 then (2 : ℂ) ^ g else 0 := by
  have : ∀ c : Vec g, chi c v = chi v c := fun c => by unfold chi; rw [dotProduct_comm]
  simp_rw [this]
  exact sum_chi v

/-- Character sum (E4) for real Pauli operators of nonzero direction `a`. -/
theorem sum_real_pauli_dir {g : ℕ} (hg : 1 ≤ g) (u : Vec g) {a : Vec g} (ha : a ≠ 0) :
    ∑ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 0),
        ((signEven u a c : ℝ) : ℂ) • pauli (a, c)
      = ((2 : ℂ) ^ (g - 1)) • edgeReal u a := by
  have hterm : ∀ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 0),
      ((signEven u a c : ℝ) : ℂ) • pauli (a, c) = chi c u • weyl (a, c) :=
    fun c hc => signEven_smul_pauli u a c (Finset.mem_filter.mp hc).2
  rw [Finset.sum_congr rfl hterm]
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, weyl, edgeReal]
  have h2pow : (2 : ℂ) ^ g = 2 * (2 : ℂ) ^ (g - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hg, pow_succ, mul_comm]
  by_cases hxy : x = y + a
  · simp only [hxy, ↓reduceIte]
    rw [Finset.sum_filter]
    have hind : ∀ c : Vec g,
        (if qform (a, c) = 0 then chi c u * chi c y else 0)
          = (chi c (u + y) + chi c (u + y + a)) / 2 := by
      intro c
      have h1 : (if qform (a, c) = 0 then chi c u * chi c y else 0)
          = (if qform (a, c) = 0 then (1 : ℂ) else 0) * (chi c u * chi c y) := by
        split_ifs <;> simp
      rw [h1, indicator_eq]
      have hq : eps (qform (a, c)) = chi c a := rfl
      rw [hq, ← chi_add_right, div_mul_eq_mul_div, add_mul, one_mul, ← chi_add_right]
      have hcomm : a + (u + y) = u + y + a := by abel
      rw [hcomm]
    simp_rw [hind, ← Finset.sum_div, Finset.sum_add_distrib, sum_chi_eq]
    have hiff1 : u + y = 0 ↔ y = u := by
      constructor
      · intro h; calc y = (u + u) + y := by rw [vec_add_self, zero_add]
          _ = u + (u + y) := by abel
          _ = u := by rw [h, add_zero]
      · intro h; rw [h]; exact vec_add_self u
    have hiff2 : u + y + a = 0 ↔ y = u + a := by
      constructor
      · intro h; calc y = (u + u) + y + (a + a) := by rw [vec_add_self, vec_add_self, zero_add, add_zero]
          _ = (u + y + a) + (u + a) := by abel
          _ = u + a := by rw [h, zero_add]
      · rintro rfl; calc u + (u + a) + a = (u + u) + (a + a) := by abel
          _ = 0 := by rw [vec_add_self, vec_add_self, add_zero]
    by_cases hyu : y = u
    · subst y
      have hne : u ≠ u + a := fun h => ha (by
        calc a = (u + u) + a := by rw [vec_add_self, zero_add]
          _ = u + (u + a) := by abel
          _ = u + u := by rw [← h]
          _ = 0 := vec_add_self u)
      have h1 : u + u = 0 := vec_add_self u
      have h2 : u + u + a ≠ 0 := by rw [h1, zero_add]; exact ha
      rw [ite_eq_left h1, ite_eq_right h2, add_zero, h2pow]
      simp [hne, hne.symm]
    · by_cases hyua : y = u + a
      · subst y
        have h1 : u + (u + a) ≠ 0 := fun h => hyu (hiff1.mp h)
        have h2 : u + (u + a) + a = 0 := hiff2.mpr rfl
        have h3 : u + a + a = u := by rw [add_assoc, vec_add_self, add_zero]
        rw [ite_eq_right h1, ite_eq_left h2, zero_add, h2pow]
        simp [h3, hyu]
      · have h1 : u + y ≠ 0 := fun h => hyu (hiff1.mp h)
        have h2 : u + y + a ≠ 0 := fun h => hyua (hiff2.mp h)
        rw [ite_eq_right h1, ite_eq_right h2]
        simp [hyu, hyua]
  · simp only [hxy, ↓reduceIte, mul_zero, Finset.sum_const_zero]
    have h1 : ¬ (x = u + a ∧ y = u) := by rintro ⟨rfl, rfl⟩; exact hxy rfl
    have h2 : ¬ (x = u ∧ y = u + a) := by
      rintro ⟨rfl, rfl⟩; apply hxy; rw [add_assoc, vec_add_self, add_zero]
    simp [h1, h2]

/-- Character sum (E10) for imaginary Pauli operators of nonzero direction `a`. -/
theorem sum_imag_pauli_dir {g : ℕ} (hg : 1 ≤ g) (u : Vec g) {a : Vec g} (ha : a ≠ 0) :
    ∑ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 1),
        ((signOdd u a c : ℝ) : ℂ) • pauli (a, c)
      = ((2 : ℂ) ^ (g - 1) * Complex.I) • edgeImag u a := by
  have hterm : ∀ c ∈ univ.filter (fun c : Vec g => qform (a, c) = 1),
      ((signOdd u a c : ℝ) : ℂ) • pauli (a, c) = (Complex.I * chi c u) • weyl (a, c) :=
    fun c hc => signOdd_smul_pauli u a c (Finset.mem_filter.mp hc).2
  rw [Finset.sum_congr rfl hterm]
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, weyl, edgeImag]
  have h2pow : (2 : ℂ) ^ g = 2 * (2 : ℂ) ^ (g - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hg, pow_succ, mul_comm]
  by_cases hxy : x = y + a
  · simp only [hxy, ↓reduceIte]
    rw [Finset.sum_filter]
    have hind : ∀ c : Vec g,
        (if qform (a, c) = 1 then Complex.I * chi c u * chi c y else 0)
          = Complex.I * ((chi c (u + y) - chi c (u + y + a)) / 2) := by
      intro c
      have hq : eps (qform (a, c)) = chi c a := rfl
      have h1 : (if qform (a, c) = 1 then (1 : ℂ) else 0) = (1 - eps (qform (a, c))) / 2 := by
        rcases zmod2_cases (qform (a, c)) with h | h <;> simp [h]
      have h2 : (if qform (a, c) = 1 then Complex.I * chi c u * chi c y else 0)
          = (if qform (a, c) = 1 then (1 : ℂ) else 0) * (Complex.I * (chi c u * chi c y)) := by
        split_ifs <;> ring
      rw [h2, h1, hq, ← chi_add_right]
      have h3 : chi c a * chi c (u + y) = chi c (u + y + a) := by
        rw [← chi_add_right, add_comm]
      linear_combination -(Complex.I / 2) * h3
    simp_rw [hind, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib, sum_chi_eq]
    have hiff1 : u + y = 0 ↔ y = u := by
      constructor
      · intro h; calc y = (u + u) + y := by rw [vec_add_self, zero_add]
          _ = u + (u + y) := by abel
          _ = u := by rw [h, add_zero]
      · intro h; rw [h]; exact vec_add_self u
    have hiff2 : u + y + a = 0 ↔ y = u + a := by
      constructor
      · intro h; calc y = (u + u) + y + (a + a) := by rw [vec_add_self, vec_add_self, zero_add, add_zero]
          _ = (u + y + a) + (u + a) := by abel
          _ = u + a := by rw [h, zero_add]
      · rintro rfl; calc u + (u + a) + a = (u + u) + (a + a) := by abel
          _ = 0 := by rw [vec_add_self, vec_add_self, add_zero]
    by_cases hyu : y = u
    · subst y
      have hne : u ≠ u + a := fun h => ha (by
        calc a = (u + u) + a := by rw [vec_add_self, zero_add]
          _ = u + (u + a) := by abel
          _ = u + u := by rw [← h]
          _ = 0 := vec_add_self u)
      have h1 : u + u = 0 := vec_add_self u
      have h2 : u + u + a ≠ 0 := by rw [h1, zero_add]; exact ha
      rw [ite_eq_left h1, ite_eq_right h2, sub_zero, h2pow]
      simp [hne, hne.symm]; ring
    · by_cases hyua : y = u + a
      · subst y
        have h1 : u + (u + a) ≠ 0 := fun h => hyu (hiff1.mp h)
        have h2 : u + (u + a) + a = 0 := hiff2.mpr rfl
        have h3 : u + a + a = u := by rw [add_assoc, vec_add_self, add_zero]
        rw [ite_eq_right h1, ite_eq_left h2, zero_sub, h2pow]
        simp [h3, hyu]; ring
      · have h1 : u + y ≠ 0 := fun h => hyu (hiff1.mp h)
        have h2 : u + y + a ≠ 0 := fun h => hyua (hiff2.mp h)
        rw [ite_eq_right h1, ite_eq_right h2]
        simp [hyu, hyua]
  · simp only [hxy, ↓reduceIte, mul_zero, Finset.sum_const_zero]
    have h1 : ¬ (x = u + a ∧ y = u) := by rintro ⟨rfl, rfl⟩; exact hxy rfl
    have h2 : ¬ (x = u ∧ y = u + a) := by
      rintro ⟨rfl, rfl⟩; apply hxy; rw [add_assoc, vec_add_self, add_zero]
    simp [h1, h2]

/-- Character sum (E4) for diagonal Pauli operators (`a = 0, c ≠ 0`). -/
theorem sum_diag_pauli {g : ℕ} (t : Vec g) :
    ∑ c ∈ (univ : Finset (Vec g)).erase 0, ((signEven t 0 c : ℝ) : ℂ) • pauli (0, c)
      = ((2 : ℂ) ^ g) • diagProj t - 1 := by
  have hterm : ∀ c : Vec g, ((signEven t 0 c : ℝ) : ℂ) • pauli (0, c) = chi c t • weyl (0, c) :=
    fun c => signEven_smul_pauli t 0 c (by simp [qform])
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  have hfull : ∑ c : Vec g, chi c t • weyl (0, c) = ((2 : ℂ) ^ g) • diagProj t := by
    ext x y
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, weyl, diagProj, add_zero]
    by_cases hxy : x = y
    · subst hxy
      simp only [↓reduceIte, ← chi_add_right, sum_chi_eq]
      have hiff : t + x = 0 ↔ x = t := by
        constructor
        · intro h; calc x = (t + t) + x := by rw [vec_add_self, zero_add]
            _ = t + (t + x) := by abel
            _ = t := by rw [h, add_zero]
        · intro h; rw [h]; exact vec_add_self t
      by_cases hxt : x = t
      · rw [ite_eq_left (hiff.mpr hxt), ite_eq_left ⟨hxt, hxt⟩, mul_one]
      · rw [ite_eq_right (fun h => hxt (hiff.mp h)), ite_eq_right (fun h => hxt h.1), mul_zero]
    · have hnot : ¬ (x = t ∧ y = t) := fun h => hxy (h.1.trans h.2.symm)
      simp [hxy, hnot]
  have h0 : chi (0 : Vec g) t • weyl ((0 : Vec g), (0 : Vec g)) = 1 := by
    rw [chi_zero_left, one_smul]; exact weyl_zero
  have hsplit := Finset.add_sum_erase (univ : Finset (Vec g)) (fun c => chi c t • weyl (0, c)) (mem_univ 0)
  rw [hfull, h0] at hsplit
  exact eq_sub_of_add_eq' hsplit

end GraphSums

end HoggarBound.ConjectureE

/-
Hoggar Bound Lab — Lean 4 formalization of Corollaries 16 and 18 of the unified paper:
* **Corollary 18 (General Cone Lift, Jonah [J3] Lemma D (D2)):**
  For any closed `N`-qubit Pauli configuration `Y` (`0 ∉ Y`), polar point `d`, and sign carrier `σ`,
  the `(N+1)`-qubit cone lift `(X', d', σ')` satisfies:
  - `A_{σ'}` is unitarily equivalent to `(I + 2 A_σ) ⊕ (-I)`,
  - `Λ_{σ'}` is orthogonally equivalent (via the 2×2 Hadamard transform) to `(I + 2 Λ_σ) ⊕ (-I)`,
  - `tr(Λ_{σ'}³) = 8 tr(Λ_σ³) + 12 tr(Λ_σ²) + 6 tr(Λ_σ)`,
  - if `σ, τ` refute the strict law on `(Y, d)`, then `(σ', τ')` refutes the strict law on `(X', d')`,
  - applied to `C3` (`N - 1 ≥ 3`), this gives `C11` for every `N ≥ 4` (`corollary18_c11_from_c3`).
* **Corollary 16 (Four-qubit C3 binary completion minima differ):**
  For the explicit four-qubit C3 pair `(signA, signB)` on the 71-point section of `Q⁺(7,2)` and its
  64-point complement (1,120 outside contexts), proved directly via `lemma20_jordan_action` and exact
  8×8 pure-integer fraction-free `L D Lᵀ` positivity certificates for `111 I - 4 C₀` and `111 I - 4 C₁`:
  - every binary completion of `signA` violates at least **347** outside contexts,
  - every binary completion of `signB` violates at least **315** outside contexts,
  - an explicit binary completion of `signB` violates **exactly 344** outside contexts,
  - hence `min_y F(signB, y) ≤ 344 < 347 ≤ min_y F(signA, y)`.

Zero `sorry`, zero `admit`, zero `native_decide`, zero `set_option`, strictly standard axioms
`[propext, Classical.choice, Quot.sound]`.
-/
import HoggarBound.ConjectureE
import HoggarBound.C3Geometry

open Finset Matrix

namespace HoggarBound.ConjectureE

@[nolint unusedArguments]
private lemma reindex_mul_eq {α β R : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Semiring R] (e : α ≃ β) (A B : Matrix α α R) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Equiv.sum_comp e.symm _).symm

private lemma trace_reindex_eq {α β R : Type*} [Fintype α] [Fintype β] [AddCommMonoid R]
    (e : α ≃ β) (A : Matrix α α R) :
    (Matrix.reindex e e A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

/-! ### Part 1. General Linear-Scale Charpoly Lemma and Corollary 18 (Cone Lift) -/

section ConeLift

/-- Exact characteristic polynomial under affine rescaling `a • 1 + b • M` over any field `K`
with `b ≠ 0`: `(a • 1 + b • M).charpoly = C(b^n) * M.charpoly.comp(C(b⁻¹) * (X - C a))`. -/
theorem charpoly_affine_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (a b : K) (hb : b ≠ 0) (M : Matrix ι ι K) :
    (a • (1 : Matrix ι ι K) + b • M).charpoly
      = Polynomial.C (b ^ Fintype.card ι)
          * M.charpoly.comp (Polynomial.C b⁻¹ * (Polynomial.X - Polynomial.C a)) := by
  let p : Polynomial K := Polynomial.C b⁻¹ * (Polynomial.X - Polynomial.C a)
  let φ : Polynomial K →+* Polynomial K := Polynomial.compRingHom p
  have hcm : (a • (1 : Matrix ι ι K) + b • M).charmatrix
      = Polynomial.C b • (M.charmatrix.map φ) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, φ, Polynomial.coe_compRingHom]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_eq]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, p]
      rw [mul_sub, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hb, Polynomial.C_1, one_mul,
        Polynomial.C_add, Polynomial.C_mul]
      ring
    · rw [Matrix.charmatrix_apply_ne _ _ _ hij, Matrix.charmatrix_apply_ne _ _ _ hij]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_eq_mul,
        mul_zero, zero_add, Polynomial.neg_comp, Polynomial.C_comp, Polynomial.C_mul]
      ring
  have hdet : (M.charmatrix.map φ).det = M.charpoly.comp p := by
    have hm : M.charmatrix.map φ = φ.mapMatrix M.charmatrix := rfl
    rw [hm, ← RingHom.map_det, Matrix.charpoly]
    rfl
  rw [Matrix.charpoly, hcm, Matrix.det_smul, hdet, ← Polynomial.C_pow]

/-- Affine rescaling `1 + 2 • M` preserves and reflects characteristic polynomial equality
over any field of characteristic zero. -/
theorem charpoly_one_add_two_smul_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] [CharZero K] (A B : Matrix ι ι K) :
    (1 + (2 : K) • A).charpoly = (1 + (2 : K) • B).charpoly ↔ A.charpoly = B.charpoly := by
  have h2 : (2 : K) ≠ 0 := by norm_num
  have h1A : (1 : Matrix ι ι K) + (2 : K) • A = (1 : K) • 1 + (2 : K) • A := by simp
  have h1B : (1 : Matrix ι ι K) + (2 : K) • B = (1 : K) • 1 + (2 : K) • B := by simp
  rw [h1A, h1B, charpoly_affine_scale 1 2 h2 A, charpoly_affine_scale 1 2 h2 B]
  constructor
  · intro h
    have hpow : Polynomial.C ((2 : K) ^ Fintype.card ι) ≠ 0 :=
      Polynomial.C_ne_zero.mpr (pow_ne_zero _ h2)
    have hcomp := mul_left_cancel₀ hpow h
    have hback := congrArg (fun q : Polynomial K => q.comp (Polynomial.C (2 : K) * Polynomial.X + 1)) hcomp
    simp only [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.C_comp,
      Polynomial.X_comp] at hback
    have hid : Polynomial.C (2 : K)⁻¹ * (Polynomial.C (2 : K) * Polynomial.X + 1 - Polynomial.C 1)
        = Polynomial.X := by
      rw [Polynomial.C_1, add_sub_cancel_right, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ h2,
        Polynomial.C_1, one_mul]
    simpa only [hid, Polynomial.comp_X] using hback
  · intro h; rw [h]

/-- Cone lift of an `N`-qubit Pauli configuration `Y` to `N + 1` qubits with apex `e = Z₀`. -/
def coneLiftCfg {N : ℕ} (Y : Finset (Pt N)) : Finset (Pt (N + 1)) :=
  insert (ptZ 0) (Y.image (consPt 0 0) ∪ Y.image (consPt 0 1))

/-- Cone-lifted sign carrier: `+1` on `Z₀` and `σ(u)` on both `I ⊗ u` and `Z ⊗ u`. -/
def coneLiftCarrier {N : ℕ} (σ : Pt N → ℝ) : Pt (N + 1) → ℝ :=
  fun s => if tailPt s = 0 then 1 else σ (tailPt s)

lemma coneLiftCarrier_eq_one_or {N : ℕ} {σ : Pt N → ℝ} (hσ : ∀ s, σ s = 1 ∨ σ s = -1) :
    ∀ s : Pt (N + 1), coneLiftCarrier σ s = 1 ∨ coneLiftCarrier σ s = -1 := by
  intro s; unfold coneLiftCarrier; split_ifs
  · left; rfl
  · exact hσ _

lemma lineSign_consPt_Z {N : ℕ} (b₁ b₂ : ZMod 2) (p q : Pt N) :
    lineSign (consPt 0 b₁ p) (consPt 0 b₂ q) = lineSign p q := by
  have hmul : pauli (consPt 0 b₁ p) * pauli (consPt 0 b₂ q)
      = tau (consPt 0 b₁ p) (consPt 0 b₂ q) • pauli (consPt 0 (b₁ + b₂) (p + q)) := by
    have hadd : consPt 0 b₁ p + consPt 0 b₂ q = consPt 0 (b₁ + b₂) (p + q) := by
      rw [consPt_add, add_zero]
    rw [← hadd, pauli_mul]
  have hre := congrArg (Matrix.reindex (splitSum N) (splitSum N)) hmul
  have hre_mul : Matrix.reindex (splitSum N) (splitSum N)
        (pauli (consPt 0 b₁ p) * pauli (consPt 0 b₂ q))
      = Matrix.reindex (splitSum N) (splitSum N) (pauli (consPt 0 b₁ p))
        * Matrix.reindex (splitSum N) (splitSum N) (pauli (consPt 0 b₂ q)) := by
    ext x y
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    exact (Equiv.sum_comp (splitSum N).symm _).symm
  have hre_smul : Matrix.reindex (splitSum N) (splitSum N)
        (tau (consPt 0 b₁ p) (consPt 0 b₂ q) • pauli (consPt 0 (b₁ + b₂) (p + q)))
      = tau (consPt 0 b₁ p) (consPt 0 b₂ q) •
          Matrix.reindex (splitSum N) (splitSum N) (pauli (consPt 0 (b₁ + b₂) (p + q))) := by
    ext x y; simp [Matrix.reindex_apply, Matrix.smul_apply]
  rw [hre_mul, hre_smul, reindex_pauli_cons_Z, reindex_pauli_cons_Z, reindex_pauli_cons_Z,
    fromBlocks_multiply, fromBlocks_smul] at hre
  have htl : pauli p * pauli q = tau (consPt 0 b₁ p) (consPt 0 b₂ q) • pauli (p + q) := by
    ext x y
    have hxy := congrFun (congrFun hre (Sum.inl x)) (Sum.inl y)
    simpa [fromBlocks_apply₁₁] using hxy
  rw [pauli_mul] at htl
  have htr := congrArg (fun M : Matrix (Vec N) (Vec N) ℂ => (M * pauli (p + q)).trace) htl
  simp only [Matrix.smul_mul, pauli_mul_self, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const, Finset.card_univ,
    smul_eq_mul] at htr
  have h2ne : ((2 ^ N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
  have htau : tau p q = tau (consPt 0 b₁ p) (consPt 0 b₂ q) := mul_right_cancel₀ h2ne htr
  unfold lineSign
  rw [htau]

lemma sectionOf_coneLift {N : ℕ} (Y : Finset (Pt N)) (d : Pt N) :
    sectionOf (coneLiftCfg Y) (consPt 0 0 d)
      = insert (ptZ 0) ((sectionOf Y d).image (consPt 0 0) ∪ (sectionOf Y d).image (consPt 0 1)) := by
  ext s
  simp only [sectionOf, coneLiftCfg, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨rfl | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩, hsd⟩
    · left; rfl
    · right; left; refine ⟨u, ⟨hu, ?_⟩, rfl⟩
      simpa [symp_consPt] using hsd
    · right; right; refine ⟨u, ⟨hu, ?_⟩, rfl⟩
      simpa [symp_consPt] using hsd
  · rintro (rfl | ⟨u, ⟨hu, hud⟩, rfl⟩ | ⟨u, ⟨hu, hud⟩, rfl⟩)
    · exact ⟨Or.inl rfl, by rw [symp_comm, symp_ptZ]; rfl⟩
    · exact ⟨Or.inr (Or.inl ⟨u, hu, rfl⟩), by simp [symp_consPt, hud]⟩
    · exact ⟨Or.inr (Or.inr ⟨u, hu, rfl⟩), by simp [symp_consPt, hud]⟩

lemma outsideOf_coneLift {N : ℕ} (Y : Finset (Pt N)) (d : Pt N) :
    outsideOf (coneLiftCfg Y) (consPt 0 0 d)
      = (outsideOf Y d).image (consPt 0 0) ∪ (outsideOf Y d).image (consPt 0 1) := by
  ext s
  simp only [outsideOf, coneLiftCfg, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨rfl | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩, hsd⟩
    · exfalso
      have h0 : symp (ptZ (0 : Fin (N + 1))) (consPt 0 0 d) = 0 := by
        rw [symp_comm, symp_ptZ]; rfl
      rw [h0] at hsd; exact absurd hsd (by decide)
    · left; refine ⟨u, ⟨hu, ?_⟩, rfl⟩; simpa [symp_consPt] using hsd
    · right; refine ⟨u, ⟨hu, ?_⟩, rfl⟩; simpa [symp_consPt] using hsd
  · rintro (⟨u, ⟨hu, hud⟩, rfl⟩ | ⟨u, ⟨hu, hud⟩, rfl⟩)
    · exact ⟨Or.inr (Or.inl ⟨u, hu, rfl⟩), by simp [symp_consPt, hud]⟩
    · exact ⟨Or.inr (Or.inr ⟨u, hu, rfl⟩), by simp [symp_consPt, hud]⟩

/-- Lifted carrier operator splits into `(I + 2 A_σ) ⊕ (-I)` via `splitSum N`. -/
theorem cone_lift_opA_reindex {N : ℕ} (Y : Finset (Pt N)) (h0 : (0 : Pt N) ∉ Y) (d : Pt N)
    (σ : Pt N → ℝ) :
    Matrix.reindex (splitSum N) (splitSum N)
        (opA (sectionOf (coneLiftCfg Y) (consPt 0 0 d)) (coneLiftCarrier σ))
      = fromBlocks (1 + (2 : ℂ) • opA (sectionOf Y d) σ) 0 0 (-1) := by
  have h0H : (0 : Pt N) ∉ sectionOf Y d := fun h => h0 (Finset.mem_filter.mp h).1
  have hσ0 : coneLiftCarrier σ (ptZ 0) = 1 := by
    have ht : tailPt (ptZ (0 : Fin (N + 1))) = 0 := by ext i <;> simp [tailPt, ptZ]
    simp [coneLiftCarrier, ht]
  rw [reindex_opA_Z_split (sectionOf Y d) h0H _ (sectionOf_coneLift Y d) (coneLiftCarrier σ) hσ0]
  congr 1
  · ext x y
    simp only [opA, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu0 : u ≠ 0 := fun h => h0H (h ▸ hu)
    simp only [coneLiftCarrier, tailPt_consPt, hu0, ↓reduceIte]
    push_cast; ring
  · have hz : ∑ u ∈ sectionOf Y d,
        (((coneLiftCarrier σ (consPt 0 0 u) - coneLiftCarrier σ (consPt 0 1 u) : ℝ) : ℂ))
          • pauli u = 0 := by
      refine Finset.sum_eq_zero fun u _ => by simp [coneLiftCarrier]
    rw [hz, add_zero]

/-- **Cone lift carrier spectrum (Corollary 18, carrier part):**
`A_{σ'}` has characteristic polynomial `(1 + 2 A_σ).charpoly * (-1).charpoly`. -/
theorem cone_lift_carrier_charpoly {N : ℕ} (Y : Finset (Pt N)) (h0 : (0 : Pt N) ∉ Y) (d : Pt N)
    (σ : Pt N → ℝ) :
    (opA (sectionOf (coneLiftCfg Y) (consPt 0 0 d)) (coneLiftCarrier σ)).charpoly
      = (1 + (2 : ℂ) • opA (sectionOf Y d) σ).charpoly
        * (-1 : Matrix (Vec N) (Vec N) ℂ).charpoly := by
  rw [← Matrix.charpoly_reindex (splitSum N), cone_lift_opA_reindex Y h0 d σ,
    charpoly_fromBlocks_zero₁₂]

/-- Bijection `{p // p ∈ outsideOf (coneLiftCfg Y) (consPt 0 0 d)} ≃ {p // p ∈ outsideOf Y d} ⊕ {p // p ∈ outsideOf Y d}`. -/
def outsideLiftEquiv {N : ℕ} (Y : Finset (Pt N)) (d : Pt N) :
    {p // p ∈ outsideOf (coneLiftCfg Y) (consPt 0 0 d)}
      ≃ {p // p ∈ outsideOf Y d} ⊕ {p // p ∈ outsideOf Y d} where
  toFun p :=
    let hp : p.1 ∈ (outsideOf Y d).image (consPt 0 0) ∪ (outsideOf Y d).image (consPt 0 1) := by
      rw [← outsideOf_coneLift Y d]; exact p.2
    have htail : tailPt p.1 ∈ outsideOf Y d := by
      rcases Finset.mem_union.mp hp with h | h
      · obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp h
        simpa [← heq] using hu
      · obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp h
        simpa [← heq] using hu
    if p.1.2 0 = 0 then Sum.inl ⟨tailPt p.1, htail⟩ else Sum.inr ⟨tailPt p.1, htail⟩
  invFun
    | Sum.inl p => ⟨consPt 0 0 p.1, by
        rw [outsideOf_coneLift]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ p.2)⟩
    | Sum.inr p => ⟨consPt 0 1 p.1, by
        rw [outsideOf_coneLift]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ p.2)⟩
  left_inv p := by
    have hp : p.1 ∈ (outsideOf Y d).image (consPt 0 0) ∪ (outsideOf Y d).image (consPt 0 1) := by
      rw [← outsideOf_coneLift Y d]; exact p.2
    rcases Finset.mem_union.mp hp with h | h
    · obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
      apply Subtype.ext
      simp [← hu]
    · obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
      apply Subtype.ext
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      simp [← hu, h10]
  right_inv
    | Sum.inl p => by simp
    | Sum.inr p => by
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      simp [h10]

/-- **Cone lift completion block structure (Jonah [J3], Lemma D (D2)):**
In the basis `(I ⊗ p, Z ⊗ p)`, the lifted completion matrix equals
`fromBlocks Λ (Λ + 1) (Λ + 1) Λ`. -/
theorem cone_lift_completion_reindex {N : ℕ} (Y : Finset (Pt N)) (_h0 : (0 : Pt N) ∉ Y) (d : Pt N)
    (σ : Pt N → ℝ) :
    Matrix.reindex (outsideLiftEquiv Y d) (outsideLiftEquiv Y d)
        (completionMat (coneLiftCfg Y) (consPt 0 0 d) (coneLiftCarrier σ))
      = fromBlocks
          (completionMat Y d σ) (completionMat Y d σ + 1)
          (completionMat Y d σ + 1) (completionMat Y d σ) := by
  have hptZ0 : ptZ (0 : Fin (N + 1)) = consPt 0 1 0 := by
    ext i <;> refine Fin.cases (by simp [ptZ, consPt]) (fun j => by simp [ptZ, consPt]) i
  have hsec_mem : ∀ (b : ZMod 2) (u : Pt N),
      consPt 0 b u ∈ sectionOf (coneLiftCfg Y) (consPt 0 0 d) ↔
        (b = 1 ∧ u = 0) ∨ u ∈ sectionOf Y d := by
    intro b u
    rw [sectionOf_coneLift, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (h | ⟨v, hv, heq⟩ | ⟨v, hv, heq⟩)
      · left
        have h1 := congrFun (congrArg Prod.snd h) 0
        have h2 := congrArg tailPt h
        have htz : tailPt (ptZ (0 : Fin (N + 1))) = 0 := by ext i <;> simp [tailPt, ptZ]
        rw [tailPt_consPt, htz] at h2
        simp only [consPt, ptZ, Fin.cons_zero, Pi.single_eq_same] at h1
        exact ⟨h1, h2⟩
      · right; have := congrArg tailPt heq; simp only [tailPt_consPt] at this; rwa [← this]
      · right; have := congrArg tailPt heq; simp only [tailPt_consPt] at this; rwa [← this]
    · rintro (⟨rfl, rfl⟩ | hu)
      · left; exact hptZ0.symm
      · rcases zmod2_cases b with rfl | rfl
        · right; left; exact ⟨u, hu, rfl⟩
        · right; right; exact ⟨u, hu, rfl⟩
  have hentry : ∀ (b₁ b₂ : ZMod 2) (p q : {p // p ∈ outsideOf Y d}),
      completionMat (coneLiftCfg Y) (consPt 0 0 d) (coneLiftCarrier σ)
          ⟨consPt 0 b₁ p.1, by
            rw [outsideOf_coneLift]; rcases zmod2_cases b₁ with rfl | rfl
            · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ p.2)
            · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ p.2)⟩
          ⟨consPt 0 b₂ q.1, by
            rw [outsideOf_coneLift]; rcases zmod2_cases b₂ with rfl | rfl
            · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ q.2)
            · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ q.2)⟩
        = completionMat Y d σ p q + if b₁ ≠ b₂ ∧ p = q then 1 else 0 := by
    intro b₁ b₂ p q
    simp only [completionMat]
    have hadd : consPt 0 b₁ p.1 + consPt 0 b₂ q.1 = consPt 0 (b₁ + b₂) (p.1 + q.1) := by
      rw [consPt_add, add_zero]
    have hsymp : symp (consPt 0 b₁ p.1) (consPt 0 b₂ q.1) = symp p.1 q.1 := by
      simp [symp_consPt]
    have hne_iff : consPt 0 b₁ p.1 ≠ consPt 0 b₂ q.1 ↔ b₁ ≠ b₂ ∨ p.1 ≠ q.1 := by
      rw [ne_eq, ne_eq, ne_eq, ← not_and_or]
      refine not_congr ⟨fun h => ?_, ?_⟩
      · have h1 := congrFun (congrArg Prod.snd h) 0
        have h2 := congrArg tailPt h
        rw [tailPt_consPt, tailPt_consPt] at h2
        simp only [consPt, Fin.cons_zero] at h1
        exact ⟨h1, h2⟩
      · rintro ⟨rfl, hpq⟩; rw [hpq]
    simp only [hadd, hsymp, lineSign_consPt_Z, hne_iff]
    by_cases hpq : p = q
    · subst hpq
      have hne_self : ¬ p.1 ≠ p.1 := not_not.mpr rfl
      have hadd0 : p.1 + p.1 = 0 := pt_add_self p.1
      have hls0 : lineSign (0 : Pt N) p.1 = 1 := by
        unfold lineSign tau chi eps
        simp only [Prod.snd_zero, zero_add, zero_dotProduct, ↓reduceIte, mul_one]
        have hy0 : ycount (0 : Pt N) = 0 := by simp [ycount]
        rw [hy0, zero_add, show ycount p.1 + 3 * ycount p.1 = 4 * ycount p.1 by ring,
          pow_mul, Complex.I_pow_four, one_pow]
        simp
      by_cases hb : b₁ = b₂
      · subst hb; simp [hne_self]
      · have hb1 : b₁ + b₂ = 1 := by
          rcases zmod2_cases b₁ with rfl | rfl <;> rcases zmod2_cases b₂ with rfl | rfl
          · exact absurd rfl hb
          · decide
          · decide
          · exact absurd rfl hb
        simp [hb, hadd0, symp_self, hls0, coneLiftCarrier]
    · have hpq1 : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
      have hadd_ne : p.1 + q.1 ≠ 0 := by
        intro h; apply hpq1
        calc p.1 = p.1 + (q.1 + q.1) := by rw [pt_add_self, add_zero]
          _ = (p.1 + q.1) + q.1 := by abel
          _ = q.1 := by rw [h, zero_add]
      have hht : tailPt (consPt 0 (b₁ + b₂) (p.1 + q.1)) ≠ 0 := by
        rw [tailPt_consPt]; exact hadd_ne
      simp [hpq, hpq1, coneLiftCarrier, hadd_ne]
  ext x y
  rcases x with p | p <;> rcases y with q | q <;>
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, outsideLiftEquiv, Equiv.coe_fn_symm_mk,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.add_apply, Matrix.one_apply]
  · simpa using hentry 0 0 p q
  · have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simpa [h01] using hentry 0 1 p q
  · have h10 : (1 : ZMod 2) ≠ 0 := by decide
    simpa [h10] using hentry 1 0 p q
  · simpa using hentry 1 1 p q

/-- 2×2 Hadamard diagonalization of `fromBlocks Λ (Λ + 1) (Λ + 1) Λ` into
`fromBlocks (1 + 2 • Λ) 0 0 (-1)`. -/
theorem hadamard_diag_cone_block {α : Type*} [Fintype α] [DecidableEq α] (Λ : Matrix α α ℝ) :
    ((1 / 2 : ℝ) • fromBlocks (1 : Matrix α α ℝ) 1 1 (-1))
      * fromBlocks Λ (Λ + 1) (Λ + 1) Λ
      * fromBlocks (1 : Matrix α α ℝ) 1 1 (-1)
      = fromBlocks (1 + (2 : ℝ) • Λ) 0 0 (-1) := by
  rw [Matrix.smul_mul, Matrix.smul_mul, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul]
  congr 1 <;> ext i j <;>
    simp [Matrix.add_apply, Matrix.neg_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul] <;> ring

/-- **Cone lift completion characteristic polynomial (Corollary 18, completion part):**
`Λ_{σ'}` has characteristic polynomial `(1 + 2 Λ_σ).charpoly * (-1).charpoly`. -/
theorem cone_lift_completion_charpoly {N : ℕ} (Y : Finset (Pt N)) (h0 : (0 : Pt N) ∉ Y) (d : Pt N)
    (σ : Pt N → ℝ) :
    (completionMat (coneLiftCfg Y) (consPt 0 0 d) (coneLiftCarrier σ)).charpoly
      = (1 + (2 : ℝ) • completionMat Y d σ).charpoly
        * (-1 : Matrix {p // p ∈ outsideOf Y d} {p // p ∈ outsideOf Y d} ℝ).charpoly := by
  let H₂ : Matrix ({p // p ∈ outsideOf Y d} ⊕ {p // p ∈ outsideOf Y d})
      ({p // p ∈ outsideOf Y d} ⊕ {p // p ∈ outsideOf Y d}) ℝ := fromBlocks 1 1 1 (-1)
  have hHinv : ((1 / 2 : ℝ) • H₂) * H₂ = 1 := by
    dsimp only [H₂]; rw [Matrix.smul_mul, fromBlocks_multiply, fromBlocks_smul, ← fromBlocks_one]
    congr 1 <;> ext i j <;> simp [Matrix.add_apply, Matrix.one_apply] <;> ring
  have hHinvR : H₂ * ((1 / 2 : ℝ) • H₂) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, hHinv]
  rw [← Matrix.charpoly_reindex (outsideLiftEquiv Y d), cone_lift_completion_reindex Y h0 d σ]
  have hconj : (((1 / 2 : ℝ) • H₂) *
        fromBlocks (completionMat Y d σ) (completionMat Y d σ + 1)
          (completionMat Y d σ + 1) (completionMat Y d σ) * H₂).charpoly
      = (fromBlocks (completionMat Y d σ) (completionMat Y d σ + 1)
          (completionMat Y d σ + 1) (completionMat Y d σ)).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hHinvR, one_mul]
  rw [← hconj, hadamard_diag_cone_block, charpoly_fromBlocks_zero₁₂]

/-- **Cone lift cubic trace identity:**
`tr(Λ_{σ'}³) = 8 tr(Λ_σ³) + 12 tr(Λ_σ²) + 6 tr(Λ_σ)`. -/
theorem cone_lift_completion_trace_cube {N : ℕ} (Y : Finset (Pt N)) (h0 : (0 : Pt N) ∉ Y) (d : Pt N)
    (σ : Pt N → ℝ) :
    (completionMat (coneLiftCfg Y) (consPt 0 0 d) (coneLiftCarrier σ) ^ 3).trace
      = 8 * (completionMat Y d σ ^ 3).trace
        + 12 * (completionMat Y d σ ^ 2).trace
        + 6 * (completionMat Y d σ).trace := by
  let Λ := completionMat Y d σ
  let H₂ : Matrix ({p // p ∈ outsideOf Y d} ⊕ {p // p ∈ outsideOf Y d})
      ({p // p ∈ outsideOf Y d} ⊕ {p // p ∈ outsideOf Y d}) ℝ := fromBlocks 1 1 1 (-1)
  have hHinv : ((1 / 2 : ℝ) • H₂) * H₂ = 1 := by
    dsimp only [H₂]; rw [Matrix.smul_mul, fromBlocks_multiply, fromBlocks_smul, ← fromBlocks_one]
    congr 1 <;> ext i j <;> simp [Matrix.add_apply, Matrix.one_apply] <;> ring
  have hHinvR : H₂ * ((1 / 2 : ℝ) • H₂) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, hHinv]
  have hre : (completionMat (coneLiftCfg Y) (consPt 0 0 d) (coneLiftCarrier σ) ^ 3).trace
      = (fromBlocks Λ (Λ + 1) (Λ + 1) Λ ^ 3).trace := by
    have h1 := cone_lift_completion_reindex Y h0 d σ
    have hpow : Matrix.reindex (outsideLiftEquiv Y d) (outsideLiftEquiv Y d)
          (completionMat (coneLiftCfg Y) (consPt 0 0 d) (coneLiftCarrier σ) ^ 3)
        = fromBlocks Λ (Λ + 1) (Λ + 1) Λ ^ 3 := by
      simp only [pow_three, reindex_mul_eq, h1]; rfl
    rw [← hpow, trace_reindex_eq]
  have hconj3 : ((1 / 2 : ℝ) • H₂) * fromBlocks Λ (Λ + 1) (Λ + 1) Λ ^ 3 * H₂
      = fromBlocks ((1 + (2 : ℝ) • Λ) ^ 3) 0 0
          ((-1 : Matrix {p // p ∈ outsideOf Y d} {p // p ∈ outsideOf Y d} ℝ) ^ 3) := by
    have h1 := hadamard_diag_cone_block Λ
    have hpow : (((1 / 2 : ℝ) • H₂) * fromBlocks Λ (Λ + 1) (Λ + 1) Λ * H₂) ^ 3
        = ((1 / 2 : ℝ) • H₂) * fromBlocks Λ (Λ + 1) (Λ + 1) Λ ^ 3 * H₂ := by
      simp only [pow_three, Matrix.mul_assoc]
      have hmid : H₂ * ((1 / 2 : ℝ) • H₂) = 1 := hHinvR
      simp only [← Matrix.mul_assoc H₂ ((1 / 2 : ℝ) • H₂), hmid, one_mul]
    rw [← hpow, h1]
    simp only [pow_three, fromBlocks_multiply, zero_mul, mul_zero, add_zero, zero_add]
  have htr_conj : (fromBlocks Λ (Λ + 1) (Λ + 1) Λ ^ 3).trace
      = (((1 / 2 : ℝ) • H₂) * fromBlocks Λ (Λ + 1) (Λ + 1) Λ ^ 3 * H₂).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hHinvR, one_mul]
  have htr_fb : (fromBlocks ((1 + (2 : ℝ) • Λ) ^ 3) 0 0
        ((-1 : Matrix {p // p ∈ outsideOf Y d} {p // p ∈ outsideOf Y d} ℝ) ^ 3)).trace
      = ((1 + (2 : ℝ) • Λ) ^ 3).trace
        + ((-1 : Matrix {p // p ∈ outsideOf Y d} {p // p ∈ outsideOf Y d} ℝ) ^ 3).trace := by
    simp [Matrix.trace, Matrix.diag_apply]
  rw [hre, htr_conj, hconj3, htr_fb]
  have hexp : (1 + (2 : ℝ) • Λ) ^ 3 = 1 + (6 : ℝ) • Λ + (12 : ℝ) • Λ ^ 2 + (8 : ℝ) • Λ ^ 3 := by
    simp only [pow_three, pow_two, add_mul, mul_add, one_mul, mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ext i j; simp [Matrix.add_apply, Matrix.smul_apply]; ring
  have hneg1 : (-1 : Matrix {p // p ∈ outsideOf Y d} {p // p ∈ outsideOf Y d} ℝ) ^ 3 = -1 := by
    simp [pow_three]
  rw [hexp, hneg1, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_neg]
  simp only [smul_eq_mul]
  ring

/-- **General Cone-Lift Theorem (Jonah [J3], Lemma D (D2)):**
If `(σ, τ)` refutes the strict law on `(Y, d)`, then its cone lift `(coneLiftCarrier σ, coneLiftCarrier τ)`
refutes the strict law on `(coneLiftCfg Y, consPt 0 0 d)`. -/
theorem cone_lift_strict_law_fails {N : ℕ} (Y : Finset (Pt N)) (h0 : (0 : Pt N) ∉ Y) (d : Pt N)
    (σ τ : Pt N → ℝ)
    (hcpA : (opA (sectionOf Y d) σ).charpoly = (opA (sectionOf Y d) τ).charpoly)
    (hcpL : (completionMat Y d σ).charpoly ≠ (completionMat Y d τ).charpoly) :
    (opA (sectionOf (coneLiftCfg Y) (consPt 0 0 d)) (coneLiftCarrier σ)).charpoly
        = (opA (sectionOf (coneLiftCfg Y) (consPt 0 0 d)) (coneLiftCarrier τ)).charpoly ∧
      (completionMat (coneLiftCfg Y) (consPt 0 0 d) (coneLiftCarrier σ)).charpoly
        ≠ (completionMat (coneLiftCfg Y) (consPt 0 0 d) (coneLiftCarrier τ)).charpoly := by
  constructor
  · rw [cone_lift_carrier_charpoly Y h0 d σ, cone_lift_carrier_charpoly Y h0 d τ,
      (charpoly_one_add_two_smul_iff _ _).mpr hcpA]
  · intro heq
    rw [cone_lift_completion_charpoly Y h0 d σ, cone_lift_completion_charpoly Y h0 d τ] at heq
    have hmon : ((-1 : Matrix {p // p ∈ outsideOf Y d} {p // p ∈ outsideOf Y d} ℝ).charpoly).Monic :=
      Matrix.charpoly_monic _
    have hmul := mul_right_cancel₀ hmon.ne_zero heq
    exact hcpL ((charpoly_one_add_two_smul_iff _ _).mp hmul)

/-- **Corollary 18 (case C11 via the cone lift, every `N ≥ 4`):**
Lifting the C3 pairs of `c3_strict_law_fails` (`N - 1 ≥ 3`) via `coneLiftCfg` yields
cospectral ±1 carriers with noncospectral completions on `Q⁺(2N-1,2) ∩ Z₀⊥` (`d = Z₁`). -/
theorem corollary18_c11_from_c3 {g : ℕ} (hg : 2 ≤ g) :
    let e : Pt (g + 2) := ptZ 0
    let d : Pt (g + 2) := ptZ ⟨1, by omega⟩
    let X : Finset (Pt (g + 2)) := perpSet (quadric (g + 2) 0) e
    ∃ σ τ : Pt (g + 2) → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  intro e d X
  obtain ⟨σ, τ, hσ, hτ, hcpA, hcpL⟩ := c3_strict_law_fails hg
  have h0Q : (0 : Pt (g + 1)) ∉ quadric (g + 1) 0 := by simp [quadric]
  have hXeq : X = coneLiftCfg (quadric (g + 1) 0) := by
    have hq0_N : ∀ s : Pt (g + 2), qformShift (0 : Pt (g + 2)) s = qform s := fun s => by
      rw [qformShift, symp_comm, symp_zero_right, add_zero]
    have hq0_m : ∀ u : Pt (g + 1), qformShift (0 : Pt (g + 1)) u = qform u := fun u => by
      rw [qformShift, symp_comm, symp_zero_right, add_zero]
    ext s
    simp only [X, perpSet, quadric, e, hq0_N, hq0_m, coneLiftCfg, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_union, Finset.mem_image, symp_ptZ]
    constructor
    · rintro ⟨⟨hs0, hqs⟩, ha0⟩
      have hqt : qform (tailPt s) = 0 := by
        have h := qform_consPt (s.1 0) (s.2 0) (tailPt s)
        rw [consPt_tailPt, ha0, mul_zero, zero_add] at h
        rwa [← h]
      by_cases ht : tailPt s = 0
      · left
        rcases zmod2_cases (s.2 0) with hc | hc
        · exfalso; apply hs0; rw [← consPt_tailPt s, ha0, hc, ht]; exact consPt_zero
        · rw [← consPt_tailPt s, ha0, hc, ht]
          ext i <;> refine Fin.cases (by simp [ptZ, consPt]) (fun j => by simp [ptZ, consPt]) i
      · right
        rcases zmod2_cases (s.2 0) with hc | hc
        · left; exact ⟨tailPt s, ⟨ht, hqt⟩, consPt_eq_of_eq ha0 hc⟩
        · right; exact ⟨tailPt s, ⟨ht, hqt⟩, consPt_eq_of_eq ha0 hc⟩
    · rintro (rfl | ⟨u, ⟨hu0, hqu⟩, rfl⟩ | ⟨u, ⟨hu0, hqu⟩, rfl⟩)
      · exact ⟨⟨ptZ_ne_zero 0, qform_ptZ 0⟩, rfl⟩
      · exact ⟨⟨fun h => hu0 ((consPt_eq_zero_iff 0 0 u).mp h).2.2, by rw [qform_consPt, hqu]; simp⟩, rfl⟩
      · exact ⟨⟨fun h => hu0 ((consPt_eq_zero_iff 0 1 u).mp h).2.2, by rw [qform_consPt, hqu]; simp⟩, rfl⟩
  have hdeq : d = consPt 0 0 (ptZ 0) := (consPt_zero_ptZ 0).symm
  obtain ⟨hcpA', hcpL'⟩ := cone_lift_strict_law_fails (quadric (g + 1) 0) h0Q (ptZ 0) σ τ hcpA hcpL
  refine ⟨coneLiftCarrier σ, coneLiftCarrier τ, coneLiftCarrier_eq_one_or hσ,
    coneLiftCarrier_eq_one_or hτ, ?_, ?_⟩
  · rwa [hXeq, hdeq]
  · rwa [hXeq, hdeq]

end ConeLift

/-! ### Part 2. Corollary 16 (Four-Qubit C3 Binary Completion Minima Separation: `≤ 344 < 347`) -/

section Corollary16

open HoggarBound.C3

/-- Fast bitwise 4-bit popcount for kernel evaluation. -/
def pop4 (n : ℕ) : ℕ :=
  (n &&& 1) + ((n >>> 1) &&& 1) + ((n >>> 2) &&& 1) + ((n >>> 3) &&& 1)

lemma bitCount4_land_eq_pop4 : ∀ a b : Fin 16, bitCount4 (Nat.land a.val b.val) = pop4 (a.val &&& b.val) := by
  decide +kernel

/-- Fast bitwise section membership predicate on four-qubit codes `< 256`. -/
def isSectionFast (v : ℕ) : Bool :=
  (v != 0) && (pop4 ((v % 16) &&& (v / 16)) % 2 == 0) && !(v.testBit 3)

lemma mem_sectionCodes_iff_fast : ∀ v : Fin 256, v ∈ sectionCodes ↔ isSectionFast v.val = true := by
  decide +kernel

/-- Fast bitwise symplectic form modulo 2 on four-qubit codes `< 256`. -/
def sympFast (u v : ℕ) : ℕ :=
  (pop4 ((u / 16) &&& (v % 16)) + pop4 ((v / 16) &&& (u % 16))) % 2

lemma symp_codePoint_eq_fast (u v : Fin 256) :
    symp (codePoint u) (codePoint v) = 0 ↔ sympFast u.val v.val = 0 := by
  unfold symp codePoint sympFast
  rw [dot_bits, dot_bits, bitCount4_land_eq_pop4, bitCount4_land_eq_pop4, ← Nat.cast_add,
    ZMod.natCast_eq_zero_iff]
  simp only [xCode, zCode, Nat.dvd_iff_mod_eq_zero]

/-- Fast bitwise predicate for an ordered outside-context pair `(i, j)` in the four-qubit C3 geometry. -/
def isC3OutsidePair (i j : Fin 64) : Bool :=
  isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
    (sympFast (outsideLabel i).val (outsideLabel j).val == 0)

lemma isC3OutsidePair_iff (i j : Fin 64) :
    isC3OutsidePair i j = true ↔
      codeAdd (outsideLabel i) (outsideLabel j) ∈ sectionCodes ∧
        symp (codePoint (outsideLabel i)) (codePoint (outsideLabel j)) = 0 := by
  have hlt : Nat.xor (outsideLabel i).val (outsideLabel j).val < 256 :=
    Nat.xor_lt_two_pow (n := 8) (outsideLabel i).isLt (outsideLabel j).isLt
  have haddv : (codeAdd (outsideLabel i) (outsideLabel j)).val
      = (outsideLabel i).val ^^^ (outsideLabel j).val := by
    simp only [codeAdd, Nat.mod_eq_of_lt hlt]; rfl
  simp only [isC3OutsidePair, Bool.and_eq_true, beq_iff_eq,
    mem_sectionCodes_iff_fast, symp_codePoint_eq_fast, haddv]

open Classical in
/-- Number of ordered outside-context pairs violated by section assignment `f` and outside
binary assignment `y : Fin 64 → ℝ`. -/
noncomputable def c3ViolatedOutsidePairs (f : Fin 256 → ℤ) (y : Fin 64 → ℝ) : ℕ :=
  ∑ i : Fin 64, ∑ j : Fin 64,
    if isC3OutsidePair i j = true ∧ y i * (completionOf f i j : ℝ) * y j = -1 then 1 else 0

/-- Number of unordered outside contexts violated by `(f, y)` (each context corresponds to two
ordered pairs `(i, j)` and `(j, i)`). -/
noncomputable def c3ViolatedOutsideContexts (f : Fin 256 → ℤ) (y : Fin 64 → ℝ) : ℕ :=
  c3ViolatedOutsidePairs f y / 2

/-- Top-left 8×8 integer block `C₀` of `carrierA`. -/
def c3BlockA : Matrix (Fin 8) (Fin 8) ℤ := fun i j => carrierA (Fin.castAdd 8 i) (Fin.castAdd 8 j)

/-- Top-left 8×8 integer block `C₁` of `carrierB`. -/
def c3BlockB : Matrix (Fin 8) (Fin 8) ℤ := fun i j => carrierB (Fin.castAdd 8 i) (Fin.castAdd 8 j)

/-- Pure-integer fraction-free `L D Lᵀ` certificate for `111 • I - 4 • C₀`:
`ldltScale0 * (111 • I - 4 • C₀) = ∑ k, ldltW0 k • (col k) (col k)ᵀ`,
with `ldltScale0 > 0`, `ldltW0 k > 0`, `ldltL0` lower-triangular with strictly positive diagonal. -/
def ldltScale0 : ℤ := 77983400744792110830313798577535

/-- Diagonal integer weight vector `W₀` for the first `8 × 8` `LDLᵀ` block certificate. -/
def ldltW0 : Fin 8 → ℤ :=
  ![1163931354399882251198713411605, 207511384275250891638208845,
    43478810606470911182565, 595293135456428326948960294485,
    27169167556720504285, 194840750440219623869,
    4075866812255516685, 8170165545041533924775792916217341]

/-- Lower-triangular integer factor `L₀` for the first `8 × 8` `LDLᵀ` block certificate. -/
def ldltL0 : Matrix (Fin 8) (Fin 8) ℤ := !![
  67, 0, 0, 0, 0, 0, 0, 0;
  -32, 5609, 0, 0, 0, 0, 0, 0;
  -32, -3168, 319771, 0, 0, 0, 0, 0;
  0, 0, 0, 131, 0, 0, 0, 0;
  -32, -3168, -325264, -16, 8976081, 0, 0, 0;
  0, 0, -89744, 16, -4579328, 5841265, 0, 0;
  -16, -1584, -117760, 0, -13542400, -1884160, 12376823, 0;
  16, -560, 16384, 0, 1884160, 262144, 19570688, 1
]

/-- Pure-integer fraction-free `L D Lᵀ` certificate for `111 • I - 4 • C₁`. -/
def ldltScale1 : ℤ := 294700838952328035

/-- Diagonal integer weight vector `W₁` for the second `8 × 8` `LDLᵀ` block certificate. -/
def ldltW1 : Fin 8 → ℤ :=
  ![4398519984363105, 784189692345, 128299841, 33890596479517724025,
    1127409, 2949225788301841225, 33890596479517724025, 33890596479517724025]

/-- Lower-triangular integer factor `L₁` for the second `8 × 8` `LDLᵀ` block certificate. -/
def ldltL1 : Matrix (Fin 8) (Fin 8) ℤ := !![
  67, 0, 0, 0, 0, 0, 0, 0;
  -32, 5609, 0, 0, 0, 0, 0, 0;
  -32, -3168, 409515, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0, 0;
  -32, -3168, -415008, 0, 1914923, 0, 0, 0;
  0, 0, -179488, 0, -4426752, 1, 0, 0;
  0, 0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 1
]

/-- Explicit 64-point binary witness for `signB` attaining 344 violated outside contexts
(negative on the 30 outside codes of Appendix B / `scripts/cospectral_pair.py`). -/
def c3WitnessNegCodes : Finset (Fin 256) :=
  {26, 41, 59, 63, 72, 88, 90, 104, 105, 120, 123, 153, 155, 159, 170, 171, 175,
   204, 205, 206, 217, 219, 220, 222, 234, 235, 236, 237, 252, 255}

/-- Integer `±1` binary completion witness on the 64 outside points for `signB` (attaining `344`). -/
def c3WitnessInt (i : Fin 64) : ℤ :=
  if outsideLabel i ∈ c3WitnessNegCodes then -1 else 1

/-- Fast bitwise integer context sign on four-qubit codes `< 256`. -/
def lineSignFast (u v : ℕ) : ℤ :=
  iPowerReal (pop4 ((u % 16) &&& (u / 16)) + pop4 ((v % 16) &&& (v / 16))
      + 3 * pop4 (((u ^^^ v) % 16) &&& ((u ^^^ v) / 16))) *
    (if pop4 ((u / 16) &&& (v % 16)) % 2 == 0 then 1 else -1)

lemma integerLineSign_codePoint_eq_fast (u v : Fin 256) :
    integerLineSign (codePoint u) (codePoint v) = lineSignFast u.val v.val := by
  have hlt : Nat.xor u.val v.val < 256 := Nat.xor_lt_two_pow (n := 8) u.isLt v.isLt
  have haddv : (codeAdd u v).val = u.val ^^^ v.val := by
    simp only [codeAdd, Nat.mod_eq_of_lt hlt]; rfl
  unfold integerLineSign lineSignFast
  rw [← codePoint_add, ycount_code, ycount_code, ycount_code,
    bitCount4_land_eq_pop4, bitCount4_land_eq_pop4, bitCount4_land_eq_pop4]
  simp only [xCode, zCode, haddv]
  congr 1
  have hdot : (codePoint u).2 ⬝ᵥ (codePoint v).1 = 0 ↔ pop4 ((u.val / 16) &&& (v.val % 16)) % 2 = 0 := by
    simp only [codePoint, dot_bits, bitCount4_land_eq_pop4, ZMod.natCast_eq_zero_iff,
      Nat.dvd_iff_mod_eq_zero]
    rfl
  by_cases h : pop4 ((u.val / 16) &&& (v.val % 16)) % 2 = 0
  · rw [ite_eq_left (hdot.mpr h)]; simp [h]
  · rw [ite_eq_right (fun h' => h (hdot.mp h'))]; simp [h]

/-- Fast bitwise `signB` evaluator on four-qubit codes `< 256`. -/
def signBFast (w : ℕ) : ℤ :=
  if w == 87 || w == 144 || w == 176 || w == 215 then -1 else 1

lemma signB_eq_fast : ∀ w : Fin 256, signB w = signBFast w.val := by
  decide +kernel

/-- Explicit list of the 64 outside codes (matching `outsideLabel`). -/
def outNatArr : List ℕ :=
  [8, 9, 10, 11, 12, 13, 14, 15, 24, 26, 28, 30, 40, 41, 44, 45,
   56, 59, 60, 63, 72, 73, 74, 75, 88, 90, 93, 95, 104, 105, 110, 111,
   120, 123, 125, 126, 153, 155, 157, 159, 170, 171, 174, 175, 185, 186, 189, 190,
   204, 205, 206, 207, 217, 219, 220, 222, 234, 235, 236, 237, 249, 250, 252, 255]

lemma map_outsideLabel_val : (List.finRange 64).map (fun i => (outsideLabel i).val) = outNatArr := by
  decide +kernel

/-- Explicit 64-entry list of `(outsideCode, witnessSign)` pairs for `c3WitnessInt`. -/
def outWithSign : List (ℕ × ℤ) :=
  [(8, 1), (9, 1), (10, 1), (11, 1), (12, 1), (13, 1), (14, 1), (15, 1),
   (24, 1), (26, -1), (28, 1), (30, 1), (40, 1), (41, -1), (44, 1), (45, 1),
   (56, 1), (59, -1), (60, 1), (63, -1), (72, -1), (73, 1), (74, 1), (75, 1),
   (88, -1), (90, -1), (93, 1), (95, 1), (104, -1), (105, -1), (110, 1), (111, 1),
   (120, -1), (123, -1), (125, 1), (126, 1), (153, -1), (155, -1), (157, 1), (159, -1),
   (170, -1), (171, -1), (174, 1), (175, -1), (185, 1), (186, 1), (189, 1), (190, 1),
   (204, -1), (205, -1), (206, -1), (207, 1), (217, -1), (219, -1), (220, -1), (222, -1),
   (234, -1), (235, -1), (236, -1), (237, -1), (249, 1), (250, 1), (252, -1), (255, -1)]

lemma map_outsideLabel_witness :
    (List.finRange 64).map (fun i => ((outsideLabel i).val, c3WitnessInt i)) = outWithSign := by
  decide +kernel

/-- Real-valued cast of `c3WitnessInt` attaining `344` violated outside contexts for `signB`. -/
def c3WitnessReal (i : Fin 64) : ℝ := (c3WitnessInt i : ℝ)

lemma c3WitnessReal_values (i : Fin 64) : c3WitnessReal i = 1 ∨ c3WitnessReal i = -1 := by
  unfold c3WitnessReal c3WitnessInt; split_ifs <;> simp

private lemma lineSign_eq_one_or_neg_one {N : ℕ} {u v : Pt N} (h : symp u v = 0) :
    lineSign u v = 1 ∨ lineSign u v = -1 := by
  unfold lineSign
  rcases tau_eq_one_or_neg_one h with ht | ht <;> simp [ht]

lemma isC3OutsidePair_sum :
    (∑ i : Fin 64, ∑ j : Fin 64, if isC3OutsidePair i j = true then (1 : ℕ) else 0) = 2240 := by
  have hfast : (outNatArr.map fun u =>
      (outNatArr.map fun v =>
        if isSectionFast (u ^^^ v) && (sympFast u v == 0) then (1 : ℕ) else 0).sum).sum = 2240 := by
    decide +kernel
  have hpt : ∀ i j : Fin 64,
      (if isC3OutsidePair i j = true then (1 : ℕ) else 0) =
        if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
            (sympFast (outsideLabel i).val (outsideLabel j).val == 0) then (1 : ℕ) else 0 :=
    fun _ _ => rfl
  simp_rw [hpt]
  have hlist : (∑ i : Fin 64, ∑ j : Fin 64,
        if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
            (sympFast (outsideLabel i).val (outsideLabel j).val == 0) then (1 : ℕ) else 0)
      = (outNatArr.map fun u =>
          (outNatArr.map fun v =>
            if isSectionFast (u ^^^ v) && (sympFast u v == 0) then (1 : ℕ) else 0).sum).sum := by
    simp only [Fin.sum_univ_def]
    have hinner : ∀ u : ℕ,
        ((List.finRange 64).map fun j =>
          if isSectionFast (u ^^^ (outsideLabel j).val) &&
              (sympFast u (outsideLabel j).val == 0) then (1 : ℕ) else 0).sum
        = (outNatArr.map fun v =>
            if isSectionFast (u ^^^ v) && (sympFast u v == 0) then (1 : ℕ) else 0).sum := by
      intro u
      rw [← map_outsideLabel_val, List.map_map]; rfl
    have houter : ((List.finRange 64).map fun i =>
          ((List.finRange 64).map fun j =>
            if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
                (sympFast (outsideLabel i).val (outsideLabel j).val == 0) then (1 : ℕ) else 0).sum)
        = outNatArr.map fun u =>
            (outNatArr.map fun v =>
              if isSectionFast (u ^^^ v) && (sympFast u v == 0) then (1 : ℕ) else 0).sum := by
      rw [← map_outsideLabel_val, List.map_map]
      refine List.map_congr_left fun i _ => ?_
      dsimp only [Function.comp_apply]
      exact hinner (outsideLabel i).val
    rw [houter]
  rw [hlist, hfast]

lemma isC3OutsidePair_symm {i j : Fin 64} (h : isC3OutsidePair i j = true) :
    isC3OutsidePair j i = true := by
  rw [isC3OutsidePair_iff] at h ⊢
  have hadd : codeAdd (outsideLabel j) (outsideLabel i) = codeAdd (outsideLabel i) (outsideLabel j) := by
    apply Fin.ext; simp [codeAdd, Nat.xor_comm]
  rw [hadd, symp_comm]
  exact h

lemma isC3OutsidePair_irrefl (i : Fin 64) : isC3OutsidePair i i ≠ true := by
  intro h
  rw [isC3OutsidePair_iff] at h
  have hadd : codeAdd (outsideLabel i) (outsideLabel i) = 0 := by
    apply Fin.ext; simp [codeAdd]
  rw [hadd] at h
  have h0 : (0 : Fin 256) ∉ sectionCodes := by decide +kernel
  exact h0 h.1

lemma completionOf_symm (f : Fin 256 → ℤ) (i j : Fin 64) :
    completionOf f i j = completionOf f j i := by
  dsimp only [completionOf]
  have hadd : codeAdd (outsideLabel j) (outsideLabel i) = codeAdd (outsideLabel i) (outsideLabel j) := by
    apply Fin.ext; simp [codeAdd, Nat.xor_comm]
  rw [hadd, symp_comm (codePoint (outsideLabel j))]
  split_ifs with h
  · congr 1
    have h1 := lineSign_eq_integer (codePoint (outsideLabel i)) (codePoint (outsideLabel j))
    have h2 := lineSign_eq_integer (codePoint (outsideLabel j)) (codePoint (outsideLabel i))
    have hcomm : lineSign (codePoint (outsideLabel i)) (codePoint (outsideLabel j))
        = lineSign (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) := by
      unfold lineSign; rw [tau_swap, symp_comm, h.2]; simp
    have hreal : (integerLineSign (codePoint (outsideLabel i)) (codePoint (outsideLabel j)) : ℝ)
        = (integerLineSign (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) : ℝ) := by
      rw [← h1, ← h2, hcomm]
    exact_mod_cast hreal
  · rfl

open Classical in
lemma c3ViolatedOutsidePairs_even (f : Fin 256 → ℤ) (y : Fin 64 → ℝ) :
    Even (c3ViolatedOutsidePairs f y) := by
  unfold c3ViolatedOutsidePairs
  let g : Fin 64 → Fin 64 → ℕ := fun i j =>
    if isC3OutsidePair i j = true ∧ y i * (completionOf f i j : ℝ) * y j = -1 then 1 else 0
  have hsymm : ∀ i j : Fin 64, g i j = g j i := by
    intro i j
    dsimp only [g]
    have hiff : (isC3OutsidePair i j = true ∧ y i * (completionOf f i j : ℝ) * y j = -1) ↔
        (isC3OutsidePair j i = true ∧ y j * (completionOf f j i : ℝ) * y i = -1) := by
      constructor <;> rintro ⟨hp, hv⟩ <;> refine ⟨isC3OutsidePair_symm hp, ?_⟩ <;>
        rw [completionOf_symm] <;> linarith
    by_cases h : isC3OutsidePair i j = true ∧ y i * (completionOf f i j : ℝ) * y j = -1
    · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]
  have hdiag : ∀ i : Fin 64, g i i = 0 := fun i => by
    dsimp only [g]; rw [ite_eq_right]; exact fun h => isC3OutsidePair_irrefl i h.1
  have hsplit : ∀ i j : Fin 64,
      g i j = (if i < j then g i j else 0) + (if j < i then g i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · simp [hlt, not_lt.mpr (le_of_lt hlt)]
    · simp [hdiag i]
    · simp [hgt, not_lt.mpr (le_of_lt hgt)]
  have htotal : (∑ i : Fin 64, ∑ j : Fin 64, g i j)
      = (∑ i : Fin 64, ∑ j : Fin 64, if i < j then g i j else 0)
        + (∑ i : Fin 64, ∑ j : Fin 64, if j < i then g i j else 0) := by
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
  have hswap : (∑ i : Fin 64, ∑ j : Fin 64, if j < i then g i j else 0)
      = ∑ i : Fin 64, ∑ j : Fin 64, if i < j then g i j else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsymm j i]
  change Even (∑ i : Fin 64, ∑ j : Fin 64, g i j)
  rw [htotal, hswap]
  exact ⟨_, rfl⟩

open Classical in
/-- Exact quadratic-form identity:
`∑_{i,j} y_i (completionOf f)_{ij} y_j = 2240 - 4 * c3ViolatedOutsideContexts f y`. -/
theorem c3_quadForm_eq (f : Fin 256 → ℤ) (hf : ∀ v, f v = 1 ∨ f v = -1)
    (y : Fin 64 → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) :
    (∑ i : Fin 64, ∑ j : Fin 64, y i * (completionOf f i j : ℝ) * y j)
      = 2240 - 4 * (c3ViolatedOutsideContexts f y : ℝ) := by
  have hpt : ∀ i j : Fin 64,
      y i * (completionOf f i j : ℝ) * y j
        = (if isC3OutsidePair i j = true then (1 : ℝ) else 0)
          - 2 * (if isC3OutsidePair i j = true ∧ y i * (completionOf f i j : ℝ) * y j = -1
                 then (1 : ℝ) else 0) := by
    intro i j
    by_cases hp : isC3OutsidePair i j = true
    · obtain ⟨hsec, hcomm⟩ := (isC3OutsidePair_iff i j).mp hp
      have hcomp : (completionOf f i j : ℝ) = (f (codeAdd (outsideLabel i) (outsideLabel j)) : ℝ)
          * lineSign (codePoint (outsideLabel i)) (codePoint (outsideLabel j)) := by
        unfold completionOf
        rw [ite_eq_left ⟨hsec, hcomm⟩, Int.cast_mul, ← lineSign_eq_integer]
      have hls : lineSign (codePoint (outsideLabel i)) (codePoint (outsideLabel j)) = 1 ∨
          lineSign (codePoint (outsideLabel i)) (codePoint (outsideLabel j)) = -1 :=
        lineSign_eq_one_or_neg_one hcomm
      have hpm : y i * (completionOf f i j : ℝ) * y j = 1 ∨
          y i * (completionOf f i j : ℝ) * y j = -1 := by
        rw [hcomp]
        rcases hy i with hi | hi <;> rcases hy j with hj | hj <;>
          rcases hf (codeAdd (outsideLabel i) (outsideLabel j)) with hf' | hf' <;>
          rcases hls with hl | hl <;> simp [hi, hj, hf', hl]
      rcases hpm with h1 | hneg1
      · simp [hp, h1]; norm_num
      · simp [hp, hneg1]; ring
    · have h0 : completionOf f i j = 0 := by
        unfold completionOf
        rw [ite_eq_right]
        intro h; exact hp ((isC3OutsidePair_iff i j).mpr h)
      simp [hp, h0]
  have hsum : (∑ i : Fin 64, ∑ j : Fin 64, y i * (completionOf f i j : ℝ) * y j)
      = ((∑ i : Fin 64, ∑ j : Fin 64, if isC3OutsidePair i j = true then (1 : ℕ) else 0 : ℕ) : ℝ)
        - 2 * (c3ViolatedOutsidePairs f y : ℝ) := by
    have h1 : (∑ i : Fin 64, ∑ j : Fin 64, y i * (completionOf f i j : ℝ) * y j)
        = ∑ i : Fin 64, ∑ j : Fin 64,
            ((if isC3OutsidePair i j = true then (1 : ℝ) else 0)
            - 2 * (if isC3OutsidePair i j = true ∧ y i * (completionOf f i j : ℝ) * y j = -1
                   then (1 : ℝ) else 0)) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
    rw [h1]
    simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    unfold c3ViolatedOutsidePairs
    congr 1
    · rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    · congr 1
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  have heven := c3ViolatedOutsidePairs_even f y
  have h2 : 2 * c3ViolatedOutsideContexts f y = c3ViolatedOutsidePairs f y := by
    obtain ⟨k, hk⟩ := heven
    unfold c3ViolatedOutsideContexts; omega
  rw [hsum, isC3OutsidePair_sum, ← h2]
  push_cast; ring

/-- General strict positive-definiteness lemma from a pure-integer fraction-free `L D Lᵀ`
certificate for `scale * (111 • I - 4 • C)`. -/
theorem pos_def_of_int_ldlt (C : Matrix (Fin 8) (Fin 8) ℤ)
    (scale : ℤ) (L : Matrix (Fin 8) (Fin 8) ℤ) (W : Fin 8 → ℤ)
    (hscale : 0 < scale)
    (hL_lo : ∀ i j : Fin 8, i < j → L i j = 0)
    (hL_diag : ∀ i : Fin 8, 0 < L i i)
    (hW_pos : ∀ k : Fin 8, 0 < W k)
    (hfac : ∀ i j : Fin 8,
      scale * ((if i = j then (111 : ℤ) else 0) - 4 * C i j) = ∑ k : Fin 8, W k * L i k * L j k)
    (v : Fin 8 → ℂ) (hv : v ≠ 0) :
    4 * (∑ i : Fin 8, ∑ j : Fin 8, star (v i) * (C i j : ℂ) * v j).re
      < 111 * (∑ i : Fin 8, (star (v i) * v i).re) := by
  let w : Fin 8 → ℂ := fun k => ∑ i : Fin 8, (L i k : ℂ) * v i
  have hform : (scale : ℝ) * (111 * (∑ i : Fin 8, (star (v i) * v i).re)
      - 4 * (∑ i : Fin 8, ∑ j : Fin 8, star (v i) * (C i j : ℂ) * v j).re)
      = ∑ k : Fin 8, (W k : ℝ) * ((w k).re ^ 2 + (w k).im ^ 2) := by
    have hcomplex : (scale : ℂ) * ((111 : ℂ) * (∑ i : Fin 8, star (v i) * v i)
        - 4 * (∑ i : Fin 8, ∑ j : Fin 8, star (v i) * (C i j : ℂ) * v j))
        = ∑ k : Fin 8, (W k : ℂ) * (star (w k) * w k) := by
      have hlhs : (scale : ℂ) * ((111 : ℂ) * (∑ i : Fin 8, star (v i) * v i)
          - 4 * (∑ i : Fin 8, ∑ j : Fin 8, star (v i) * (C i j : ℂ) * v j))
          = ∑ i : Fin 8, ∑ j : Fin 8,
              star (v i) * ((scale * ((if i = j then (111 : ℤ) else 0) - 4 * C i j) : ℤ) : ℂ) * v j := by
        have h1 : (111 : ℂ) * (∑ i : Fin 8, star (v i) * v i)
            = ∑ i : Fin 8, ∑ j : Fin 8, star (v i) * (if i = j then (111 : ℂ) else 0) * v j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single i]
          · simp; ring
          · intro j _ hji; simp [Ne.symm hji]
          · intro hi; exact absurd (mem_univ i) hi
        rw [h1, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hij : i = j <;> simp [hij] <;> ring
      rw [hlhs]
      simp_rw [hfac, Int.cast_sum, Int.cast_mul]
      have hswap : (∑ i : Fin 8, ∑ j : Fin 8,
            star (v i) * (∑ k : Fin 8, (W k : ℂ) * (L i k : ℂ) * (L j k : ℂ)) * v j)
          = ∑ k : Fin 8, (W k : ℂ) *
              ((∑ i : Fin 8, (L i k : ℂ) * star (v i)) * (∑ j : Fin 8, (L j k : ℂ) * v j)) := by
        calc (∑ i : Fin 8, ∑ j : Fin 8,
              star (v i) * (∑ k : Fin 8, (W k : ℂ) * (L i k : ℂ) * (L j k : ℂ)) * v j)
            = ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
                (W k : ℂ) * (((L i k : ℂ) * star (v i)) * ((L j k : ℂ) * v j)) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun k _ => by ring
          _ = ∑ i : Fin 8, ∑ k : Fin 8, ∑ j : Fin 8,
                (W k : ℂ) * (((L i k : ℂ) * star (v i)) * ((L j k : ℂ) * v j)) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ k : Fin 8, ∑ i : Fin 8, ∑ j : Fin 8,
                (W k : ℂ) * (((L i k : ℂ) * star (v i)) * ((L j k : ℂ) * v j)) := Finset.sum_comm
          _ = ∑ k : Fin 8, (W k : ℂ) *
                ((∑ i : Fin 8, (L i k : ℂ) * star (v i)) * (∑ j : Fin 8, (L j k : ℂ) * v j)) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              simp_rw [← Finset.mul_sum]
              congr 1
              rw [Finset.sum_mul]
      rw [hswap]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hstar : star (w k) = ∑ i : Fin 8, (L i k : ℂ) * star (v i) := by
        simp only [w, star_sum, star_mul', Complex.star_def, map_intCast]
      rw [hstar]
    have hre := congrArg Complex.re hcomplex
    have hscaleC : (scale : ℂ) = ((scale : ℝ) : ℂ) := by push_cast; rfl
    have h111C : (111 : ℂ) = ((111 : ℝ) : ℂ) := by norm_num
    have h4C : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_num
    rw [hscaleC, h111C, h4C, Complex.re_ofReal_mul, Complex.sub_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hre
    rw [← Complex.re_sum, hre, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hWkC : (W k : ℂ) = ((W k : ℝ) : ℂ) := by push_cast; rfl
    rw [hWkC, Complex.re_ofReal_mul]
    congr 1
    simp [Complex.mul_re, sq]
  have hne : w ≠ 0 := by
    intro hw0
    apply hv
    have hback : ∀ m : ℕ, ∀ i : Fin 8, 7 - i.val < m → v i = 0 := by
      intro m
      induction m with
      | zero => intro i hi; omega
      | succ m ih =>
        intro i hi
        have hwi : w i = 0 := congrFun hw0 i
        have hsum : w i = (L i i : ℂ) * v i + ∑ j ∈ univ.erase i, (L j i : ℂ) * v j := by
          dsimp only [w]
          rw [← Finset.add_sum_erase _ _ (mem_univ i)]
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
    funext i
    exact hback 8 i (by omega)
  have hex : ∃ k : Fin 8, w k ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  obtain ⟨k₀, hk₀⟩ := hex
  have hpos : 0 < ∑ k : Fin 8, (W k : ℝ) * ((w k).re ^ 2 + (w k).im ^ 2) := by
    refine Finset.sum_pos' (fun k _ => ?_) ⟨k₀, mem_univ k₀, ?_⟩
    · have hWk : (0 : ℝ) < (W k : ℝ) := by exact_mod_cast hW_pos k
      positivity
    · have hWk : (0 : ℝ) < (W k₀ : ℝ) := by exact_mod_cast hW_pos k₀
      have hnorm : 0 < (w k₀).re ^ 2 + (w k₀).im ^ 2 := by
        by_contra hle
        push Not at hle
        have hre0 : (w k₀).re = 0 := by nlinarith [sq_nonneg (w k₀).re, sq_nonneg (w k₀).im]
        have him0 : (w k₀).im = 0 := by nlinarith [sq_nonneg (w k₀).re, sq_nonneg (w k₀).im]
        exact hk₀ (Complex.ext hre0 him0)
      exact mul_pos hWk hnorm
  have hsc : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hscale
  have hdiff_pos : 0 < 111 * (∑ i : Fin 8, (star (v i) * v i).re)
      - 4 * (∑ i : Fin 8, ∑ j : Fin 8, star (v i) * (C i j : ℂ) * v j).re := by
    nlinarith
  linarith

lemma ldlt0_valid :
    0 < ldltScale0 ∧
    (∀ i j : Fin 8, i < j → ldltL0 i j = 0) ∧
    (∀ i : Fin 8, 0 < ldltL0 i i) ∧
    (∀ k : Fin 8, 0 < ldltW0 k) ∧
    (∀ i j : Fin 8,
      ldltScale0 * ((if i = j then (111 : ℤ) else 0) - 4 * c3BlockA i j)
        = ∑ k : Fin 8, ldltW0 k * ldltL0 i k * ldltL0 j k) := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [ldltL0]

lemma ldlt1_valid :
    0 < ldltScale1 ∧
    (∀ i j : Fin 8, i < j → ldltL1 i j = 0) ∧
    (∀ i : Fin 8, 0 < ldltL1 i i) ∧
    (∀ k : Fin 8, 0 < ldltW1 k) ∧
    (∀ i j : Fin 8,
      ldltScale1 * ((if i = j then (111 : ℤ) else 0) - 4 * c3BlockB i j)
        = ∑ k : Fin 8, ldltW1 k * ldltL1 i k * ldltL1 j k) := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [ldltL1]

/-- Splitting `Fin 16 ≃ Fin 8 ⊕ Fin 8` (`0..7` vs `8..15`). -/
def fin16Split : Fin 16 ≃ Fin 8 ⊕ Fin 8 where
  toFun i := if h : i.val < 8 then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - 8, by omega⟩
  invFun
    | Sum.inl i => Fin.castAdd 8 i
    | Sum.inr i => Fin.natAdd 8 i
  left_inv i := by
    by_cases h : i.val < 8
    · simp [h]
    · simp [h, Fin.ext_iff]; omega
  right_inv
    | Sum.inl i => by simp [i.isLt]
    | Sum.inr i => by simp

/-- When `u` and `v` commute, `lineSign (u + v) v = lineSign u v`. -/
private lemma lineSign_add_right_of_comm {N : ℕ} (u v : Pt N) (hcomm : symp u v = 0) :
    lineSign (u + v) v = lineSign u v := by
  have h1 : pauli (u + v) * pauli v = (lineSign (u + v) v : ℂ) • pauli u := by
    rw [pauli_mul, add_assoc, pt_add_self, add_zero,
      tau_eq_lineSign (by rw [symp_add_self_right, hcomm])]
  have h2 : pauli u * pauli v = (lineSign u v : ℂ) • pauli (u + v) := by
    rw [pauli_mul, tau_eq_lineSign hcomm]
  have h3 : ((lineSign u v * lineSign (u + v) v : ℝ) : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ) = 1 := by
    calc ((lineSign u v * lineSign (u + v) v : ℝ) : ℂ) • (1 : Matrix (Vec N) (Vec N) ℂ)
        = (lineSign u v : ℂ) • (((lineSign (u + v) v : ℂ) • pauli u) * pauli u) := by
            rw [Matrix.smul_mul, pauli_mul_self, smul_smul]; push_cast; rfl
      _ = (lineSign u v : ℂ) • ((pauli (u + v) * pauli v) * pauli u) := by rw [h1]
      _ = (((lineSign u v : ℂ) • pauli (u + v)) * pauli v) * pauli u := by
            rw [Matrix.smul_mul, Matrix.smul_mul]
      _ = ((pauli u * pauli v) * pauli v) * pauli u := by rw [h2]
      _ = 1 := by rw [Matrix.mul_assoc (pauli u), pauli_mul_self, mul_one, pauli_mul_self]
  have h4 := congrFun (congrFun h3 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h4
  have hprod : lineSign u v * lineSign (u + v) v = 1 := by exact_mod_cast h4
  have hsq : lineSign u v * lineSign u v = 1 := by
    rcases lineSign_eq_one_or_neg_one hcomm with h | h <;> simp [h]
  calc lineSign (u + v) v
      = (lineSign u v * lineSign u v) * lineSign (u + v) v := by rw [hsq, one_mul]
    _ = lineSign u v * (lineSign u v * lineSign (u + v) v) := by ring
    _ = lineSign u v := by rw [hprod, mul_one]

/-- Outside Pauli linear combination `T = ∑ i, y_i P_{o_i}` in the `Fin 16` basis. -/
noncomputable def c3OpT16 (y : Fin 64 → ℝ) : Matrix (Fin 16) (Fin 16) ℂ :=
  ∑ i : Fin 64, (y i : ℂ) • (realPauliCode (outsideLabel i)).map (Int.castRingHom ℂ)

/-- Section carrier operator `A_f` in the `Fin 16` basis. -/
noncomputable def c3OpA16 (f : Fin 256 → ℤ) : Matrix (Fin 16) (Fin 16) ℂ :=
  (carrierOf f).map (Int.castRingHom ℂ)

private lemma c3OpT16_eq_reindex (y : Fin 64 → ℝ) :
    c3OpT16 y = Matrix.reindex (Equiv.ofBijective bits bits_bijective).symm
        (Equiv.ofBijective bits bits_bijective).symm
        (∑ i : Fin 64, (y i : ℂ) • pauli (codePoint (outsideLabel i))) := by
  have hout_even : ∀ i : Fin 64,
      bitCount4 (Nat.land (xCode (outsideLabel i)).val (zCode (outsideLabel i)).val) % 2 = 0 := by
    intro i
    have hmem : outsideLabel i ∈ outsideCodes := by
      rw [← outside_labels_complete]; exact Finset.mem_image_of_mem _ (mem_univ i)
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2.2
  ext a b
  simp only [c3OpT16, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
    Int.coe_castRingHom, smul_eq_mul, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [realPauliCode_cast (outsideLabel i) (hout_even i)]
  rfl

private lemma c3OpA16_eq_reindex (f : Fin 256 → ℤ) :
    c3OpA16 f = Matrix.reindex (Equiv.ofBijective bits bits_bijective).symm
        (Equiv.ofBijective bits bits_bijective).symm
        (∑ v ∈ sectionCodes, (f v : ℂ) • pauli (codePoint v)) := by
  have hsec_even : ∀ v ∈ sectionCodes,
      bitCount4 (Nat.land (xCode v).val (zCode v).val) % 2 = 0 := fun v hv =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.2
  ext a b
  simp only [c3OpA16, carrierOf, Matrix.map_apply, Int.coe_castRingHom, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [realPauliCode_cast v (hsec_even v hv)]
  rfl

private lemma c3_trace_T16_sq (y : Fin 64 → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) :
    (c3OpT16 y * c3OpT16 y).trace = 1024 := by
  rw [c3OpT16_eq_reindex, ← reindex_mul_eq, trace_reindex_eq]
  rw [Finset.sum_mul, Matrix.trace_sum]
  have hinner : ∀ i : Fin 64,
      (((y i : ℂ) • pauli (codePoint (outsideLabel i))) *
        ∑ j : Fin 64, (y j : ℂ) • pauli (codePoint (outsideLabel j))).trace = 16 := by
    intro i
    rw [Finset.mul_sum, Matrix.trace_sum, Finset.sum_eq_single i]
    · rw [Matrix.smul_mul, Matrix.mul_smul, pauli_mul_self, Matrix.trace_smul,
        Matrix.trace_smul, Matrix.trace_one]
      rcases hy i with hi | hi <;> simp [hi, Fintype.card_pi, ZMod.card]
    · intro j _ hji
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
        trace_pauli_mul, ite_eq_right]
      · simp
      · exact fun h => hji (outside_labels_injective (codePoint_injective h)).symm
    · intro hi; exact absurd (mem_univ i) hi
  rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

private lemma outNatArr_closed_fast :
    outNatArr.all (fun u => outNatArr.all (fun v =>
      (u == v) || (sympFast u v != 0) || isSectionFast (u ^^^ v))) = true := by
  decide +kernel

private lemma c3_outside_add_mem_section (j i : Fin 64)
    (hne : codePoint (outsideLabel j) ≠ codePoint (outsideLabel i))
    (hcomm : symp (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) = 0) :
    codeAdd (outsideLabel j) (outsideLabel i) ∈ sectionCodes := by
  have hj_mem : (outsideLabel j).val ∈ outNatArr := by
    rw [← map_outsideLabel_val]; exact List.mem_map_of_mem (List.mem_finRange j)
  have hi_mem : (outsideLabel i).val ∈ outNatArr := by
    rw [← map_outsideLabel_val]; exact List.mem_map_of_mem (List.mem_finRange i)
  have hall := List.all_eq_true.mp outNatArr_closed_fast (outsideLabel j).val hj_mem
  have hspec := List.all_eq_true.mp hall (outsideLabel i).val hi_mem
  have hne_val : (outsideLabel j).val ≠ (outsideLabel i).val :=
    fun h => hne (congrArg codePoint (Fin.ext h))
  have hsymp0 : sympFast (outsideLabel j).val (outsideLabel i).val = 0 :=
    (symp_codePoint_eq_fast _ _).mp hcomm
  have hsec_fast : isSectionFast ((outsideLabel j).val ^^^ (outsideLabel i).val) = true := by
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hspec
    rcases hspec with (heq | hns) | hs
    · exact absurd heq hne_val
    · exact absurd hsymp0 hns
    · exact hs
  have hlt : Nat.xor (outsideLabel j).val (outsideLabel i).val < 256 :=
    Nat.xor_lt_two_pow (n := 8) (outsideLabel j).isLt (outsideLabel i).isLt
  have haddv : (codeAdd (outsideLabel j) (outsideLabel i)).val
      = (outsideLabel j).val ^^^ (outsideLabel i).val := by
    simp only [codeAdd, Nat.mod_eq_of_lt hlt]; rfl
  exact (mem_sectionCodes_iff_fast _).mpr (haddv ▸ hsec_fast)

private lemma c3_trace_TAT_eq (f : Fin 256 → ℤ) (y : Fin 64 → ℝ) :
    (c3OpT16 y * c3OpA16 f * c3OpT16 y).trace
      = 16 * ∑ i : Fin 64, ∑ j : Fin 64, ((y i * (completionOf f i j : ℝ) * y j : ℝ) : ℂ) := by
  rw [c3OpT16_eq_reindex, c3OpA16_eq_reindex, ← reindex_mul_eq, ← reindex_mul_eq, trace_reindex_eq]
  let T : Matrix (Vec 4) (Vec 4) ℂ := ∑ i : Fin 64, (y i : ℂ) • pauli (codePoint (outsideLabel i))
  let A : Matrix (Vec 4) (Vec 4) ℂ := ∑ v ∈ sectionCodes, (f v : ℂ) • pauli (codePoint v)
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
  let σ4 : Pt 4 → ℝ := fun u => (f (Equiv.ofBijective codePoint codePoint_bijective |>.symm u) : ℝ)
  have hσ4 : ∀ v : Fin 256, σ4 (codePoint v) = (f v : ℝ) := fun v => by
    dsimp only [σ4]
    have hinv : (Equiv.ofBijective codePoint codePoint_bijective).symm (codePoint v) = v :=
      (Equiv.ofBijective codePoint codePoint_bijective).symm_apply_apply v
    rw [hinv]
  have hA_eq : A = opA (sectionOf X4 d4) σ4 := by
    unfold opA
    rw [← hsec_eq, Finset.sum_image (fun _ _ _ _ h => codePoint_injective h)]
    refine Finset.sum_congr rfl fun v _ => by rw [hσ4 v]; push_cast; rfl
  have hT_jordan : (1 / 2 : ℂ) • (A * T + T * A)
      = ∑ j : Fin 64, (∑ i : Fin 64, ((completionOf f j i : ℝ) : ℂ) * (y i : ℂ))
          • pauli (codePoint (outsideLabel j)) := by
    rw [hA_eq]
    dsimp only [T]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.smul_sum]
    have hterm : ∀ i : Fin 64,
        (1 / 2 : ℂ) • (opA (sectionOf X4 d4) σ4 * ((y i : ℂ) • pauli (codePoint (outsideLabel i)))
          + ((y i : ℂ) • pauli (codePoint (outsideLabel i))) * opA (sectionOf X4 d4) σ4)
        = ∑ j : Fin 64, (((completionOf f j i : ℝ) : ℂ) * (y i : ℂ))
            • pauli (codePoint (outsideLabel j)) := by
      intro i
      have hi_mem : codePoint (outsideLabel i) ∈ outsideOf X4 d4 := by
        rw [← hout_eq, ← outside_labels_complete]
        exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (mem_univ i))
      have hJ := lemma20_jordan_action (isClosedCfg_quadric 0) d4 σ4
        ⟨codePoint (outsideLabel i), hi_mem⟩
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
      rw [smul_smul, mul_comm (y i : ℂ)]
      congr 2
      have hj_mem : codePoint (outsideLabel j) ∈ outsideOf X4 d4 := by
        rw [← hout_eq, ← outside_labels_complete]
        exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (mem_univ j))
      have hcomp : completionMat X4 d4 σ4
            ⟨codePoint (outsideLabel j), hj_mem⟩ ⟨codePoint (outsideLabel i), hi_mem⟩
          = (completionOf f j i : ℝ) := by
        unfold completionMat completionOf
        have hcond_iff : (codePoint (outsideLabel j) ≠ codePoint (outsideLabel i) ∧
              symp (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) = 0) ↔
            (codeAdd (outsideLabel j) (outsideLabel i) ∈ sectionCodes ∧
              symp (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) = 0) := by
          constructor
          · rintro ⟨hne, hcomm⟩
            exact ⟨c3_outside_add_mem_section j i hne hcomm, hcomm⟩
          · rintro ⟨hsec, hcomm⟩
            refine ⟨fun h => ?_, hcomm⟩
            have hji : j = i := outside_labels_injective (codePoint_injective h)
            subst hji
            exact isC3OutsidePair_irrefl j ((isC3OutsidePair_iff j j).mpr ⟨hsec, hcomm⟩)
        by_cases hcond : codePoint (outsideLabel j) ≠ codePoint (outsideLabel i) ∧
            symp (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) = 0
        · have hcond2 := hcond_iff.mp hcond
          rw [ite_eq_left hcond, ite_eq_left hcond2, ← codePoint_add, hσ4, Int.cast_mul,
            ← lineSign_eq_integer, codePoint_add, lineSign_add_right_of_comm _ _ hcond.2, mul_comm]
        · have hcond2 : ¬ (codeAdd (outsideLabel j) (outsideLabel i) ∈ sectionCodes ∧
              symp (codePoint (outsideLabel j)) (codePoint (outsideLabel i)) = 0) :=
            fun h => hcond (hcond_iff.mpr h)
          rw [ite_eq_right hcond, ite_eq_right hcond2, Int.cast_zero]
      rw [hcomp]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_smul]
  have htr_sym : (T * A * T).trace = (T * ((1 / 2 : ℂ) • (A * T + T * A))).trace := by
    rw [Matrix.mul_smul, mul_add, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_mul_comm T (T * A), Matrix.mul_assoc]
    simp only [smul_eq_mul]; ring
  change (T * A * T).trace = _
  rw [htr_sym, hT_jordan]
  dsimp only [T]
  rw [Finset.sum_mul, Matrix.trace_sum]
  calc (∑ i : Fin 64, (((y i : ℂ) • pauli (codePoint (outsideLabel i))) *
          ∑ j : Fin 64, (∑ k : Fin 64, ((completionOf f j k : ℝ) : ℂ) * (y k : ℂ))
            • pauli (codePoint (outsideLabel j))).trace)
      = ∑ i : Fin 64, (16 : ℂ) * ((y i : ℂ) *
          ∑ k : Fin 64, ((completionOf f i k : ℝ) : ℂ) * (y k : ℂ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Matrix.trace_sum, Finset.sum_eq_single i]
        · rw [Matrix.smul_mul, Matrix.mul_smul, pauli_mul_self, Matrix.trace_smul,
            Matrix.trace_smul, Matrix.trace_one]
          simp only [Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const,
            Finset.card_univ, smul_eq_mul]
          norm_num; ring
        · intro j _ hji
          rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
            trace_pauli_mul, ite_eq_right]
          · simp
          · exact fun h => hji (outside_labels_injective (codePoint_injective h)).symm
        · intro hi; exact absurd (mem_univ i) hi
    _ = 16 * ∑ i : Fin 64, ∑ j : Fin 64, ((y i * (completionOf f i j : ℝ) * y j : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by push_cast; ring

private lemma c3_T16_herm_off (y : Fin 64 → ℝ) :
    (c3OpT16 y)ᴴ = c3OpT16 y ∧
    ∀ a b : Fin 16, (a.val < 8 ↔ b.val < 8) → c3OpT16 y a b = 0 := by
  constructor
  · rw [c3OpT16_eq_reindex, Matrix.conjTranspose_reindex]
    congr 1
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_smul, (pauli_isHermitian _).eq]; simp
  · have hout_bit3 : ∀ i : Fin 64, (xCode (outsideLabel i)).val.testBit 3 = true := by
      intro i
      have hmem : outsideLabel i ∈ outsideCodes := by
        rw [← outside_labels_complete]; exact Finset.mem_image_of_mem _ (mem_univ i)
      have hb : (outsideLabel i).val.testBit 3 = true := (Finset.mem_filter.mp hmem).2
      have hmod : (outsideLabel i).val % 2 ^ 4 = (xCode (outsideLabel i)).val := rfl
      rw [← hmod, Nat.testBit_mod_two_pow]
      simp [hb]
    have hfin16_bit3 : ∀ x : Fin 16, x.val.testBit 3 = decide (8 ≤ x.val) := by decide +kernel
    intro a b hsame
    simp only [c3OpT16, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Int.coe_castRingHom,
      smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : realPauliCode (outsideLabel i) a b = 0 := by
      unfold realPauliCode
      rw [ite_eq_right]
      intro heq
      have hbit : a.val.testBit 3 = (b.val ^^^ (xCode (outsideLabel i)).val).testBit 3 :=
        congrArg (fun n : ℕ => n.testBit 3) heq
      rw [Nat.testBit_xor, hout_bit3 i, hfin16_bit3 a, hfin16_bit3 b] at hbit
      by_cases ha : a.val < 8
      · have hb : b.val < 8 := hsame.mp ha
        simp [not_le.mpr ha, not_le.mpr hb] at hbit
      · have hb : ¬ b.val < 8 := fun h => ha (hsame.mpr h)
        simp [not_lt.mp ha, not_lt.mp hb] at hbit
    rw [h0, Int.cast_zero, mul_zero]

private lemma c3_block_trace_identities (T16 A16 : Matrix (Fin 16) (Fin 16) ℂ)
    (C : Matrix (Fin 8) (Fin 8) ℤ) (D : Fin 8 → ℤ)
    (hT_herm : T16ᴴ = T16)
    (hT_off : ∀ a b : Fin 16, (a.val < 8 ↔ b.val < 8) → T16 a b = 0)
    (hA_ul : ∀ i j : Fin 8, A16 (Fin.castAdd 8 i) (Fin.castAdd 8 j) = (C i j : ℂ))
    (hA_ur : ∀ i j : Fin 8, A16 (Fin.castAdd 8 i) (Fin.natAdd 8 j) = 0)
    (hA_ll : ∀ i j : Fin 8, A16 (Fin.natAdd 8 i) (Fin.castAdd 8 j) = 0)
    (hA_lr : ∀ i j : Fin 8, A16 (Fin.natAdd 8 i) (Fin.natAdd 8 j) = if i = j then (D i : ℂ) else 0) :
    let M : Matrix (Fin 8) (Fin 8) ℂ := fun i j => T16 (Fin.castAdd 8 i) (Fin.natAdd 8 j)
    (T16 * T16).trace = 2 * ∑ j : Fin 8, ∑ i : Fin 8, star (M i j) * M i j ∧
    (T16 * A16 * T16).trace
      = (∑ k : Fin 8, ∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (C i j : ℂ) * M j k)
        + (∑ k : Fin 8, (D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k) := by
  intro M
  have hT_bot : ∀ i j : Fin 8, T16 (Fin.natAdd 8 j) (Fin.castAdd 8 i) = star (M i j) := by
    intro i j
    have := congrFun (congrFun hT_herm (Fin.castAdd 8 i)) (Fin.natAdd 8 j)
    simpa [M, Matrix.conjTranspose_apply] using (congrArg star this.symm).symm
  have hsum16 : ∀ g : Fin 16 → ℂ,
      (∑ a : Fin 16, g a) = (∑ i : Fin 8, g (Fin.castAdd 8 i)) + (∑ i : Fin 8, g (Fin.natAdd 8 i)) := by
    intro g
    rw [← Equiv.sum_comp fin16Split.symm, Fintype.sum_sum_type]
    rfl
  constructor
  · simp only [Matrix.trace, Matrix.diag_apply]
    simp_rw [Matrix.mul_apply, hsum16]
    have htop : (∑ i : Fin 8,
          ((∑ k : Fin 8, T16 (Fin.castAdd 8 i) (Fin.castAdd 8 k) * T16 (Fin.castAdd 8 k) (Fin.castAdd 8 i))
          + (∑ k : Fin 8, T16 (Fin.castAdd 8 i) (Fin.natAdd 8 k) * T16 (Fin.natAdd 8 k) (Fin.castAdd 8 i))))
        = ∑ k : Fin 8, ∑ i : Fin 8, star (M i k) * M i k := by
      have hz : ∀ i : Fin 8,
          ∑ k : Fin 8, T16 (Fin.castAdd 8 i) (Fin.castAdd 8 k) * T16 (Fin.castAdd 8 k) (Fin.castAdd 8 i) = 0 :=
        fun i => Finset.sum_eq_zero fun k _ => by
          rw [hT_off _ _ (by simp), zero_mul]
      simp_rw [hz, zero_add]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      rw [hT_bot i k, mul_comm]
    have hbot : (∑ j : Fin 8,
          ((∑ k : Fin 8, T16 (Fin.natAdd 8 j) (Fin.castAdd 8 k) * T16 (Fin.castAdd 8 k) (Fin.natAdd 8 j))
          + (∑ k : Fin 8, T16 (Fin.natAdd 8 j) (Fin.natAdd 8 k) * T16 (Fin.natAdd 8 k) (Fin.natAdd 8 j))))
        = ∑ j : Fin 8, ∑ k : Fin 8, star (M k j) * M k j := by
      have hz : ∀ j : Fin 8,
          ∑ k : Fin 8, T16 (Fin.natAdd 8 j) (Fin.natAdd 8 k) * T16 (Fin.natAdd 8 k) (Fin.natAdd 8 j) = 0 :=
        fun j => Finset.sum_eq_zero fun k _ => by
          rw [hT_off _ _ (by simp), zero_mul]
      simp_rw [hz, add_zero]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hT_bot k j]
    rw [htop, hbot, two_mul]
  · have h1 : (T16 * A16 * T16).trace
        = ∑ a : Fin 16, ∑ b : Fin 16, ∑ c : Fin 16, T16 a b * A16 b c * T16 c a := by
      simp only [Matrix.trace, Matrix.diag_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [h1]
    simp_rw [hsum16]
    have hzero_top_ll : ∀ i : Fin 8,
        ∑ b : Fin 8, ((∑ c : Fin 8, T16 (Fin.castAdd 8 i) (Fin.castAdd 8 b) * A16 (Fin.castAdd 8 b) (Fin.castAdd 8 c) * T16 (Fin.castAdd 8 c) (Fin.castAdd 8 i))
          + (∑ c : Fin 8, T16 (Fin.castAdd 8 i) (Fin.castAdd 8 b) * A16 (Fin.castAdd 8 b) (Fin.natAdd 8 c) * T16 (Fin.natAdd 8 c) (Fin.castAdd 8 i))) = 0 :=
      fun i => Finset.sum_eq_zero fun b _ => by
        rw [Finset.sum_eq_zero fun c _ => by rw [hT_off _ _ (by simp), zero_mul, zero_mul],
          Finset.sum_eq_zero fun c _ => by rw [hA_ur, mul_zero, zero_mul], add_zero]
    have hzero_bot_rr : ∀ k : Fin 8,
        ∑ b : Fin 8, ((∑ c : Fin 8, T16 (Fin.natAdd 8 k) (Fin.natAdd 8 b) * A16 (Fin.natAdd 8 b) (Fin.castAdd 8 c) * T16 (Fin.castAdd 8 c) (Fin.natAdd 8 k))
          + (∑ c : Fin 8, T16 (Fin.natAdd 8 k) (Fin.natAdd 8 b) * A16 (Fin.natAdd 8 b) (Fin.natAdd 8 c) * T16 (Fin.natAdd 8 c) (Fin.natAdd 8 k))) = 0 :=
      fun k => Finset.sum_eq_zero fun b _ => by
        rw [Finset.sum_eq_zero fun c _ => by rw [hA_ll, mul_zero, zero_mul],
          Finset.sum_eq_zero fun c _ => by
            rw [hT_off _ _ (by simp), zero_mul, zero_mul], add_zero]
    have hpartD : (∑ i : Fin 8, ∑ b : Fin 8,
          ((∑ c : Fin 8, T16 (Fin.castAdd 8 i) (Fin.natAdd 8 b) * A16 (Fin.natAdd 8 b) (Fin.castAdd 8 c) * T16 (Fin.castAdd 8 c) (Fin.castAdd 8 i))
          + (∑ c : Fin 8, T16 (Fin.castAdd 8 i) (Fin.natAdd 8 b) * A16 (Fin.natAdd 8 b) (Fin.natAdd 8 c) * T16 (Fin.natAdd 8 c) (Fin.castAdd 8 i))))
        = ∑ k : Fin 8, (D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k := by
      have h0 : ∀ i b : Fin 8,
          ∑ c : Fin 8, T16 (Fin.castAdd 8 i) (Fin.natAdd 8 b) * A16 (Fin.natAdd 8 b) (Fin.castAdd 8 c) * T16 (Fin.castAdd 8 c) (Fin.castAdd 8 i) = 0 :=
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
    have hpartC : (∑ k : Fin 8, ∑ i : Fin 8,
          ((∑ j : Fin 8, T16 (Fin.natAdd 8 k) (Fin.castAdd 8 i) * A16 (Fin.castAdd 8 i) (Fin.castAdd 8 j) * T16 (Fin.castAdd 8 j) (Fin.natAdd 8 k))
          + (∑ j : Fin 8, T16 (Fin.natAdd 8 k) (Fin.castAdd 8 i) * A16 (Fin.castAdd 8 i) (Fin.natAdd 8 j) * T16 (Fin.natAdd 8 j) (Fin.natAdd 8 k))))
        = ∑ k : Fin 8, ∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (C i j : ℂ) * M j k := by
      have h0 : ∀ k i : Fin 8,
          ∑ j : Fin 8, T16 (Fin.natAdd 8 k) (Fin.castAdd 8 i) * A16 (Fin.castAdd 8 i) (Fin.natAdd 8 j) * T16 (Fin.natAdd 8 j) (Fin.natAdd 8 k) = 0 :=
        fun k i => Finset.sum_eq_zero fun j _ => by rw [hA_ur, mul_zero, zero_mul]
      simp_rw [h0, add_zero, hA_ul]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hT_bot i k]
    simp_rw [hzero_top_ll, hzero_bot_rr, zero_add, add_zero]
    rw [hpartD, hpartC, add_comm]

/-- General spectral upper bound on `yᵀ Λ_f y` from a block-diagonal carrier matrix `A = C ⊕ D`
with `4 C < 111 I` and `D` diagonal with entries `≤ dmax`. -/
theorem c3_quadForm_lt_of_block_bound (f : Fin 256 → ℤ) (C : Matrix (Fin 8) (Fin 8) ℤ)
    (D : Fin 8 → ℤ) (dmax : ℤ)
    (hA_ul_int : ∀ i j : Fin 8, carrierOf f (Fin.castAdd 8 i) (Fin.castAdd 8 j) = C i j)
    (hA_ur_int : ∀ i j : Fin 8, carrierOf f (Fin.castAdd 8 i) (Fin.natAdd 8 j) = 0)
    (hA_ll_int : ∀ i j : Fin 8, carrierOf f (Fin.natAdd 8 i) (Fin.castAdd 8 j) = 0)
    (hA_lr_int : ∀ i j : Fin 8, carrierOf f (Fin.natAdd 8 i) (Fin.natAdd 8 j) = if i = j then D i else 0)
    (hD_le : ∀ i : Fin 8, D i ≤ dmax)
    (hC_pos : ∀ v : Fin 8 → ℂ, v ≠ 0 →
      4 * (∑ i : Fin 8, ∑ j : Fin 8, star (v i) * (C i j : ℂ) * v j).re
        < 111 * (∑ i : Fin 8, (star (v i) * v i).re))
    (y : Fin 64 → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) :
    4 * (∑ i : Fin 64, ∑ j : Fin 64, y i * (completionOf f i j : ℝ) * y j)
      < (111 + 4 * (dmax : ℝ)) * 32 := by
  have htrT2 := c3_trace_T16_sq y hy
  have htrTAT := c3_trace_TAT_eq f y
  obtain ⟨hT_herm, hT_off⟩ := c3_T16_herm_off y
  have hA_ul : ∀ i j : Fin 8, c3OpA16 f (Fin.castAdd 8 i) (Fin.castAdd 8 j) = (C i j : ℂ) := fun i j => by
    simp only [c3OpA16, Matrix.map_apply, Int.coe_castRingHom, hA_ul_int]
  have hA_ur : ∀ i j : Fin 8, c3OpA16 f (Fin.castAdd 8 i) (Fin.natAdd 8 j) = 0 := fun i j => by
    simp only [c3OpA16, Matrix.map_apply, Int.coe_castRingHom, hA_ur_int, Int.cast_zero]
  have hA_ll : ∀ i j : Fin 8, c3OpA16 f (Fin.natAdd 8 i) (Fin.castAdd 8 j) = 0 := fun i j => by
    simp only [c3OpA16, Matrix.map_apply, Int.coe_castRingHom, hA_ll_int, Int.cast_zero]
  have hA_lr : ∀ i j : Fin 8, c3OpA16 f (Fin.natAdd 8 i) (Fin.natAdd 8 j) = if i = j then (D i : ℂ) else 0 := fun i j => by
    simp only [c3OpA16, Matrix.map_apply, Int.coe_castRingHom, hA_lr_int]
    split_ifs <;> simp
  obtain ⟨hT2_block, htrTAT_block⟩ :=
    c3_block_trace_identities (c3OpT16 y) (c3OpA16 f) C D hT_herm hT_off hA_ul hA_ur hA_ll hA_lr
  let M : Matrix (Fin 8) (Fin 8) ℂ := fun i j => c3OpT16 y (Fin.castAdd 8 i) (Fin.natAdd 8 j)
  have hM_norm : ∑ j : Fin 8, ∑ i : Fin 8, (star (M i j) * M i j).re = 512 := by
    rw [hT2_block] at htrT2
    have hre := congrArg Complex.re htrT2
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.re_sum] at hre
    simp only [Complex.re_sum, Complex.re_ofNat] at hre
    linarith
  -- Step 6: Bound the `C` and `D` real parts!
  have hC_le_col : ∀ k : Fin 8,
      4 * (∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (C i j : ℂ) * M j k).re
        ≤ 111 * (∑ i : Fin 8, (star (M i k) * M i k).re) := by
    intro k
    by_cases hk : (fun i => M i k) = 0
    · have h0 : ∀ i : Fin 8, M i k = 0 := fun i => congrFun hk i
      simp [h0]
    · exact le_of_lt (hC_pos (fun i => M i k) hk)
  have hex_col : ∃ k₀ : Fin 8, (fun i => M i k₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hz : ∑ j : Fin 8, ∑ i : Fin 8, (star (M i j) * M i j).re = 0 := by
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_
      have h0 : M i j = 0 := congrFun (hall j) i
      simp [h0]
    linarith
  obtain ⟨k₀, hk₀⟩ := hex_col
  have hC_strict : 4 * (∑ k : Fin 8, ∑ i : Fin 8, ∑ j : Fin 8, star (M i k) * (C i j : ℂ) * M j k).re
      < 111 * (∑ k : Fin 8, ∑ i : Fin 8, (star (M i k) * M i k).re) := by
    rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_lt_sum (fun k _ => hC_le_col k) ⟨k₀, mem_univ k₀, hC_pos (fun i => M i k₀) hk₀⟩
  have hD_bound : (∑ k : Fin 8, (D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k).re
      ≤ (dmax : ℝ) * (∑ k : Fin 8, ∑ i : Fin 8, (star (M i k) * M i k).re) := by
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hre : ((D k : ℂ) * ∑ i : Fin 8, star (M i k) * M i k).re
        = (D k : ℝ) * ∑ i : Fin 8, (star (M i k) * M i k).re := by
      rw [show (D k : ℂ) = ((D k : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, Complex.re_sum]
    rw [hre]
    have hnn : 0 ≤ ∑ i : Fin 8, (star (M i k) * M i k).re :=
      Finset.sum_nonneg fun i _ => by
        simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul,
          sub_neg_eq_add]
        nlinarith [mul_self_nonneg (M i k).re, mul_self_nonneg (M i k).im]
    have hDk : (D k : ℝ) ≤ (dmax : ℝ) := by exact_mod_cast hD_le k
    exact mul_le_mul_of_nonneg_right hDk hnn
  have hre_eq := congrArg Complex.re (htrTAT.symm.trans htrTAT_block)
  rw [show (16 : ℂ) = ((16 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.add_re] at hre_eq
  have hlhs_re : (∑ i : Fin 64, ∑ j : Fin 64, ((y i * (completionOf f i j : ℝ) * y j : ℝ) : ℂ)).re
      = ∑ i : Fin 64, ∑ j : Fin 64, y i * (completionOf f i j : ℝ) * y j := by
    simp only [Complex.re_sum, Complex.ofReal_re]
  rw [hlhs_re] at hre_eq
  rw [hM_norm] at hC_strict hD_bound
  linarith

/-- **Corollary 16(a):** Every binary completion of `signA` violates at least **347** of the
1,120 outside contexts. -/
theorem corollary16_sigmaA_lower (y : Fin 64 → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) :
    347 ≤ c3ViolatedOutsideContexts signA y := by
  have hul : ∀ i j : Fin 8, carrierOf signA (Fin.castAdd 8 i) (Fin.castAdd 8 j) = c3BlockA i j := by
    rw [carrierA_from_section]; intro i j; rfl
  have hur : ∀ i j : Fin 8, carrierOf signA (Fin.castAdd 8 i) (Fin.natAdd 8 j) = 0 := by
    rw [carrierA_from_section]; decide +kernel
  have hll : ∀ i j : Fin 8, carrierOf signA (Fin.natAdd 8 i) (Fin.castAdd 8 j) = 0 := by
    rw [carrierA_from_section]; decide +kernel
  have hlr : ∀ i j : Fin 8, carrierOf signA (Fin.natAdd 8 i) (Fin.natAdd 8 j) = if i = j then (-1 : ℤ) else 0 := by
    rw [carrierA_from_section]; decide +kernel
  have hlt := c3_quadForm_lt_of_block_bound signA c3BlockA (fun _ => -1) (-1)
    hul hur hll hlr (fun _ => le_rfl)
    (pos_def_of_int_ldlt c3BlockA ldltScale0 ldltL0 ldltW0
      ldlt0_valid.1 ldlt0_valid.2.1 ldlt0_valid.2.2.1 ldlt0_valid.2.2.2.1 ldlt0_valid.2.2.2.2)
    y hy
  rw [c3_quadForm_eq signA signA_values y hy] at hlt
  norm_num at hlt
  have hreal : (346 : ℝ) < (c3ViolatedOutsideContexts signA y : ℝ) := by linarith
  have hnat : 346 < c3ViolatedOutsideContexts signA y := by exact_mod_cast hreal
  omega

/-- **Corollary 16(b):** Every binary completion of `signB` violates at least **315** of the
1,120 outside contexts. -/
theorem corollary16_sigmaB_lower (y : Fin 64 → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) :
    315 ≤ c3ViolatedOutsideContexts signB y := by
  let DB : Fin 8 → ℤ := ![3, -5, -1, -1, 3, -5, -1, -1]
  have hul : ∀ i j : Fin 8, carrierOf signB (Fin.castAdd 8 i) (Fin.castAdd 8 j) = c3BlockB i j := by
    rw [carrierB_from_section]; intro i j; rfl
  have hur : ∀ i j : Fin 8, carrierOf signB (Fin.castAdd 8 i) (Fin.natAdd 8 j) = 0 := by
    rw [carrierB_from_section]; decide +kernel
  have hll : ∀ i j : Fin 8, carrierOf signB (Fin.natAdd 8 i) (Fin.castAdd 8 j) = 0 := by
    rw [carrierB_from_section]; decide +kernel
  have hlr : ∀ i j : Fin 8, carrierOf signB (Fin.natAdd 8 i) (Fin.natAdd 8 j) = if i = j then DB i else 0 := by
    rw [carrierB_from_section]; decide +kernel
  have hDle : ∀ i : Fin 8, DB i ≤ 3 := by intro i; fin_cases i <;> decide
  have hlt := c3_quadForm_lt_of_block_bound signB c3BlockB DB 3
    hul hur hll hlr hDle
    (pos_def_of_int_ldlt c3BlockB ldltScale1 ldltL1 ldltW1
      ldlt1_valid.1 ldlt1_valid.2.1 ldlt1_valid.2.2.1 ldlt1_valid.2.2.2.1 ldlt1_valid.2.2.2.2)
    y hy
  rw [c3_quadForm_eq signB signB_values y hy] at hlt
  norm_num at hlt
  have hreal : (314 : ℝ) < (c3ViolatedOutsideContexts signB y : ℝ) := by linarith
  have hnat : 314 < c3ViolatedOutsideContexts signB y := by exact_mod_cast hreal
  omega

/-- **Corollary 16(c):** The explicit 64-point binary completion `c3WitnessReal` of `signB`
violates **exactly 344** of the 1,120 outside contexts. -/
theorem corollary16_sigmaB_witness :
    c3ViolatedOutsideContexts signB c3WitnessReal = 344 := by
  have hcomp_fast : ∀ i j : Fin 64,
      completionOf signB i j =
        if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
            (sympFast (outsideLabel i).val (outsideLabel j).val == 0)
        then signBFast ((outsideLabel i).val ^^^ (outsideLabel j).val)
              * lineSignFast (outsideLabel i).val (outsideLabel j).val
        else 0 := by
    intro i j
    have hlt : Nat.xor (outsideLabel i).val (outsideLabel j).val < 256 :=
      Nat.xor_lt_two_pow (n := 8) (outsideLabel i).isLt (outsideLabel j).isLt
    have haddv : (codeAdd (outsideLabel i) (outsideLabel j)).val
        = (outsideLabel i).val ^^^ (outsideLabel j).val := by
      simp only [codeAdd, Nat.mod_eq_of_lt hlt]; rfl
    unfold completionOf
    simp only [mem_sectionCodes_iff_fast, symp_codePoint_eq_fast, signB_eq_fast,
      integerLineSign_codePoint_eq_fast, haddv, Bool.and_eq_true, beq_iff_eq]
  have hfast : (outWithSign.map fun p => p.2 *
      (outWithSign.map fun q =>
        (if isSectionFast (p.1 ^^^ q.1) && (sympFast p.1 q.1 == 0)
          then signBFast (p.1 ^^^ q.1) * lineSignFast p.1 q.1 else 0) * q.2).sum).sum = 864 := by
    decide +kernel
  have hint : (∑ i : Fin 64, ∑ j : Fin 64, c3WitnessInt i * completionOf signB i j * c3WitnessInt j) = 864 := by
    have hrew : (∑ i : Fin 64, ∑ j : Fin 64, c3WitnessInt i * completionOf signB i j * c3WitnessInt j)
        = ∑ i : Fin 64, c3WitnessInt i * ∑ j : Fin 64,
            (if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
                (sympFast (outsideLabel i).val (outsideLabel j).val == 0)
              then signBFast ((outsideLabel i).val ^^^ (outsideLabel j).val)
                    * lineSignFast (outsideLabel i).val (outsideLabel j).val
              else 0) * c3WitnessInt j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by rw [hcomp_fast i j]; ring
    rw [hrew]
    have hlist : (∑ i : Fin 64, c3WitnessInt i * ∑ j : Fin 64,
          (if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
              (sympFast (outsideLabel i).val (outsideLabel j).val == 0)
            then signBFast ((outsideLabel i).val ^^^ (outsideLabel j).val)
                  * lineSignFast (outsideLabel i).val (outsideLabel j).val
            else 0) * c3WitnessInt j)
        = (outWithSign.map fun p => p.2 *
            (outWithSign.map fun q =>
              (if isSectionFast (p.1 ^^^ q.1) && (sympFast p.1 q.1 == 0)
                then signBFast (p.1 ^^^ q.1) * lineSignFast p.1 q.1 else 0) * q.2).sum).sum := by
      simp only [Fin.sum_univ_def]
      have h1 : ∀ p : ℕ × ℤ,
          ((List.finRange 64).map fun j =>
            (if isSectionFast (p.1 ^^^ (outsideLabel j).val) &&
                (sympFast p.1 (outsideLabel j).val == 0)
              then signBFast (p.1 ^^^ (outsideLabel j).val)
                    * lineSignFast p.1 (outsideLabel j).val
              else 0) * c3WitnessInt j).sum
          = (outWithSign.map fun q =>
              (if isSectionFast (p.1 ^^^ q.1) && (sympFast p.1 q.1 == 0)
                then signBFast (p.1 ^^^ q.1) * lineSignFast p.1 q.1 else 0) * q.2).sum := by
        intro p
        rw [← map_outsideLabel_witness, List.map_map]
        rfl
      have h2 : ((List.finRange 64).map fun i => c3WitnessInt i *
            ((List.finRange 64).map fun j =>
              (if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
                  (sympFast (outsideLabel i).val (outsideLabel j).val == 0)
                then signBFast ((outsideLabel i).val ^^^ (outsideLabel j).val)
                      * lineSignFast (outsideLabel i).val (outsideLabel j).val
                else 0) * c3WitnessInt j).sum)
          = outWithSign.map fun p => p.2 *
              (outWithSign.map fun q =>
                (if isSectionFast (p.1 ^^^ q.1) && (sympFast p.1 q.1 == 0)
                  then signBFast (p.1 ^^^ q.1) * lineSignFast p.1 q.1 else 0) * q.2).sum := by
        rw [← map_outsideLabel_witness, List.map_map]
        refine List.map_congr_left fun i _ => ?_
        dsimp only [Function.comp_apply]
        rw [h1 ((outsideLabel i).val, c3WitnessInt i), map_outsideLabel_witness]
      rw [h2]
    rw [hlist, hfast]
  have hquad : (∑ i : Fin 64, ∑ j : Fin 64,
      c3WitnessReal i * (completionOf signB i j : ℝ) * c3WitnessReal j) = 864 := by
    have hcast : ((∑ i : Fin 64, ∑ j : Fin 64, c3WitnessInt i * completionOf signB i j * c3WitnessInt j : ℤ) : ℝ) = 864 := by
      rw [hint]; norm_num
    rw [← hcast]
    push_cast
    rfl
  have hform := c3_quadForm_eq signB signB_values c3WitnessReal c3WitnessReal_values
  rw [hquad] at hform
  have hreal : (c3ViolatedOutsideContexts signB c3WitnessReal : ℝ) = 344 := by linarith
  exact_mod_cast hreal

/-- **Corollary 16 (Combined separation of binary completion minima):**
For the explicit four-qubit C3 cospectral pair `(signA, signB)`:
`min_y F(signB, y) ≤ 344 < 347 ≤ min_y F(signA, y)` and `315 ≤ min_y F(signB, y)`. -/
theorem corollary16_binary_minima_differ :
    (∃ y₁ : Fin 64 → ℝ, (∀ i, y₁ i = 1 ∨ y₁ i = -1) ∧ c3ViolatedOutsideContexts signB y₁ = 344) ∧
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) → 315 ≤ c3ViolatedOutsideContexts signB y) ∧
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) → 347 ≤ c3ViolatedOutsideContexts signA y) :=
  ⟨⟨c3WitnessReal, c3WitnessReal_values, corollary16_sigmaB_witness⟩,
   corollary16_sigmaB_lower, corollary16_sigmaA_lower⟩

end Corollary16

end HoggarBound.ConjectureE


/-
Hoggar Bound Lab — Theorem 2 (Quaternionic / Kramers spectral floor) and elliptic quadrics `Q⁻(2N−1, 2)`.

This module formalizes the quaternionic refinement of the spectral floor (Theorem 2 of the unified
paper; originally posted by B. W. Jonah, doi:10.5281/zenodo.23538829) and its elliptic-quadric
corollaries, closing the formalization gap listed in Sections 3, 9.1, and 12 of the paper.

Main results:
* `kramers_even_mult`              : every eigenvalue of a Hermitian matrix commuting with an
                                     antiunitary `θ` with `θ² = -I` has even multiplicity.
* `trace_cube_le_kramers`          : paired third-moment bound with effective dimension `d / 2`.
* `hoggar_bound_quaternionic`      : for `N ≥ 2` and any non-identity Pauli set `S` invariant under
                                     an antiunitary `P_w K` with `q₀(w) = 1`,
                                     `(2^(N-1) - 1) · β₆ ≤ (2^(N-1) - 2) · |S| · √((2^(N-1) - 1) · |S|)`.
* `card_ellipticPoints`            : `2 · |Q⁻(2N-1,2)| + 2 = 4^N - 2^N`.
* `card_flags_elliptic`            : exact flag count of `Q⁻(2N-1,2)` for every `N`.
* `elliptic_fraction`              : for all `N ≥ 2`, violated fraction ≥ `1/2 - √(D+1)/(D+2)`.
* `three_qubit_elliptic_contexts`  : `d(Q⁻(5,2)) ≥ 9` (exact).
* `four_qubit_elliptic_contexts`   : `d(Q⁻(7,2)) ≥ 291`.
* `five_qubit_elliptic_contexts`   : `d(Q⁻(9,2)) ≥ 6501`.
-/
import HoggarBound.Quadric

open Finset Matrix
open scoped InnerProductSpace

namespace HoggarBound

/-! ### Part 1. Kramers degeneracy: even multiplicity from an antiunitary with `θ² = -I` -/

section KramersAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Antiunitary action `θ v = J *ᵥ star v` on `EuclideanSpace ℂ n`. -/
noncomputable def antiunitary (J : Matrix n n ℂ) (v : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (J *ᵥ star v.ofLp)

omit [DecidableEq n] in
lemma antiunitary_add (J : Matrix n n ℂ) (v w : EuclideanSpace ℂ n) :
    antiunitary J (v + w) = antiunitary J v + antiunitary J w := by
  ext i
  simp only [antiunitary, PiLp.add_apply, WithLp.ofLp_add, star_add, mulVec_add, Pi.add_apply]

omit [DecidableEq n] in
lemma antiunitary_smul (J : Matrix n n ℂ) (c : ℂ) (v : EuclideanSpace ℂ n) :
    antiunitary J (c • v) = star c • antiunitary J v := by
  ext i
  simp only [antiunitary, PiLp.smul_apply, WithLp.ofLp_smul, star_smul, mulVec_smul, Pi.smul_apply]

lemma antiunitary_inner (J : Matrix n n ℂ) (hJu : Jᴴ * J = 1) (v w : EuclideanSpace ℂ n) :
    ⟪antiunitary J v, antiunitary J w⟫_ℂ = ⟪w, v⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (J *ᵥ star w.ofLp) ⬝ᵥ star (J *ᵥ star v.ofLp) = v.ofLp ⬝ᵥ star w.ofLp
  rw [dotProduct_comm]
  have hstar : star (J *ᵥ star v.ofLp) = v.ofLp ᵥ* Jᴴ := by
    ext j
    simp only [Pi.star_apply, mulVec, dotProduct, vecMul, conjTranspose_apply, star_sum,
      star_mul', star_star, mul_comm]
  rw [hstar, dotProduct_mulVec, vecMul_vecMul, hJu, vecMul_one]

lemma antiunitary_sq (J : Matrix n n ℂ) (hJ2 : J * J.map star = -1) (v : EuclideanSpace ℂ n) :
    antiunitary J (antiunitary J v) = -v := by
  ext i
  change (J *ᵥ star (J *ᵥ star v.ofLp)) i = -(v.ofLp i)
  have hstar : star (J *ᵥ star v.ofLp) = (J.map star) *ᵥ v.ofLp := by
    ext j
    simp only [Pi.star_apply, mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul', star_star]
  rw [hstar, mulVec_mulVec, hJ2, neg_mulVec, one_mulVec, Pi.neg_apply]

lemma antiunitary_inner_self_eq_zero (J : Matrix n n ℂ) (hJu : Jᴴ * J = 1)
    (hJ2 : J * J.map star = -1) (v : EuclideanSpace ℂ n) :
    ⟪v, antiunitary J v⟫_ℂ = 0 := by
  have h1 : ⟪antiunitary J (antiunitary J v), antiunitary J v⟫_ℂ = ⟪v, antiunitary J v⟫_ℂ :=
    antiunitary_inner J hJu (antiunitary J v) v
  rw [antiunitary_sq J hJ2, inner_neg_left] at h1
  have h2 : ⟪v, antiunitary J v⟫_ℂ + ⟪v, antiunitary J v⟫_ℂ = 0 := by
    calc ⟪v, antiunitary J v⟫_ℂ + ⟪v, antiunitary J v⟫_ℂ
        = -⟪v, antiunitary J v⟫_ℂ + ⟪v, antiunitary J v⟫_ℂ := by rw [h1]
      _ = 0 := neg_add_cancel _
  have h3 : (2 : ℂ) * ⟪v, antiunitary J v⟫_ℂ = 0 := by linear_combination h2
  exact (mul_eq_zero.mp h3).resolve_left (by norm_num)

/-- Any finite-dimensional complex subspace invariant under an antiunitary `θ` with `θ² = -I`
has even dimension. -/
theorem even_finrank_of_antiunitary_neg_one (J : Matrix n n ℂ) (hJu : Jᴴ * J = 1)
    (hJ2 : J * J.map star = -1) :
    ∀ (d : ℕ) (W : Submodule ℂ (EuclideanSpace ℂ n)),
      Module.finrank ℂ W = d →
      (∀ v ∈ W, antiunitary J v ∈ W) → Even d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro W hW hinv
    by_cases hd0 : d = 0
    · rw [hd0]; exact ⟨0, rfl⟩
    · have hpos : 0 < Module.finrank ℂ W := by omega
      have hne : W ≠ ⊥ := by
        intro hbot
        rw [hbot, finrank_bot] at hpos
        omega
      obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      set θv := antiunitary J v
      have hθvW : θv ∈ W := hinv v hvW
      have horth : ⟪v, θv⟫_ℂ = 0 := antiunitary_inner_self_eq_zero J hJu hJ2 v
      have horth' : ⟪θv, v⟫_ℂ = 0 := by rw [← inner_conj_symm, horth, map_zero]
      have hθv0 : θv ≠ 0 := by
        intro h
        have h1 : ⟪θv, θv⟫_ℂ = ⟪v, v⟫_ℂ := antiunitary_inner J hJu v v
        rw [h, inner_zero_left] at h1
        exact hv0 (inner_self_eq_zero.mp h1.symm)
      set U : Submodule ℂ (EuclideanSpace ℂ n) := Submodule.span ℂ ({v, θv} : Set _)
      have hUW : U ≤ W := by
        rw [Submodule.span_le]
        rintro x (rfl | rfl) <;> assumption
      -- `v` and `θv` are linearly independent over `ℂ`.
      have hli : LinearIndependent ℂ ![v, θv] := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
        have hinner_v : ⟪v, g 0 • v + g 1 • θv⟫_ℂ = 0 := by rw [hg, inner_zero_right]
        rw [inner_add_right, inner_smul_right, inner_smul_right, horth, mul_zero, add_zero] at hinner_v
        have hg0 : g 0 = 0 := (mul_eq_zero.mp hinner_v).resolve_right (inner_self_ne_zero.mpr hv0)
        have hinner_θ : ⟪θv, g 0 • v + g 1 • θv⟫_ℂ = 0 := by rw [hg, inner_zero_right]
        rw [hg0, zero_smul, zero_add, inner_smul_right] at hinner_θ
        have hg1 : g 1 = 0 := (mul_eq_zero.mp hinner_θ).resolve_right (inner_self_ne_zero.mpr hθv0)
        fin_cases i <;> assumption
      have hUrange : U = Submodule.span ℂ (Set.range ![v, θv]) := by
        dsimp only [U]
        congr 1
        ext x
        constructor
        · rintro (rfl | rfl)
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
        · rintro ⟨i, rfl⟩
          fin_cases i
          · left; rfl
          · right; rfl
      have hUdim : Module.finrank ℂ U = 2 := by
        rw [hUrange, finrank_span_eq_card hli, Fintype.card_fin]
      -- `U` is `θ`-invariant.
      have hUinv : ∀ u ∈ U, antiunitary J u ∈ U := by
        intro u hu
        rw [hUrange, Submodule.mem_span_range_iff_exists_fun] at hu
        obtain ⟨c, rfl⟩ := hu
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [antiunitary_add, antiunitary_smul, antiunitary_smul, antiunitary_sq J hJ2]
        rw [hUrange, Submodule.mem_span_range_iff_exists_fun]
        refine ⟨![-star (c 1), star (c 0)], ?_⟩
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          neg_smul, smul_neg]
        abel
      -- Orthogonal complement inside `W`: `W' = W ⊓ Uᗮ`.
      set W' : Submodule ℂ (EuclideanSpace ℂ n) := W ⊓ Uᗮ
      have hW'inv : ∀ w ∈ W', antiunitary J w ∈ W' := by
        intro w ⟨hwW, hwU⟩
        refine ⟨hinv w hwW, ?_⟩
        change w ∈ Uᗮ at hwU
        change antiunitary J w ∈ Uᗮ
        rw [Submodule.mem_orthogonal] at hwU ⊢
        intro u huU
        have hθuU : antiunitary J u ∈ U := hUinv u huU
        have h1 : ⟪antiunitary J u, w⟫_ℂ = 0 := hwU (antiunitary J u) hθuU
        have h2 : ⟪antiunitary J (antiunitary J u), antiunitary J w⟫_ℂ = ⟪w, antiunitary J u⟫_ℂ :=
          antiunitary_inner J hJu (antiunitary J u) w
        rw [antiunitary_sq J hJ2, inner_neg_left] at h2
        have h3 : ⟪w, antiunitary J u⟫_ℂ = 0 := by
          rw [← inner_conj_symm, h1, map_zero]
        rw [h3] at h2
        exact neg_eq_zero.mp h2
      have hdisj : Disjoint U W' := by
        rw [Submodule.disjoint_def]
        intro x hxU hxW'
        have hperp : ⟪x, x⟫_ℂ = 0 := (Submodule.mem_orthogonal U x).mp hxW'.2 x hxU
        exact inner_self_eq_zero.mp hperp
      have hsup : U ⊔ W' = W := by
        apply le_antisymm
        · exact sup_le hUW inf_le_left
        · intro w hw
          set c1 : ℂ := ⟪v, w⟫_ℂ / ⟪v, v⟫_ℂ
          set c2 : ℂ := ⟪θv, w⟫_ℂ / ⟪θv, θv⟫_ℂ
          set u : EuclideanSpace ℂ n := c1 • v + c2 • θv
          have huU : u ∈ U := by
            rw [hUrange, Submodule.mem_span_range_iff_exists_fun]
            refine ⟨![c1, c2], ?_⟩
            simp [u, Fin.sum_univ_two]
          have hwu : w - u ∈ Uᗮ := by
            rw [Submodule.mem_orthogonal]
            intro z hz
            rw [hUrange, Submodule.mem_span_range_iff_exists_fun] at hz
            obtain ⟨a, rfl⟩ := hz
            simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
            have hv_perp : ⟪v, w - u⟫_ℂ = 0 := by
              rw [inner_sub_right, inner_add_right, inner_smul_right, inner_smul_right,
                horth, mul_zero, add_zero]
              dsimp [c1]
              rw [div_mul_cancel₀ _ (inner_self_ne_zero.mpr hv0), sub_self]
            have hθ_perp : ⟪θv, w - u⟫_ℂ = 0 := by
              rw [inner_sub_right, inner_add_right, inner_smul_right, inner_smul_right,
                horth', mul_zero, zero_add]
              dsimp [c2]
              rw [div_mul_cancel₀ _ (inner_self_ne_zero.mpr hθv0), sub_self]
            rw [inner_add_left, inner_smul_left, inner_smul_left, hv_perp, hθ_perp]
            ring
          have hwuW : w - u ∈ W := W.sub_mem hw (hUW huU)
          have heq : w = u + (w - u) := by abel
          rw [heq]
          exact Submodule.add_mem_sup huU ⟨hwuW, hwu⟩
      have hdim_add : Module.finrank ℂ U + Module.finrank ℂ W' = Module.finrank ℂ W := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq U W'
        rw [hsup, hdisj.eq_bot, finrank_bot, add_zero] at h
        exact h.symm
      rw [hUdim, hW] at hdim_add
      have hlt : Module.finrank ℂ W' < d := by omega
      have hevenW' : Even (Module.finrank ℂ W') := ih (Module.finrank ℂ W') hlt W' rfl hW'inv
      obtain ⟨k, hk⟩ := hevenW'
      refine ⟨k + 1, ?_⟩
      omega

/-- **Kramers degeneracy theorem.** If a Hermitian matrix `A` commutes with an antiunitary `θ`
(`J * A.map star = A * J`) where `J` is unitary and `J * J.map star = -1`, then every eigenvalue
of `A` occurs with even multiplicity. -/
theorem kramers_even_mult {A J : Matrix n n ℂ} (hA : A.IsHermitian)
    (hJu : Jᴴ * J = 1) (hJ2 : J * J.map star = -1) (hJA : J * A.map star = A * J)
    (r : ℝ) : Even (univ.filter fun i : n => hA.eigenvalues i = r).card := by
  classical
  -- Eigenspace `E_r = {v : A *ᵥ v = r • v}`.
  set E : Submodule ℂ (EuclideanSpace ℂ n) :=
    LinearMap.ker (Matrix.toEuclideanLin A - (r : ℂ) • LinearMap.id)
  have hmemE : ∀ v : EuclideanSpace ℂ n, v ∈ E ↔ A *ᵥ v.ofLp = (r : ℂ) • v.ofLp := by
    intro v
    simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, Matrix.toLpLin_apply]
    constructor
    · intro h; exact congrArg WithLp.ofLp h
    · intro h; exact WithLp.ofLp_injective _ h
  -- `E` is `θ`-invariant.
  have hEinv : ∀ v ∈ E, antiunitary J v ∈ E := by
    intro v hv
    rw [hmemE] at hv ⊢
    change A *ᵥ (J *ᵥ star v.ofLp) = (r : ℂ) • (J *ᵥ star v.ofLp)
    have hstarAv : star (A *ᵥ v.ofLp) = (A.map star) *ᵥ star v.ofLp := by
      ext i
      simp only [Pi.star_apply, mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul']
    have hstarRv : star ((r : ℂ) • v.ofLp) = (r : ℂ) • star v.ofLp := by
      ext i
      simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
        Complex.conj_ofReal]
    calc A *ᵥ (J *ᵥ star v.ofLp)
        = (A * J) *ᵥ star v.ofLp := by rw [mulVec_mulVec]
      _ = (J * A.map star) *ᵥ star v.ofLp := by rw [hJA]
      _ = J *ᵥ ((A.map star) *ᵥ star v.ofLp) := by rw [← mulVec_mulVec]
      _ = J *ᵥ star (A *ᵥ v.ofLp) := by rw [← hstarAv]
      _ = J *ᵥ star ((r : ℂ) • v.ofLp) := by rw [hv]
      _ = J *ᵥ ((r : ℂ) • star v.ofLp) := by rw [hstarRv]
      _ = (r : ℂ) • (J *ᵥ star v.ofLp) := by rw [mulVec_smul]
  -- `E` is spanned by the eigenvectors with eigenvalue `r`.
  set S : Finset n := univ.filter fun i : n => hA.eigenvalues i = r
  have hEeq : E = Submodule.span ℂ (Set.range fun i : S => hA.eigenvectorBasis i.1) := by
    apply le_antisymm
    · intro v hv
      rw [hmemE] at hv
      have hrepr := hA.eigenvectorBasis.sum_repr' v
      have hcoeff : ∀ i : n, hA.eigenvectorBasis.repr v i ≠ 0 → hA.eigenvalues i = r := by
        intro i hne
        -- Take inner product of `A *ᵥ v = r • v` with `b_i`.
        have h1 : ⟪hA.eigenvectorBasis i, Matrix.toEuclideanLin A v⟫_ℂ
            = (r : ℂ) * ⟪hA.eigenvectorBasis i, v⟫_ℂ := by
          have hAv : Matrix.toEuclideanLin A v = (r : ℂ) • v := by
            apply WithLp.ofLp_injective
            exact hv
          rw [hAv, inner_smul_right]
        have h2 : ⟪hA.eigenvectorBasis i, Matrix.toEuclideanLin A v⟫_ℂ
            = (hA.eigenvalues i : ℂ) * ⟪hA.eigenvectorBasis i, v⟫_ℂ := by
          have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
          rw [← hsym (hA.eigenvectorBasis i) v]
          have hbi : Matrix.toEuclideanLin A (hA.eigenvectorBasis i)
              = (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
            apply WithLp.ofLp_injective
            simpa [RCLike.real_smul_eq_coe_smul] using hA.mulVec_eigenvectorBasis i
          rw [hbi, inner_smul_left]
          simp
        have hinner : ⟪hA.eigenvectorBasis i, v⟫_ℂ = hA.eigenvectorBasis.repr v i := by
          simpa using (hA.eigenvectorBasis.repr_apply_apply v i).symm
        rw [h2, hinner] at h1
        have heqC : ((hA.eigenvalues i : ℂ) - (r : ℂ)) * hA.eigenvectorBasis.repr v i = 0 := by
          linear_combination h1
        have heqC' : (hA.eigenvalues i : ℂ) = (r : ℂ) :=
          sub_eq_zero.mp ((mul_eq_zero.mp heqC).resolve_right hne)
        exact Complex.ofReal_injective heqC'
      rw [← hrepr]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← hA.eigenvectorBasis.repr_apply_apply v i]
      by_cases hc : hA.eigenvectorBasis.repr v i = 0
      · rw [hc, zero_smul]; exact Submodule.zero_mem _
      · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨mem_univ _, hcoeff i hc⟩
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hiS⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨⟨i, hiS⟩, rfl⟩
      rw [SetLike.mem_coe, hmemE]
      have hir : hA.eigenvalues i = r := (Finset.mem_filter.mp hiS).2
      simpa [hir, RCLike.real_smul_eq_coe_smul] using hA.mulVec_eigenvectorBasis i
  have hli : LinearIndependent ℂ (fun i : S => hA.eigenvectorBasis i.1) :=
    hA.eigenvectorBasis.toBasis.linearIndependent.comp (fun i : S => i.1) Subtype.val_injective
  have hdim : Module.finrank ℂ E = S.card := by
    rw [hEeq, finrank_span_eq_card hli, Fintype.card_coe]
  exact even_finrank_of_antiunitary_neg_one J hJu hJ2 S.card E hdim hEinv

/-! ### Part 2. Paired third-moment bound -/

/-- **Paired third-moment bound.** If `x : ι → ℝ` has every value occurring with even
multiplicity (`|ι| ≥ 4`), zero sum, and `∑ xᵢ² = |ι| · m`, then with `n = |ι| / 2` and
`a² = (n - 1) · m`:
`(n - 1) · ∑ xᵢ³ ≤ |ι| · m · (n - 2) · a`. -/
theorem sum_cube_le_even_mult {ι : Type*} [Fintype ι] (x : ι → ℝ) (m a : ℝ)
    (heven : ∀ r : ℝ, Even (univ.filter fun i : ι => x i = r).card)
    (hcard : 4 ≤ Fintype.card ι)
    (h1 : ∑ i, x i = 0) (h2 : ∑ i, x i ^ 2 = Fintype.card ι * m)
    (ha : 0 ≤ a) (ha2 : a ^ 2 = (((Fintype.card ι / 2 : ℕ) : ℝ) - 1) * m) :
    (((Fintype.card ι / 2 : ℕ) : ℝ) - 1) * ∑ i, x i ^ 3
      ≤ Fintype.card ι * m * (((Fintype.card ι / 2 : ℕ) : ℝ) - 2) * a := by
  classical
  let R : Finset ℝ := univ.image x
  let mult : ℝ → ℕ := fun r => (univ.filter fun i : ι => x i = r).card
  let half : ℝ → ℕ := fun r => mult r / 2
  have h2half : ∀ r, 2 * half r = mult r := by
    intro r
    obtain ⟨k, hk⟩ := heven r
    dsimp [half, mult]
    omega
  let κ := Σ r : R, Fin (half r.1)
  let y : κ → ℝ := fun p => p.1.1
  have hsum_eq : ∀ g : ℝ → ℝ, ∑ i : ι, g (x i) = 2 * ∑ p : κ, g (y p) := by
    intro g
    have hfib : ∑ i : ι, g (x i) = ∑ r ∈ R, ∑ i ∈ univ.filter (fun i : ι => x i = r), g (x i) := by
      rw [← Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem x (mem_univ i))]
    rw [hfib]
    have hterm : ∀ r ∈ R, ∑ i ∈ univ.filter (fun i : ι => x i = r), g (x i)
        = (2 : ℝ) * ((half r : ℕ) : ℝ) * g r := by
      intro r _
      have hconst : ∀ i ∈ univ.filter (fun i : ι => x i = r), g (x i) = g r := by
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcast : ((mult r : ℕ) : ℝ) = 2 * ((half r : ℕ) : ℝ) := by
        have := h2half r
        exact_mod_cast this.symm
      exact congrArg (· * g r) hcast
    rw [Finset.sum_congr rfl hterm]
    have hκsum : ∑ p : κ, g (y p) = ∑ r : R, ((half r.1 : ℕ) : ℝ) * g r.1 := by
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp [y]
    rw [hκsum, ← Finset.sum_attach R, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => by ring
  have hcardκ : 2 * Fintype.card κ = Fintype.card ι := by
    have h1' : (Fintype.card ι : ℝ) = 2 * (Fintype.card κ : ℝ) := by
      simpa using hsum_eq (fun _ => (1 : ℝ))
    have h2' : Fintype.card ι = 2 * Fintype.card κ := by exact_mod_cast h1'
    omega
  have hκ_eq : Fintype.card κ = Fintype.card ι / 2 := by omega
  have hκ2 : 2 ≤ Fintype.card κ := by omega
  have hy1 : ∑ p : κ, y p = 0 := by
    have := hsum_eq id
    dsimp at this
    linarith
  have hy2 : ∑ p : κ, y p ^ 2 = Fintype.card κ * m := by
    have h := hsum_eq (fun t => t ^ 2)
    have hc : (Fintype.card ι : ℝ) = 2 * (Fintype.card κ : ℝ) := by exact_mod_cast hcardκ.symm
    rw [h2, hc] at h
    linarith
  have hha2 : a ^ 2 = ((Fintype.card κ : ℝ) - 1) * m := by rw [hκ_eq]; exact ha2
  have hbound := sum_cube_le y m a hκ2 hy1 hy2 ha hha2
  have hy3 : ∑ i : ι, x i ^ 3 = 2 * ∑ p : κ, y p ^ 3 := hsum_eq (fun t => t ^ 3)
  have hc : (Fintype.card ι : ℝ) = 2 * (Fintype.card κ : ℝ) := by exact_mod_cast hcardκ.symm
  rw [← hκ_eq, hy3, hc]
  linarith

/-- **Kramers third-moment bound for a Hermitian matrix.** -/
theorem trace_cube_le_kramers {A J : Matrix n n ℂ} (hA : A.IsHermitian)
    (hJu : Jᴴ * J = 1) (hJ2 : J * J.map star = -1) (hJA : J * A.map star = A * J)
    (m a : ℝ) (hcard : 4 ≤ Fintype.card n) (h1 : A.trace = 0)
    (h2 : (A ^ 2).trace = (((Fintype.card n : ℝ) * m : ℝ) : ℂ))
    (ha : 0 ≤ a) (ha2 : a ^ 2 = (((Fintype.card n / 2 : ℕ) : ℝ) - 1) * m) :
    (((Fintype.card n / 2 : ℕ) : ℝ) - 1) * ((A ^ 3).trace).re
      ≤ Fintype.card n * m * (((Fintype.card n / 2 : ℕ) : ℝ) - 2) * a := by
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
  exact sum_cube_le_even_mult hA.eigenvalues m a
    (kramers_even_mult hA hJu hJ2 hJA) hcard e1 e2 ha ha2

end KramersAlgebra

/-! ### Part 3. Pauli antiunitaries and Theorem 2 (quaternionic spectral floor) -/

section QuaternionicFloor

variable {N : ℕ}

lemma weyl_map_star (u : Pt N) : (weyl u).map star = weyl u := by
  ext x y
  simp only [Matrix.map_apply, weyl]
  split_ifs
  · exact star_chi _ _
  · simp

/-- Entrywise complex conjugation of a Pauli operator: `P_u^* = (-1)^{q₀(u)} P_u`. -/
lemma pauli_map_star (u : Pt N) : (pauli u).map star = eps (qform u) • pauli u := by
  ext x y
  simp only [Matrix.map_apply, pauli, Matrix.smul_apply, smul_eq_mul, Complex.star_def,
    map_mul, map_pow, Complex.conj_I]
  have hw : (starRingEnd ℂ) (weyl u x y) = weyl u x y := by
    have := congrFun (congrFun (weyl_map_star u) x) y
    simpa [Matrix.map_apply, Complex.star_def] using this
  rw [hw]
  have hI : (-Complex.I) ^ ycount u = (-1 : ℂ) ^ ycount u * Complex.I ^ ycount u := by
    rw [← mul_pow]; ring_nf
  rw [hI, ← eps_natCast, ← dot_eq_ycount]
  simp only [qform]
  ring

/-- **Theorem 2 (Quaternionic / Kramers spectral floor).**
For `N ≥ 2`, if every Pauli observable `P_u` (`u ∈ S`) is invariant under the Pauli antiunitary
`P_w K` with `q₀(w) = 1` (i.e. `q₀(u) + ⟨w, u⟩ = 0`, for instance `S ⊆ Q_w`), then
`(2^(N-1) - 1) · β₆(S, f) ≤ (2^(N-1) - 2) · |S| · √((2^(N-1) - 1) · |S|)`. -/
theorem hoggar_bound_quaternionic (hN : 2 ≤ N) (w : Pt N) (hw : qform w = 1)
    (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S)
    (hS : ∀ u ∈ S, qform u + symp w u = 0)
    (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ (N - 1) - 1) * beta6 S f
      ≤ ((2 : ℝ) ^ (N - 1) - 2) * S.card * Real.sqrt (((2 : ℝ) ^ (N - 1) - 1) * S.card) := by
  set J : Matrix (Vec N) (Vec N) ℂ := pauli w
  have hJu : Jᴴ * J = 1 := by
    rw [(pauli_isHermitian w).eq, pauli_mul_self]
  have hJ2 : J * J.map star = -1 := by
    rw [pauli_map_star, hw, eps_one, Matrix.mul_smul, pauli_mul_self, neg_one_smul]
  have hJA : J * (opA S f).map star = opA S f * J := by
    unfold opA
    have hmap : (∑ u ∈ S, ((f u : ℝ) : ℂ) • pauli u).map star
        = ∑ u ∈ S, ((f u : ℝ) : ℂ) • (pauli u).map star := by
      ext x y
      simp [Matrix.map_apply, Matrix.sum_apply, Complex.conj_ofReal]
    rw [hmap, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, pauli_map_star, Matrix.mul_smul, pauli_comm u w,
      symp_comm u w, smul_smul, smul_smul, mul_assoc, ← eps_add, hS u hu, eps_zero, mul_one]
  have hcard4 : 4 ≤ Fintype.card (Vec N) := by
    rw [card_vec]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have hhalf_nat : Fintype.card (Vec N) / 2 = 2 ^ (N - 1) := by
    rw [card_vec]
    have hpow : 2 ^ N = 2 * 2 ^ (N - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ N), pow_succ, mul_comm]
    omega
  have hhalfR : ((Fintype.card (Vec N) / 2 : ℕ) : ℝ) = (2 : ℝ) ^ (N - 1) := by
    rw [hhalf_nat]; push_cast; rfl
  have hcardR : ((Fintype.card (Vec N) : ℕ) : ℝ) = (2 : ℝ) ^ N := by
    rw [card_vec]; push_cast; rfl
  have hDhalf : (2 : ℝ) ≤ (2 : ℝ) ^ (N - 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (N - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hnonneg : 0 ≤ ((2 : ℝ) ^ (N - 1) - 1) * S.card :=
    mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have key := trace_cube_le_kramers (opA_isHermitian S f) hJu hJ2 hJA (S.card : ℝ)
    (Real.sqrt (((2 : ℝ) ^ (N - 1) - 1) * S.card)) hcard4 (trace_opA S f h0)
    (by rw [trace_opA_sq S f hf, hcardR]) (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt hnonneg, hhalfR])
  rw [trace_opA_cube, Complex.ofReal_re, hcardR, hhalfR] at key
  have hDpos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have h2 : (2 : ℝ) ^ N * (((2 : ℝ) ^ (N - 1) - 1) * beta6 S f)
      ≤ (2 : ℝ) ^ N * (((2 : ℝ) ^ (N - 1) - 2) * S.card
          * Real.sqrt (((2 : ℝ) ^ (N - 1) - 1) * S.card)) := by
    linear_combination key
  exact le_of_mul_le_mul_left h2 hDpos

/-- Theorem 2 in terms of violated flags. -/
theorem hoggar_bound_quaternionic_violated (hN : 2 ≤ N) (w : Pt N) (hw : qform w = 1)
    (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S)
    (hS : ∀ u ∈ S, qform u + symp w u = 0)
    (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ (N - 1) - 1) * (((flags S).card : ℝ) - 2 * ((violated S f).card : ℝ))
      ≤ ((2 : ℝ) ^ (N - 1) - 2) * S.card * Real.sqrt (((2 : ℝ) ^ (N - 1) - 1) * S.card) := by
  rw [← beta6_eq_card S f hf]
  exact hoggar_bound_quaternionic hN w hw S h0 hS f hf

end QuaternionicFloor

/-! ### Part 4. Elliptic quadrics `Q⁻(2N−1, 2)` -/

section EllipticQuadric

variable {N : ℕ}

/-- Shifted quadratic form `q_w(u) = q₀(u) + ⟨w, u⟩`. -/
def qformShift (w u : Pt N) : ZMod 2 := qform u + symp w u

/-- The elliptic quadric `Q_w = {u ≠ 0 : q₀(u) + ⟨w, u⟩ = 0}` (elliptic when `q₀(w) = 1`). -/
def ellipticPoints (N : ℕ) (w : Pt N) : Finset (Pt N) :=
  univ.filter fun u => u ≠ 0 ∧ qformShift w u = 0

lemma qformShift_zero (w : Pt N) : qformShift w 0 = 0 := by
  simp [qformShift, qform_zero, symp_zero_right]

lemma qformShift_add (w u v : Pt N) :
    qformShift w (u + v) = qformShift w u + qformShift w v + symp u v := by
  simp only [qformShift, qform_add, symp_add_right]
  ring

/-- Gauss sum for a shifted quadratic form: `∑_v (-1)^{q₀(v) + ⟨u, v⟩} = (-1)^{q₀(u)} · 2^N`. -/
lemma sum_eps_qform_add_symp (u : Pt N) :
    ∑ v : Pt N, eps (qform v + symp u v) = eps (qform u) * (2 : ℂ) ^ N := by
  rw [← sum_eps_qform (N := N), Finset.mul_sum]
  refine Finset.sum_nbij' (fun v : Pt N => v + u) (fun v : Pt N => v + u) ?_ ?_ ?_ ?_ ?_
  · intro v _; exact mem_univ _
  · intro v _; exact mem_univ _
  · intro v _; show v + u + u = v; rw [add_assoc, pt_add_self, add_zero]
  · intro v _; show v + u + u = v; rw [add_assoc, pt_add_self, add_zero]
  · intro v _
    show eps (qform v + symp u v) = eps (qform u) * eps (qform (v + u))
    rw [qform_add, symp_comm v u, ← eps_add]
    congr 1
    have h2 : qform u + qform u = 0 := zmod2_add_self _
    linear_combination -h2

/-- `2 · #{u : q_w(u) = 0} = 4^N - 2^N` when `q₀(w) = 1`. -/
lemma card_qshift_zero {w : Pt N} (hw : qform w = 1) :
    2 * (univ.filter fun u : Pt N => qformShift w u = 0).card + 2 ^ N = 4 ^ N := by
  have hC : (((univ.filter fun u : Pt N => qformShift w u = 0).card : ℕ) : ℂ)
      = ((4 : ℂ) ^ N - (2 : ℂ) ^ N) / 2 := by
    rw [Finset.card_filter]
    push_cast
    have hterm : ∀ u : Pt N, (if qformShift w u = 0 then (1 : ℂ) else 0)
        = (1 + eps (qform u + symp w u)) / 2 := fun u => indicator_eq (qformShift w u)
    simp_rw [hterm, ← Finset.sum_div, Finset.sum_add_distrib, sum_eps_qform_add_symp, hw, eps_one,
      neg_one_mul, Finset.sum_const, Finset.card_univ, card_pt, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have h2 : ((2 * (univ.filter fun u : Pt N => qformShift w u = 0).card + 2 ^ N : ℕ) : ℂ)
      = ((4 ^ N : ℕ) : ℂ) := by
    push_cast
    rw [hC]
    ring
  exact_mod_cast h2

/-- Point count of the elliptic quadric: `|Q⁻(2N-1,2)| = (D+1)(D-2)/2`, i.e.,
`2 · |Q⁻| + 2 + 2^N = 4^N`. -/
theorem card_ellipticPoints {w : Pt N} (hw : qform w = 1) :
    2 * (ellipticPoints N w).card + 2 + 2 ^ N = 4 ^ N := by
  have heq : ellipticPoints N w = (univ.filter fun u : Pt N => qformShift w u = 0).erase 0 := by
    ext u; simp [ellipticPoints, and_comm]
  have h0 : (0 : Pt N) ∈ univ.filter fun u : Pt N => qformShift w u = 0 := by
    simp [qformShift_zero]
  have hpos : 0 < (univ.filter fun u : Pt N => qformShift w u = 0).card := Finset.card_pos.2 ⟨0, h0⟩
  rw [heq, Finset.card_erase_of_mem h0]
  have := card_qshift_zero hw
  omega

/-- For `u ∈ Q_w` (`q₀(w) = 1`): `4 · #{v : q_w(v) = 0, ⟨u, v⟩ = 0} + 2·2^N = 4^N`. -/
lemma card_qshift_commuting {w u : Pt N} (hw : qform w = 1) (hu : u ≠ 0)
    (hqu : qformShift w u = 0) :
    4 * (univ.filter fun v : Pt N => qformShift w v = 0 ∧ symp u v = 0).card + 2 * 2 ^ N
      = 4 ^ N := by
  have hind : ∀ v : Pt N, (if qformShift w v = 0 ∧ symp u v = 0 then (1 : ℂ) else 0)
      = (1 + eps (qformShift w v) + eps (symp u v) + eps (qformShift w v + symp u v)) / 4 := by
    intro v
    have h1 : (if qformShift w v = 0 ∧ symp u v = 0 then (1 : ℂ) else 0)
        = (if qformShift w v = 0 then (1 : ℂ) else 0) * (if symp u v = 0 then (1 : ℂ) else 0) := by
      by_cases ha : qformShift w v = 0 <;> by_cases hb : symp u v = 0 <;> simp [ha, hb]
    rw [h1, indicator_eq, indicator_eq, eps_add]
    ring
  have hwu : qform (w + u) = 1 := by
    rw [qform_add]
    have hq : qform u + symp w u = 0 := hqu
    rw [hw]
    linear_combination hq
  have hsum4 : ∑ v : Pt N, eps (qformShift w v + symp u v) = -(2 : ℂ) ^ N := by
    have hrew : ∀ v : Pt N, qformShift w v + symp u v = qform v + symp (w + u) v := by
      intro v
      simp only [qformShift, symp_comm (w + u) v, symp_add_right, symp_comm v w, symp_comm v u]
      ring
    simp_rw [hrew, sum_eps_qform_add_symp, hwu, eps_one, neg_one_mul]
  have hC : (((univ.filter fun v : Pt N => qformShift w v = 0 ∧ symp u v = 0).card : ℕ) : ℂ)
      = ((4 : ℂ) ^ N - 2 * (2 : ℂ) ^ N) / 4 := by
    rw [Finset.card_filter]
    push_cast
    simp only [hind, ← Finset.sum_div, Finset.sum_add_distrib, sum_eps_symp hu, hsum4,
      Finset.sum_const, Finset.card_univ, card_pt, nsmul_eq_mul, mul_one]
    have hsum2 : ∑ v : Pt N, eps (qformShift w v) = -(2 : ℂ) ^ N := by
      simp only [qformShift, sum_eps_qform_add_symp, hw, eps_one, neg_one_mul]
    rw [hsum2]
    push_cast
    ring
  have h2 : ((4 * (univ.filter fun v : Pt N => qformShift w v = 0 ∧ symp u v = 0).card
        + 2 * 2 ^ N : ℕ) : ℂ) = ((4 ^ N : ℕ) : ℂ) := by
    push_cast
    rw [hC]
    ring
  exact_mod_cast h2

lemma inner_filter_elliptic {w u : Pt N} (hq : qformShift w u = 0) :
    ((ellipticPoints N w).filter fun v => u + v ∈ ellipticPoints N w ∧ symp u v = 0)
      = ((univ.filter fun v : Pt N => qformShift w v = 0 ∧ symp u v = 0).erase 0).erase u := by
  ext v
  simp only [ellipticPoints, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, ne_eq]
  constructor
  · rintro ⟨⟨hv0, hqv⟩, ⟨huv, _⟩, hs⟩
    refine ⟨fun h => huv ?_, hv0, hqv, hs⟩
    rw [h, pt_add_self]
  · rintro ⟨hvu, hv0, hqv, hs⟩
    refine ⟨⟨hv0, hqv⟩, ⟨fun h => hvu (pt_eq_of_add_eq_zero h).symm, ?_⟩, hs⟩
    rw [qformShift_add, hq, hqv, hs]
    simp

lemma card_inner_elliptic {w u : Pt N} (hw : qform w = 1) (hu : u ≠ 0)
    (hq : qformShift w u = 0) :
    4 * ((ellipticPoints N w).filter fun v => u + v ∈ ellipticPoints N w ∧ symp u v = 0).card
        + 8 + 2 * 2 ^ N = 4 ^ N := by
  rw [inner_filter_elliptic hq]
  have h0 : (0 : Pt N) ∈ univ.filter fun v : Pt N => qformShift w v = 0 ∧ symp u v = 0 := by
    simp [qformShift_zero, symp_zero_right]
  have hu' : u ∈ (univ.filter fun v : Pt N => qformShift w v = 0 ∧ symp u v = 0).erase 0 := by
    simp [symp_self, hu, hq]
  have hc1 : 0 < ((univ.filter fun v : Pt N => qformShift w v = 0 ∧ symp u v = 0).erase 0).card :=
    Finset.card_pos.2 ⟨u, hu'⟩
  have hc0 : 0 < (univ.filter fun v : Pt N => qformShift w v = 0 ∧ symp u v = 0).card :=
    Finset.card_pos.2 ⟨0, h0⟩
  rw [Finset.card_erase_of_mem hu']
  have e2 := Finset.card_erase_of_mem h0
  have := card_qshift_commuting hw hu hq
  omega

/-- Flag count of the elliptic quadric:
`4 · #flags + (8 + 2·2^N) · #points = #points · 4^N`. -/
theorem card_flags_elliptic {w : Pt N} (hw : qform w = 1) :
    4 * (flags (ellipticPoints N w)).card + (8 + 2 * 2 ^ N) * (ellipticPoints N w).card
      = (ellipticPoints N w).card * 4 ^ N := by
  rw [card_flags, Finset.mul_sum]
  have hterm : ∀ u ∈ ellipticPoints N w,
      4 * ((ellipticPoints N w).filter fun v => u + v ∈ ellipticPoints N w ∧ symp u v = 0).card
        = 4 ^ N - (8 + 2 * 2 ^ N) := by
    intro u hu
    obtain ⟨hu0, hq⟩ := (Finset.mem_filter.1 hu).2
    have := card_inner_elliptic hw hu0 hq
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  by_cases hc : (ellipticPoints N w).card = 0
  · simp [hc]
  · obtain ⟨u, hu⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hc)
    obtain ⟨hu0, hq⟩ := (Finset.mem_filter.1 hu).2
    have hle : 8 + 2 * 2 ^ N ≤ 4 ^ N := by
      have := card_inner_elliptic hw hu0 hq
      omega
    have hadd : 4 ^ N - (8 + 2 * 2 ^ N) + (8 + 2 * 2 ^ N) = 4 ^ N := by omega
    calc (ellipticPoints N w).card * (4 ^ N - (8 + 2 * 2 ^ N))
            + (8 + 2 * 2 ^ N) * (ellipticPoints N w).card
        = (ellipticPoints N w).card * (4 ^ N - (8 + 2 * 2 ^ N) + (8 + 2 * 2 ^ N)) := by ring
      _ = (ellipticPoints N w).card * 4 ^ N := by rw [hadd]

lemma card_ellipticPoints_cast {w : Pt N} (hw : qform w = 1) :
    (((ellipticPoints N w).card : ℕ) : ℝ)
      = ((2 : ℝ) ^ N + 1) * ((2 : ℝ) ^ N - 2) / 2 := by
  have h := card_ellipticPoints hw
  have hR : (2 : ℝ) * ((ellipticPoints N w).card : ℝ) + 2 + (2 : ℝ) ^ N = (4 : ℝ) ^ N := by
    exact_mod_cast h
  have h42 : (4 : ℝ) ^ N = ((2 : ℝ) ^ N) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 N, pow_mul]
  rw [h42] at hR
  linarith

lemma card_flags_elliptic_cast {w : Pt N} (hw : qform w = 1) :
    (((flags (ellipticPoints N w)).card : ℕ) : ℝ)
      = ((2 : ℝ) ^ N + 1) * ((2 : ℝ) ^ N - 2) * ((2 : ℝ) ^ N + 2) * ((2 : ℝ) ^ N - 4) / 8 := by
  have h := card_flags_elliptic hw
  have hR : (4 : ℝ) * ((flags (ellipticPoints N w)).card : ℝ)
      + (8 + 2 * (2 : ℝ) ^ N) * ((ellipticPoints N w).card : ℝ)
      = ((ellipticPoints N w).card : ℝ) * (4 : ℝ) ^ N := by
    exact_mod_cast h
  have h42 : (4 : ℝ) ^ N = ((2 : ℝ) ^ N) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 N, pow_mul]
  rw [h42, card_ellipticPoints_cast hw] at hR
  linarith

/-- **Elliptic quadric violated fraction (all `N ≥ 2`).** Every assignment on `Q⁻(2N-1,2)`
violates at least the fraction `1/2 - √(D+1)/(D+2)` of all flags (hence contexts). -/
theorem elliptic_fraction (hN : 2 ≤ N) (w : Pt N) (hw : qform w = 1) (f : Pt N → ℝ)
    (hf : ∀ u ∈ ellipticPoints N w, f u = 1 ∨ f u = -1) :
    (1 / 2 - Real.sqrt ((2 : ℝ) ^ N + 1) / ((2 : ℝ) ^ N + 2))
        * ((flags (ellipticPoints N w)).card : ℝ)
      ≤ ((violated (ellipticPoints N w) f).card : ℝ) := by
  have h0 : (0 : Pt N) ∉ ellipticPoints N w := by simp [ellipticPoints]
  have hS : ∀ u ∈ ellipticPoints N w, qform u + symp w u = 0 := fun u hu =>
    (Finset.mem_filter.mp hu).2.2
  have hb := hoggar_bound_quaternionic_violated hN w hw (ellipticPoints N w) h0 hS f hf
  set D : ℝ := (2 : ℝ) ^ N with hD
  have hD4 : (4 : ℝ) ≤ D := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hhalf : (2 : ℝ) ^ (N - 1) = D / 2 := by
    have h1 : (2 : ℝ) ^ N = 2 * (2 : ℝ) ^ (N - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ N), pow_succ, mul_comm]
    linarith
  rw [hhalf, card_ellipticPoints_cast hw] at hb
  have hsq : Real.sqrt ((D / 2 - 1) * ((D + 1) * (D - 2) / 2))
      = (D / 2 - 1) * Real.sqrt (D + 1) := by
    have heq : (D / 2 - 1) * ((D + 1) * (D - 2) / 2) = (D / 2 - 1) ^ 2 * (D + 1) := by ring
    rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  rw [hsq] at hb
  have hpos1 : (0 : ℝ) < D / 2 - 1 := by linarith
  have hpos2 : (0 : ℝ) < D + 2 := by linarith
  have hb2 : ((flags (ellipticPoints N w)).card : ℝ) - 2 * ((violated (ellipticPoints N w) f).card : ℝ)
      ≤ (D / 2 - 2) * ((D + 1) * (D - 2) / 2) * Real.sqrt (D + 1) := by
    have hmul : (D / 2 - 1) * (((flags (ellipticPoints N w)).card : ℝ)
          - 2 * ((violated (ellipticPoints N w) f).card : ℝ))
        ≤ (D / 2 - 1) * ((D / 2 - 2) * ((D + 1) * (D - 2) / 2) * Real.sqrt (D + 1)) := by
      linear_combination hb
    exact le_of_mul_le_mul_left hmul hpos1
  have hF := card_flags_elliptic_cast hw
  set F : ℝ := ((flags (ellipticPoints N w)).card : ℝ)
  set V : ℝ := ((violated (ellipticPoints N w) f).card : ℝ)
  set s : ℝ := Real.sqrt (D + 1)
  have hkey : (D / 2 - 2) * ((D + 1) * (D - 2) / 2) * s = F * (2 * s / (D + 2)) := by
    rw [show F = (D + 1) * (D - 2) * (D + 2) * (D - 4) / 8 from hF]
    field_simp
    ring
  rw [hkey] at hb2
  have hrew : (1 / 2 - s / (D + 2)) * F = (F - F * (2 * s / (D + 2))) / 2 := by field_simp
  rw [hrew]
  linarith

/-! ### Part 5. Concrete elliptic-quadric corollaries (`N = 3, 4, 5`) -/

/-- **`Q⁻(5,2)`.** Every assignment of the 27 observables of any three-qubit elliptic quadric
violates at least 9 of the 45 contexts (exact). -/
theorem three_qubit_elliptic_contexts (w : Pt 3) (hw : qform w = 1) (f : Pt 3 → ℝ)
    (hf : ∀ u ∈ ellipticPoints 3 w, f u = 1 ∨ f u = -1) :
    9 ≤ (violatedLines (ellipticPoints 3 w) f).card := by
  have h0 : (0 : Pt 3) ∉ ellipticPoints 3 w := by simp [ellipticPoints]
  have hb := elliptic_fraction (N := 3) (by norm_num) w hw f hf
  have hS : (ellipticPoints 3 w).card = 27 := by
    have := card_ellipticPoints (N := 3) hw; norm_num at this; omega
  have hF : (flags (ellipticPoints 3 w)).card = 270 := by
    have := card_flags_elliptic (N := 3) hw; rw [hS] at this; norm_num at this; omega
  rw [hF] at hb
  have hs : Real.sqrt ((2 : ℝ) ^ 3 + 1) = 3 := by
    rw [show ((2 : ℝ) ^ 3 + 1) = 3 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [hs] at hb
  norm_num at hb
  have h2 := card_violated_le (ellipticPoints 3 w) h0 f
  omega

/-- **`Q⁻(7,2)`.** Every assignment of the 119 observables of any four-qubit elliptic quadric
violates at least 291 of the 1071 contexts. -/
theorem four_qubit_elliptic_contexts (w : Pt 4) (hw : qform w = 1) (f : Pt 4 → ℝ)
    (hf : ∀ u ∈ ellipticPoints 4 w, f u = 1 ∨ f u = -1) :
    291 ≤ (violatedLines (ellipticPoints 4 w) f).card := by
  have h0 : (0 : Pt 4) ∉ ellipticPoints 4 w := by simp [ellipticPoints]
  have hb := elliptic_fraction (N := 4) (by norm_num) w hw f hf
  have hS : (ellipticPoints 4 w).card = 119 := by
    have := card_ellipticPoints (N := 4) hw; norm_num at this; omega
  have hF : (flags (ellipticPoints 4 w)).card = 6426 := by
    have := card_flags_elliptic (N := 4) hw; rw [hS] at this; norm_num at this; omega
  rw [hF] at hb
  have h17 : (2 : ℝ) ^ 4 + 1 = 17 := by norm_num
  have h18 : (2 : ℝ) ^ 4 + 2 = 18 := by norm_num
  have hF' : ((6426 : ℕ) : ℝ) = 6426 := by norm_num
  rw [h17, h18, hF'] at hb
  have hsqrt : Real.sqrt 17 < 4.1232 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hV' : 1742 ≤ (violated (ellipticPoints 4 w) f).card := by
    by_contra hlt
    have hV : ((violated (ellipticPoints 4 w) f).card : ℝ) ≤ 1741 := by
      have : (violated (ellipticPoints 4 w) f).card ≤ 1741 := by omega
      exact_mod_cast this
    linarith
  have h2 := card_violated_le (ellipticPoints 4 w) h0 f
  omega

/-- **`Q⁻(9,2)`.** Every assignment of the 495 observables of any five-qubit elliptic quadric
violates at least 6501 of the 19635 contexts. -/
theorem five_qubit_elliptic_contexts (w : Pt 5) (hw : qform w = 1) (f : Pt 5 → ℝ)
    (hf : ∀ u ∈ ellipticPoints 5 w, f u = 1 ∨ f u = -1) :
    6501 ≤ (violatedLines (ellipticPoints 5 w) f).card := by
  have h0 : (0 : Pt 5) ∉ ellipticPoints 5 w := by simp [ellipticPoints]
  have hb := elliptic_fraction (N := 5) (by norm_num) w hw f hf
  have hS : (ellipticPoints 5 w).card = 495 := by
    have := card_ellipticPoints (N := 5) hw; norm_num at this; omega
  have hF : (flags (ellipticPoints 5 w)).card = 117810 := by
    have := card_flags_elliptic (N := 5) hw; rw [hS] at this; norm_num at this; omega
  rw [hF] at hb
  have h33 : (2 : ℝ) ^ 5 + 1 = 33 := by norm_num
  have h34 : (2 : ℝ) ^ 5 + 2 = 34 := by norm_num
  have hF' : ((117810 : ℕ) : ℝ) = 117810 := by norm_num
  rw [h33, h34, hF'] at hb
  have hsqrt : Real.sqrt 33 < 5.74457 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hV' : 39001 ≤ (violated (ellipticPoints 5 w) f).card := by
    by_contra hlt
    have hV : ((violated (ellipticPoints 5 w) f).card : ℝ) ≤ 39000 := by
      have : (violated (ellipticPoints 5 w) f).card ≤ 39000 := by omega
      exact_mod_cast this
    linarith
  have h2 := card_violated_le (ellipticPoints 5 w) h0 f
  omega

end EllipticQuadric

end HoggarBound

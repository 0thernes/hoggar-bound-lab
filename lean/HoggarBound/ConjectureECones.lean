/-
Hoggar Bound Lab — Character-sum formulas, master separation criteria, and the cone cases
(C6, C11, C14, plus Corollary 18's cone lift) of Jonah's Conjecture E.

Main results:
* `charSumOut_C1`, `charSumOut_C3_C5`, `charSumOut_C8`, `charSumOut_C12_C15`,
  `charSumOut_C6`, `charSumOut_C11_C14`: exact character sums `c_O(s) = ∑_{p ∈ O} (-1)^{⟨s, p⟩}`
  for all nine vertex cases of Jonah's classification.
* `completion_charpoly_ne_of_trace_sq_ne`: master separation criterion for C1, C3, C5, C8, C12, C15.
* `completion_charpoly_ne_of_cone_diff`: master separation criterion for C6, C11, C14.
* `c6_strict_law_fails`  (`N ≥ 3`): explicit pair-swap witnesses for case C6.
* `c11_strict_law_fails` (`N ≥ 3`): explicit pair-swap witnesses for case C11.
* `c14_strict_law_fails` (`N ≥ 4`): explicit pair-swap witnesses for case C14.
-/
import HoggarBound.ConjectureECore

open Finset Matrix

namespace HoggarBound.ConjectureE

/-! ### Part 1. Single-qubit Paulis, closed configurations, and `tau` on `Z`-shifts -/

section Geometry

variable {N : ℕ}

/-- Single-qubit `Z` operator on qubit `i`. -/
def ptZ (i : Fin N) : Pt N := (0, Pi.single i 1)

/-- Single-qubit `X` operator on qubit `i`. -/
def ptX (i : Fin N) : Pt N := (Pi.single i 1, 0)

/-- Single-qubit `Y` operator on qubit `i`. -/
def ptY (i : Fin N) : Pt N := (Pi.single i 1, Pi.single i 1)

/-- General quadric `Q_c = {v ≠ 0 : q₀(v) + ⟨c, v⟩ = 0}` (hyperbolic if `q₀(c)=0`, elliptic if `q₀(c)=1`). -/
def quadric (N : ℕ) (c : Pt N) : Finset (Pt N) :=
  univ.filter fun v => v ≠ 0 ∧ qformShift c v = 0

/-- Orthogonal hyperplane section `X ∩ e⊥`. -/
def perpSet (X : Finset (Pt N)) (e : Pt N) : Finset (Pt N) :=
  X.filter fun v => symp v e = 0

lemma ptZ_ne_zero (i : Fin N) : ptZ i ≠ 0 := by
  intro h
  have := congrFun (congrArg Prod.snd h) i
  simp [ptZ] at this

lemma ptY_ne_zero (i : Fin N) : ptY i ≠ 0 := by
  intro h
  have := congrFun (congrArg Prod.fst h) i
  simp [ptY] at this

lemma ptZ_ne_ptZ {i j : Fin N} (hij : i ≠ j) : ptZ i ≠ ptZ j := by
  intro h
  have := congrFun (congrArg Prod.snd h) i
  simp [ptZ, hij] at this

lemma qform_ptZ (i : Fin N) : qform (ptZ i) = 0 := by simp [qform, ptZ]

lemma qform_ptY (i : Fin N) : qform (ptY i) = 1 := by
  simp [qform, ptY, dotProduct_single]

lemma symp_ptZ (u : Pt N) (i : Fin N) : symp u (ptZ i) = u.1 i := by
  simp [symp, ptZ, single_dotProduct]

lemma symp_ptZ_left (i : Fin N) (u : Pt N) : symp (ptZ i) u = u.1 i := by
  rw [symp_comm, symp_ptZ]

lemma symp_ptY (u : Pt N) (i : Fin N) : symp u (ptY i) = u.2 i + u.1 i := by
  simp [symp, ptY, dotProduct_single, single_dotProduct]

lemma symp_ptZ_ptZ (i j : Fin N) : symp (ptZ i) (ptZ j) = 0 := by
  rw [symp_ptZ]; rfl

lemma symp_ptY_ptZ {i j : Fin N} (hij : i ≠ j) : symp (ptY i) (ptZ j) = 0 := by
  simp [symp_ptZ, ptY, hij.symm]

lemma symp_ptY_ptY (i j : Fin N) : symp (ptY i) (ptY j) = 0 := by
  rw [symp_ptY]
  by_cases h : i = j
  · subst h; simp [ptY]; exact zmod2_add_self 1
  · simp [ptY, Ne.symm h]

lemma isClosedCfg_allPoints : IsClosedCfg (allPoints N) := by
  refine ⟨by simp [allPoints], fun u _ v _ huv _ => ?_⟩
  simp only [allPoints, Finset.mem_erase, Finset.mem_univ, and_true]
  exact fun h => huv (pt_eq_of_add_eq_zero h)

lemma isClosedCfg_quadric (c : Pt N) : IsClosedCfg (quadric N c) := by
  refine ⟨by simp [quadric], fun u hu v hv huv hs => ?_⟩
  obtain ⟨_, hqu⟩ := (Finset.mem_filter.mp hu).2
  obtain ⟨_, hqv⟩ := (Finset.mem_filter.mp hv).2
  refine Finset.mem_filter.mpr ⟨mem_univ _, fun h => huv (pt_eq_of_add_eq_zero h), ?_⟩
  rw [qformShift_add, hqu, hqv, hs]
  simp

lemma isClosedCfg_perpSet {X : Finset (Pt N)} (hX : IsClosedCfg X) (e : Pt N) :
    IsClosedCfg (perpSet X e) := by
  refine ⟨fun h => hX.1 (Finset.mem_filter.mp h).1, fun u hu v hv huv hs => ?_⟩
  obtain ⟨huX, hue⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvX, hve⟩ := Finset.mem_filter.mp hv
  refine Finset.mem_filter.mpr ⟨hX.2 u huX v hvX huv hs, ?_⟩
  rw [symp_comm, symp_add_right, symp_comm e u, hue, symp_comm e v, hve, add_zero]

/-- Adding a `Z` factor on a qubit where `u` has no `X` preserves `ycount`. -/
lemma ycount_add_ptZ {u : Pt N} {i : Fin N} (hu : u.1 i = 0) : ycount (u + ptZ i) = ycount u := by
  unfold ycount
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_add, Prod.snd_add, ptZ,
    Pi.add_apply, Pi.zero_apply, add_zero]
  by_cases hki : k = i
  · subst hki
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp [hu, h01]
  · simp [Pi.single_eq_of_ne hki]

/-- Context phase `τ(u, u + Z_i) = 1` whenever `u` commutes with `Z_i`. -/
lemma tau_add_ptZ {u : Pt N} {i : Fin N} (hu : u.1 i = 0) : tau u (u + ptZ i) = 1 := by
  have hy : ycount (u + ptZ i) = ycount u := ycount_add_ptZ hu
  have hsum : u + (u + ptZ i) = ptZ i := by rw [← add_assoc, pt_add_self, zero_add]
  have hyz : ycount (ptZ i) = 0 := by
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp [ycount, ptZ, h01]
  have hchi : chi u.2 (u + ptZ i).1 = (-1 : ℂ) ^ ycount u := by
    have h1 : (u + ptZ i).1 = u.1 := by simp [ptZ]
    rw [h1, chi_self]
  unfold tau
  rw [hsum, hy, hyz, hchi]
  simp only [mul_zero, add_zero, ← two_mul, pow_mul, Complex.I_sq, ← mul_pow]
  simp

/-- Context phase `τ(u, u + Z_i + Z_j) = 1` whenever `u` commutes with both `Z_i` and `Z_j`. -/
lemma tau_add_ptZ_add_ptZ {u : Pt N} {i j : Fin N} (hi : u.1 i = 0) (hj : u.1 j = 0) :
    tau u (u + (ptZ i + ptZ j)) = 1 := by
  have h1 : (u + ptZ i).1 j = 0 := by simp [ptZ, hj]
  have hy : ycount (u + (ptZ i + ptZ j)) = ycount u := by
    rw [← add_assoc, ycount_add_ptZ h1, ycount_add_ptZ hi]
  have hsum : u + (u + (ptZ i + ptZ j)) = ptZ i + ptZ j := by
    rw [← add_assoc, pt_add_self, zero_add]
  have hyz : ycount (ptZ i + ptZ j) = 0 := by
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp [ycount, ptZ, h01]
  have hchi : chi u.2 (u + (ptZ i + ptZ j)).1 = (-1 : ℂ) ^ ycount u := by
    have hf : (u + (ptZ i + ptZ j)).1 = u.1 := by simp [ptZ]
    rw [hf, chi_self]
  unfold tau
  rw [hsum, hy, hyz, hchi]
  simp only [mul_zero, add_zero, ← two_mul, pow_mul, Complex.I_sq, ← mul_pow]
  simp

end Geometry

/-! ### Part 2. Exact `charSumOut` character sums for all nine vertex cases -/

section CharacterSums

variable {N : ℕ}

lemma sum_eps_symp_all (u : Pt N) :
    ∑ p : Pt N, eps (symp u p) = if u = 0 then (4 : ℂ) ^ N else 0 := by
  by_cases hu : u = 0
  · subst hu
    simp only [symp, Prod.snd_zero, Prod.fst_zero, zero_dotProduct, dotProduct_zero, add_zero,
      eps_zero, Finset.sum_const, Finset.card_univ, card_pt, nsmul_eq_mul, mul_one, ↓reduceIte]
    push_cast; rfl
  · rw [ite_eq_right hu]
    exact sum_eps_symp hu

lemma sum_eps_qshift_symp (c u : Pt N) :
    ∑ p : Pt N, eps (qformShift c p + symp u p) = eps (qform (c + u)) * (2 : ℂ) ^ N := by
  have hrew : ∀ p : Pt N, qformShift c p + symp u p = qform p + symp (c + u) p := by
    intro p
    simp only [qformShift, symp_comm (c + u) p, symp_add_right, symp_comm p c, symp_comm p u]
    ring
  simp_rw [hrew]
  exact sum_eps_qform_add_symp (c + u)

lemma indicator_eq_one (t : ZMod 2) : (if t = 1 then (1 : ℂ) else 0) = (1 - eps t) / 2 := by
  rcases zmod2_cases t with rfl | rfl
  · have h : (0 : ZMod 2) ≠ 1 := by decide
    simp [h]
  · simp

lemma symp_add_left (u v p : Pt N) : symp (u + v) p = symp u p + symp v p := by
  rw [symp_comm, symp_add_right, symp_comm p u, symp_comm p v]

lemma eq_add_zero_iff (u v : Pt N) : u + v = 0 ↔ u = v :=
  ⟨pt_eq_of_add_eq_zero, fun h => by rw [h, pt_add_self]⟩

lemma qform_add_shift (c u : Pt N) : qform (c + u) = qform c + qformShift c u := by
  rw [qform_add, qformShift]; ring

/-- Case C1 (`X = W`, `d ≠ 0`): `c_O(s) = -(4^N / 2) [s = d]` for `s ∈ H`. -/
theorem charSumOut_C1 {d s : Pt N} (hs0 : s ≠ 0) :
    charSumOut (outsideOf (allPoints N) d) s = if s = d then -((4 : ℂ) ^ N / 2) else 0 := by
  have hO : outsideOf (allPoints N) d = univ.filter (fun p : Pt N => symp p d = 1) := by
    ext p
    simp only [outsideOf, allPoints, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun hp => ?_, h⟩
      rw [hp, symp_comm, symp_zero_right] at h
      exact absurd h (by decide)
  rw [charSumOut, hO, Finset.sum_filter]
  have hterm : ∀ p : Pt N,
      (if symp p d = 1 then eps (symp s p) else 0)
        = (eps (symp s p) - eps (symp (s + d) p)) / 2 := by
    intro p
    have h1 : (if symp p d = 1 then eps (symp s p) else 0)
        = (if symp p d = 1 then (1 : ℂ) else 0) * eps (symp s p) := by split_ifs <;> simp
    rw [h1, indicator_eq_one, div_mul_eq_mul_div, sub_mul, one_mul, ← eps_add, symp_comm p d,
      add_comm (symp d p), ← symp_add_left]
  simp_rw [hterm, ← Finset.sum_div, Finset.sum_sub_distrib, sum_eps_symp_all,
    ite_eq_right hs0, eq_add_zero_iff]
  by_cases hsd : s = d
  · simp [hsd]; ring
  · simp [hsd]

/-- Cases C3 and C5 (`X = Q_c`, `q_c(d) = 0`): `c_O(s) = -(4^N / 4) [s = d]` for `s ∈ H`. -/
theorem charSumOut_C3_C5 {c d s : Pt N} (hqd : qformShift c d = 0)
    (hs0 : s ≠ 0) (hqs : qformShift c s = 0) (hsd : symp s d = 0) :
    charSumOut (outsideOf (quadric N c) d) s = if s = d then -((4 : ℂ) ^ N / 4) else 0 := by
  have hO : outsideOf (quadric N c) d
      = univ.filter (fun p : Pt N => qformShift c p = 0 ∧ symp p d = 1) := by
    ext p
    simp only [outsideOf, quadric, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hq⟩, hd⟩; exact ⟨hq, hd⟩
    · rintro ⟨hq, hd⟩
      refine ⟨⟨fun hp => ?_, hq⟩, hd⟩
      rw [hp, symp_comm, symp_zero_right] at hd; exact absurd hd (by decide)
  rw [charSumOut, hO, Finset.sum_filter]
  have hterm : ∀ p : Pt N,
      (if qformShift c p = 0 ∧ symp p d = 1 then eps (symp s p) else 0)
        = (eps (symp s p) - eps (symp (s + d) p)
            + eps (qformShift c p + symp s p) - eps (qformShift c p + symp (s + d) p)) / 4 := by
    intro p
    have h1 : (if qformShift c p = 0 ∧ symp p d = 1 then eps (symp s p) else 0)
        = (if qformShift c p = 0 then (1 : ℂ) else 0) * (if symp p d = 1 then (1 : ℂ) else 0)
          * eps (symp s p) := by
      by_cases ha : qformShift c p = 0 <;> by_cases hb : symp p d = 1 <;> simp [ha, hb]
    rw [h1, indicator_eq, indicator_eq_one]
    have e1 : eps (symp p d) * eps (symp s p) = eps (symp (s + d) p) := by
      rw [← eps_add, symp_comm p d, add_comm (symp d p), ← symp_add_left]
    have e2 : eps (qformShift c p) * eps (symp s p) = eps (qformShift c p + symp s p) :=
      (eps_add _ _).symm
    have e3 : eps (qformShift c p) * eps (symp p d) * eps (symp s p)
        = eps (qformShift c p + symp (s + d) p) := by
      rw [mul_assoc, e1, ← eps_add]
    linear_combination -(1 / 4 : ℂ) * e1 + (1 / 4 : ℂ) * e2 - (1 / 4 : ℂ) * e3
  simp_rw [hterm, ← Finset.sum_div]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_eps_symp_all, sum_eps_qshift_symp,
    ite_eq_right hs0, eq_add_zero_iff]
  have hq1 : qform (c + s) = qform c := by rw [qform_add_shift, hqs, add_zero]
  have hq2 : qform (c + (s + d)) = qform c := by
    rw [qform_add_shift, qformShift_add, hqs, hqd, hsd]; simp
  rw [hq1, hq2]
  by_cases h : s = d
  · simp [h]; ring
  · simp [h]

/-- Case C8 (`X = Q⁺ ∩ e⊥`, `q₀(e) = 1`, `q₀(d) = 0`, `⟨d, e⟩ = 0`):
`c_O(s) = -(4^N / 8) [s = d]` for `s ∈ H`. -/
theorem charSumOut_C8 {e d s : Pt N} (hqe : qform e = 1) (hqd : qform d = 0) (hde : symp d e = 0)
    (hs0 : s ≠ 0) (hqs : qform s = 0) (hse : symp s e = 0) (hsd : symp s d = 0) :
    charSumOut (outsideOf (perpSet (quadric N 0) e) d) s
      = if s = d then -((4 : ℂ) ^ N / 8) else 0 := by
  have hO : outsideOf (perpSet (quadric N 0) e) d
      = univ.filter (fun p : Pt N => qform p = 0 ∧ symp p e = 0 ∧ symp p d = 1) := by
    ext p
    have hq0p : qformShift (0 : Pt N) p = qform p := by
      rw [qformShift, symp_comm, symp_zero_right, add_zero]
    simp only [outsideOf, perpSet, quadric, hq0p, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨_, hq⟩, he⟩, hd⟩; exact ⟨hq, he, hd⟩
    · rintro ⟨hq, he, hd⟩
      refine ⟨⟨⟨fun hp => ?_, hq⟩, he⟩, hd⟩
      rw [hp, symp_comm, symp_zero_right] at hd; exact absurd hd (by decide)
  rw [charSumOut, hO, Finset.sum_filter]
  have hterm : ∀ p : Pt N,
      (if qform p = 0 ∧ symp p e = 0 ∧ symp p d = 1 then eps (symp s p) else 0)
        = ((eps (symp s p) + eps (symp (s + e) p) - eps (symp (s + d) p) - eps (symp (s + d + e) p))
          + (eps (qform p + symp s p) + eps (qform p + symp (s + e) p)
             - eps (qform p + symp (s + d) p) - eps (qform p + symp (s + d + e) p))) / 8 := by
    intro p
    have h1 : (if qform p = 0 ∧ symp p e = 0 ∧ symp p d = 1 then eps (symp s p) else 0)
        = (if qform p = 0 then (1 : ℂ) else 0) * (if symp p e = 0 then (1 : ℂ) else 0)
          * (if symp p d = 1 then (1 : ℂ) else 0) * eps (symp s p) := by
      by_cases ha : qform p = 0 <;> by_cases hb : symp p e = 0 <;>
        by_cases hc : symp p d = 1 <;> simp [ha, hb, hc]
    rw [h1, indicator_eq, indicator_eq, indicator_eq_one]
    have ea : eps (symp p e) * eps (symp s p) = eps (symp (s + e) p) := by
      rw [← eps_add, symp_comm p e, add_comm (symp e p), ← symp_add_left]
    have eb : eps (symp p d) * eps (symp s p) = eps (symp (s + d) p) := by
      rw [← eps_add, symp_comm p d, add_comm (symp d p), ← symp_add_left]
    have ec : eps (symp p e) * eps (symp p d) * eps (symp s p) = eps (symp (s + d + e) p) := by
      rw [mul_assoc, eb, ← eps_add, symp_comm p e, add_comm (symp e p), ← symp_add_left]
    have qa : eps (qform p) * eps (symp s p) = eps (qform p + symp s p) := (eps_add _ _).symm
    have qb : eps (qform p) * eps (symp p e) * eps (symp s p) = eps (qform p + symp (s + e) p) := by
      rw [mul_assoc, ea, ← eps_add]
    have qc' : eps (qform p) * eps (symp p d) * eps (symp s p) = eps (qform p + symp (s + d) p) := by
      rw [mul_assoc, eb, ← eps_add]
    have qd' : eps (qform p) * eps (symp p e) * eps (symp p d) * eps (symp s p)
        = eps (qform p + symp (s + d + e) p) := by
      rw [mul_assoc, mul_assoc, ← mul_assoc (eps (symp p e)), ec, ← eps_add]
    linear_combination (1/8 : ℂ)*ea - (1/8 : ℂ)*eb - (1/8 : ℂ)*ec + (1/8 : ℂ)*qa
      + (1/8 : ℂ)*qb - (1/8 : ℂ)*qc' - (1/8 : ℂ)*qd'
  simp_rw [hterm, ← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_eps_symp_all, sum_eps_qform_add_symp, ite_eq_right hs0, eq_add_zero_iff]
  have hne_se : s ≠ e := fun h => by rw [h, hqe] at hqs; exact absurd hqs (by decide)
  have hne_sde : s + d ≠ e := by
    intro h
    have hq1 : qform (s + d) = 0 := by rw [qform_add, hqs, hqd, hsd]; simp
    rw [h, hqe] at hq1; exact absurd hq1 (by decide)
  have hq_se : qform (s + e) = 1 := by rw [qform_add, hqs, hqe, hse]; simp
  have hq_sd : qform (s + d) = 0 := by rw [qform_add, hqs, hqd, hsd]; simp
  have hq_sde : qform (s + d + e) = 1 := by
    rw [qform_add, hq_sd, hqe, symp_add_left, hse, hde]; simp
  rw [ite_eq_right hne_se, ite_eq_right hne_sde, hqs, hq_se, hq_sd, hq_sde]
  by_cases h : s = d
  · simp [h]; ring
  · simp [h]

/-- Cases C12 and C15 (`X = Q_c ∩ e⊥`, `q_c(e) = 0`, `q_c(d) = 1`, `⟨d, e⟩ = 0`):
`c_O(s) = (4^N / 8) [s = e] + (eps(q₀(c)) · 2^N / 2)` for `s ∈ H`. -/
theorem charSumOut_C12_C15 {c e d s : Pt N} (hqe : qformShift c e = 0)
    (hqd : qformShift c d = 1) (hde : symp d e = 0)
    (hs0 : s ≠ 0) (hqs : qformShift c s = 0) (hse : symp s e = 0) (hsd : symp s d = 0) :
    charSumOut (outsideOf (perpSet (quadric N c) e) d) s
      = (if s = e then (4 : ℂ) ^ N / 8 else 0) + eps (qform c) * (2 : ℂ) ^ N / 2 := by
  have hO : outsideOf (perpSet (quadric N c) e) d
      = univ.filter (fun p : Pt N => qformShift c p = 0 ∧ symp p e = 0 ∧ symp p d = 1) := by
    ext p
    simp only [outsideOf, perpSet, quadric, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨_, hq⟩, he⟩, hd⟩; exact ⟨hq, he, hd⟩
    · rintro ⟨hq, he, hd⟩
      refine ⟨⟨⟨fun hp => ?_, hq⟩, he⟩, hd⟩
      rw [hp, symp_comm, symp_zero_right] at hd; exact absurd hd (by decide)
  rw [charSumOut, hO, Finset.sum_filter]
  have hterm : ∀ p : Pt N,
      (if qformShift c p = 0 ∧ symp p e = 0 ∧ symp p d = 1 then eps (symp s p) else 0)
        = ((eps (symp s p) + eps (symp (s + e) p) - eps (symp (s + d) p) - eps (symp (s + d + e) p))
          + (eps (qformShift c p + symp s p) + eps (qformShift c p + symp (s + e) p)
             - eps (qformShift c p + symp (s + d) p) - eps (qformShift c p + symp (s + d + e) p))) / 8 := by
    intro p
    have h1 : (if qformShift c p = 0 ∧ symp p e = 0 ∧ symp p d = 1 then eps (symp s p) else 0)
        = (if qformShift c p = 0 then (1 : ℂ) else 0) * (if symp p e = 0 then (1 : ℂ) else 0)
          * (if symp p d = 1 then (1 : ℂ) else 0) * eps (symp s p) := by
      by_cases ha : qformShift c p = 0 <;> by_cases hb : symp p e = 0 <;>
        by_cases hc : symp p d = 1 <;> simp [ha, hb, hc]
    rw [h1, indicator_eq, indicator_eq, indicator_eq_one]
    have ea : eps (symp p e) * eps (symp s p) = eps (symp (s + e) p) := by
      rw [← eps_add, symp_comm p e, add_comm (symp e p), ← symp_add_left]
    have eb : eps (symp p d) * eps (symp s p) = eps (symp (s + d) p) := by
      rw [← eps_add, symp_comm p d, add_comm (symp d p), ← symp_add_left]
    have ec : eps (symp p e) * eps (symp p d) * eps (symp s p) = eps (symp (s + d + e) p) := by
      rw [mul_assoc, eb, ← eps_add, symp_comm p e, add_comm (symp e p), ← symp_add_left]
    have qa : eps (qformShift c p) * eps (symp s p) = eps (qformShift c p + symp s p) := (eps_add _ _).symm
    have qb : eps (qformShift c p) * eps (symp p e) * eps (symp s p)
        = eps (qformShift c p + symp (s + e) p) := by rw [mul_assoc, ea, ← eps_add]
    have qc' : eps (qformShift c p) * eps (symp p d) * eps (symp s p)
        = eps (qformShift c p + symp (s + d) p) := by rw [mul_assoc, eb, ← eps_add]
    have qd' : eps (qformShift c p) * eps (symp p e) * eps (symp p d) * eps (symp s p)
        = eps (qformShift c p + symp (s + d + e) p) := by
      rw [mul_assoc, mul_assoc, ← mul_assoc (eps (symp p e)), ec, ← eps_add]
    linear_combination (1/8 : ℂ)*ea - (1/8 : ℂ)*eb - (1/8 : ℂ)*ec + (1/8 : ℂ)*qa
      + (1/8 : ℂ)*qb - (1/8 : ℂ)*qc' - (1/8 : ℂ)*qd'
  simp_rw [hterm, ← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_eps_symp_all, sum_eps_qshift_symp, ite_eq_right hs0, eq_add_zero_iff]
  have hne_sd : s ≠ d := fun h => by rw [h, hqd] at hqs; exact absurd hqs (by decide)
  have hne_sde : s + d ≠ e := by
    intro h
    have h1 : qformShift c (s + d) = 1 := by rw [qformShift_add, hqs, hqd, hsd]; simp
    rw [h, hqe] at h1; exact absurd h1 (by decide)
  have hq1 : qform (c + s) = qform c := by rw [qform_add_shift, hqs, add_zero]
  have hq2 : qform (c + (s + e)) = qform c := by
    rw [qform_add_shift, qformShift_add, hqs, hqe, hse]; simp
  have hq3 : qform (c + (s + d)) = qform c + 1 := by
    rw [qform_add_shift, qformShift_add, hqs, hqd, hsd]; simp
  have hq4 : qform (c + (s + d + e)) = qform c + 1 := by
    rw [qform_add_shift, qformShift_add, qformShift_add, hqs, hqd, hsd, hqe, symp_add_left,
      hse, hde]
    simp
  rw [ite_eq_right hne_sd, ite_eq_right hne_sde, hq1, hq2, hq3, hq4, eps_add, eps_one]
  by_cases h : s = e <;> simp [h] <;> ring

/-- Case C6 (cone `W ∩ e⊥`): `c_O(s) = (4^N / 4) ([s = e] - [s = d] - [s = e + d])` for `s ∈ H`. -/
theorem charSumOut_C6 {e d s : Pt N} (hs0 : s ≠ 0) :
    charSumOut (outsideOf (perpSet (allPoints N) e) d) s
      = ((4 : ℂ) ^ N / 4) * ((if s = e then (1 : ℂ) else 0)
          - (if s = d then 1 else 0) - (if s = e + d then 1 else 0)) := by
  have hO : outsideOf (perpSet (allPoints N) e) d
      = univ.filter (fun p : Pt N => symp p e = 0 ∧ symp p d = 1) := by
    ext p
    simp only [outsideOf, perpSet, allPoints, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, true_and]
    constructor
    · rintro ⟨⟨_, he⟩, hd⟩; exact ⟨he, hd⟩
    · rintro ⟨he, hd⟩
      refine ⟨⟨fun hp => ?_, he⟩, hd⟩
      rw [hp, symp_comm, symp_zero_right] at hd; exact absurd hd (by decide)
  rw [charSumOut, hO, Finset.sum_filter]
  have hterm : ∀ p : Pt N,
      (if symp p e = 0 ∧ symp p d = 1 then eps (symp s p) else 0)
        = (eps (symp s p) + eps (symp (s + e) p) - eps (symp (s + d) p)
            - eps (symp (s + (e + d)) p)) / 4 := by
    intro p
    have h1 : (if symp p e = 0 ∧ symp p d = 1 then eps (symp s p) else 0)
        = (if symp p e = 0 then (1 : ℂ) else 0) * (if symp p d = 1 then (1 : ℂ) else 0)
          * eps (symp s p) := by
      by_cases ha : symp p e = 0 <;> by_cases hb : symp p d = 1 <;> simp [ha, hb]
    rw [h1, indicator_eq, indicator_eq_one]
    have ea : eps (symp p e) * eps (symp s p) = eps (symp (s + e) p) := by
      rw [← eps_add, symp_comm p e, add_comm (symp e p), ← symp_add_left]
    have eb : eps (symp p d) * eps (symp s p) = eps (symp (s + d) p) := by
      rw [← eps_add, symp_comm p d, add_comm (symp d p), ← symp_add_left]
    have ec : eps (symp p e) * eps (symp p d) * eps (symp s p) = eps (symp (s + (e + d)) p) := by
      rw [mul_assoc, eb, ← eps_add, symp_comm p e, add_comm (symp e p), ← symp_add_left]
      congr 2; abel
    linear_combination (1/4 : ℂ)*ea - (1/4 : ℂ)*eb - (1/4 : ℂ)*ec
  simp_rw [hterm, ← Finset.sum_div]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_eps_symp_all, ite_eq_right hs0, eq_add_zero_iff]
  have hite : ∀ (P : Prop) [Decidable P],
      (if P then (4 : ℂ) ^ N else 0) = (if P then (1 : ℂ) else 0) * (4 : ℂ) ^ N := fun P _ => by
    split_ifs <;> ring
  simp_rw [hite]
  ring

/-- Cases C11 and C14 (cones `Q_c ∩ e⊥`, `q_c(e) = q_c(d) = 0`, `⟨d, e⟩ = 0`):
`c_O(s) = (4^N / 8) ([s = e] - [s = d] - [s = e + d])` for `s ∈ H`. -/
theorem charSumOut_C11_C14 {c e d s : Pt N} (hqe : qformShift c e = 0)
    (hqd : qformShift c d = 0) (hde : symp d e = 0)
    (hs0 : s ≠ 0) (hqs : qformShift c s = 0) (hse : symp s e = 0) (hsd : symp s d = 0) :
    charSumOut (outsideOf (perpSet (quadric N c) e) d) s
      = ((4 : ℂ) ^ N / 8) * ((if s = e then (1 : ℂ) else 0)
          - (if s = d then 1 else 0) - (if s = e + d then 1 else 0)) := by
  have hO : outsideOf (perpSet (quadric N c) e) d
      = univ.filter (fun p : Pt N => qformShift c p = 0 ∧ symp p e = 0 ∧ symp p d = 1) := by
    ext p
    simp only [outsideOf, perpSet, quadric, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨_, hq⟩, he⟩, hd⟩; exact ⟨hq, he, hd⟩
    · rintro ⟨hq, he, hd⟩
      refine ⟨⟨⟨fun hp => ?_, hq⟩, he⟩, hd⟩
      rw [hp, symp_comm, symp_zero_right] at hd; exact absurd hd (by decide)
  rw [charSumOut, hO, Finset.sum_filter]
  have hterm : ∀ p : Pt N,
      (if qformShift c p = 0 ∧ symp p e = 0 ∧ symp p d = 1 then eps (symp s p) else 0)
        = ((eps (symp s p) + eps (symp (s + e) p) - eps (symp (s + d) p) - eps (symp (s + (e + d)) p))
          + (eps (qformShift c p + symp s p) + eps (qformShift c p + symp (s + e) p)
             - eps (qformShift c p + symp (s + d) p) - eps (qformShift c p + symp (s + (e + d)) p))) / 8 := by
    intro p
    have h1 : (if qformShift c p = 0 ∧ symp p e = 0 ∧ symp p d = 1 then eps (symp s p) else 0)
        = (if qformShift c p = 0 then (1 : ℂ) else 0) * (if symp p e = 0 then (1 : ℂ) else 0)
          * (if symp p d = 1 then (1 : ℂ) else 0) * eps (symp s p) := by
      by_cases ha : qformShift c p = 0 <;> by_cases hb : symp p e = 0 <;>
        by_cases hc : symp p d = 1 <;> simp [ha, hb, hc]
    rw [h1, indicator_eq, indicator_eq, indicator_eq_one]
    have ea : eps (symp p e) * eps (symp s p) = eps (symp (s + e) p) := by
      rw [← eps_add, symp_comm p e, add_comm (symp e p), ← symp_add_left]
    have eb : eps (symp p d) * eps (symp s p) = eps (symp (s + d) p) := by
      rw [← eps_add, symp_comm p d, add_comm (symp d p), ← symp_add_left]
    have ec : eps (symp p e) * eps (symp p d) * eps (symp s p) = eps (symp (s + (e + d)) p) := by
      rw [mul_assoc, eb, ← eps_add, symp_comm p e, add_comm (symp e p), ← symp_add_left]
      congr 2; abel
    have qa : eps (qformShift c p) * eps (symp s p) = eps (qformShift c p + symp s p) := (eps_add _ _).symm
    have qb : eps (qformShift c p) * eps (symp p e) * eps (symp s p)
        = eps (qformShift c p + symp (s + e) p) := by rw [mul_assoc, ea, ← eps_add]
    have qc' : eps (qformShift c p) * eps (symp p d) * eps (symp s p)
        = eps (qformShift c p + symp (s + d) p) := by rw [mul_assoc, eb, ← eps_add]
    have qd' : eps (qformShift c p) * eps (symp p e) * eps (symp p d) * eps (symp s p)
        = eps (qformShift c p + symp (s + (e + d)) p) := by
      rw [mul_assoc, mul_assoc, ← mul_assoc (eps (symp p e)), ec, ← eps_add]
    linear_combination (1/8 : ℂ)*ea - (1/8 : ℂ)*eb - (1/8 : ℂ)*ec + (1/8 : ℂ)*qa
      + (1/8 : ℂ)*qb - (1/8 : ℂ)*qc' - (1/8 : ℂ)*qd'
  simp_rw [hterm, ← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_eps_symp_all, sum_eps_qshift_symp, ite_eq_right hs0, eq_add_zero_iff]
  have hq1 : qform (c + s) = qform c := by rw [qform_add_shift, hqs, add_zero]
  have hq2 : qform (c + (s + e)) = qform c := by
    rw [qform_add_shift, qformShift_add, hqs, hqe, hse]; simp
  have hq3 : qform (c + (s + d)) = qform c := by
    rw [qform_add_shift, qformShift_add, hqs, hqd, hsd]; simp
  have hq4 : qform (c + (s + (e + d))) = qform c := by
    rw [qform_add_shift, qformShift_add, qformShift_add, hqs, hqe, hqd, symp_comm e d, hde,
      symp_add_right, hse, hsd]; simp
  rw [hq1, hq2, hq3, hq4]
  have hite : ∀ (P : Prop) [Decidable P],
      (if P then (4 : ℂ) ^ N else 0) = (if P then (1 : ℂ) else 0) * (4 : ℂ) ^ N := fun P _ => by
    split_ifs <;> ring
  simp_rw [hite]
  ring

end CharacterSums

/-! ### Part 3. Master completion-separation criteria -/

section Separation

variable {N : ℕ}

lemma sum_sigma_trace_opA_sq (H : Finset (Pt N)) (σ : Pt N → ℝ) :
    ∑ s ∈ H, ((σ s : ℝ) : ℂ) * (opA H σ ^ 2 * pauli s).trace = (opA H σ ^ 3).trace := by
  have h3 : opA H σ ^ 3 = opA H σ ^ 2 * ∑ s ∈ H, ((σ s : ℝ) : ℂ) • pauli s := by
    rw [pow_succ]; rfl
  rw [h3, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- **Master separation criterion for single-vertex cases (C1, C3, C5, C8, C12, C15).**
Whenever `c_O(s) = α [s = z] + β` on `H` with `z ∈ H` and `α ≠ 0`, two cospectral carriers
`σ, τ` with `σ z = 1 = τ z` and `tr(A_σ² P_z) ≠ tr(A_τ² P_z)` have non-cospectral completions. -/
theorem completion_charpoly_ne_of_trace_sq_ne {X : Finset (Pt N)} (hX : IsClosedCfg X) (d z : Pt N)
    (hz : z ∈ sectionOf X d) (α β : ℂ) (hα : α ≠ 0)
    (hcO : ∀ s ∈ sectionOf X d, charSumOut (outsideOf X d) s = (if s = z then α else 0) + β)
    {σ τ : Pt N → ℝ} (hσz : σ z = 1) (hτz : τ z = 1)
    (hcpA : (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly)
    (htr_ne : (opA (sectionOf X d) σ ^ 2 * pauli z).trace
        ≠ (opA (sectionOf X d) τ ^ 2 * pauli z).trace) :
    (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  intro hcpL
  have htrL : (completionMat X d σ ^ 3).trace = (completionMat X d τ ^ 3).trace :=
    trace_pow_eq_of_charpoly_eq_real (completionMat_transpose X d σ)
      (completionMat_transpose X d τ) hcpL 3
  have htrA : (opA (sectionOf X d) σ ^ 3).trace = (opA (sectionOf X d) τ ^ 3).trace :=
    trace_pow_eq_of_charpoly_eq_complex (opA_isHermitian _ _) (opA_isHermitian _ _) hcpA 3
  have heval : ∀ f : Pt N → ℝ, f z = 1 →
      ∑ s ∈ sectionOf X d, ((f s : ℝ) : ℂ) * charSumOut (outsideOf X d) s
          * (opA (sectionOf X d) f ^ 2 * pauli s).trace
        = α * (opA (sectionOf X d) f ^ 2 * pauli z).trace + β * (opA (sectionOf X d) f ^ 3).trace := by
    intro f hfz
    have hsplit : ∀ s ∈ sectionOf X d,
        ((f s : ℝ) : ℂ) * charSumOut (outsideOf X d) s * (opA (sectionOf X d) f ^ 2 * pauli s).trace
          = (if s = z then α * (opA (sectionOf X d) f ^ 2 * pauli z).trace else 0)
            + β * (((f s : ℝ) : ℂ) * (opA (sectionOf X d) f ^ 2 * pauli s).trace) := by
      intro s hs
      rw [hcO s hs]
      by_cases hsz : s = z
      · subst hsz; simp [hfz]; ring
      · simp [hsz]; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left hz,
      ← Finset.mul_sum, sum_sigma_trace_opA_sq]
  have u1 := trace_completion_cube_universal hX d σ
  have u2 := trace_completion_cube_universal hX d τ
  rw [heval σ hσz] at u1
  rw [heval τ hτz] at u2
  rw [htrL, htrA] at u1
  have hdiff : 6 * α * ((opA (sectionOf X d) σ ^ 2 * pauli z).trace
      - (opA (sectionOf X d) τ ^ 2 * pauli z).trace) = 0 := by
    linear_combination u2 - u1
  have h6α : (6 : ℂ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  exact htr_ne (sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left h6α))

/-- **Master separation criterion for cone cases (C6, C11, C14).** -/
theorem completion_charpoly_ne_of_cone_diff {X : Finset (Pt N)} (hX : IsClosedCfg X) (e d : Pt N)
    (he : e ∈ sectionOf X d) (hd : d ∈ sectionOf X d) (hed : e + d ∈ sectionOf X d)
    (hed_ne : e ≠ d) (he0 : e ≠ 0) (hd0 : d ≠ 0)
    (α : ℂ) (hα : α ≠ 0)
    (hcO : ∀ s ∈ sectionOf X d, charSumOut (outsideOf X d) s
        = α * ((if s = e then (1 : ℂ) else 0) - (if s = d then 1 else 0)
            - (if s = e + d then 1 else 0)))
    {σ τ : Pt N → ℝ}
    (hσe : σ e = 1) (hσd : σ d = 1) (hσed : σ (e + d) = 1)
    (hτe : τ e = 1) (hτd : τ d = 1) (hτed : τ (e + d) = 1)
    (hcpA : (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly)
    (htr_ne : ((opA (sectionOf X d) σ ^ 2 * pauli e).trace
          - (opA (sectionOf X d) σ ^ 2 * pauli d).trace
          - (opA (sectionOf X d) σ ^ 2 * pauli (e + d)).trace)
        ≠ ((opA (sectionOf X d) τ ^ 2 * pauli e).trace
          - (opA (sectionOf X d) τ ^ 2 * pauli d).trace
          - (opA (sectionOf X d) τ ^ 2 * pauli (e + d)).trace)) :
    (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  intro hcpL
  have htrL : (completionMat X d σ ^ 3).trace = (completionMat X d τ ^ 3).trace :=
    trace_pow_eq_of_charpoly_eq_real (completionMat_transpose X d σ)
      (completionMat_transpose X d τ) hcpL 3
  have htrA : (opA (sectionOf X d) σ ^ 3).trace = (opA (sectionOf X d) τ ^ 3).trace :=
    trace_pow_eq_of_charpoly_eq_complex (opA_isHermitian _ _) (opA_isHermitian _ _) hcpA 3
  have heval : ∀ f : Pt N → ℝ, f e = 1 → f d = 1 → f (e + d) = 1 →
      ∑ s ∈ sectionOf X d, ((f s : ℝ) : ℂ) * charSumOut (outsideOf X d) s
          * (opA (sectionOf X d) f ^ 2 * pauli s).trace
        = α * ((opA (sectionOf X d) f ^ 2 * pauli e).trace
            - (opA (sectionOf X d) f ^ 2 * pauli d).trace
            - (opA (sectionOf X d) f ^ 2 * pauli (e + d)).trace) := by
    intro f hfe hfd hfed
    have hsplit : ∀ s ∈ sectionOf X d,
        ((f s : ℝ) : ℂ) * charSumOut (outsideOf X d) s * (opA (sectionOf X d) f ^ 2 * pauli s).trace
          = α * ((if s = e then (opA (sectionOf X d) f ^ 2 * pauli e).trace else 0)
              - (if s = d then (opA (sectionOf X d) f ^ 2 * pauli d).trace else 0)
              - (if s = e + d then (opA (sectionOf X d) f ^ 2 * pauli (e + d)).trace else 0)) := by
      intro s hs
      rw [hcO s hs]
      have hne1 : e ≠ e + d := fun h => hd0 (by
        calc d = (e + e) + d := by rw [pt_add_self, zero_add]
          _ = e + (e + d) := by abel
          _ = e + e := by rw [← h]
          _ = 0 := pt_add_self e)
      have hne2 : d ≠ e + d := fun h => he0 (by
        calc e = e + (d + d) := by rw [pt_add_self, add_zero]
          _ = (e + d) + d := by abel
          _ = d + d := by rw [← h]
          _ = 0 := pt_add_self d)
      by_cases h1 : s = e
      · subst h1; simp [hfe, hed_ne, hne1]
      · by_cases h2 : s = d
        · subst h2; simp [hfd, h1, hne2]
        · by_cases h3 : s = e + d
          · subst h3; simp [hfed, h1, h2]
          · simp [h1, h2, h3]
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq',
      ite_eq_left he, ite_eq_left hd, ite_eq_left hed]
  have u1 := trace_completion_cube_universal hX d σ
  have u2 := trace_completion_cube_universal hX d τ
  rw [heval σ hσe hσd hσed] at u1
  rw [heval τ hτe hτd hτed] at u2
  rw [htrL, htrA] at u1
  have hdiff : 6 * α * (((opA (sectionOf X d) σ ^ 2 * pauli e).trace
        - (opA (sectionOf X d) σ ^ 2 * pauli d).trace
        - (opA (sectionOf X d) σ ^ 2 * pauli (e + d)).trace)
      - ((opA (sectionOf X d) τ ^ 2 * pauli e).trace
        - (opA (sectionOf X d) τ ^ 2 * pauli d).trace
        - (opA (sectionOf X d) τ ^ 2 * pauli (e + d)).trace)) = 0 := by
    linear_combination u2 - u1
  have h6α : (6 : ℂ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  exact htr_ne (sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left h6α))

end Separation

/-! ### Part 4. Unified Pair-Swap Proof of Cone Cases C6, C11, and C14 -/

section ConePairSwap

/-- Predicate: `u` is supported purely on qubits `0, 1` (i.e., belongs to `{0, e, d, e+d}`). -/
def isConeVert {N : ℕ} (hN : 2 ≤ N) (u : Pt N) : Prop :=
  ∀ i : Fin N, i ≠ ⟨0, by omega⟩ → i ≠ ⟨1, by omega⟩ → u.1 i = 0 ∧ u.2 i = 0

instance {N : ℕ} (hN : 2 ≤ N) (u : Pt N) : Decidable (isConeVert hN u) :=
  inferInstanceAs (Decidable (∀ _i : Fin N, _))

/-- First pair-swap carrier `σ`: `+1` on `{e, d, e+d}` and `(-1)^{z₀ + z₁}` on base points. -/
def coneSigma {N : ℕ} (hN : 2 ≤ N) (u : Pt N) : ℝ :=
  if isConeVert hN u then 1
  else if u.2 ⟨0, by omega⟩ + u.2 ⟨1, by omega⟩ = 0 then 1 else -1

/-- Second pair-swap carrier `τ`: `+1` on `{e, d, e+d}` and `(-1)^{z₁}` on base points. -/
def coneTau {N : ℕ} (hN : 2 ≤ N) (u : Pt N) : ℝ :=
  if isConeVert hN u then 1
  else if u.2 ⟨1, by omega⟩ = 0 then 1 else -1

lemma coneSigma_eq_one_or {N : ℕ} (hN : 2 ≤ N) (u : Pt N) :
    coneSigma hN u = 1 ∨ coneSigma hN u = -1 := by
  unfold coneSigma; split_ifs <;> tauto

lemma coneTau_eq_one_or {N : ℕ} (hN : 2 ≤ N) (u : Pt N) :
    coneTau hN u = 1 ∨ coneTau hN u = -1 := by
  unfold coneTau; split_ifs <;> tauto

/-- CNOT permutation on `Vec N`: flips bit `0` when bit `1` is `1`. -/
def cnotVec {N : ℕ} (hN : 2 ≤ N) (x : Vec N) : Vec N :=
  fun i => if i = ⟨0, by omega⟩ then x ⟨0, by omega⟩ + x ⟨1, by omega⟩ else x i

lemma cnotVec_invol {N : ℕ} (hN : 2 ≤ N) (x : Vec N) : cnotVec hN (cnotVec hN x) = x := by
  funext i
  have h10 : (⟨1, by omega⟩ : Fin N) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  unfold cnotVec
  by_cases hi : i = ⟨0, by omega⟩
  · subst hi; simp [h10, add_assoc, zmod2_add_self]
  · simp [hi]

/-- Involutive CNOT equivalence on `Vec N` (`N ≥ 2`). -/
def cnotEquiv {N : ℕ} (hN : 2 ≤ N) : Vec N ≃ Vec N :=
  ⟨cnotVec hN, cnotVec hN, cnotVec_invol hN, cnotVec_invol hN⟩

/-- Dual CNOT action on Pauli labels: adds `z₀` into `z₁` (leaves `x` and all other qubits fixed). -/
def cnotPt {N : ℕ} (hN : 2 ≤ N) (u : Pt N) : Pt N :=
  (u.1, fun i => if i = ⟨1, by omega⟩ then u.2 ⟨0, by omega⟩ + u.2 ⟨1, by omega⟩ else u.2 i)

lemma cnotPt_invol {N : ℕ} (hN : 2 ≤ N) (u : Pt N) : cnotPt hN (cnotPt hN u) = u := by
  ext i
  · rfl
  · have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    unfold cnotPt
    by_cases hi : i = ⟨1, by omega⟩
    · subst hi; simp [h01, ← add_assoc, zmod2_add_self]
    · simp [hi]

lemma reindex_cnot_pauli {N : ℕ} (hN : 2 ≤ N) {u : Pt N}
    (hu0 : u.1 ⟨0, by omega⟩ = 0) (hu1 : u.1 ⟨1, by omega⟩ = 0) :
    Matrix.reindex (cnotEquiv hN) (cnotEquiv hN) (pauli u) = pauli (cnotPt hN u) := by
  have hy : ycount (cnotPt hN u) = ycount u := by
    unfold ycount
    congr 1; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change u.1 i = 1 ∧ (cnotPt hN u).2 i = 1 ↔ u.1 i = 1 ∧ u.2 i = 1
    by_cases hi : i = ⟨1, by omega⟩
    · subst hi
      have h01 : (0 : ZMod 2) ≠ 1 := by decide
      simp [hu1, h01]
    · simp [cnotPt, hi]
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, cnotEquiv, Equiv.coe_fn_symm_mk,
    pauli, Matrix.smul_apply, smul_eq_mul, hy, weyl]
  congr 1
  have hadd : cnotVec hN y + u.1 = cnotVec hN (y + u.1) := by
    funext i
    unfold cnotVec
    by_cases hi : i = ⟨0, by omega⟩
    · subst hi; simp [hu0, hu1]
    · simp [hi]
  have hiff : cnotVec hN x = cnotVec hN y + u.1 ↔ x = y + u.1 := by
    rw [hadd]
    exact ⟨fun h => by simpa [cnotVec_invol] using congrArg (cnotVec hN) h, fun h => by rw [h]⟩
  have hdot : u.2 ⬝ᵥ cnotVec hN y = (cnotPt hN u).2 ⬝ᵥ y := by
    have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    simp only [dotProduct, cnotVec, cnotPt]
    have hsplit : ∀ f : Fin N → ZMod 2,
        ∑ i : Fin N, f i = f ⟨0, by omega⟩ + f ⟨1, by omega⟩
          + ∑ i ∈ (univ.erase ⟨0, by omega⟩).erase ⟨1, by omega⟩, f i := by
      intro f
      have h1 : (⟨1, by omega⟩ : Fin N) ∈ univ.erase ⟨0, by omega⟩ :=
        Finset.mem_erase.mpr ⟨h01.symm, mem_univ _⟩
      rw [← Finset.add_sum_erase _ f (mem_univ ⟨0, by omega⟩),
        ← Finset.add_sum_erase _ f h1]
      ring
    rw [hsplit, hsplit]
    have hrest : ∑ i ∈ (univ.erase ⟨0, by omega⟩).erase ⟨1, by omega⟩,
          u.2 i * (if i = ⟨0, by omega⟩ then y ⟨0, by omega⟩ + y ⟨1, by omega⟩ else y i)
        = ∑ i ∈ (univ.erase ⟨0, by omega⟩).erase ⟨1, by omega⟩,
          (if i = ⟨1, by omega⟩ then u.2 ⟨0, by omega⟩ + u.2 ⟨1, by omega⟩ else u.2 i) * y i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi1 : i ≠ ⟨1, by omega⟩ := Finset.ne_of_mem_erase hi
      have hi0 : i ≠ ⟨0, by omega⟩ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      simp [hi0, hi1]
    rw [hrest]
    simp only [↓reduceIte, h01, h01.symm]
    ring
  change (if cnotVec hN x = cnotVec hN y + u.1 then chi u.2 (cnotVec hN y) else 0)
      = if x = y + u.1 then chi (cnotPt hN u).2 y else 0
  by_cases h : x = y + u.1
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
    unfold chi; rw [hdot]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]

lemma coneSigma_eq_coneTau_cnot {N : ℕ} (hN : 2 ≤ N) (u : Pt N) :
    coneSigma hN u = coneTau hN (cnotPt hN u) := by
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hvert : isConeVert hN (cnotPt hN u) ↔ isConeVert hN u := by
    unfold isConeVert cnotPt
    constructor <;> intro h i hi0 hi1 <;> simpa [hi1] using h i hi0 hi1
  unfold coneSigma coneTau
  by_cases hv : isConeVert hN u
  · rw [ite_eq_left hv, ite_eq_left (hvert.mpr hv)]
  · rw [ite_eq_right hv, ite_eq_right (fun h => hv (hvert.mp h))]
    simp [cnotPt]

/-- Unified pair-swap theorem covering C6, C11, and C14 simultaneously. -/
theorem cone_pair_swap_strict_law_fails {N : ℕ} (hN : 2 ≤ N)
    (X : Finset (Pt N)) (hX : IsClosedCfg X)
    (hX_e : ∀ u ∈ X, symp u (ptZ ⟨0, by omega⟩) = 0)
    (hX_cnot : ∀ u ∈ sectionOf X (ptZ ⟨1, by omega⟩), cnotPt hN u ∈ sectionOf X (ptZ ⟨1, by omega⟩))
    (he_mem : ptZ ⟨0, by omega⟩ ∈ sectionOf X (ptZ ⟨1, by omega⟩))
    (hd_mem : ptZ ⟨1, by omega⟩ ∈ sectionOf X (ptZ ⟨1, by omega⟩))
    (hed_mem : ptZ ⟨0, by omega⟩ + ptZ ⟨1, by omega⟩ ∈ sectionOf X (ptZ ⟨1, by omega⟩))
    (hbase : ∃ u₀ ∈ sectionOf X (ptZ ⟨1, by omega⟩), ¬ isConeVert hN u₀)
    (α : ℂ) (hα : α ≠ 0)
    (hcO : ∀ s ∈ sectionOf X (ptZ ⟨1, by omega⟩),
        charSumOut (outsideOf X (ptZ ⟨1, by omega⟩)) s
          = α * ((if s = ptZ ⟨0, by omega⟩ then (1 : ℂ) else 0)
              - (if s = ptZ ⟨1, by omega⟩ then 1 else 0)
              - (if s = ptZ ⟨0, by omega⟩ + ptZ ⟨1, by omega⟩ then 1 else 0))) :
    ∃ σ τ : Pt N → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X (ptZ ⟨1, by omega⟩)) σ).charpoly
        = (opA (sectionOf X (ptZ ⟨1, by omega⟩)) τ).charpoly ∧
      (completionMat X (ptZ ⟨1, by omega⟩) σ).charpoly
        ≠ (completionMat X (ptZ ⟨1, by omega⟩) τ).charpoly := by
  set e : Pt N := ptZ ⟨0, by omega⟩
  set d : Pt N := ptZ ⟨1, by omega⟩
  set H : Finset (Pt N) := sectionOf X d
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hed_ne : e ≠ d := ptZ_ne_ptZ h01
  have hre_opA : Matrix.reindex (cnotEquiv hN) (cnotEquiv hN) (opA H (coneSigma hN))
      = opA H (coneTau hN) := by
    have hsum : Matrix.reindex (cnotEquiv hN) (cnotEquiv hN) (opA H (coneSigma hN))
        = ∑ u ∈ H, ((coneSigma hN u : ℝ) : ℂ) •
            Matrix.reindex (cnotEquiv hN) (cnotEquiv hN) (pauli u) := by
      ext x y
      simp [Matrix.reindex_apply, opA, Matrix.sum_apply, Matrix.smul_apply]
    rw [hsum]
    unfold opA
    refine Finset.sum_nbij' (cnotPt hN) (cnotPt hN)
      (fun u hu => hX_cnot u hu) (fun u hu => hX_cnot u hu)
      (fun u _ => cnotPt_invol hN u) (fun u _ => cnotPt_invol hN u) ?_
    intro u hu
    have huX : u ∈ X := (Finset.mem_filter.mp hu).1
    have hu0 : u.1 ⟨0, by omega⟩ = 0 := by simpa [symp_ptZ, e] using hX_e u huX
    have hu1 : u.1 ⟨1, by omega⟩ = 0 := by simpa [symp_ptZ, d] using (Finset.mem_filter.mp hu).2
    rw [reindex_cnot_pauli hN hu0 hu1, coneSigma_eq_coneTau_cnot hN u]
  have hcpA : (opA H (coneSigma hN)).charpoly = (opA H (coneTau hN)).charpoly := by
    rw [← hre_opA, Matrix.charpoly_reindex]
  refine ⟨coneSigma hN, coneTau hN, coneSigma_eq_one_or hN, coneTau_eq_one_or hN, hcpA, ?_⟩
  · -- Unequal completion charpoly via master cone criterion.
    have hvert_e : isConeVert hN e := fun i hi0 _ => by simp [e, ptZ, hi0]
    have hvert_d : isConeVert hN d := fun i _ hi1 => by simp [d, ptZ, hi1]
    have hvert_ed : isConeVert hN (e + d) := fun i hi0 hi1 => by simp [e, d, ptZ, hi0, hi1]
    have hσe : coneSigma hN e = 1 := by simp [coneSigma, hvert_e]
    have hσd : coneSigma hN d = 1 := by simp [coneSigma, hvert_d]
    have hσed : coneSigma hN (e + d) = 1 := by simp [coneSigma, hvert_ed]
    have hτe : coneTau hN e = 1 := by simp [coneTau, hvert_e]
    have hτd : coneTau hN d = 1 := by simp [coneTau, hvert_d]
    have hτed : coneTau hN (e + d) = 1 := by simp [coneTau, hvert_ed]
    apply completion_charpoly_ne_of_cone_diff hX e d he_mem hd_mem hed_mem hed_ne
      (ptZ_ne_zero _) (ptZ_ne_zero _) α hα hcO hσe hσd hσed hτe hτd hτed hcpA
    -- Compute `tr(A_σ² P_z) - tr(A_τ² P_z)` for `z ∈ {e, d, e + d}`.
    have hcomm_e : ∀ u ∈ H, symp u e = 0 := fun u hu => hX_e u (Finset.mem_filter.mp hu).1
    have hcomm_d : ∀ u ∈ H, symp u d = 0 := fun u hu => (Finset.mem_filter.mp hu).2
    have hcomm_ed : ∀ u ∈ H, symp u (e + d) = 0 := fun u hu => by
      rw [symp_add_right, hcomm_e u hu, hcomm_d u hu, add_zero]
    have hed0 : e + d ≠ 0 := fun h => hed_ne (pt_eq_of_add_eq_zero h)
    rw [trace_opA_sq_mul_central (coneSigma hN) (ptZ_ne_zero _) hcomm_e,
      trace_opA_sq_mul_central (coneSigma hN) (ptZ_ne_zero _) hcomm_d,
      trace_opA_sq_mul_central (coneSigma hN) hed0 hcomm_ed,
      trace_opA_sq_mul_central (coneTau hN) (ptZ_ne_zero _) hcomm_e,
      trace_opA_sq_mul_central (coneTau hN) (ptZ_ne_zero _) hcomm_d,
      trace_opA_sq_mul_central (coneTau hN) hed0 hcomm_ed]
    have htau_e : ∀ u ∈ H, tau u (u + e) = 1 := fun u hu =>
      tau_add_ptZ (by simpa [symp_ptZ, e] using hcomm_e u hu)
    have htau_d : ∀ u ∈ H, tau u (u + d) = 1 := fun u hu =>
      tau_add_ptZ (by simpa [symp_ptZ, d] using hcomm_d u hu)
    have htau_ed : ∀ u ∈ H, tau u (u + (e + d)) = 1 := fun u hu =>
      tau_add_ptZ_add_ptZ (by simpa [symp_ptZ, e] using hcomm_e u hu)
        (by simpa [symp_ptZ, d] using hcomm_d u hu)
    -- Every base point `u ∈ H` with `¬ isConeVert hN u` satisfies `u + z ∈ H` for `z ∈ {e, d, e+d}`.
    have hH_closed : IsClosedCfg H := isClosedCfg_perpSet hX d
    have hvert_shift : ∀ (u z : Pt N), isConeVert hN z → (isConeVert hN (u + z) ↔ isConeVert hN u) := by
      intro u z hz
      unfold isConeVert
      constructor <;> intro h i hi0 hi1
      · have h1 := h i hi0 hi1; have h2 := hz i hi0 hi1
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, h2.1, h2.2, add_zero] at h1
        exact h1
      · have h1 := h i hi0 hi1; have h2 := hz i hi0 hi1
        exact ⟨by simp [h1.1, h2.1], by simp [h1.2, h2.2]⟩
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    -- Compute difference on `d`: `0`!
    have hdiff_d :
        (∑ u ∈ H.filter (fun u => u + d ∈ H),
            ((coneSigma hN u : ℝ) : ℂ) * ((coneSigma hN (u + d) : ℝ) : ℂ) * tau u (u + d))
        = (∑ u ∈ H.filter (fun u => u + d ∈ H),
            ((coneTau hN u : ℝ) : ℂ) * ((coneTau hN (u + d) : ℝ) : ℂ) * tau u (u + d)) := by
      refine Finset.sum_congr rfl fun u hu => ?_
      have huH : u ∈ H := (Finset.mem_filter.mp hu).1
      rw [htau_d u huH, mul_one, mul_one]
      have hvs := hvert_shift u d hvert_d
      unfold coneSigma coneTau
      by_cases hv : isConeVert hN u
      · simp [hv, hvs.mpr hv]
      · have hv' : ¬ isConeVert hN (u + d) := fun h => hv (hvs.mp h)
        have h1 : (u + d).2 ⟨0, by omega⟩ = u.2 ⟨0, by omega⟩ := by simp [d, ptZ, h01]
        have h2 : (u + d).2 ⟨1, by omega⟩ = u.2 ⟨1, by omega⟩ + 1 := by simp [d, ptZ]
        simp only [hv, hv', ↓reduceIte, h1, h2]
        rcases zmod2_cases (u.2 ⟨0, by omega⟩) with a | a <;>
          rcases zmod2_cases (u.2 ⟨1, by omega⟩) with b | b <;>
          simp [a, b, h11, h10]
    -- For `e`: on vertices both give `1`; on base points `σ` gives `-1` and `τ` gives `+1`.
    have hdiff_e :
        (∑ u ∈ H.filter (fun u => u + e ∈ H),
            ((coneSigma hN u : ℝ) : ℂ) * ((coneSigma hN (u + e) : ℝ) : ℂ) * tau u (u + e))
        - (∑ u ∈ H.filter (fun u => u + e ∈ H),
            ((coneTau hN u : ℝ) : ℂ) * ((coneTau hN (u + e) : ℝ) : ℂ) * tau u (u + e))
        = -2 * (((H.filter (fun u => ¬ isConeVert hN u)).card : ℕ) : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ u ∈ H.filter (fun u => u + e ∈ H),
          ((coneSigma hN u : ℝ) : ℂ) * ((coneSigma hN (u + e) : ℝ) : ℂ) * tau u (u + e)
            - ((coneTau hN u : ℝ) : ℂ) * ((coneTau hN (u + e) : ℝ) : ℂ) * tau u (u + e)
          = if ¬ isConeVert hN u then (-2 : ℂ) else 0 := by
        intro u hu
        have huH : u ∈ H := (Finset.mem_filter.mp hu).1
        rw [htau_e u huH, mul_one, mul_one]
        have hvs := hvert_shift u e hvert_e
        unfold coneSigma coneTau
        by_cases hv : isConeVert hN u
        · simp [hv, hvs.mpr hv]
        · have hv' : ¬ isConeVert hN (u + e) := fun h => hv (hvs.mp h)
          have h1 : (u + e).2 ⟨0, by omega⟩ = u.2 ⟨0, by omega⟩ + 1 := by simp [e, ptZ]
          have h2 : (u + e).2 ⟨1, by omega⟩ = u.2 ⟨1, by omega⟩ := by simp [e, ptZ, h01.symm]
          simp only [hv, hv', not_false_eq_true, ↓reduceIte, h1, h2]
          rcases zmod2_cases (u.2 ⟨0, by omega⟩) with a | a <;>
            rcases zmod2_cases (u.2 ⟨1, by omega⟩) with b | b <;>
            simp [a, b, h11, h10] <;> norm_num
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hfilt : (H.filter (fun u => u + e ∈ H)).filter (fun u => ¬ isConeVert hN u)
          = H.filter (fun u => ¬ isConeVert hN u) := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨huH, _⟩, hv⟩; exact ⟨huH, hv⟩
        · rintro ⟨huH, hv⟩
          refine ⟨⟨huH, ?_⟩, hv⟩
          have hne : u ≠ e := fun h => hv (h ▸ hvert_e)
          exact hH_closed.2 u huH e he_mem hne (hcomm_e u huH)
      rw [hfilt]; ring
    -- For `e + d`: on vertices both give `1`; on base points `σ` gives `+1` and `τ` gives `-1`.
    have hdiff_ed :
        (∑ u ∈ H.filter (fun u => u + (e + d) ∈ H),
            ((coneSigma hN u : ℝ) : ℂ) * ((coneSigma hN (u + (e + d)) : ℝ) : ℂ) * tau u (u + (e + d)))
        - (∑ u ∈ H.filter (fun u => u + (e + d) ∈ H),
            ((coneTau hN u : ℝ) : ℂ) * ((coneTau hN (u + (e + d)) : ℝ) : ℂ) * tau u (u + (e + d)))
        = 2 * (((H.filter (fun u => ¬ isConeVert hN u)).card : ℕ) : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ u ∈ H.filter (fun u => u + (e + d) ∈ H),
          ((coneSigma hN u : ℝ) : ℂ) * ((coneSigma hN (u + (e + d)) : ℝ) : ℂ) * tau u (u + (e + d))
            - ((coneTau hN u : ℝ) : ℂ) * ((coneTau hN (u + (e + d)) : ℝ) : ℂ) * tau u (u + (e + d))
          = if ¬ isConeVert hN u then (2 : ℂ) else 0 := by
        intro u hu
        have huH : u ∈ H := (Finset.mem_filter.mp hu).1
        rw [htau_ed u huH, mul_one, mul_one]
        have hvs := hvert_shift u (e + d) hvert_ed
        unfold coneSigma coneTau
        by_cases hv : isConeVert hN u
        · simp [hv, hvs.mpr hv]
        · have hv' : ¬ isConeVert hN (u + (e + d)) := fun h => hv (hvs.mp h)
          have h1 : (u + (e + d)).2 ⟨0, by omega⟩ = u.2 ⟨0, by omega⟩ + 1 := by simp [e, d, ptZ, h01]
          have h2 : (u + (e + d)).2 ⟨1, by omega⟩ = u.2 ⟨1, by omega⟩ + 1 := by simp [e, d, ptZ, h01.symm]
          simp only [hv, hv', not_false_eq_true, ↓reduceIte, h1, h2]
          rcases zmod2_cases (u.2 ⟨0, by omega⟩) with a | a <;>
            rcases zmod2_cases (u.2 ⟨1, by omega⟩) with b | b <;>
            simp [a, b, h11, h10] <;> norm_num
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hfilt : (H.filter (fun u => u + (e + d) ∈ H)).filter (fun u => ¬ isConeVert hN u)
          = H.filter (fun u => ¬ isConeVert hN u) := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨huH, _⟩, hv⟩; exact ⟨huH, hv⟩
        · rintro ⟨huH, hv⟩
          refine ⟨⟨huH, ?_⟩, hv⟩
          have hne : u ≠ e + d := fun h => hv (h ▸ hvert_ed)
          exact hH_closed.2 u huH (e + d) hed_mem hne (hcomm_ed u huH)
      rw [hfilt]; ring
    -- Conclude the total difference is `-4 * 2^N * |B| ≠ 0`.
    intro heq
    have hcomb : (2 : ℂ) ^ N * (-4 * (((H.filter (fun u => ¬ isConeVert hN u)).card : ℕ) : ℂ)) = 0 := by
      linear_combination heq - (2 : ℂ) ^ N * hdiff_e + (2 : ℂ) ^ N * hdiff_d + (2 : ℂ) ^ N * hdiff_ed
    have h2ne : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
    have hcard0 : (((H.filter (fun u => ¬ isConeVert hN u)).card : ℕ) : ℂ) = 0 := by
      have h1 := (mul_eq_zero.mp hcomb).resolve_left h2ne
      exact (mul_eq_zero.mp h1).resolve_left (by norm_num)
    have hcardN : (H.filter (fun u => ¬ isConeVert hN u)).card = 0 := by exact_mod_cast hcard0
    obtain ⟨u₀, hu₀H, hu₀v⟩ := hbase
    have hpos : 0 < (H.filter (fun u => ¬ isConeVert hN u)).card :=
      Finset.card_pos.mpr ⟨u₀, Finset.mem_filter.mpr ⟨hu₀H, hu₀v⟩⟩
    omega

/-- **Case C6 (all `N ≥ 3`).** Cone `X = W ∩ Z₀⊥` with hyperplane `d = Z₁`. -/
theorem c6_strict_law_fails {N : ℕ} (hN : 3 ≤ N) :
    let e : Pt N := ptZ ⟨0, by omega⟩
    let d : Pt N := ptZ ⟨1, by omega⟩
    let X : Finset (Pt N) := perpSet (allPoints N) e
    ∃ σ τ : Pt N → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  intro e d X
  have h2 : 2 ≤ N := by omega
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h20 : (⟨2, by omega⟩ : Fin N) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have h21 : (⟨2, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  refine cone_pair_swap_strict_law_fails h2 X (isClosedCfg_perpSet isClosedCfg_allPoints e)
    (fun u hu => (Finset.mem_filter.mp hu).2) ?_ ?_ ?_ ?_ ?_ ((4 : ℂ) ^ N / 4)
    (div_ne_zero (pow_ne_zero N (by norm_num)) (by norm_num)) ?_
  · intro u hu
    obtain ⟨huX, hud⟩ := Finset.mem_filter.mp hu
    obtain ⟨huall, hue⟩ := Finset.mem_filter.mp huX
    have hu0 : u ≠ 0 := Finset.ne_of_mem_erase huall
    have hne0 : cnotPt h2 u ≠ 0 := by
      intro h
      have h0 : cnotPt h2 0 = 0 := by ext i <;> simp [cnotPt]
      have h1 := congrArg (cnotPt h2) h
      rw [cnotPt_invol, h0] at h1
      exact hu0 h1
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne0, mem_univ _⟩, ?_⟩, ?_⟩
    · rw [symp_ptZ]; exact (symp_ptZ u _).symm.trans hue
    · rw [symp_ptZ]; exact (symp_ptZ u _).symm.trans hud
  · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ptZ_ne_zero _, mem_univ _⟩,
      symp_ptZ_ptZ _ _⟩, symp_ptZ_ptZ _ _⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ptZ_ne_zero _, mem_univ _⟩,
      symp_ptZ_ptZ _ _⟩, symp_ptZ_ptZ _ _⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, mem_univ _⟩, ?_⟩, ?_⟩
    · exact fun h => ptZ_ne_ptZ h01 (pt_eq_of_add_eq_zero h)
    · rw [symp_add_left, symp_ptZ_ptZ, symp_ptZ_ptZ, add_zero]
    · rw [symp_add_left, symp_ptZ_ptZ, symp_ptZ_ptZ, add_zero]
  · refine ⟨ptZ ⟨2, by omega⟩, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ptZ_ne_zero _, mem_univ _⟩,
        symp_ptZ_ptZ _ _⟩, symp_ptZ_ptZ _ _⟩
    · intro hv
      have h := (hv ⟨2, by omega⟩ h20 h21).2
      simp [ptZ] at h
  · intro s hs
    have hs0 : s ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
    exact charSumOut_C6 hs0

/-- **Case C11 (all `N ≥ 3`).** Cone `X = Q⁺ ∩ Z₀⊥` with hyperplane `d = Z₁`. -/
theorem c11_strict_law_fails {N : ℕ} (hN : 3 ≤ N) :
    let e : Pt N := ptZ ⟨0, by omega⟩
    let d : Pt N := ptZ ⟨1, by omega⟩
    let X : Finset (Pt N) := perpSet (quadric N 0) e
    ∃ σ τ : Pt N → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  intro e d X
  have h2 : 2 ≤ N := by omega
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h20 : (⟨2, by omega⟩ : Fin N) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have h21 : (⟨2, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hq0 : ∀ u : Pt N, qformShift (0 : Pt N) u = qform u := fun u => by
    simp [qformShift, symp_comm 0 u, symp_zero_right]
  refine cone_pair_swap_strict_law_fails h2 X (isClosedCfg_perpSet (isClosedCfg_quadric 0) e)
    (fun u hu => (Finset.mem_filter.mp hu).2) ?_ ?_ ?_ ?_ ?_ ((4 : ℂ) ^ N / 8)
    (div_ne_zero (pow_ne_zero N (by norm_num)) (by norm_num)) ?_
  · intro u hu
    obtain ⟨huX, hud⟩ := Finset.mem_filter.mp hu
    obtain ⟨huQ, hue⟩ := Finset.mem_filter.mp huX
    obtain ⟨hu0, hqu⟩ := (Finset.mem_filter.mp huQ).2
    have hu1 : u.1 ⟨1, by omega⟩ = 0 := by simpa [symp_ptZ, d] using hud
    have hne0 : cnotPt h2 u ≠ 0 := by
      intro h
      have h0 : cnotPt h2 0 = 0 := by ext i <;> simp [cnotPt]
      have h1 := congrArg (cnotPt h2) h
      rw [cnotPt_invol, h0] at h1
      exact hu0 h1
    have hq_cnot : qform (cnotPt h2 u) = qform u := by
      unfold qform cnotPt dotProduct
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i = ⟨1, by omega⟩
      · subst hi; simp [hu1]
      · simp [hi]
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, hne0, ?_⟩, ?_⟩, ?_⟩
    · rw [hq0, hq_cnot]; rwa [hq0] at hqu
    · rw [symp_ptZ]; exact (symp_ptZ u _).symm.trans hue
    · rw [symp_ptZ]; exact (symp_ptZ u _).symm.trans hud
  · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, ptZ_ne_zero _,
      by rw [hq0]; exact qform_ptZ _⟩, symp_ptZ_ptZ _ _⟩, symp_ptZ_ptZ _ _⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, ptZ_ne_zero _,
      by rw [hq0]; exact qform_ptZ _⟩, symp_ptZ_ptZ _ _⟩, symp_ptZ_ptZ _ _⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, ?_⟩, ?_⟩
    · exact fun h => ptZ_ne_ptZ h01 (pt_eq_of_add_eq_zero h)
    · rw [hq0, qform_add, qform_ptZ, qform_ptZ, symp_ptZ_ptZ]; simp
    · rw [symp_add_left, symp_ptZ_ptZ, symp_ptZ_ptZ, add_zero]
    · rw [symp_add_left, symp_ptZ_ptZ, symp_ptZ_ptZ, add_zero]
  · refine ⟨ptZ ⟨2, by omega⟩, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, ptZ_ne_zero _,
        by rw [hq0]; exact qform_ptZ _⟩, symp_ptZ_ptZ _ _⟩, symp_ptZ_ptZ _ _⟩
    · intro hv; have h := (hv ⟨2, by omega⟩ h20 h21).2; simp [ptZ] at h
  · intro s hs
    obtain ⟨hsX, hsd⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsQ, hse⟩ := Finset.mem_filter.mp hsX
    obtain ⟨hs0, hqs⟩ := (Finset.mem_filter.mp hsQ).2
    exact charSumOut_C11_C14 (by rw [hq0]; exact qform_ptZ _) (by rw [hq0]; exact qform_ptZ _)
      (symp_ptZ_ptZ _ _) hs0 hqs hse hsd

/-- **Case C14 (all `N ≥ 4`).** Cone `X = Q⁻ ∩ Z₀⊥` (`c = Y₂`) with hyperplane `d = Z₁`. -/
theorem c14_strict_law_fails {N : ℕ} (hN : 4 ≤ N) :
    let c : Pt N := ptY ⟨2, by omega⟩
    let e : Pt N := ptZ ⟨0, by omega⟩
    let d : Pt N := ptZ ⟨1, by omega⟩
    let X : Finset (Pt N) := perpSet (quadric N c) e
    ∃ σ τ : Pt N → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionOf X d) σ).charpoly = (opA (sectionOf X d) τ).charpoly ∧
      (completionMat X d σ).charpoly ≠ (completionMat X d τ).charpoly := by
  intro c e d X
  have h2 : 2 ≤ N := by omega
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h20 : (⟨2, by omega⟩ : Fin N) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have h21 : (⟨2, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h30 : (⟨3, by omega⟩ : Fin N) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have h31 : (⟨3, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h23 : (⟨2, by omega⟩ : Fin N) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have hqe : qformShift c e = 0 := by
    rw [qformShift, qform_ptZ, symp_ptY_ptZ h20, add_zero]
  have hqd : qformShift c d = 0 := by
    rw [qformShift, qform_ptZ, symp_ptY_ptZ h21, add_zero]
  refine cone_pair_swap_strict_law_fails h2 X (isClosedCfg_perpSet (isClosedCfg_quadric c) e)
    (fun u hu => (Finset.mem_filter.mp hu).2) ?_ ?_ ?_ ?_ ?_ ((4 : ℂ) ^ N / 8)
    (div_ne_zero (pow_ne_zero N (by norm_num)) (by norm_num)) ?_
  · intro u hu
    obtain ⟨huX, hud⟩ := Finset.mem_filter.mp hu
    obtain ⟨huQ, hue⟩ := Finset.mem_filter.mp huX
    obtain ⟨hu0, hqu⟩ := (Finset.mem_filter.mp huQ).2
    have hu1 : u.1 ⟨1, by omega⟩ = 0 := by simpa [symp_ptZ, d] using hud
    have hne0 : cnotPt h2 u ≠ 0 := by
      intro h
      have h0 : cnotPt h2 0 = 0 := by ext i <;> simp [cnotPt]
      have h1 := congrArg (cnotPt h2) h
      rw [cnotPt_invol, h0] at h1
      exact hu0 h1
    have hq_cnot : qformShift c (cnotPt h2 u) = qformShift c u := by
      have hq0 : qform (cnotPt h2 u) = qform u := by
        unfold qform cnotPt dotProduct
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i = ⟨1, by omega⟩
        · subst hi; simp [hu1]
        · simp [hi]
      have hsc : symp c (cnotPt h2 u) = symp c u := by
        rw [symp_comm, symp_ptY, symp_comm c u, symp_ptY]
        simp [cnotPt, h21]
      rw [qformShift, qformShift, hq0, hsc]
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, hne0, ?_⟩, ?_⟩, ?_⟩
    · rwa [hq_cnot]
    · rw [symp_ptZ]; exact (symp_ptZ u _).symm.trans hue
    · rw [symp_ptZ]; exact (symp_ptZ u _).symm.trans hud
  · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, ptZ_ne_zero _, hqe⟩,
      symp_ptZ_ptZ _ _⟩, symp_ptZ_ptZ _ _⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, ptZ_ne_zero _, hqd⟩,
      symp_ptZ_ptZ _ _⟩, symp_ptZ_ptZ _ _⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, ?_⟩, ?_⟩
    · exact fun h => ptZ_ne_ptZ h01 (pt_eq_of_add_eq_zero h)
    · rw [qformShift_add, hqe, hqd, symp_ptZ_ptZ]; simp
    · rw [symp_add_left, symp_ptZ_ptZ, symp_ptZ_ptZ, add_zero]
    · rw [symp_add_left, symp_ptZ_ptZ, symp_ptZ_ptZ, add_zero]
  · refine ⟨ptZ ⟨3, by omega⟩, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, ptZ_ne_zero _, ?_⟩,
        symp_ptZ_ptZ _ _⟩, symp_ptZ_ptZ _ _⟩
      rw [qformShift, qform_ptZ, symp_ptY_ptZ h23, add_zero]
    · intro hv; have h := (hv ⟨3, by omega⟩ h30 h31).2; simp [ptZ] at h
  · intro s hs
    obtain ⟨hsX, hsd⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsQ, hse⟩ := Finset.mem_filter.mp hsX
    obtain ⟨hs0, hqs⟩ := (Finset.mem_filter.mp hsQ).2
    exact charSumOut_C11_C14 hqe hqd (symp_ptZ_ptZ _ _) hs0 hqs hse hsd

end ConePairSwap

end HoggarBound.ConjectureE

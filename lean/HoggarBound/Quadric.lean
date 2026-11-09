/-
Hoggar Bound Lab — the hyperbolic ("real") quadric `Q⁺(2N−1, 2)`.

The real quadric consists of the non-identity Pauli observables with an even number of `Y`
factors, i.e. those represented by real symmetric matrices.  We count its points and flags for
every `N` by character sums and specialise the Hoggar bound:

* `four_qubit_hyperbolic_contexts` : at least 315 of the 1575 contexts of `Q⁺(7,2)` are violated
  (the exact value, proved by Li, Gupta and Ganesh in 2026 by a different argument);
* `five_qubit_hyperbolic_contexts` : at least 6426 of the 23715 contexts of `Q⁺(9,2)` are
  violated — so the degree of `Q⁺(9,2)` is not `23715/5 = 4743`.
-/
import HoggarBound.Counting

open Finset Matrix

namespace HoggarBound

variable {N : ℕ}

/-- The quadratic form `(a, c) ↦ a·c`: the parity of the number of `Y` factors. -/
def qform (u : Pt N) : ZMod 2 := u.2 ⬝ᵥ u.1

/-- Non-identity observables with an even number of `Y` factors. -/
def realPoints (N : ℕ) : Finset (Pt N) := univ.filter fun u => u ≠ 0 ∧ qform u = 0

lemma qform_zero : qform (0 : Pt N) = 0 := by simp [qform]

lemma qform_add (u v : Pt N) : qform (u + v) = qform u + qform v + symp u v := by
  simp only [qform, symp, Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
  ring

/-- Indicator of `t = 0` through the character. -/
lemma indicator_eq (t : ZMod 2) : (if t = 0 then (1 : ℂ) else 0) = (1 + eps t) / 2 := by
  rcases zmod2_cases t with rfl | rfl
  · simp
  · have h : (1 : ZMod 2) ≠ 0 := by decide
    simp [h]

lemma sum_eps_qform : ∑ u : Pt N, eps (qform u) = (2 : ℂ) ^ N := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ a : Vec N, ∑ c : Vec N, eps (qform (a, c)) = if a = 0 then (2 : ℂ) ^ N else 0 := by
    intro a
    have : ∀ c : Vec N, eps (qform (a, c)) = chi a c := by
      intro c
      simp only [qform, chi]
      rw [dotProduct_comm]
    simp only [this]
    exact sum_chi a
  simp only [hinner]
  simp

lemma sum_eps_symp {u : Pt N} (hu : u ≠ 0) : ∑ v : Pt N, eps (symp u v) = 0 := by
  obtain ⟨e, he⟩ := exists_symp_eq_one hu
  refine Finset.sum_ninvolution (fun v : Pt N => v + e) ?_ ?_ ?_ ?_
  · intro v
    rw [symp_add_right, eps_add, he, eps_one]
    ring
  · intro v _ hv
    have h1 : symp u (v + e) = symp u v := by rw [hv]
    rw [symp_add_right, he] at h1
    have h2 := congrArg (fun t => symp u v + t) h1
    simp [← add_assoc, zmod2_add_self] at h2
  · intro v
    exact mem_univ _
  · intro v
    rw [add_assoc, pt_add_self, add_zero]

lemma sum_eps_qform_symp {u : Pt N} (hq : qform u = 0) :
    ∑ v : Pt N, eps (qform v + symp u v) = (2 : ℂ) ^ N := by
  rw [← sum_eps_qform (N := N)]
  refine Finset.sum_nbij' (fun v : Pt N => v + u) (fun v : Pt N => v + u) ?_ ?_ ?_ ?_ ?_
  · intro v _
    exact mem_univ _
  · intro v _
    exact mem_univ _
  · intro v _
    show v + u + u = v
    rw [add_assoc, pt_add_self, add_zero]
  · intro v _
    show v + u + u = v
    rw [add_assoc, pt_add_self, add_zero]
  · intro v _
    show eps (qform v + symp u v) = eps (qform (v + u))
    rw [qform_add, hq, add_zero, symp_comm v u]

/-- `2 · #{u : q(u) = 0} = 4^N + 2^N`. -/
lemma card_qzero : 2 * (univ.filter fun u : Pt N => qform u = 0).card = 4 ^ N + 2 ^ N := by
  have hC : (((univ.filter fun u : Pt N => qform u = 0).card : ℕ) : ℂ)
      = ((4 : ℂ) ^ N + (2 : ℂ) ^ N) / 2 := by
    rw [Finset.card_filter]
    push_cast
    simp only [indicator_eq, ← Finset.sum_div, Finset.sum_add_distrib, sum_eps_qform,
      Finset.sum_const, Finset.card_univ, card_pt, nsmul_eq_mul, mul_one]
    push_cast
    rfl
  have h2 : ((2 * (univ.filter fun u : Pt N => qform u = 0).card : ℕ) : ℂ)
      = ((4 ^ N + 2 ^ N : ℕ) : ℂ) := by
    push_cast
    rw [hC]
    ring
  exact_mod_cast h2

lemma card_realPoints : 2 * (realPoints N).card + 2 = 4 ^ N + 2 ^ N := by
  have heq : realPoints N = (univ.filter fun u : Pt N => qform u = 0).erase 0 := by
    ext u
    simp [realPoints, and_comm]
  have h0 : (0 : Pt N) ∈ univ.filter fun u : Pt N => qform u = 0 := by
    simp [qform_zero]
  have hpos : 0 < (univ.filter fun u : Pt N => qform u = 0).card := Finset.card_pos.2 ⟨0, h0⟩
  rw [heq, Finset.card_erase_of_mem h0]
  have := card_qzero (N := N)
  omega

/-- For `u` on the quadric: `4 · #{v : q(v) = 0, v commutes with u} = 4^N + 2·2^N`. -/
lemma card_qzero_commuting {u : Pt N} (hu : u ≠ 0) (hq : qform u = 0) :
    4 * (univ.filter fun v : Pt N => qform v = 0 ∧ symp u v = 0).card = 4 ^ N + 2 * 2 ^ N := by
  have hind : ∀ v : Pt N, (if qform v = 0 ∧ symp u v = 0 then (1 : ℂ) else 0)
      = (1 + eps (qform v) + eps (symp u v) + eps (qform v + symp u v)) / 4 := by
    intro v
    have h1 : (if qform v = 0 ∧ symp u v = 0 then (1 : ℂ) else 0)
        = (if qform v = 0 then (1 : ℂ) else 0) * (if symp u v = 0 then (1 : ℂ) else 0) := by
      by_cases ha : qform v = 0 <;> by_cases hb : symp u v = 0 <;> simp [ha, hb]
    rw [h1, indicator_eq, indicator_eq, eps_add]
    ring
  have hC : (((univ.filter fun v : Pt N => qform v = 0 ∧ symp u v = 0).card : ℕ) : ℂ)
      = ((4 : ℂ) ^ N + 2 * (2 : ℂ) ^ N) / 4 := by
    rw [Finset.card_filter]
    push_cast
    simp only [hind, ← Finset.sum_div, Finset.sum_add_distrib, sum_eps_qform, sum_eps_symp hu,
      sum_eps_qform_symp hq, Finset.sum_const, Finset.card_univ, card_pt, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have h2 : ((4 * (univ.filter fun v : Pt N => qform v = 0 ∧ symp u v = 0).card : ℕ) : ℂ)
      = ((4 ^ N + 2 * 2 ^ N : ℕ) : ℂ) := by
    push_cast
    rw [hC]
    ring
  exact_mod_cast h2

lemma inner_filter_real {u : Pt N} (hq : qform u = 0) :
    ((realPoints N).filter fun v => u + v ∈ realPoints N ∧ symp u v = 0)
      = ((univ.filter fun v : Pt N => qform v = 0 ∧ symp u v = 0).erase 0).erase u := by
  ext v
  simp only [realPoints, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, ne_eq]
  constructor
  · rintro ⟨⟨hv0, hqv⟩, ⟨huv, _⟩, hs⟩
    refine ⟨fun h => huv ?_, hv0, hqv, hs⟩
    rw [h, pt_add_self]
  · rintro ⟨hvu, hv0, hqv, hs⟩
    refine ⟨⟨hv0, hqv⟩, ⟨fun h => hvu (pt_eq_of_add_eq_zero h).symm, ?_⟩, hs⟩
    rw [qform_add, hq, hqv, hs]
    simp

lemma card_inner_real {u : Pt N} (hu : u ≠ 0) (hq : qform u = 0) :
    4 * ((realPoints N).filter fun v => u + v ∈ realPoints N ∧ symp u v = 0).card + 8
      = 4 ^ N + 2 * 2 ^ N := by
  rw [inner_filter_real hq]
  have h0 : (0 : Pt N) ∈ univ.filter fun v : Pt N => qform v = 0 ∧ symp u v = 0 := by
    simp [qform_zero, symp_zero_right]
  have hu' : u ∈ (univ.filter fun v : Pt N => qform v = 0 ∧ symp u v = 0).erase 0 := by
    simp [symp_self, hu, hq]
  have hc1 : 0 < ((univ.filter fun v : Pt N => qform v = 0 ∧ symp u v = 0).erase 0).card :=
    Finset.card_pos.2 ⟨u, hu'⟩
  have hc0 : 0 < (univ.filter fun v : Pt N => qform v = 0 ∧ symp u v = 0).card :=
    Finset.card_pos.2 ⟨0, h0⟩
  rw [Finset.card_erase_of_mem hu']
  have e2 := Finset.card_erase_of_mem h0
  have := card_qzero_commuting hu hq
  omega

/-- Flags of the real quadric: `4 · #flags + 8 · #points = #points · (4^N + 2·2^N)`. -/
theorem card_flags_real :
    4 * (flags (realPoints N)).card + 8 * (realPoints N).card
      = (realPoints N).card * (4 ^ N + 2 * 2 ^ N) := by
  rw [card_flags, Finset.mul_sum]
  have hterm : ∀ u ∈ realPoints N,
      4 * ((realPoints N).filter fun v => u + v ∈ realPoints N ∧ symp u v = 0).card
        = (4 ^ N + 2 * 2 ^ N) - 8 := by
    intro u hu
    obtain ⟨hu0, hq⟩ := (Finset.mem_filter.1 hu).2
    have := card_inner_real hu0 hq
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  have h8 : 8 ≤ 4 ^ N + 2 * 2 ^ N ∨ (realPoints N).card = 0 := by
    by_cases hc : (realPoints N).card = 0
    · exact Or.inr hc
    · left
      obtain ⟨u, hu⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hc)
      obtain ⟨hu0, hq⟩ := (Finset.mem_filter.1 hu).2
      have := card_inner_real hu0 hq
      omega
  rcases h8 with h8 | h8
  · have hmul : (realPoints N).card * (4 ^ N + 2 * 2 ^ N - 8) + 8 * (realPoints N).card
        = (realPoints N).card * (4 ^ N + 2 * 2 ^ N) := by
      have : 4 ^ N + 2 * 2 ^ N - 8 + 8 = 4 ^ N + 2 * 2 ^ N := by omega
      calc (realPoints N).card * (4 ^ N + 2 * 2 ^ N - 8) + 8 * (realPoints N).card
          = (realPoints N).card * (4 ^ N + 2 * 2 ^ N - 8 + 8) := by ring
        _ = (realPoints N).card * (4 ^ N + 2 * 2 ^ N) := by rw [this]
    exact hmul
  · simp [h8]

/-! ### Corollaries for four and five qubits -/

/-- **`Q⁺(7,2)`.**  Every assignment of the 135 real four-qubit observables violates at least
315 of the 1575 contexts.  (This is the exact contextuality degree.) -/
theorem four_qubit_hyperbolic_contexts (f : Pt 4 → ℝ)
    (hf : ∀ u ∈ realPoints 4, f u = 1 ∨ f u = -1) :
    315 ≤ (violatedLines (realPoints 4) f).card := by
  have h0 : (0 : Pt 4) ∉ realPoints 4 := by simp [realPoints]
  have hb := hoggar_bound_violated (N := 4) (by norm_num) (realPoints 4) h0 f hf
  have hS : (realPoints 4).card = 135 := by
    have := card_realPoints (N := 4)
    norm_num at this
    omega
  have hF : (flags (realPoints 4)).card = 9450 := by
    have := card_flags_real (N := 4)
    rw [hS] at this
    norm_num at this
    omega
  rw [hF, hS] at hb
  have e1 : ((2 : ℝ) ^ 4 - 1) * ((135 : ℕ) : ℝ) = 2025 := by norm_num
  have e3 : ((2 : ℝ) ^ 4 - 2) * ((135 : ℕ) : ℝ) = 1890 := by norm_num
  have e2 : ((2 : ℝ) ^ 4 - 1) = 15 := by norm_num
  rw [e1, e3, e2] at hb
  have hs : Real.sqrt 2025 = 45 := by
    rw [show (2025 : ℝ) = 45 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hF' : ((9450 : ℕ) : ℝ) = 9450 := by norm_num
  rw [hs, hF'] at hb
  have hV : (1890 : ℝ) ≤ ((violated (realPoints 4) f).card : ℝ) := by linarith
  have hV' : 1890 ≤ (violated (realPoints 4) f).card := by exact_mod_cast hV
  have h2 := card_violated_le (realPoints 4) h0 f
  omega

/-- **`Q⁺(9,2)`.**  Every assignment of the 527 real five-qubit observables violates at least
6426 of the 23715 contexts.  In particular the contextuality degree of the five-qubit hyperbolic
quadric is strictly larger than `23715 / 5 = 4743`. -/
theorem five_qubit_hyperbolic_contexts (f : Pt 5 → ℝ)
    (hf : ∀ u ∈ realPoints 5, f u = 1 ∨ f u = -1) :
    6426 ≤ (violatedLines (realPoints 5) f).card := by
  have h0 : (0 : Pt 5) ∉ realPoints 5 := by simp [realPoints]
  have hb := hoggar_bound_violated (N := 5) (by norm_num) (realPoints 5) h0 f hf
  have hS : (realPoints 5).card = 527 := by
    have := card_realPoints (N := 5)
    norm_num at this
    omega
  have hF : (flags (realPoints 5)).card = 142290 := by
    have := card_flags_real (N := 5)
    rw [hS] at this
    norm_num at this
    omega
  rw [hF, hS] at hb
  have e1 : ((2 : ℝ) ^ 5 - 1) * ((527 : ℕ) : ℝ) = 16337 := by norm_num
  have e3 : ((2 : ℝ) ^ 5 - 2) * ((527 : ℕ) : ℝ) = 15810 := by norm_num
  have e2 : ((2 : ℝ) ^ 5 - 1) = 31 := by norm_num
  rw [e1, e3, e2] at hb
  have hF' : ((142290 : ℕ) : ℝ) = 142290 := by norm_num
  rw [hF'] at hb
  have hsqrt : Real.sqrt 16337 < 127.8164 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hV' : 38552 ≤ (violated (realPoints 5) f).card := by
    by_contra hlt
    have hV : ((violated (realPoints 5) f).card : ℝ) ≤ 38551 := by
      have : (violated (realPoints 5) f).card ≤ 38551 := by omega
      exact_mod_cast this
    linarith
  have h2 := card_violated_le (realPoints 5) h0 f
  omega

end HoggarBound

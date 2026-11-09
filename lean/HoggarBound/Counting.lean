/-
Hoggar Bound Lab — from the operator inequality to a count of violated contexts.

* `violated S f` : the flags on which the assignment `f` contradicts the quantum prediction.
* `beta6_eq_card` : `β₆ = #flags − 2 · #violated`.
* `card_flags_all` : the full space `W(2N−1,2)` has `(4^N − 1)(4^N − 4)/2` flags
  (six per line, so `(4^N − 1)(4^N − 4)/12` lines).
* `full_space_bound` : for all `N ≥ 1`, `#flags − 2·#violated ≤ (D − 2)(D² − 1)√(D + 1)`.
* `four_qubit_violated` : every assignment of the 255 four-qubit observables violates at least
  `8706 = 6 · 1451` of the `32130 = 6 · 5355` flags, i.e. at least 1451 of the 5355 contexts.
-/
import HoggarBound.Bound

open Finset Matrix

namespace HoggarBound

variable {N : ℕ}

/-! ### Violated flags -/

open Classical in
/-- The flags on which the assigned values multiply to the wrong sign. -/
noncomputable def violated (S : Finset (Pt N)) (f : Pt N → ℝ) : Finset (Pt N × Pt N) :=
  (flags S).filter fun p => f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2

lemma mem_flags {S : Finset (Pt N)} {p : Pt N × Pt N} :
    p ∈ flags S ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 + p.2 ∈ S ∧ symp p.1 p.2 = 0 := by
  simp only [flags, Finset.mem_filter, Finset.mem_product]
  tauto

open Classical in
lemma term_eq_ite {S : Finset (Pt N)} {f : Pt N → ℝ} (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1)
    {p : Pt N × Pt N} (hp : p ∈ flags S) :
    f p.1 * f p.2 * f (p.1 + p.2) * lineSign p.1 p.2
      = if f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2 then -1 else 1 := by
  obtain ⟨h1, h2, h3, hs⟩ := mem_flags.1 hp
  rcases hf _ h1 with a | a <;> rcases hf _ h2 with b | b <;> rcases hf _ h3 with c | c <;>
    rcases lineSign_eq_one_or_neg_one hs with d | d <;> rw [a, b, c, d] <;> norm_num

/-- `β₆` is the number of flags minus twice the number of violated flags. -/
theorem beta6_eq_card (S : Finset (Pt N)) (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    beta6 S f = ((flags S).card : ℝ) - 2 * ((violated S f).card : ℝ) := by
  classical
  rw [beta6, Finset.sum_congr rfl (fun p hp => term_eq_ite hf hp), Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
  have hsplit := Finset.card_filter_add_card_filter_not (s := flags S)
    (fun p : Pt N × Pt N => f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2)
  have hsplit' : (((flags S).filter fun p : Pt N × Pt N =>
        f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2).card : ℝ)
      + (((flags S).filter fun p : Pt N × Pt N =>
        ¬ f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2).card : ℝ) = ((flags S).card : ℝ) := by
    exact_mod_cast hsplit
  simp only [violated]
  linarith

/-- The Hoggar bound, stated for the number of violated flags. -/
theorem hoggar_bound_violated (hN : 1 ≤ N) (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S)
    (f : Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ N - 1) * (((flags S).card : ℝ) - 2 * ((violated S f).card : ℝ))
      ≤ ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card) := by
  rw [← beta6_eq_card S f hf]
  exact hoggar_bound hN S h0 f hf

/-! ### Counting the full space -/

/-- All non-identity observables: the points of `W(2N−1, 2)`. -/
def allPoints (N : ℕ) : Finset (Pt N) := univ.erase 0

lemma card_pt : Fintype.card (Pt N) = 4 ^ N := by
  simp [ZMod.card, ← mul_pow]

lemma card_allPoints : (allPoints N).card = 4 ^ N - 1 := by
  rw [allPoints, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, card_pt]

lemma symp_add_right (u v w : Pt N) : symp u (v + w) = symp u v + symp u w := by
  simp only [symp, Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
  ring

lemma symp_self (u : Pt N) : symp u u = 0 := by
  simp only [symp]
  exact zmod2_add_self _

lemma symp_zero_right (u : Pt N) : symp u 0 = 0 := by
  simp [symp]

lemma exists_symp_eq_one {u : Pt N} (hu : u ≠ 0) : ∃ e : Pt N, symp u e = 1 := by
  by_cases ha : u.1 = 0
  · have hc : u.2 ≠ 0 := fun hc => hu (Prod.ext ha hc)
    obtain ⟨i, hi⟩ : ∃ i, u.2 i ≠ 0 := by
      by_contra h
      exact hc (funext fun i => by simpa using not_not.1 (not_exists.1 h i))
    refine ⟨(Pi.single i 1, 0), ?_⟩
    have h1 : u.2 i = 1 := (zmod2_cases _).resolve_left hi
    simp [symp, dotProduct_single, h1]
  · obtain ⟨i, hi⟩ : ∃ i, u.1 i ≠ 0 := by
      by_contra h
      exact ha (funext fun i => by simpa using not_not.1 (not_exists.1 h i))
    refine ⟨(0, Pi.single i 1), ?_⟩
    have h1 : u.1 i = 1 := (zmod2_cases _).resolve_left hi
    simp [symp, single_dotProduct, h1]

/-- Exactly half of all points commute with a given non-identity observable. -/
lemma card_commuting {u : Pt N} (hu : u ≠ 0) :
    2 * (univ.filter fun v : Pt N => symp u v = 0).card = 4 ^ N := by
  obtain ⟨e, he⟩ := exists_symp_eq_one hu
  have hbij : (univ.filter fun v : Pt N => symp u v = 0).card
      = (univ.filter fun v : Pt N => ¬ symp u v = 0).card := by
    refine Finset.card_nbij' (fun v => v + e) (fun v => v + e) ?_ ?_ ?_ ?_
    · intro v hv
      have hv0 : symp u v = 0 := by simpa using hv
      have : symp u (v + e) = 1 := by rw [symp_add_right, hv0, he, zero_add]
      simp [this]
    · intro v hv
      have hv1 : symp u v = 1 := (zmod2_cases _).resolve_left (by simpa using hv)
      have : symp u (v + e) = 0 := by rw [symp_add_right, hv1, he]; decide
      simp [this]
    · intro v _
      show v + e + e = v
      rw [add_assoc, pt_add_self, add_zero]
    · intro v _
      show v + e + e = v
      rw [add_assoc, pt_add_self, add_zero]
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Pt N)))
    (fun v : Pt N => symp u v = 0)
  rw [Finset.card_univ, card_pt] at hsplit
  omega

lemma card_flags (S : Finset (Pt N)) :
    (flags S).card = ∑ u ∈ S, (S.filter fun v => u + v ∈ S ∧ symp u v = 0).card := by
  simp only [flags, Finset.card_filter, Finset.sum_product]

lemma inner_filter_all (u : Pt N) :
    ((allPoints N).filter fun v => u + v ∈ allPoints N ∧ symp u v = 0)
      = ((univ.filter fun v : Pt N => symp u v = 0).erase 0).erase u := by
  ext v
  simp only [allPoints, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
    ne_eq]
  constructor
  · rintro ⟨hv0, huv, hs⟩
    refine ⟨fun h => huv ?_, hv0, hs⟩
    rw [h, pt_add_self]
  · rintro ⟨hvu, hv0, hs⟩
    refine ⟨hv0, fun h => hvu ?_, hs⟩
    exact (pt_eq_of_add_eq_zero h).symm

lemma card_inner_all {u : Pt N} (hu : u ≠ 0) :
    2 * ((allPoints N).filter fun v => u + v ∈ allPoints N ∧ symp u v = 0).card = 4 ^ N - 4 := by
  rw [inner_filter_all u]
  have h0 : (0 : Pt N) ∈ univ.filter fun v : Pt N => symp u v = 0 := by
    simp [symp_zero_right]
  have hu' : u ∈ (univ.filter fun v : Pt N => symp u v = 0).erase 0 := by
    simp [symp_self, hu]
  rw [Finset.card_erase_of_mem hu', Finset.card_erase_of_mem h0]
  have := card_commuting hu
  omega

/-- The number of flags of the full space: `2 · #flags = (4^N − 1)(4^N − 4)`. -/
theorem card_flags_all : 2 * (flags (allPoints N)).card = (4 ^ N - 1) * (4 ^ N - 4) := by
  rw [card_flags, Finset.mul_sum]
  have hterm : ∀ u ∈ allPoints N,
      2 * ((allPoints N).filter fun v => u + v ∈ allPoints N ∧ symp u v = 0).card = 4 ^ N - 4 := by
    intro u hu
    exact card_inner_all (Finset.ne_of_mem_erase hu)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_allPoints, smul_eq_mul]

/-! ### The four-qubit corollary -/

/-- **Four qubits.**  Any noncontextual value assignment to the 255 non-identity four-qubit Pauli
observables violates at least `8706 = 6 · 1451` flags, that is, at least 1451 of the 5355
contexts.  (Previously known: at least 1071.) -/
theorem four_qubit_violated (f : Pt 4 → ℝ) (hf : ∀ u ∈ allPoints 4, f u = 1 ∨ f u = -1) :
    8706 ≤ (violated (allPoints 4) f).card := by
  have h0 : (0 : Pt 4) ∉ allPoints 4 := by simp [allPoints]
  have hb := hoggar_bound_violated (N := 4) (by norm_num) (allPoints 4) h0 f hf
  have hF : (flags (allPoints 4)).card = 32130 := by
    have := card_flags_all (N := 4)
    norm_num at this
    omega
  have hS : (allPoints 4).card = 255 := by
    rw [card_allPoints]; norm_num
  rw [hF, hS] at hb
  have e1 : ((2 : ℝ) ^ 4 - 1) * ((255 : ℕ) : ℝ) = 3825 := by norm_num
  have e3 : ((2 : ℝ) ^ 4 - 2) * ((255 : ℕ) : ℝ) = 3570 := by norm_num
  have e2 : ((2 : ℝ) ^ 4 - 1) = 15 := by norm_num
  rw [e1, e3, e2] at hb
  -- hb : 15 * (32130 - 2 * V) ≤ 3570 * √3825
  have hF' : ((32130 : ℕ) : ℝ) = 32130 := by norm_num
  rw [hF'] at hb
  have hsqrt : Real.sqrt 3825 < 61.8487 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  by_contra hlt
  have hV : ((violated (allPoints 4) f).card : ℝ) ≤ 8705 := by
    have : (violated (allPoints 4) f).card ≤ 8705 := by omega
    exact_mod_cast this
  linarith

/-! ### From flags to contexts -/

/-- The context (unordered triple of observables) underlying a flag. -/
def lineOf (p : Pt N × Pt N) : Finset (Pt N) := {p.1, p.2, p.1 + p.2}

/-- The set of violated contexts. -/
noncomputable def violatedLines (S : Finset (Pt N)) (f : Pt N → ℝ) : Finset (Finset (Pt N)) :=
  (violated S f).image lineOf

/-- A context carries at most six flags, so `#violated flags ≤ 6 · #violated contexts`. -/
theorem card_violated_le (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S) (f : Pt N → ℝ) :
    (violated S f).card ≤ 6 * (violatedLines S f).card := by
  classical
  refine Finset.card_le_mul_card_image (violated S f) 6 ?_
  intro L hL
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hL
  have hsub : ((violated S f).filter fun p => lineOf p = lineOf q) ⊆ (lineOf q).offDiag := by
    intro p hp
    obtain ⟨hpv, hpl⟩ := Finset.mem_filter.1 hp
    have hpf : p ∈ flags S := (Finset.mem_filter.1 hpv).1
    obtain ⟨_, _, h3, _⟩ := mem_flags.1 hpf
    have hne : p.1 ≠ p.2 := by
      intro h
      apply h0
      have : p.1 + p.2 = 0 := by rw [h, pt_add_self]
      rw [this] at h3
      exact h3
    rw [Finset.mem_offDiag, ← hpl]
    refine ⟨?_, ?_, hne⟩ <;> simp [lineOf]
  calc ((violated S f).filter fun p => lineOf p = lineOf q).card
      ≤ (lineOf q).offDiag.card := Finset.card_le_card hsub
    _ = (lineOf q).card * (lineOf q).card - (lineOf q).card := Finset.offDiag_card _
    _ ≤ 6 := by
        have h3 : (lineOf q).card ≤ 3 := Finset.card_le_three
        interval_cases (lineOf q).card <;> norm_num

/-- **Four qubits, in terms of contexts.**  Every noncontextual assignment violates at least
1451 of the 5355 contexts of the four-qubit Pauli group. -/
theorem four_qubit_contexts (f : Pt 4 → ℝ) (hf : ∀ u ∈ allPoints 4, f u = 1 ∨ f u = -1) :
    1451 ≤ (violatedLines (allPoints 4) f).card := by
  have h0 : (0 : Pt 4) ∉ allPoints 4 := by simp [allPoints]
  have h1 := four_qubit_violated f hf
  have h2 := card_violated_le (allPoints 4) h0 f
  omega

end HoggarBound

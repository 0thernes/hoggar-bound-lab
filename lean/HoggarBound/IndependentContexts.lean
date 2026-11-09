/- Exact conversion between ordered flags and unordered contexts. -/
import HoggarBound.Counting

open Finset Matrix

namespace HoggarBound

variable {N : ℕ}

lemma tau_rotate (u v : Pt N) : tau v (u + v) = tau u v := by
  have h := Matrix.trace_mul_cycle (pauli v) (pauli (u + v)) (pauli u)
  have hv : v + (u + v) = u := by
    rw [add_comm u v, ← add_assoc, pt_add_self, zero_add]
  rw [trace_pauli_triple, trace_pauli_triple, hv, ite_eq_left rfl, ite_eq_left rfl] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)) h

lemma lineSign_rotate (u v : Pt N) : lineSign v (u + v) = lineSign u v := by
  unfold lineSign
  rw [tau_rotate]

lemma lineSign_swap {u v : Pt N} (hs : symp u v = 0) :
    lineSign v u = lineSign u v := by
  unfold lineSign
  rw [tau_swap, hs, eps_zero, one_mul]

lemma violated_rotate {S : Finset (Pt N)} {f : Pt N → ℝ} {u v : Pt N}
    (h : (u, v) ∈ violated S f) : (v, u + v) ∈ violated S f := by
  obtain ⟨hp, hbad⟩ := mem_filter.1 h
  obtain ⟨hu, hv, huv, hs⟩ := mem_flags.1 hp
  have hvsum : v + (u + v) = u := by
    rw [add_comm u v, ← add_assoc, pt_add_self, zero_add]
  apply mem_filter.2
  refine ⟨mem_flags.2 ⟨hv, huv, ?_, ?_⟩, ?_⟩
  · simpa [hvsum] using hu
  · rw [symp_add_right, symp_comm v u, hs, symp_self, add_zero]
  · change f v * f (u + v) * f (v + (u + v)) ≠ lineSign v (u + v)
    rw [hvsum, lineSign_rotate]
    convert hbad using 1; ring

lemma violated_swap {S : Finset (Pt N)} {f : Pt N → ℝ} {u v : Pt N}
    (h : (u, v) ∈ violated S f) : (v, u) ∈ violated S f := by
  obtain ⟨hp, hbad⟩ := mem_filter.1 h
  obtain ⟨hu, hv, huv, hs⟩ := mem_flags.1 hp
  apply mem_filter.2
  refine ⟨mem_flags.2 ⟨hv, hu, ?_, ?_⟩, ?_⟩
  · simpa [add_comm] using huv
  · simpa [symp_comm] using hs
  · change f v * f u * f (v + u) ≠ lineSign v u
    rw [add_comm v u, lineSign_swap hs, mul_comm (f v) (f u)]
    exact hbad

lemma mem_violated_of_mem_offDiag {S : Finset (Pt N)} {f : Pt N → ℝ}
    {q p : Pt N × Pt N} (hq : q ∈ violated S f) (hp : p ∈ (lineOf q).offDiag) :
    p ∈ violated S f := by
  rcases q with ⟨u, v⟩
  rcases p with ⟨a, b⟩
  obtain ⟨ha, hb, hab⟩ := mem_offDiag.1 hp
  simp only [lineOf, mem_insert, mem_singleton] at ha hb
  have hrot := violated_rotate hq
  have hrot2 := violated_rotate hrot
  have hsum : v + (u + v) = u := by
    rw [add_comm u v, ← add_assoc, pt_add_self, zero_add]
  rw [hsum] at hrot2
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (hab rfl).elim
  · exact hq
  · exact violated_swap hrot2
  · exact violated_swap hq
  · exact (hab rfl).elim
  · exact hrot
  · exact hrot2
  · exact violated_swap hrot
  · exact (hab rfl).elim

lemma lineOf_of_mem_offDiag {q p : Pt N × Pt N} (hp : p ∈ (lineOf q).offDiag) :
    lineOf p = lineOf q := by
  rcases q with ⟨u, v⟩
  rcases p with ⟨a, b⟩
  obtain ⟨ha, hb, hab⟩ := mem_offDiag.1 hp
  simp only [lineOf, mem_insert, mem_singleton] at ha hb
  have hvsum : v + (u + v) = u := by
    rw [add_comm u v, ← add_assoc, pt_add_self, zero_add]
  have husum : u + (u + v) = v := by rw [← add_assoc, pt_add_self, zero_add]
  have hvsum' : (u + v) + v = u := by rw [add_assoc, pt_add_self, add_zero]
  have husum' : (u + v) + u = v := by rw [add_comm (u + v) u, husum]
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals try exact (hab rfl).elim
  all_goals simp only [lineOf, hvsum, husum, hvsum', husum']
  all_goals ext x
  all_goals simp only [mem_insert, mem_singleton, add_comm, or_comm, or_left_comm, or_assoc]

lemma card_lineOf_of_flag {S : Finset (Pt N)} (h0 : (0 : Pt N) ∉ S)
    {q : Pt N × Pt N} (hq : q ∈ flags S) : (lineOf q).card = 3 := by
  obtain ⟨hu, hv, huv, _⟩ := mem_flags.1 hq
  have hune : q.1 ≠ 0 := fun h => h0 (h ▸ hu)
  have hvne : q.2 ≠ 0 := fun h => h0 (h ▸ hv)
  have huvne : q.1 ≠ q.2 := by
    intro h
    apply h0
    simpa only [h, pt_add_self] using huv
  have huadd : q.1 ≠ q.1 + q.2 := by
    intro h
    apply hvne
    have he : q.1 + 0 = q.1 + q.2 := by simpa using h
    exact (add_left_cancel he).symm
  have hvadd : q.2 ≠ q.1 + q.2 := by
    intro h
    apply hune
    have he : 0 + q.2 = q.1 + q.2 := by simpa using h
    exact (add_right_cancel he).symm
  simp [lineOf, huvne, huadd, hvadd]

lemma violated_fiber_eq_offDiag {S : Finset (Pt N)} (h0 : (0 : Pt N) ∉ S)
    {f : Pt N → ℝ} {q : Pt N × Pt N} (hq : q ∈ violated S f) :
    ((violated S f).filter fun p => lineOf p = lineOf q) = (lineOf q).offDiag := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpv, hpl⟩ := mem_filter.1 hp
    have hpf : p ∈ flags S := (mem_filter.1 hpv).1
    obtain ⟨_, _, h3, _⟩ := mem_flags.1 hpf
    have hne : p.1 ≠ p.2 := by
      intro h
      apply h0
      simpa only [h, pt_add_self] using h3
    rw [mem_offDiag, ← hpl]
    exact ⟨by simp [lineOf], by simp [lineOf], hne⟩
  · intro hp
    exact mem_filter.2 ⟨mem_violated_of_mem_offDiag hq hp, lineOf_of_mem_offDiag hp⟩

/-- Every violated unordered context has exactly six ordered flags.
This statement needs no sign-valuedness assumption on the assignment. -/
theorem card_violated_eq_six (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S)
    (f : Pt N → ℝ) : (violated S f).card = 6 * (violatedLines S f).card := by
  classical
  rw [Finset.card_eq_sum_card_image lineOf (violated S f)]
  have hfiber : ∀ L ∈ (violated S f).image lineOf,
      ((violated S f).filter fun p => lineOf p = L).card = 6 := by
    intro L hL
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hL
    rw [violated_fiber_eq_offDiag h0 hq, Finset.offDiag_card,
      card_lineOf_of_flag h0 (mem_filter.1 hq).1]
  rw [Finset.sum_congr rfl hfiber]
  simp [violatedLines, Nat.mul_comm]

/-- All unordered contexts in the observable set. -/
def contexts (S : Finset (Pt N)) : Finset (Finset (Pt N)) := (flags S).image lineOf

lemma violated_zero_eq_flags (S : Finset (Pt N)) : violated S (fun _ => 0) = flags S := by
  classical
  ext p
  simp only [violated, mem_filter, zero_mul]
  constructor
  · exact And.left
  · intro hp
    refine ⟨hp, ?_⟩
    have hs := (mem_flags.1 hp).2.2.2
    rcases lineSign_eq_one_or_neg_one hs with h | h <;> rw [h] <;> norm_num

/-- All contexts, like violated contexts, carry exactly six flags. -/
theorem card_flags_eq_six_contexts (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S) :
    (flags S).card = 6 * (contexts S).card := by
  have h := card_violated_eq_six S h0 (fun _ => 0)
  simpa only [violatedLines, violated_zero_eq_flags, contexts] using h

end HoggarBound

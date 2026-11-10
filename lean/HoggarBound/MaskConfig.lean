/-
Hoggar Bound Lab — configurations given by a bit mask.

A configuration is given by a bit mask: bit `z` of the mask says whether the observable with code
`z = a + 2^N · c` (`a` the X-part, `c` the Z-part, bit `k` for qubit `k`) belongs to it.  For such a
configuration the number of flags, and the number of flags violated by an assignment that is itself
given by a mask, are double sums over codes of expressions built from bit operations on natural
numbers (`card_flags_cfg`, `card_violated_cfg`), which the kernel can evaluate.

`degree_of_certificate` turns three such evaluated counts and `hoggar_bound` into an exact
contextuality degree.  The instances are in `Saturated.lean`.
-/
import HoggarBound.IndependentContexts

open Finset Matrix

namespace HoggarBound

variable {N : ℕ}

/-! ### Codes -/

/-- Bit `k` of the natural number `z`, as an element of `ZMod 2`. -/
def bitZ (z k : ℕ) : ZMod 2 := if z.testBit k = true then 1 else 0

lemma bitZ_eq_one {z k : ℕ} : bitZ z k = 1 ↔ z.testBit k = true := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  unfold bitZ
  cases z.testBit k <;> simp [h01]

lemma bitZ_xor (z w k : ℕ) : bitZ (z ^^^ w) k = bitZ z k + bitZ w k := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  unfold bitZ
  rw [Nat.testBit_xor]
  cases z.testBit k <;> cases w.testBit k <;> simp [h11]

lemma bitZ_inj {z w k : ℕ} (h : bitZ z k = bitZ w k) : z.testBit k = w.testBit k := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  unfold bitZ at h
  cases h1 : z.testBit k <;> cases h2 : w.testBit k <;> simp [h1, h2, h01, h10] at h ⊢

/-- The observable with code `z`: bit `k` of `z` is its X-part at qubit `k`, bit `N + k` its Z-part. -/
def ptOfCode (N z : ℕ) : Pt N := (fun k => bitZ z k.val, fun k => bitZ z (N + k.val))

lemma ptOfCode_zero (N : ℕ) : ptOfCode N 0 = 0 := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [ptOfCode, bitZ]

lemma ptOfCode_xor (N z w : ℕ) : ptOfCode N (z ^^^ w) = ptOfCode N z + ptOfCode N w := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [ptOfCode, bitZ_xor]

lemma ptOfCode_inj {z w : ℕ} (hz : z < 2 ^ (2 * N)) (hw : w < 2 ^ (2 * N))
    (h : ptOfCode N z = ptOfCode N w) : z = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · exact bitZ_inj (k := i) (congrFun (congrArg Prod.fst h) ⟨i, hi⟩)
  · by_cases hi2 : i < 2 * N
    · have hk : i - N < N := by omega
      have h2 : z.testBit (N + (i - N)) = w.testBit (N + (i - N)) :=
        bitZ_inj (k := N + (i - N)) (congrFun (congrArg Prod.snd h) ⟨i - N, hk⟩)
      have e : N + (i - N) = i := by omega
      rwa [e] at h2
    · have hle : 2 ^ (2 * N) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hz hle),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hw hle)]

/-! ### Counting common bits -/

/-- The number of `k < n` for which bit `i + k` of `z` and bit `j + k` of `w` are both set. -/
def common (z i w j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => common z i w j n + (if (z.testBit (i + n) && w.testBit (j + n)) = true then 1 else 0)

lemma sum_common (z i w j n : ℕ) :
    (∑ k : Fin n, if (z.testBit (i + k.val) && w.testBit (j + k.val)) = true then 1 else 0)
      = common z i w j n := by
  induction n with
  | zero => simp [common]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, common]

lemma ycount_ptOfCode (N z : ℕ) : ycount (ptOfCode N z) = common z 0 z N N := by
  rw [← sum_common, ycount, Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ptOfCode, bitZ_eq_one, zero_add, Bool.and_eq_true]

lemma bitZ_mul (z w i j : ℕ) :
    bitZ z i * bitZ w j
      = (((if (z.testBit i && w.testBit j) = true then 1 else 0 : ℕ)) : ZMod 2) := by
  unfold bitZ
  cases z.testBit i <;> cases w.testBit j <;> simp

lemma dot_ptOfCode (N z w : ℕ) :
    (ptOfCode N z).2 ⬝ᵥ (ptOfCode N w).1 = ((common z N w 0 N : ℕ) : ZMod 2) := by
  rw [← sum_common, Nat.cast_sum]
  simp only [dotProduct, ptOfCode, zero_add]
  exact Finset.sum_congr rfl fun k _ => bitZ_mul z w (N + k.val) k.val

/-- Whether the observables with codes `z` and `w` commute. -/
def commB (N z w : ℕ) : Bool := (common z N w 0 N + common w N z 0 N) % 2 == 0

lemma symp_ptOfCode_eq_zero (N z w : ℕ) :
    symp (ptOfCode N z) (ptOfCode N w) = 0 ↔ commB N z w = true := by
  rw [symp, dot_ptOfCode, dot_ptOfCode, ← Nat.cast_add, ZMod.natCast_eq_zero_iff_even,
    Nat.even_iff, commB, beq_iff_eq]

/-! ### Configurations given by a mask -/

/-- The codes selected by a mask. -/
def codes (N mask : ℕ) : Finset ℕ := (range (2 ^ (2 * N))).filter fun z => mask.testBit z = true

/-- The configuration (set of observables) selected by a mask. -/
def cfg (N mask : ℕ) : Finset (Pt N) := (codes N mask).image (ptOfCode N)

lemma mem_codes {mask z : ℕ} : z ∈ codes N mask ↔ z < 2 ^ (2 * N) ∧ mask.testBit z = true := by
  simp [codes]

lemma ptOfCode_mem_cfg {mask z : ℕ} (hz : z < 2 ^ (2 * N)) :
    ptOfCode N z ∈ cfg N mask ↔ mask.testBit z = true := by
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := Finset.mem_image.1 h
    obtain ⟨hw1, hw2⟩ := mem_codes.1 hw
    rwa [← ptOfCode_inj hw1 hz he]
  · intro h
    exact Finset.mem_image.2 ⟨z, mem_codes.2 ⟨hz, h⟩, rfl⟩

lemma zero_not_mem_cfg {mask : ℕ} (h0 : mask.testBit 0 = false) : (0 : Pt N) ∉ cfg N mask := by
  intro h
  rw [← ptOfCode_zero N, ptOfCode_mem_cfg (Nat.two_pow_pos _), h0] at h
  exact Bool.false_ne_true h

lemma card_cfg (N mask : ℕ) : (cfg N mask).card = (codes N mask).card := by
  refine Finset.card_image_of_injOn fun z hz w hw h => ?_
  exact ptOfCode_inj (mem_codes.1 (Finset.mem_coe.1 hz)).1 (mem_codes.1 (Finset.mem_coe.1 hw)).1 h

/-! ### Sums that the kernel can evaluate -/

/-- `loop g n = g 0 + ⋯ + g (n − 1)`, by plain recursion. -/
def loop (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => loop g n + g n

lemma sum_range_eq_loop (g : ℕ → ℕ) (n : ℕ) : ∑ i ∈ range n, g i = loop g n := by
  induction n with
  | zero => simp [loop]
  | succ n ih => rw [Finset.sum_range_succ, ih, loop]

lemma card_codes (N mask : ℕ) :
    (codes N mask).card = loop (fun z => if mask.testBit z = true then 1 else 0) (2 ^ (2 * N)) := by
  rw [codes, Finset.card_filter, sum_range_eq_loop]

lemma card_pairs (p : ℕ → ℕ → Bool) (n : ℕ) :
    (((range n) ×ˢ (range n)).filter fun q => p q.1 q.2 = true).card
      = loop (fun z => loop (fun w => if p z w = true then 1 else 0) n) n := by
  rw [Finset.card_filter, Finset.sum_product, sum_range_eq_loop]
  congr 1
  funext z
  rw [sum_range_eq_loop]

lemma loop_add (g : ℕ → ℕ) (a b : ℕ) :
    loop g (a + b) = loop g a + loop (fun i => g (a + i)) b := by
  induction b with
  | zero => simp [loop]
  | succ b ih => rw [← Nat.add_assoc, loop, ih, loop, Nat.add_assoc]

/-- Block `k` (of length `m`) of a sum: `g (m k) + ⋯ + g (m k + m − 1)`.  A long sum is evaluated
block by block, in separate theorems, so that no single kernel evaluation is large. -/
def block (g : ℕ → ℕ) (m k : ℕ) : ℕ := loop (fun i => g (m * k + i)) m

lemma loop_blocks (g : ℕ → ℕ) (m n : ℕ) : loop g (m * n) = loop (block g m) n := by
  induction n with
  | zero => simp [loop]
  | succ n ih => rw [Nat.mul_succ, loop_add, ih, loop, block]

lemma loop_sixteen (g : ℕ → ℕ) :
    loop g 16 = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 + g 6 + g 7 + g 8 + g 9 + g 10 + g 11 + g 12
      + g 13 + g 14 + g 15 := by
  simp [loop]

/-! ### Flags of a mask configuration -/

/-- Whether the pair of codes `(z, w)` is a flag of the configuration with the given mask. -/
def flagB (N mask z w : ℕ) : Bool :=
  mask.testBit z && (mask.testBit w && (mask.testBit (z ^^^ w) && commB N z w))

/-- A pair of codes as a pair of observables. -/
def codePair (N : ℕ) (q : ℕ × ℕ) : Pt N × Pt N := (ptOfCode N q.1, ptOfCode N q.2)

lemma codePair_injOn (N : ℕ) :
    Set.InjOn (codePair N) (↑((range (2 ^ (2 * N))) ×ˢ (range (2 ^ (2 * N))) : Finset (ℕ × ℕ))) := by
  intro q hq r hr h
  have hq' := Finset.mem_product.1 (Finset.mem_coe.1 hq)
  have hr' := Finset.mem_product.1 (Finset.mem_coe.1 hr)
  rw [Finset.mem_range, Finset.mem_range] at hq' hr'
  exact Prod.ext (ptOfCode_inj hq'.1 hr'.1 (congrArg Prod.fst h))
    (ptOfCode_inj hq'.2 hr'.2 (congrArg Prod.snd h))

lemma flags_cfg (N mask : ℕ) :
    flags (cfg N mask)
      = (((range (2 ^ (2 * N))) ×ˢ (range (2 ^ (2 * N)))).filter
          fun q => flagB N mask q.1 q.2 = true).image (codePair N) := by
  ext p
  rcases p with ⟨u, v⟩
  rw [mem_flags, Finset.mem_image]
  constructor
  · rintro ⟨hu, hv, huv, hs⟩
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨hz1, hz2⟩ := mem_codes.1 hz
    obtain ⟨hw1, hw2⟩ := mem_codes.1 hw
    refine ⟨(z, w), Finset.mem_filter.2 ⟨Finset.mem_product.2
      ⟨Finset.mem_range.2 hz1, Finset.mem_range.2 hw1⟩, ?_⟩, rfl⟩
    have hx : mask.testBit (z ^^^ w) = true := by
      have := huv
      rwa [← ptOfCode_xor, ptOfCode_mem_cfg (Nat.xor_lt_two_pow hz1 hw1)] at this
    have hc : commB N z w = true := (symp_ptOfCode_eq_zero N z w).1 hs
    simp [flagB, hz2, hw2, hx, hc]
  · rintro ⟨⟨z, w⟩, hq, he⟩
    obtain ⟨hzw, hf⟩ := Finset.mem_filter.1 hq
    obtain ⟨hz1, hw1⟩ := Finset.mem_product.1 hzw
    rw [Finset.mem_range] at hz1 hw1
    have hf' : mask.testBit z = true ∧ mask.testBit w = true ∧ mask.testBit (z ^^^ w) = true ∧
        commB N z w = true := by
      simpa [flagB, Bool.and_eq_true] using hf
    obtain ⟨hz2, hw2, hx, hc⟩ := hf'
    have hu : u = ptOfCode N z := (congrArg Prod.fst he).symm
    have hv : v = ptOfCode N w := (congrArg Prod.snd he).symm
    subst hu
    subst hv
    refine ⟨(ptOfCode_mem_cfg hz1).2 hz2, (ptOfCode_mem_cfg hw1).2 hw2, ?_,
      (symp_ptOfCode_eq_zero N z w).2 hc⟩
    show ptOfCode N z + ptOfCode N w ∈ cfg N mask
    rw [← ptOfCode_xor]
    exact (ptOfCode_mem_cfg (Nat.xor_lt_two_pow hz1 hw1)).2 hx

/-- The number of codes `w` forming a flag with the code `z`. -/
def flagRow (N mask z : ℕ) : ℕ :=
  loop (fun w => if flagB N mask z w = true then 1 else 0) (2 ^ (2 * N))

/-- The number of flags of a mask configuration, as a sum over codes. -/
theorem card_flags_cfg (N mask : ℕ) :
    (flags (cfg N mask)).card = loop (flagRow N mask) (2 ^ (2 * N)) := by
  rw [flags_cfg, Finset.card_image_of_injOn
    ((codePair_injOn N).mono (Finset.coe_subset.2 (Finset.filter_subset _ _))), card_pairs]
  rfl

/-! ### Assignments given by a mask, and the flags they violate -/

/-- The assignment coded by a mask: `-1` on the observables whose bit is set, `+1` elsewhere. -/
def sgnOf (N neg : ℕ) (u : Pt N) : ℤ := if u ∈ cfg N neg then -1 else 1

lemma sgnOf_values (N neg : ℕ) (u : Pt N) :
    ((sgnOf N neg u : ℤ) : ℝ) = 1 ∨ ((sgnOf N neg u : ℤ) : ℝ) = -1 := by
  unfold sgnOf
  split_ifs <;> simp

/-- The same assignment on codes. -/
def sInt (neg z : ℕ) : ℤ := if neg.testBit z = true then -1 else 1

lemma sgnOf_ptOfCode {neg z : ℕ} (hz : z < 2 ^ (2 * N)) : sgnOf N neg (ptOfCode N z) = sInt neg z := by
  unfold sgnOf sInt
  simp only [ptOfCode_mem_cfg hz]

/-- The real part of `i^k`, as an integer. -/
def iPowRe (k : ℕ) : ℤ := if k % 4 = 0 then 1 else if k % 4 = 2 then -1 else 0

/-- The context sign as an integer (the device of `IndependentWitness.lean`). -/
def lineSignInt (u v : Pt N) : ℤ :=
  iPowRe (ycount u + ycount v + 3 * ycount (u + v)) * (if u.2 ⬝ᵥ v.1 = 0 then 1 else -1)

lemma lineSign_eq_int (u v : Pt N) : lineSign u v = ((lineSignInt u v : ℤ) : ℝ) := by
  unfold lineSign tau chi eps lineSignInt iPowRe
  rw [Complex.I_pow_eq_pow_mod]
  have hk : (ycount u + ycount v + 3 * ycount (u + v)) % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases h : (ycount u + ycount v + 3 * ycount (u + v)) % 4 <;>
    by_cases hs : u.2 ⬝ᵥ v.1 = 0 <;> simp [hs, Complex.I_sq, Complex.I_pow_three]

/-- The context sign of a pair of codes. -/
def lineSignCode (N z w : ℕ) : ℤ :=
  iPowRe (common z 0 z N N + common w 0 w N N + 3 * common (z ^^^ w) 0 (z ^^^ w) N N) *
    (if common z N w 0 N % 2 = 0 then 1 else -1)

lemma lineSignInt_ptOfCode (N z w : ℕ) :
    lineSignInt (ptOfCode N z) (ptOfCode N w) = lineSignCode N z w := by
  unfold lineSignInt lineSignCode
  rw [← ptOfCode_xor, ycount_ptOfCode, ycount_ptOfCode, ycount_ptOfCode, dot_ptOfCode]
  simp only [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]

/-- Whether the pair of codes `(z, w)` is a flag violated by the assignment with mask `neg`. -/
def violB (N mask neg z w : ℕ) : Bool :=
  flagB N mask z w &&
    decide (sInt neg z * sInt neg w * sInt neg (z ^^^ w) ≠ lineSignCode N z w)

lemma violated_cfg (N mask neg : ℕ) :
    violated (cfg N mask) (fun u => ((sgnOf N neg u : ℤ) : ℝ))
      = (((range (2 ^ (2 * N))) ×ˢ (range (2 ^ (2 * N)))).filter
          fun q => violB N mask neg q.1 q.2 = true).image (codePair N) := by
  classical
  rw [violated, flags_cfg, Finset.filter_image]
  congr 1
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun q hq => ?_
  obtain ⟨hz, hw⟩ := Finset.mem_product.1 hq
  rw [Finset.mem_range] at hz hw
  simp only [codePair, violB, Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr_right fun _ => ?_
  rw [← ptOfCode_xor, sgnOf_ptOfCode hz, sgnOf_ptOfCode hw,
    sgnOf_ptOfCode (Nat.xor_lt_two_pow hz hw), lineSign_eq_int, lineSignInt_ptOfCode]
  norm_cast

/-- The number of codes `w` forming with `z` a flag violated by the assignment with mask `neg`. -/
def violRow (N mask neg z : ℕ) : ℕ :=
  loop (fun w => if violB N mask neg z w = true then 1 else 0) (2 ^ (2 * N))

/-- The number of flags violated by a mask assignment, as a sum over codes. -/
theorem card_violated_cfg (N mask neg : ℕ) :
    (violated (cfg N mask) (fun u => ((sgnOf N neg u : ℤ) : ℝ))).card
      = loop (violRow N mask neg) (2 ^ (2 * N)) := by
  rw [violated_cfg, Finset.card_image_of_injOn
    ((codePair_injOn N).mono (Finset.coe_subset.2 (Finset.filter_subset _ _))), card_pairs]
  rfl

/-! ### From a certificate to an exact degree -/

/-- The floor when `(D − 1)·|S|` is a perfect square `m²`: `(D − 1)(F − 2V) ≤ (D − 2)·|S|·m`. -/
theorem floor_of_square (hN : 1 ≤ N) (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S) (f : Pt N → ℝ)
    (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) (m : ℝ) (hm0 : 0 ≤ m)
    (hm : ((2 : ℝ) ^ N - 1) * S.card = m ^ 2) :
    ((2 : ℝ) ^ N - 1) * (((flags S).card : ℝ) - 2 * ((violated S f).card : ℝ))
      ≤ ((2 : ℝ) ^ N - 2) * S.card * m := by
  have hb := hoggar_bound_violated hN S h0 f hf
  rwa [hm, Real.sqrt_sq hm0] at hb

/-- **Exact degree from a certificate.**  Let a mask configuration have `n` observables and `F`
flags, let `(D − 1)·n = m²`, and let a mask assignment violate `6·d` flags, where
`(D − 1)(F − 12·d) = (D − 2)·n·m`.  Then every assignment violates at least `d` contexts, and the
mask assignment violates exactly `d`. -/
theorem degree_of_certificate (hN : 1 ≤ N) (mask neg n F d : ℕ) (m : ℝ) (hm0 : 0 ≤ m)
    (h0 : mask.testBit 0 = false)
    (hn : (cfg N mask).card = n) (hF : (flags (cfg N mask)).card = F)
    (hV : (violated (cfg N mask) (fun u => ((sgnOf N neg u : ℤ) : ℝ))).card = 6 * d)
    (hm : ((2 : ℝ) ^ N - 1) * (n : ℝ) = m ^ 2)
    (htight : ((2 : ℝ) ^ N - 1) * ((F : ℝ) - 12 * (d : ℝ)) = ((2 : ℝ) ^ N - 2) * (n : ℝ) * m) :
    (∀ f : Pt N → ℝ, (∀ u ∈ cfg N mask, f u = 1 ∨ f u = -1) →
        d ≤ (violatedLines (cfg N mask) f).card) ∧
      ∃ f : Pt N → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧ (violatedLines (cfg N mask) f).card = d := by
  have hz : (0 : Pt N) ∉ cfg N mask := zero_not_mem_cfg h0
  have hD : (0 : ℝ) < (2 : ℝ) ^ N - 1 := by
    have : (2 : ℝ) ≤ (2 : ℝ) ^ N := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
    linarith
  constructor
  · intro f hf
    have hb := floor_of_square hN (cfg N mask) hz f hf m hm0 (by rw [hn]; exact hm)
    rw [hF, hn, ← htight] at hb
    have h1 : (F : ℝ) - 2 * ((violated (cfg N mask) f).card : ℝ) ≤ (F : ℝ) - 12 * (d : ℝ) :=
      le_of_mul_le_mul_left hb hD
    have h6 := card_violated_eq_six (cfg N mask) hz f
    have h2 : ((6 * d : ℕ) : ℝ) ≤ ((violated (cfg N mask) f).card : ℝ) := by
      push_cast
      linarith
    have h3 : 6 * d ≤ (violated (cfg N mask) f).card := by exact_mod_cast h2
    omega
  · refine ⟨fun u => ((sgnOf N neg u : ℤ) : ℝ), sgnOf_values N neg, ?_⟩
    have h6 := card_violated_eq_six (cfg N mask) hz (fun u => ((sgnOf N neg u : ℤ) : ℝ))
    rw [hV] at h6
    omega

/-- The number of contexts of a mask configuration with `6·L` flags. -/
theorem contexts_of_flags (mask L : ℕ) (h0 : mask.testBit 0 = false)
    (hF : (flags (cfg N mask)).card = 6 * L) : (contexts (cfg N mask)).card = L := by
  have h := card_flags_eq_six_contexts (cfg N mask) (zero_not_mem_cfg h0)
  rw [hF] at h
  omega

end HoggarBound

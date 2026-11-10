/-
Hoggar Bound Lab — the row counts of a mask configuration, evaluated on packed sets.

`MaskConfig.lean` reduces the number of flags of a mask configuration, and the number of flags violated
by a mask assignment, to double sums over codes: `card_flags_cfg` and `card_violated_cfg` are sums of
the rows `flagRow N mask z` and `violRow N mask neg z`, and each row is itself a sum over the `4^N` codes
`w`.  For seven qubits the two double sums have `2^28` terms each, too many for the kernel.

This file evaluates one row with a bounded number of operations on large natural numbers, and proves,
for every `N`, every mask and every code `z`, that the result is the row of `MaskConfig.lean`
(`flagRow_eq_fast`, `violRow_eq_fast`).

A set `S` of codes is *packed* into the number `∑_{w ∈ S} 2^(b·w)`: one digit of `b` bits per code, the
digit being `0` or `1` (`Packed`).  On packed sets

* intersection and symmetric difference are the bitwise `&&&` and `^^^`;
* the translate `{w | w ^^^ z ∈ S}` is obtained by at most `2N` exchanges of blocks of digits
  (`translate`), one for each bit of `z`;
* the set of codes commuting with `z` is the set of all codes, exclusive or at most `2N` fixed stripes,
  the sets of codes with a given bit (`commSet`);
* the number of elements is the remainder modulo `2^b − 1`, because `2^b ≡ 1`; this is the number
  itself as soon as `4^N < 2^b − 1` (`Packed.card`).

The sign of a context needs the number of `Y` factors of an observable modulo 4; its two binary digits
are packed sets as well (`yLow`, `yHigh`).

Nothing here is specific to seven qubits.  No `native_decide`, and no axiom beyond the standard three.
-/
import HoggarBound.MaskConfig

namespace HoggarBound

/-! ### Sums -/

lemma loop_congr {f g : ℕ → ℕ} {n : ℕ} (h : ∀ i, i < n → f i = g i) : loop f n = loop g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [loop, loop, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

lemma loop_zero (n : ℕ) : loop (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [loop, ih]

lemma loop_indicator_le (p : ℕ → Bool) (n : ℕ) :
    loop (fun w => if p w = true then 1 else 0) n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    have h : (if p n = true then 1 else 0) ≤ 1 := by split <;> omega
    show loop (fun w => if p w = true then 1 else 0) n + (if p n = true then 1 else 0) ≤ n + 1
    omega

/-! ### Changing one bit -/

/-- Changing bit `k` of a number in which it is clear adds `2^k`. -/
lemma xor_two_pow_of_not_testBit {w k : ℕ} (h : w.testBit k = false) : w ^^^ 2 ^ k = w + 2 ^ k := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ^ k ∧ w = 2 ^ (k + 1) * q + r := by
    refine ⟨w / 2 ^ (k + 1), w % 2 ^ (k + 1), ?_, (Nat.div_add_mod w _).symm⟩
    have h1 : ¬ (w / 2 ^ k % 2 = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at h
      exact of_decide_eq_false h
    have h2 : w / 2 ^ k % 2 = 0 := by omega
    rw [Nat.mod_pow_succ, h2, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_lt _ (Nat.two_pow_pos k)
  have hr' : r < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  have hlt : r + 2 ^ k < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow, Nat.add_assoc, Nat.testBit_two_pow_mul_add _ hr',
    Nat.testBit_two_pow_mul_add _ hlt]
  by_cases hj : j < k + 1
  · rw [ite_eq_left hj, ite_eq_left hj, ← Nat.or_two_pow_eq_add_of_lt hr, Nat.testBit_or,
      Nat.testBit_two_pow]
    by_cases hjk : k = j
    · subst hjk
      simp [Nat.testBit_lt_two_pow hr]
    · simp [hjk]
  · rw [ite_eq_right hj, ite_eq_right hj]
    have hjk : ¬ k = j := by omega
    simp [hjk]

lemma testBit_xor_two_pow_self (w k : ℕ) : (w ^^^ 2 ^ k).testBit k = !w.testBit k := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self]
  cases w.testBit k <;> rfl

/-- Changing bit `k` of a number in which it is set subtracts `2^k`. -/
lemma xor_two_pow_of_testBit {w k : ℕ} (h : w.testBit k = true) : w ^^^ 2 ^ k = w - 2 ^ k := by
  have h' : (w ^^^ 2 ^ k).testBit k = false := by rw [testBit_xor_two_pow_self, h]; rfl
  have e := xor_two_pow_of_not_testBit h'
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at e
  omega

lemma testBit_sub_two_pow {w k : ℕ} (hle : 2 ^ k ≤ w) : (w - 2 ^ k).testBit k = !w.testBit k := by
  cases hv : (w - 2 ^ k).testBit k
  · have e := xor_two_pow_of_not_testBit hv
    have e2 : w - 2 ^ k + 2 ^ k = w := Nat.sub_add_cancel hle
    have hw : w.testBit k = true := by
      rw [← e2, ← e, testBit_xor_two_pow_self, hv]; rfl
    rw [hw]; rfl
  · cases hw : w.testBit k
    · rfl
    · have e := xor_two_pow_of_testBit hw
      rw [← e, testBit_xor_two_pow_self, hw] at hv
      exact absurd hv (by decide)

/-- The low `m + 1` bits of `z`, from the low `m` bits and bit `m`. -/
lemma mod_two_pow_succ_of_testBit (z m : ℕ) :
    z % 2 ^ (m + 1) = if z.testBit m = true then z % 2 ^ m ^^^ 2 ^ m else z % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hz : z.testBit m = true
  · rw [ite_eq_left hz, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
      Nat.testBit_two_pow]
    by_cases him : m = i
    · subst him
      simp [hz]
    · by_cases h : i < m
      · have h1 : i < m + 1 := by omega
        simp [h, h1, him]
      · have h1 : ¬ i < m + 1 := by omega
        simp [h, h1, him]
  · rw [ite_eq_right hz, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    have hz' : z.testBit m = false := by simpa using hz
    by_cases him : m = i
    · subst him
      simp [hz']
    · by_cases h : i < m
      · have h1 : i < m + 1 := by omega
        simp [h, h1]
      · have h1 : ¬ i < m + 1 := by omega
        simp [h, h1]

/-! ### Parities and the two low binary digits of a count -/

lemma beq_zero_eq_decide (x : ℕ) : (x == 0) = decide (x = 0) := by
  by_cases h : x = 0 <;> simp [h]

lemma decide_even_add (a : ℕ) (t : Bool) :
    decide ((a + (if t = true then 1 else 0)) % 2 = 0) = (decide (a % 2 = 0) ^^ t) := by
  cases t
  · simp
  · by_cases h1 : (a + 1) % 2 = 0 <;> by_cases h2 : a % 2 = 0 <;> simp [h1, h2] <;> omega

lemma decide_odd_add (a : ℕ) (t : Bool) :
    decide ((a + (if t = true then 1 else 0)) % 2 = 1) = (decide (a % 2 = 1) ^^ t) := by
  cases t
  · simp
  · by_cases h1 : (a + 1) % 2 = 1 <;> by_cases h2 : a % 2 = 1 <;> simp [h1, h2] <;> omega

lemma decide_second_add (a : ℕ) (t : Bool) :
    decide ((a + (if t = true then 1 else 0)) / 2 % 2 = 1)
      = (decide (a / 2 % 2 = 1) ^^ (decide (a % 2 = 1) && t)) := by
  cases t
  · simp
  · by_cases h1 : (a + 1) / 2 % 2 = 1 <;> by_cases h2 : a / 2 % 2 = 1 <;> by_cases h3 : a % 2 = 1 <;>
      simp [h1, h2, h3] <;> omega

lemma decide_even_add_add (a c : ℕ) (t s : Bool) :
    decide ((a + (if t = true then 1 else 0) + (c + (if s = true then 1 else 0))) % 2 = 0)
      = ((decide ((a + c) % 2 = 0) ^^ t) ^^ s) := by
  have e : a + (if t = true then 1 else 0) + (c + (if s = true then 1 else 0))
      = a + c + (if t = true then 1 else 0) + (if s = true then 1 else 0) := by omega
  rw [e, decide_even_add, decide_even_add]

/-! ### Packed sets -/

/-- `Packed b n A p`: the number `A` is the set `{w < 2^n | p w}` of codes, with one digit of `b` bits
for each code: bit `b·w` of `A` is set exactly when `w < 2^n` and `p w`, and no other bit is set. -/
structure Packed (b n A : ℕ) (p : ℕ → Bool) : Prop where
  at_code : ∀ w, A.testBit (b * w) = (decide (w < 2 ^ n) && p w)
  off_code : ∀ i, i % b ≠ 0 → A.testBit i = false

namespace Packed

variable {b n A B : ℕ} {p q : ℕ → Bool}

lemma congr (h : Packed b n A p) (hpq : ∀ w, w < 2 ^ n → p w = q w) : Packed b n A q := by
  refine ⟨fun w => ?_, h.off_code⟩
  rw [h.at_code]
  by_cases hw : w < 2 ^ n
  · rw [hpq w hw]
  · simp [hw]

lemma zero (b n : ℕ) : Packed b n 0 (fun _ => false) :=
  ⟨fun w => by simp, fun i _ => Nat.zero_testBit i⟩

lemma and (hA : Packed b n A p) (hB : Packed b n B q) :
    Packed b n (A &&& B) (fun w => p w && q w) := by
  refine ⟨fun w => ?_, fun i hi => ?_⟩
  · rw [Nat.testBit_and, hA.at_code, hB.at_code]
    cases decide (w < 2 ^ n) <;> cases p w <;> cases q w <;> rfl
  · rw [Nat.testBit_and, hA.off_code i hi]; rfl

lemma or (hA : Packed b n A p) (hB : Packed b n B q) :
    Packed b n (A ||| B) (fun w => p w || q w) := by
  refine ⟨fun w => ?_, fun i hi => ?_⟩
  · rw [Nat.testBit_or, hA.at_code, hB.at_code]
    cases decide (w < 2 ^ n) <;> cases p w <;> cases q w <;> rfl
  · rw [Nat.testBit_or, hA.off_code i hi, hB.off_code i hi]; rfl

lemma xor (hA : Packed b n A p) (hB : Packed b n B q) :
    Packed b n (A ^^^ B) (fun w => p w ^^ q w) := by
  refine ⟨fun w => ?_, fun i hi => ?_⟩
  · rw [Nat.testBit_xor, hA.at_code, hB.at_code]
    cases decide (w < 2 ^ n) <;> cases p w <;> cases q w <;> rfl
  · rw [Nat.testBit_xor, hA.off_code i hi, hB.off_code i hi]; rfl

/-- A set of codes below `2^n` is also a set of codes below `2^(n+1)`. -/
lemma extend (h : Packed b n A p) : Packed b (n + 1) A (fun w => decide (w < 2 ^ n) && p w) := by
  refine ⟨fun w => ?_, h.off_code⟩
  rw [h.at_code]
  by_cases hw : w < 2 ^ n
  · have h2 : w < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
    simp [hw, h2]
  · simp [hw]

/-- Shifting by `d` digits to the left adds `d` to every code. -/
lemma shiftLeft (h : Packed b n A p) (hb : 0 < b) (d m : ℕ)
    (hm : ∀ w, w < 2 ^ n → p w = true → w + d < 2 ^ m) :
    Packed b m (A <<< (b * d))
      (fun w => decide (d ≤ w) && (decide (w - d < 2 ^ n) && p (w - d))) := by
  refine ⟨fun w => ?_, fun i hi => ?_⟩
  · rw [Nat.testBit_shiftLeft, ← Nat.mul_sub, h.at_code]
    by_cases hdw : d ≤ w
    · have h1 : b * w ≥ b * d := Nat.mul_le_mul_left b hdw
      by_cases hwn : w - d < 2 ^ n
      · cases hp : p (w - d)
        · simp
        · have h2 := hm (w - d) hwn hp
          have hwm : w < 2 ^ m := by omega
          simp [hdw, h1, hwn, hwm]
      · simp [hwn]
    · have h1 : ¬ b * w ≥ b * d := fun hc => hdw ((Nat.mul_le_mul_left_iff hb).1 hc)
      simp [hdw, h1]
  · rw [Nat.testBit_shiftLeft]
    by_cases hge : i ≥ b * d
    · rw [h.off_code (i - b * d) (by rw [Nat.sub_mul_mod hge]; exact hi)]
      simp
    · simp [hge]

/-- Shifting by `d` digits to the right subtracts `d` from every code. -/
lemma shiftRight (h : Packed b n A p) (d : ℕ) :
    Packed b n (A >>> (b * d)) (fun w => decide (d + w < 2 ^ n) && p (d + w)) := by
  refine ⟨fun w => ?_, fun i hi => ?_⟩
  · rw [Nat.testBit_shiftRight, ← Nat.mul_add, h.at_code]
    by_cases hw : d + w < 2 ^ n
    · have h2 : w < 2 ^ n := by omega
      simp [hw, h2]
    · simp [hw]
  · rw [Nat.testBit_shiftRight]
    exact h.off_code _ (by rw [Nat.mul_add_mod]; exact hi)

end Packed

/-! ### Building packed sets -/

lemma packed_toNat {b : ℕ} (hb : 0 < b) (c : Bool) : Packed b 0 c.toNat (fun _ => c) := by
  refine ⟨fun w => ?_, fun i hi => ?_⟩
  · rw [Nat.testBit_bool_toNat]
    by_cases hw : w = 0
    · subst hw
      simp
    · have h1 : b * w ≠ 0 := Nat.mul_ne_zero (Nat.pos_iff_ne_zero.1 hb) hw
      have h2 : ¬ w < 2 ^ 0 := by rw [Nat.pow_zero]; omega
      rw [decide_eq_false h1, decide_eq_false h2]
  · rw [Nat.testBit_bool_toNat]
    have h0 : i ≠ 0 := fun h => hi (by rw [h]; exact Nat.zero_mod b)
    simp [h0]

/-- The packed set of the codes `w < 2^k` with `p (lo + w)`, by repeated doubling. -/
def pack (b : ℕ) (p : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, lo => (p lo).toNat
  | k + 1, lo => pack b p k lo ||| (pack b p k (lo + 2 ^ k) <<< (b * 2 ^ k))

lemma packed_pack {b : ℕ} (hb : 0 < b) (p : ℕ → Bool) :
    ∀ k lo, Packed b k (pack b p k lo) (fun w => p (lo + w)) := by
  intro k
  induction k with
  | zero =>
    intro lo
    refine (packed_toNat hb (p lo)).congr (fun w hw => ?_)
    have hw0 : w = 0 := by rw [Nat.pow_zero] at hw; omega
    rw [hw0, Nat.add_zero]
  | succ k ih =>
    intro lo
    have hY := (ih (lo + 2 ^ k)).shiftLeft hb (2 ^ k) (k + 1)
      (fun w hw _ => by rw [Nat.pow_succ]; omega)
    show Packed b (k + 1) (pack b p k lo ||| (pack b p k (lo + 2 ^ k) <<< (b * 2 ^ k))) _
    refine ((ih lo).extend.or hY).congr (fun w hw => ?_)
    rw [Nat.pow_succ] at hw
    by_cases h : w < 2 ^ k
    · have h' : ¬ 2 ^ k ≤ w := by omega
      simp [h, h']
    · have h' : 2 ^ k ≤ w := by omega
      have h2 : w - 2 ^ k < 2 ^ k := by omega
      have e : lo + 2 ^ k + (w - 2 ^ k) = lo + w := by omega
      simp [h, h', h2, e]

/-- The packed set of all codes below `2^k`. -/
def ones (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => ones b k ||| (ones b k <<< (b * 2 ^ k))

lemma packed_ones {b : ℕ} (hb : 0 < b) : ∀ k, Packed b k (ones b k) (fun _ => true)
  | 0 => packed_toNat hb true
  | k + 1 => by
    have ih := packed_ones hb k
    have hY := ih.shiftLeft hb (2 ^ k) (k + 1) (fun w hw _ => by rw [Nat.pow_succ]; omega)
    show Packed b (k + 1) (ones b k ||| (ones b k <<< (b * 2 ^ k))) _
    refine (ih.extend.or hY).congr (fun w hw => ?_)
    rw [Nat.pow_succ] at hw
    by_cases h : w < 2 ^ k
    · simp [h]
    · have h' : 2 ^ k ≤ w := by omega
      have h2 : w - 2 ^ k < 2 ^ k := by omega
      simp [h, h', h2]

/-- The packed set of the codes below `2^k` whose bit `j` is set. -/
def stripe (b j : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if k < j then 0
    else if k = j then ones b k <<< (b * 2 ^ k)
    else stripe b j k ||| (stripe b j k <<< (b * 2 ^ k))

lemma packed_stripe {b : ℕ} (hb : 0 < b) (j : ℕ) :
    ∀ k, Packed b k (stripe b j k) (fun w => w.testBit j)
  | 0 => by
    refine (Packed.zero b 0).congr (fun w hw => ?_)
    have hw0 : w = 0 := by rw [Nat.pow_zero] at hw; omega
    rw [hw0, Nat.zero_testBit]
  | k + 1 => by
    have ih := packed_stripe hb j k
    by_cases h1 : k < j
    · rw [stripe, ite_eq_left h1]
      refine (Packed.zero b (k + 1)).congr (fun w hw => ?_)
      have hle : 2 ^ (k + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h1
      exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw hle)).symm
    · by_cases h2 : k = j
      · rw [stripe, ite_eq_right h1, ite_eq_left h2]
        subst h2
        have hY := (packed_ones hb k).shiftLeft hb (2 ^ k) (k + 1)
          (fun w hw _ => by rw [Nat.pow_succ]; omega)
        refine hY.congr (fun w hw => ?_)
        by_cases h : 2 ^ k ≤ w
        · have h3 : w - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hw; omega
          have h4 := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h hw
          simp [h, h3, h4]
        · have h4 := Nat.testBit_lt_two_pow (Nat.lt_of_not_le h)
          simp [h, h4]
      · rw [stripe, ite_eq_right h1, ite_eq_right h2]
        have hjk : j < k := by omega
        have hY := ih.shiftLeft hb (2 ^ k) (k + 1) (fun w hw _ => by rw [Nat.pow_succ]; omega)
        refine (ih.extend.or hY).congr (fun w hw => ?_)
        rw [Nat.pow_succ] at hw
        by_cases h : w < 2 ^ k
        · have h' : ¬ 2 ^ k ≤ w := by omega
          simp [h, h']
        · have h' : 2 ^ k ≤ w := by omega
          have h3 : w - 2 ^ k < 2 ^ k := by omega
          have h4 : (2 ^ k + (w - 2 ^ k)).testBit j = (w - 2 ^ k).testBit j :=
            Nat.testBit_two_pow_add_gt hjk _
          have e : 2 ^ k + (w - 2 ^ k) = w := by omega
          rw [e] at h4
          simp [h, h', h3, h4]

/-! ### Counting the elements of a packed set -/

namespace Packed

variable {b n A : ℕ} {p : ℕ → Bool}

/-- Since `2^b ≡ 1` modulo `2^b − 1`, a packed set is congruent to its number of elements. -/
lemma mod_eq (hb : 0 < b) : ∀ (n : ℕ) {A : ℕ} {p : ℕ → Bool}, Packed b n A p →
    A % (2 ^ b - 1) = loop (fun w => if p w = true then 1 else 0) (2 ^ n) % (2 ^ b - 1)
  | 0, A, p, h => by
    have hA : A = (p 0).toNat := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_bool_toNat]
      by_cases hi : i % b = 0
      · obtain ⟨w, rfl⟩ : ∃ w, i = b * w := ⟨i / b, by have := Nat.div_add_mod i b; omega⟩
        rw [h.at_code]
        by_cases hw : w = 0
        · subst hw
          simp
        · have h1 : b * w ≠ 0 := Nat.mul_ne_zero (Nat.pos_iff_ne_zero.1 hb) hw
          have h2 : ¬ w < 2 ^ 0 := by rw [Nat.pow_zero]; omega
          rw [decide_eq_false h1, decide_eq_false h2, Bool.false_and, Bool.false_and]
      · rw [h.off_code i hi]
        have h0 : i ≠ 0 := fun h0 => hi (by rw [h0]; exact Nat.zero_mod b)
        simp [h0]
    have hl : loop (fun w => if p w = true then 1 else 0) (2 ^ 0) = (p 0).toNat := by
      show 0 + (if p 0 = true then 1 else 0) = (p 0).toNat
      cases p 0 <;> rfl
    rw [hA, hl]
  | n + 1, A, p, h => by
    have hlo : Packed b n (A % 2 ^ (b * 2 ^ n)) p := by
      refine ⟨fun w => ?_, fun i hi => ?_⟩
      · rw [Nat.testBit_mod_two_pow, h.at_code]
        by_cases hw : w < 2 ^ n
        · have h1 : b * w < b * 2 ^ n := (Nat.mul_lt_mul_left hb).2 hw
          have h2 : w < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
          simp [hw, h1, h2]
        · have h1 : ¬ b * w < b * 2 ^ n := fun hc => hw ((Nat.mul_lt_mul_left hb).1 hc)
          simp [hw, h1]
      · rw [Nat.testBit_mod_two_pow, h.off_code i hi]
        simp
    have hhi : Packed b n (A >>> (b * 2 ^ n)) (fun w => p (2 ^ n + w)) := by
      refine ⟨fun w => ?_, fun i hi => ?_⟩
      · rw [Nat.testBit_shiftRight, ← Nat.mul_add, h.at_code]
        by_cases hw : w < 2 ^ n
        · have h2 : 2 ^ n + w < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
          simp [hw, h2]
        · have h2 : ¬ 2 ^ n + w < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
          simp [hw, h2]
      · rw [Nat.testBit_shiftRight]
        exact h.off_code _ (by rw [Nat.mul_add_mod]; exact hi)
    have e1 := mod_eq hb n hlo
    have e2 := mod_eq hb n hhi
    have hA : A % 2 ^ (b * 2 ^ n) + 2 ^ (b * 2 ^ n) * (A >>> (b * 2 ^ n)) = A := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.mod_add_div A _
    have h1 : 2 ^ b % (2 ^ b - 1) = 1 % (2 ^ b - 1) := by
      have e : 2 ^ b - 1 + 1 = 2 ^ b := Nat.sub_add_cancel Nat.one_le_two_pow
      have h := Nat.add_mod_left (2 ^ b - 1) 1
      rwa [e] at h
    have hpow : 2 ^ (b * 2 ^ n) % (2 ^ b - 1) = 1 % (2 ^ b - 1) := by
      rw [Nat.pow_mul, Nat.pow_mod, h1, ← Nat.pow_mod, Nat.one_pow]
    have key : 2 ^ (b * 2 ^ n) * (A >>> (b * 2 ^ n)) % (2 ^ b - 1)
        = (A >>> (b * 2 ^ n)) % (2 ^ b - 1) := by
      rw [Nat.mul_mod, hpow, ← Nat.mul_mod, Nat.one_mul]
    have hsplit : loop (fun w => if p w = true then 1 else 0) (2 ^ (n + 1))
        = loop (fun w => if p w = true then 1 else 0) (2 ^ n)
          + loop (fun w => if p (2 ^ n + w) = true then 1 else 0) (2 ^ n) := by
      have e : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
      rw [e, loop_add]
    calc A % (2 ^ b - 1)
        = (A % 2 ^ (b * 2 ^ n) + 2 ^ (b * 2 ^ n) * (A >>> (b * 2 ^ n))) % (2 ^ b - 1) := by rw [hA]
      _ = (A % 2 ^ (b * 2 ^ n) % (2 ^ b - 1)
            + 2 ^ (b * 2 ^ n) * (A >>> (b * 2 ^ n)) % (2 ^ b - 1)) % (2 ^ b - 1) := Nat.add_mod _ _ _
      _ = (loop (fun w => if p w = true then 1 else 0) (2 ^ n) % (2 ^ b - 1)
            + loop (fun w => if p (2 ^ n + w) = true then 1 else 0) (2 ^ n) % (2 ^ b - 1))
            % (2 ^ b - 1) := by rw [key, e1, e2]
      _ = (loop (fun w => if p w = true then 1 else 0) (2 ^ n)
            + loop (fun w => if p (2 ^ n + w) = true then 1 else 0) (2 ^ n)) % (2 ^ b - 1) :=
          (Nat.add_mod _ _ _).symm
      _ = loop (fun w => if p w = true then 1 else 0) (2 ^ (n + 1)) % (2 ^ b - 1) := by rw [hsplit]

/-- **Counting.**  When there are fewer than `2^b − 1` codes, the number of elements of a packed set
is its remainder modulo `2^b − 1`. -/
theorem card (h : Packed b n A p) (hb : 0 < b) (hlt : 2 ^ n < 2 ^ b - 1) :
    A % (2 ^ b - 1) = loop (fun w => if p w = true then 1 else 0) (2 ^ n) := by
  rw [mod_eq hb n h]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (loop_indicator_le p _) hlt)

end Packed

/-! ### Translates -/

/-- Exchange the digits of the codes that differ in bit `k`; `L` is the packed set of the codes whose
bit `k` is clear. -/
def swapBlocks (b k L A : ℕ) : ℕ :=
  ((A &&& L) <<< (b * 2 ^ k)) ||| ((A >>> (b * 2 ^ k)) &&& L)

lemma Packed.swap {b n A : ℕ} {p : ℕ → Bool} (hA : Packed b n A p) (hb : 0 < b) {k : ℕ}
    (hk : k < n) {L : ℕ} (hL : Packed b n L (fun w => !w.testBit k)) :
    Packed b n (swapBlocks b k L A) (fun w => p (w ^^^ 2 ^ k)) := by
  have hkn : 2 ^ k < 2 ^ n := Nat.pow_lt_pow_right (by decide) hk
  have h1 := (hA.and hL).shiftLeft hb (2 ^ k) n (fun w hw hq => by
    have hbit : w.testBit k = false := by
      cases hwk : w.testBit k
      · rfl
      · simp [hwk] at hq
    rw [← xor_two_pow_of_not_testBit hbit]
    exact Nat.xor_lt_two_pow hw hkn)
  have h2 := (hA.shiftRight (2 ^ k)).and hL
  refine (h1.or h2).congr (fun w hw => ?_)
  cases hwk : w.testBit k
  · have e : w ^^^ 2 ^ k = 2 ^ k + w := by
      rw [xor_two_pow_of_not_testBit hwk, Nat.add_comm]
    have hlt : 2 ^ k + w < 2 ^ n := by
      rw [← e]
      exact Nat.xor_lt_two_pow hw hkn
    by_cases hle : 2 ^ k ≤ w
    · have hsub : (w - 2 ^ k).testBit k = true := by
        rw [testBit_sub_two_pow hle, hwk]; rfl
      simp [hle, hsub, hlt, e]
    · simp [hle, hlt, e]
  · have hle : 2 ^ k ≤ w := Nat.ge_two_pow_of_testBit hwk
    have e := xor_two_pow_of_testBit hwk
    have hsub : (w - 2 ^ k).testBit k = false := by
      rw [testBit_sub_two_pow hle, hwk]; rfl
    have hlt : w - 2 ^ k < 2 ^ n := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hw
    simp [hle, hsub, hlt, e]

/-- The translate of the packed set `A` by the low `m` bits of `z`: one exchange of blocks for each
set bit.  `all` is the packed set of all codes and `st j` the packed set of the codes with bit `j`. -/
def translate (b all : ℕ) (st : ℕ → ℕ) (z A : ℕ) : ℕ → ℕ
  | 0 => A
  | m + 1 =>
    bif z.testBit m then swapBlocks b m (all ^^^ st m) (translate b all st z A m)
    else translate b all st z A m

lemma packed_translate {b n all A : ℕ} {st : ℕ → ℕ} {p : ℕ → Bool} (hb : 0 < b)
    (hall : Packed b n all (fun _ => true)) (hst : ∀ j, Packed b n (st j) (fun w => w.testBit j))
    (z : ℕ) (hA : Packed b n A p) :
    ∀ m, m ≤ n → Packed b n (translate b all st z A m) (fun w => p (w ^^^ z % 2 ^ m))
  | 0, _ => hA.congr (fun w _ => by rw [Nat.pow_zero, Nat.mod_one, Nat.xor_zero])
  | m + 1, hm => by
    have ih := packed_translate hb hall hst z hA m (by omega)
    have hL : Packed b n (all ^^^ st m) (fun w => !w.testBit m) :=
      (hall.xor (hst m)).congr (fun w _ => by cases w.testBit m <;> rfl)
    show Packed b n (bif z.testBit m then swapBlocks b m (all ^^^ st m) (translate b all st z A m)
      else translate b all st z A m) _
    cases hz : z.testBit m
    · refine ih.congr (fun w _ => ?_)
      rw [mod_two_pow_succ_of_testBit, hz]
      rfl
    · refine (ih.swap hb (by omega) hL).congr (fun w _ => ?_)
      rw [mod_two_pow_succ_of_testBit, hz]
      show p (w ^^^ 2 ^ m ^^^ z % 2 ^ m) = p (w ^^^ (z % 2 ^ m ^^^ 2 ^ m))
      rw [Nat.xor_assoc, Nat.xor_comm (2 ^ m)]

/-! ### Commutation and the parts of the sign that are linear in `w` -/

/-- `A ^^^ M` if `c`, and `A` otherwise. -/
def xorIf (c : Bool) (M A : ℕ) : ℕ := bif c then A ^^^ M else A

lemma Packed.xor_if {b n A M : ℕ} {p q : ℕ → Bool} (hA : Packed b n A p) (c : Bool)
    (hM : Packed b n M q) : Packed b n (xorIf c M A) (fun w => p w ^^ (c && q w)) := by
  cases c
  · exact hA.congr (fun w _ => by simp)
  · exact (hA.xor hM).congr (fun w _ => by simp)

/-- The packed set of the codes that commute with `z`. -/
def commSet (all : ℕ) (st : ℕ → ℕ) (N z : ℕ) : ℕ → ℕ
  | 0 => all
  | k + 1 =>
    xorIf (z.testBit k) (st (N + k)) (xorIf (z.testBit (N + k)) (st k) (commSet all st N z k))

lemma packed_commSet {b n all : ℕ} {st : ℕ → ℕ} (hall : Packed b n all (fun _ => true))
    (hst : ∀ j, Packed b n (st j) (fun w => w.testBit j)) (N z : ℕ) :
    ∀ k, Packed b n (commSet all st N z k)
      (fun w => decide ((common z N w 0 k + common w N z 0 k) % 2 = 0))
  | 0 => hall.congr (fun w _ => by simp [common])
  | k + 1 => by
    have ih := packed_commSet hall hst N z k
    show Packed b n (xorIf (z.testBit k) (st (N + k))
      (xorIf (z.testBit (N + k)) (st k) (commSet all st N z k))) _
    refine ((ih.xor_if _ (hst k)).xor_if _ (hst (N + k))).congr (fun w _ => ?_)
    show ((decide ((common z N w 0 k + common w N z 0 k) % 2 = 0)
        ^^ (z.testBit (N + k) && w.testBit k)) ^^ (z.testBit k && w.testBit (N + k)))
      = decide ((common z N w 0 k + (if (z.testBit (N + k) && w.testBit (0 + k)) = true then 1 else 0)
          + (common w N z 0 k + (if (w.testBit (N + k) && z.testBit (0 + k)) = true then 1 else 0)))
          % 2 = 0)
    rw [decide_even_add_add, Nat.zero_add, Bool.and_comm (w.testBit (N + k))]

/-- The packed set of the codes `w` for which the Z-part of `z` meets the X-part of `w` in an odd
number of qubits. -/
def dotSet (st : ℕ → ℕ) (N z : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => xorIf (z.testBit (N + k)) (st k) (dotSet st N z k)

lemma packed_dotSet {b n : ℕ} {st : ℕ → ℕ}
    (hst : ∀ j, Packed b n (st j) (fun w => w.testBit j)) (N z : ℕ) :
    ∀ k, Packed b n (dotSet st N z k) (fun w => decide (common z N w 0 k % 2 = 1))
  | 0 => (Packed.zero b n).congr (fun w _ => by simp [common])
  | k + 1 => by
    have ih := packed_dotSet hst N z k
    show Packed b n (xorIf (z.testBit (N + k)) (st k) (dotSet st N z k)) _
    refine (ih.xor_if _ (hst k)).congr (fun w _ => ?_)
    show (decide (common z N w 0 k % 2 = 1) ^^ (z.testBit (N + k) && w.testBit k))
      = decide ((common z N w 0 k + (if (z.testBit (N + k) && w.testBit (0 + k)) = true then 1 else 0))
          % 2 = 1)
    rw [decide_odd_add, Nat.zero_add]

/-! ### The number of `Y` factors modulo 4 -/

/-- The packed set of the codes with an odd number of `Y` factors among the first `k` qubits. -/
def yLow (st : ℕ → ℕ) (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => yLow st N k ^^^ (st k &&& st (N + k))

/-- The packed set of the codes whose number of `Y` factors among the first `k` qubits is 2 or 3
modulo 4. -/
def yHigh (st : ℕ → ℕ) (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => yHigh st N k ^^^ (yLow st N k &&& (st k &&& st (N + k)))

lemma packed_yLow {b n : ℕ} {st : ℕ → ℕ}
    (hst : ∀ j, Packed b n (st j) (fun w => w.testBit j)) (N : ℕ) :
    ∀ k, Packed b n (yLow st N k) (fun w => decide (common w 0 w N k % 2 = 1))
  | 0 => (Packed.zero b n).congr (fun w _ => by simp [common])
  | k + 1 => by
    have ih := packed_yLow hst N k
    show Packed b n (yLow st N k ^^^ (st k &&& st (N + k))) _
    refine (ih.xor ((hst k).and (hst (N + k)))).congr (fun w _ => ?_)
    show (decide (common w 0 w N k % 2 = 1) ^^ (w.testBit k && w.testBit (N + k)))
      = decide ((common w 0 w N k + (if (w.testBit (0 + k) && w.testBit (N + k)) = true then 1 else 0))
          % 2 = 1)
    rw [decide_odd_add, Nat.zero_add]

lemma packed_yHigh {b n : ℕ} {st : ℕ → ℕ}
    (hst : ∀ j, Packed b n (st j) (fun w => w.testBit j)) (N : ℕ) :
    ∀ k, Packed b n (yHigh st N k) (fun w => decide (common w 0 w N k / 2 % 2 = 1))
  | 0 => (Packed.zero b n).congr (fun w _ => by simp [common])
  | k + 1 => by
    have ih := packed_yHigh hst N k
    show Packed b n (yHigh st N k ^^^ (yLow st N k &&& (st k &&& st (N + k)))) _
    refine (ih.xor ((packed_yLow hst N k).and ((hst k).and (hst (N + k))))).congr (fun w _ => ?_)
    show (decide (common w 0 w N k / 2 % 2 = 1)
        ^^ (decide (common w 0 w N k % 2 = 1) && (w.testBit k && w.testBit (N + k))))
      = decide ((common w 0 w N k + (if (w.testBit (0 + k) && w.testBit (N + k)) = true then 1 else 0))
          / 2 % 2 = 1)
    rw [decide_second_add, Nat.zero_add]

/-! ### The sign of a context, for commuting codes -/

/-- Whether the observable with code `u` has an odd number of `Y` factors. -/
def yBit (N u : ℕ) : Bool := decide (common u 0 u N N % 2 = 1)

/-- The value of the assignment at `u` (as a bit), exclusive or the second binary digit of the number
of `Y` factors of `u`. -/
def gBit (neg N u : ℕ) : Bool := neg.testBit u ^^ decide (common u 0 u N N / 2 % 2 = 1)

/-- The number of `Y` factors of a product, modulo 2. -/
lemma common_xor_self (z w N : ℕ) : ∀ n,
    common (z ^^^ w) 0 (z ^^^ w) N n % 2
      = (common z 0 z N n + common w 0 w N n + common z N w 0 n + common w N z 0 n) % 2
  | 0 => rfl
  | n + 1 => by
    have ih := common_xor_self z w N n
    simp only [common, Nat.zero_add, Nat.testBit_xor]
    cases z.testBit n <;> cases w.testBit n <;> cases z.testBit (N + n) <;>
      cases w.testBit (N + n) <;> simp <;> omega

lemma iPowRe_mod (k : ℕ) : iPowRe k = iPowRe (k % 4) := by
  unfold iPowRe
  rw [Nat.mod_mod]

/-- The sign rule on residues: `P`, `Q`, `R` are the numbers of `Y` factors of two commuting observables
and of their product modulo 4, `D` the parity of the phase exponent, and `a`, `b`, `c` the three assigned
values as bits.  A finite statement: 8 times 128 cases, evaluated by the kernel. -/
theorem sign_table (a b c : Bool) : ∀ P < 4, ∀ Q < 4, ∀ R < 4, ∀ D < 2,
    R % 2 = (P + Q) % 2 →
    decide ((if a = true then (-1 : ℤ) else 1) * (if b = true then -1 else 1)
          * (if c = true then -1 else 1)
        ≠ iPowRe (P + Q + 3 * R) * (if D % 2 = 0 then 1 else -1))
      = (((((a ^^ decide (P / 2 % 2 = 1)) ^^ (b ^^ decide (Q / 2 % 2 = 1)))
            ^^ (c ^^ decide (R / 2 % 2 = 1)))
          ^^ (decide (P % 2 = 1) && decide (Q % 2 = 1))) ^^ decide (D % 2 = 1)) := by
  cases a <;> cases b <;> cases c <;> decide +kernel

/-- **The sign of a context.**  For commuting codes `z` and `w`, the assignment with mask `neg` violates
the context `{z, w, z ^^^ w}` exactly when an exclusive or of five bits is set. -/
theorem viol_bit (neg N z w : ℕ) (hc : commB N z w = true) :
    decide (sInt neg z * sInt neg w * sInt neg (z ^^^ w) ≠ lineSignCode N z w)
      = ((((gBit neg N z ^^ gBit neg N w) ^^ gBit neg N (z ^^^ w)) ^^ (yBit N z && yBit N w))
          ^^ decide (common z N w 0 N % 2 = 1)) := by
  have hpar := common_xor_self z w N N
  have hcomm : (common z N w 0 N + common w N z 0 N) % 2 = 0 := by
    simpa [commB] using hc
  have hR : common (z ^^^ w) 0 (z ^^^ w) N N % 4 % 2
      = (common z 0 z N N % 4 + common w 0 w N N % 4) % 2 := by omega
  have key := sign_table (neg.testBit z) (neg.testBit w) (neg.testBit (z ^^^ w))
    (common z 0 z N N % 4) (Nat.mod_lt _ (by decide))
    (common w 0 w N N % 4) (Nat.mod_lt _ (by decide))
    (common (z ^^^ w) 0 (z ^^^ w) N N % 4) (Nat.mod_lt _ (by decide))
    (common z N w 0 N % 2) (Nat.mod_lt _ (by decide)) hR
  have e0 : iPowRe (common z 0 z N N % 4 + common w 0 w N N % 4
        + 3 * (common (z ^^^ w) 0 (z ^^^ w) N N % 4))
      = iPowRe (common z 0 z N N + common w 0 w N N + 3 * common (z ^^^ w) 0 (z ^^^ w) N N) := by
    rw [iPowRe_mod, iPowRe_mod (common z 0 z N N + common w 0 w N N
      + 3 * common (z ^^^ w) 0 (z ^^^ w) N N)]
    congr 1
    omega
  have e1 : common z 0 z N N % 4 / 2 % 2 = common z 0 z N N / 2 % 2 := by omega
  have e2 : common w 0 w N N % 4 / 2 % 2 = common w 0 w N N / 2 % 2 := by omega
  have e3 : common (z ^^^ w) 0 (z ^^^ w) N N % 4 / 2 % 2
      = common (z ^^^ w) 0 (z ^^^ w) N N / 2 % 2 := by omega
  have e4 : common z 0 z N N % 4 % 2 = common z 0 z N N % 2 := by omega
  have e5 : common w 0 w N N % 4 % 2 = common w 0 w N N % 2 := by omega
  rw [e0, e1, e2, e3, e4, e5, Nat.mod_mod] at key
  exact key

/-! ### One row -/

/-- The packed set of the codes `w` such that `(z, w)` is a flag, for a code `z` of the configuration.
`sm` is the packed mask. -/
def flagSet (b N sm all : ℕ) (st : ℕ → ℕ) (z : ℕ) : ℕ :=
  sm &&& translate b all st z sm (2 * N) &&& commSet all st N z N

/-- The packed set of the codes `w` such that the context `{z, w, z ^^^ w}`, if it is one, is violated.
`sg` is the packed set of the codes with `gBit`, `y0` the packed set of the codes with `yBit`. -/
def signSet (b N neg sg y0 all : ℕ) (st : ℕ → ℕ) (z : ℕ) : ℕ :=
  xorIf (gBit neg N z) all
    (xorIf (yBit N z) y0 (sg ^^^ translate b all st z sg (2 * N) ^^^ dotSet st N z N))

/-- A row of the flag count, from the tables. -/
def flagRowOn (b N mask sm all : ℕ) (st : ℕ → ℕ) (z : ℕ) : ℕ :=
  bif mask.testBit z then flagSet b N sm all st z % (2 ^ b - 1) else 0

/-- A row of the count of violated flags, from the tables. -/
def violRowOn (b N mask neg sm sg y0 all : ℕ) (st : ℕ → ℕ) (z : ℕ) : ℕ :=
  bif mask.testBit z then
    (flagSet b N sm all st z &&& signSet b N neg sg y0 all st z) % (2 ^ b - 1)
  else 0

/-- The number of codes forming a flag with `z`, evaluated on packed sets with digits of `b` bits. -/
def fastFlagRow (b N mask : ℕ) : ℕ → ℕ :=
  flagRowOn b N mask (pack b mask.testBit (2 * N) 0) (ones b (2 * N)) (fun j => stripe b j (2 * N))

/-- The number of codes forming with `z` a flag violated by the assignment with mask `neg`, evaluated
on packed sets with digits of `b` bits. -/
def fastViolRow (b N mask neg : ℕ) : ℕ → ℕ :=
  violRowOn b N mask neg (pack b mask.testBit (2 * N) 0)
    (pack b neg.testBit (2 * N) 0 ^^^ yHigh (fun j => stripe b j (2 * N)) N N)
    (yLow (fun j => stripe b j (2 * N)) N N) (ones b (2 * N)) (fun j => stripe b j (2 * N))

lemma packed_mask {b : ℕ} (hb : 0 < b) (mask n : ℕ) :
    Packed b n (pack b mask.testBit n 0) (fun w => mask.testBit w) :=
  (packed_pack hb mask.testBit n 0).congr (fun w _ => by rw [Nat.zero_add])

lemma packed_flagSet {b : ℕ} (hb : 0 < b) (N mask : ℕ) {z : ℕ} (hz : z < 2 ^ (2 * N)) :
    Packed b (2 * N)
      (flagSet b N (pack b mask.testBit (2 * N) 0) (ones b (2 * N)) (fun j => stripe b j (2 * N)) z)
      (fun w => mask.testBit w && (mask.testBit (z ^^^ w) && commB N z w)) := by
  have hall := packed_ones hb (2 * N)
  have hst := fun j => packed_stripe hb j (2 * N)
  have hsm := packed_mask hb mask (2 * N)
  have htm := packed_translate hb hall hst z hsm (2 * N) (Nat.le_refl _)
  have hc := packed_commSet hall hst N z N
  refine ((hsm.and htm).and hc).congr (fun w _ => ?_)
  show ((mask.testBit w && mask.testBit (w ^^^ z % 2 ^ (2 * N)))
      && decide ((common z N w 0 N + common w N z 0 N) % 2 = 0))
    = (mask.testBit w && (mask.testBit (z ^^^ w)
      && ((common z N w 0 N + common w N z 0 N) % 2 == 0)))
  rw [Nat.mod_eq_of_lt hz, Nat.xor_comm w z, Bool.and_assoc, beq_zero_eq_decide]

/-- **A row of the flag count.**  For every number of qubits, every mask and every code `z`, the
evaluation on packed sets is the row of `card_flags_cfg`. -/
theorem flagRow_eq_fast {b N : ℕ} (hb : 0 < b) (hlt : 2 ^ (2 * N) < 2 ^ b - 1) (mask : ℕ) {z : ℕ}
    (hz : z < 2 ^ (2 * N)) : flagRow N mask z = fastFlagRow b N mask z := by
  show loop (fun w => if flagB N mask z w = true then 1 else 0) (2 ^ (2 * N))
    = bif mask.testBit z then
        flagSet b N (pack b mask.testBit (2 * N) 0) (ones b (2 * N))
          (fun j => stripe b j (2 * N)) z % (2 ^ b - 1)
      else 0
  cases hmz : mask.testBit z
  · show loop (fun w => if flagB N mask z w = true then 1 else 0) (2 ^ (2 * N)) = 0
    exact (loop_congr (fun w _ => by simp [flagB, hmz])).trans (loop_zero _)
  · have hF := (packed_flagSet hb N mask hz).congr (q := fun w => flagB N mask z w)
      (fun w _ => by simp [flagB, hmz])
    exact (hF.card hb hlt).symm

/-- **A row of the count of violated flags.**  For every number of qubits, every mask, every assignment
mask and every code `z`, the evaluation on packed sets is the row of `card_violated_cfg`. -/
theorem violRow_eq_fast {b N : ℕ} (hb : 0 < b) (hlt : 2 ^ (2 * N) < 2 ^ b - 1) (mask neg : ℕ)
    {z : ℕ} (hz : z < 2 ^ (2 * N)) : violRow N mask neg z = fastViolRow b N mask neg z := by
  show loop (fun w => if violB N mask neg z w = true then 1 else 0) (2 ^ (2 * N))
    = bif mask.testBit z then
        (flagSet b N (pack b mask.testBit (2 * N) 0) (ones b (2 * N))
            (fun j => stripe b j (2 * N)) z
          &&& signSet b N neg
            (pack b neg.testBit (2 * N) 0 ^^^ yHigh (fun j => stripe b j (2 * N)) N N)
            (yLow (fun j => stripe b j (2 * N)) N N) (ones b (2 * N))
            (fun j => stripe b j (2 * N)) z) % (2 ^ b - 1)
      else 0
  cases hmz : mask.testBit z
  · show loop (fun w => if violB N mask neg z w = true then 1 else 0) (2 ^ (2 * N)) = 0
    exact (loop_congr (fun w _ => by simp [violB, flagB, hmz])).trans (loop_zero _)
  · have hall := packed_ones hb (2 * N)
    have hst := fun j => packed_stripe hb j (2 * N)
    have hsg : Packed b (2 * N)
        (pack b neg.testBit (2 * N) 0 ^^^ yHigh (fun j => stripe b j (2 * N)) N N)
        (fun w => gBit neg N w) :=
      (packed_mask hb neg (2 * N)).xor (packed_yHigh hst N N)
    have hy0 : Packed b (2 * N) (yLow (fun j => stripe b j (2 * N)) N N) (fun w => yBit N w) :=
      packed_yLow hst N N
    have htg := packed_translate hb hall hst z hsg (2 * N) (Nat.le_refl _)
    have hd := packed_dotSet hst N z N
    have hS := (((hsg.xor htg).xor hd).xor_if (yBit N z) hy0).xor_if (gBit neg N z) hall
    have hV := ((packed_flagSet hb N mask hz).and hS).congr (q := fun w => violB N mask neg z w)
      (fun w _ => by
        show (mask.testBit w && (mask.testBit (z ^^^ w) && commB N z w)
            && ((((gBit neg N w ^^ gBit neg N (w ^^^ z % 2 ^ (2 * N)))
                  ^^ decide (common z N w 0 N % 2 = 1)) ^^ (yBit N z && yBit N w))
                ^^ (gBit neg N z && true)))
          = (mask.testBit z && (mask.testBit w && (mask.testBit (z ^^^ w) && commB N z w))
            && decide (sInt neg z * sInt neg w * sInt neg (z ^^^ w) ≠ lineSignCode N z w))
        rw [Nat.mod_eq_of_lt hz, Nat.xor_comm w z, hmz]
        cases hc : commB N z w
        · simp
        · rw [viol_bit neg N z w hc]
          cases gBit neg N z <;> cases gBit neg N w <;> cases gBit neg N (z ^^^ w) <;>
            cases yBit N z <;> cases yBit N w <;> cases decide (common z N w 0 N % 2 = 1) <;>
            cases mask.testBit w <;> cases mask.testBit (z ^^^ w) <;> rfl)
    exact (hV.card hb hlt).symm

/-! ### The counts of a mask configuration -/

/-- The number of observables of a mask configuration, from the packed mask. -/
theorem card_cfg_fast {b N : ℕ} (hb : 0 < b) (hlt : 2 ^ (2 * N) < 2 ^ b - 1) (mask : ℕ) :
    (cfg N mask).card = pack b mask.testBit (2 * N) 0 % (2 ^ b - 1) := by
  rw [card_cfg, card_codes]
  exact ((packed_mask hb mask (2 * N)).card hb hlt).symm

/-- The number of flags of a mask configuration, as a sum of rows evaluated on packed sets. -/
theorem card_flags_cfg_fast {b N : ℕ} (hb : 0 < b) (hlt : 2 ^ (2 * N) < 2 ^ b - 1) (mask : ℕ) :
    (flags (cfg N mask)).card = loop (fastFlagRow b N mask) (2 ^ (2 * N)) := by
  rw [card_flags_cfg]
  exact loop_congr (fun z hz => flagRow_eq_fast hb hlt mask hz)

/-- The number of flags violated by a mask assignment, as a sum of rows evaluated on packed sets. -/
theorem card_violated_cfg_fast {b N : ℕ} (hb : 0 < b) (hlt : 2 ^ (2 * N) < 2 ^ b - 1)
    (mask neg : ℕ) :
    (violated (cfg N mask) (fun u => ((sgnOf N neg u : ℤ) : ℝ))).card
      = loop (fastViolRow b N mask neg) (2 ^ (2 * N)) := by
  rw [card_violated_cfg]
  exact loop_congr (fun z hz => violRow_eq_fast hb hlt mask neg hz)

end HoggarBound

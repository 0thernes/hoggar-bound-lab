/- The concrete C3 certificate is a pair of sign assignments on an actual Pauli section. -/
import HoggarBound.C3Data
import HoggarBound.Quadric

open Matrix Finset

namespace HoggarBound.C3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bitCount4 (v : ℕ) : ℕ := ∑ i : Fin 4, if v.testBit i.val then 1 else 0

def bits (v : Fin 16) : Vec 4 := fun i => if v.val.testBit i.val then 1 else 0

def xCode (v : Fin 256) : Fin 16 := ⟨v.val % 16, Nat.mod_lt _ (by decide)⟩

def zCode (v : Fin 256) : Fin 16 := ⟨v.val / 16, by have := v.isLt; omega⟩

def codePoint (v : Fin 256) : Pt 4 := (bits (xCode v), bits (zCode v))

def codeAdd (u v : Fin 256) : Fin 256 :=
  ⟨Nat.xor u.val v.val % 256, Nat.mod_lt _ (by decide)⟩

def realCodes : Finset (Fin 256) :=
  univ.filter fun v => v ≠ 0 ∧ bitCount4 (Nat.land (xCode v).val (zCode v).val) % 2 = 0

def sectionCodes : Finset (Fin 256) :=
  realCodes.filter fun v => v.val.testBit 3 = false

def outsideCodes : Finset (Fin 256) :=
  realCodes.filter fun v => v.val.testBit 3 = true

theorem bits_injective : Function.Injective bits := by decide +kernel

theorem bits_bijective : Function.Bijective bits := by
  apply (Fintype.bijective_iff_injective_and_card bits).2
  exact ⟨bits_injective, by simp⟩

theorem codePoint_injective : Function.Injective codePoint := by
  intro u v h
  have hx := bits_injective (congrArg Prod.fst h)
  have hz := bits_injective (congrArg Prod.snd h)
  apply Fin.ext
  have hxm := congrArg Fin.val hx
  have hzm := congrArg Fin.val hz
  simp only [xCode, zCode] at hxm hzm
  have hu := Nat.mod_add_div u.val 16
  have hv := Nat.mod_add_div v.val 16
  omega

theorem codePoint_bijective : Function.Bijective codePoint := by
  apply (Fintype.bijective_iff_injective_and_card codePoint).2
  exact ⟨codePoint_injective, by simp⟩

theorem section_correct (v : Fin 256) : v ∈ sectionCodes ↔
    codePoint v ∈ realPoints 4 ∧ symp (codePoint v) (codePoint 128) = 0 := by
  revert v
  decide +kernel

theorem outside_correct (v : Fin 256) : v ∈ outsideCodes ↔
    codePoint v ∈ realPoints 4 ∧ symp (codePoint v) (codePoint 128) ≠ 0 := by
  revert v
  decide +kernel

theorem section_card : sectionCodes.card = 71 := by decide +kernel
theorem outside_card : outsideCodes.card = 64 := by decide +kernel
theorem polar_point_real : codePoint 128 ∈ realPoints 4 := by decide +kernel

theorem outside_labels_complete : univ.image outsideLabel = outsideCodes := by decide +kernel
theorem outside_labels_injective : Function.Injective outsideLabel := by decide +kernel

theorem ycount_code (v : Fin 256) :
    ycount (codePoint v) = bitCount4 (Nat.land (xCode v).val (zCode v).val) := by
  revert v
  decide +kernel

theorem dot_bits (c j : Fin 16) :
    bits c ⬝ᵥ bits j = (bitCount4 (Nat.land c.val j.val) : ZMod 2) := by
  revert c j
  decide +kernel

theorem bits_add_iff (i j a : Fin 16) :
    bits i = bits j + bits a ↔ i.val = Nat.xor j.val a.val := by
  revert i j a
  decide +kernel

theorem codePoint_add (u v : Fin 256) : codePoint (codeAdd u v) = codePoint u + codePoint v := by
  have hlt : Nat.xor u.val v.val < 256 := Nat.xor_lt_two_pow (n := 8) u.isLt v.isLt
  apply Prod.ext
  · apply (bits_add_iff (xCode (codeAdd u v)) (xCode u) (xCode v)).2
    simp only [xCode, codeAdd, Nat.mod_eq_of_lt hlt]
    exact Nat.xor_mod_two_pow (n := 4)
  · apply (bits_add_iff (zCode (codeAdd u v)) (zCode u) (zCode v)).2
    simp only [zCode, codeAdd, Nat.mod_eq_of_lt hlt]
    exact Nat.xor_div_two_pow (n := 4)

/-- Integral entries of a real four-qubit Pauli, in binary computational-basis order. -/
def realPauliCode (v : Fin 256) : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if i.val = Nat.xor j.val (xCode v).val then
    (-1) ^ (bitCount4 (Nat.land (xCode v).val (zCode v).val) / 2 +
      bitCount4 (Nat.land (zCode v).val j.val))
  else 0

/-- The integral entry formula is the explicit complex Pauli matrix already proved in `Pauli.lean`. -/
theorem realPauliCode_cast (v : Fin 256)
    (heven : bitCount4 (Nat.land (xCode v).val (zCode v).val) % 2 = 0) (i j : Fin 16) :
    (realPauliCode v i j : ℂ) = pauli (codePoint v) (bits i) (bits j) := by
  unfold realPauliCode
  have hrow : bits i = bits j + (codePoint v).1 ↔ i.val = Nat.xor j.val (xCode v).val :=
    bits_add_iff i j (xCode v)
  have hchi : chi (codePoint v).2 (bits j) =
      (-1 : ℂ) ^ bitCount4 (Nat.land (zCode v).val j.val) := by
    change chi (bits (zCode v)) (bits j) = _
    rw [chi, dot_bits, eps_natCast]
  have hp : Complex.I ^ ycount (codePoint v) =
      (-1 : ℂ) ^ (bitCount4 (Nat.land (xCode v).val (zCode v).val) / 2) := by
    rw [ycount_code]
    have hk : bitCount4 (Nat.land (xCode v).val (zCode v).val) =
        2 * (bitCount4 (Nat.land (xCode v).val (zCode v).val) / 2) := by omega
    nth_rw 1 [hk]
    rw [pow_mul, Complex.I_sq]
  simp only [pauli, Matrix.smul_apply, smul_eq_mul, weyl]
  rw [hp]
  by_cases h : i.val = Nat.xor j.val (xCode v).val
  · rw [ite_eq_left (hrow.2 h), hchi]
    simp only [ite_eq_left h, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, pow_add]
  · rw [ite_eq_right (fun h' => h (hrow.1 h')), mul_zero]
    simp only [ite_eq_right h, Int.cast_zero]

def signA (v : Fin 256) : ℤ := if v ∈ ({48, 102, 176, 230} : Finset (Fin 256)) then -1 else 1
def signB (v : Fin 256) : ℤ := if v ∈ ({87, 144, 176, 215} : Finset (Fin 256)) then -1 else 1

theorem signA_values (v : Fin 256) : signA v = 1 ∨ signA v = -1 := by
  unfold signA
  split_ifs <;> simp

theorem signB_values (v : Fin 256) : signB v = 1 ∨ signB v = -1 := by
  unfold signB
  split_ifs <;> simp

def carrierOf (f : Fin 256 → ℤ) : Matrix (Fin 16) (Fin 16) ℤ :=
  ∑ v ∈ sectionCodes, f v • realPauliCode v

/-- Completion adjacency on all 64 outside points, using the proved Pauli context sign. -/
def completionOf (f : Fin 256 → ℤ) : Matrix (Fin 64) (Fin 64) ℤ := fun i j =>
  let u := outsideLabel i
  let v := outsideLabel j
  let s := codeAdd u v
  if s ∈ sectionCodes ∧ symp (codePoint u) (codePoint v) = 0 then
    f s * integerLineSign (codePoint u) (codePoint v)
  else 0

theorem carrierA_from_section : carrierOf signA = carrierA := by
  ext i j
  fin_cases i <;> revert j <;> decide +kernel

theorem carrierB_from_section : carrierOf signB = carrierB := by
  ext i j
  fin_cases i <;> revert j <;> decide +kernel

theorem completionA_from_contexts : completionOf signA = completionA := by
  ext i j
  fin_cases i <;> revert j <;> decide +kernel

theorem completionB_from_contexts : completionOf signB = completionB := by
  ext i j
  fin_cases i <;> revert j <;> decide +kernel

end HoggarBound.C3

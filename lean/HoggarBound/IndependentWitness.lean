/-
An exact finite certificate for the three-qubit Hoggar assignment.

The certificate uses integers and kernel reduction, never floating-point arithmetic
or `native_decide`. The integer context sign is proved equal to the real part of
the explicit complex Pauli product used by the general theorem.
-/
import HoggarBound.Corollaries

open Finset Matrix

namespace HoggarBound

variable {N : ℕ}

/-- The real part of an integral power of `i`, computed with integers. -/
def iPowerReal (k : ℕ) : ℤ :=
  if k % 4 = 0 then 1 else if k % 4 = 2 then -1 else 0

/-- A computable integer presentation of the context sign. -/
def integerLineSign (u v : Pt N) : ℤ :=
  iPowerReal (ycount u + ycount v + 3 * ycount (u + v)) *
    (if u.2 ⬝ᵥ v.1 = 0 then 1 else -1)

lemma lineSign_eq_integer (u v : Pt N) :
    lineSign u v = (integerLineSign u v : ℝ) := by
  unfold lineSign tau chi eps integerLineSign iPowerReal
  rw [Complex.I_pow_eq_pow_mod]
  have hk : (ycount u + ycount v + 3 * ycount (u + v)) % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases h : (ycount u + ycount v + 3 * ycount (u + v)) % 4 <;>
    by_cases hs : u.2 ⬝ᵥ v.1 = 0 <;> simp [hs, Complex.I_sq, Complex.I_pow_three]

/-- Violated flags for an integer-valued assignment. -/
def integerViolated (S : Finset (Pt N)) (f : Pt N → ℤ) : Finset (Pt N × Pt N) :=
  (flags S).filter fun p => f p.1 * f p.2 * f (p.1 + p.2) ≠ integerLineSign p.1 p.2

lemma violated_cast_integer (S : Finset (Pt N)) (f : Pt N → ℤ) :
    violated S (fun u => (f u : ℝ)) = integerViolated S f := by
  classical
  ext p
  simp only [violated, integerViolated, mem_filter, lineSign_eq_integer]
  rw [← Int.cast_mul, ← Int.cast_mul]
  simp only [ne_eq, Int.cast_inj]

/-- Signs of the Pauli expectations of `(-1+2i,1,1,1,1,1,1,1)/sqrt(12)`.
The finite certificate below does not assume the state interpretation. -/
def hoggarSign (u : Pt 3) : ℤ :=
  if u.1 = 0 ∨ u.2 = 0 ∨ 2 ≤ ycount u then 1 else -1

lemma hoggarSign_values (u : Pt 3) : hoggarSign u = 1 ∨ hoggarSign u = -1 := by
  unfold hoggarSign
  split_ifs <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact, kernel-checked enumeration: the Hoggar assignment violates 378 ordered flags. -/
theorem hoggar_flags_certificate :
    (integerViolated (allPoints 3) hoggarSign).card = 378 := by
  decide +kernel

/-- The finite certificate concerns the same Pauli model as `hoggar_bound`. -/
theorem hoggar_violated_flags :
    (violated (allPoints 3) (fun u => (hoggarSign u : ℝ))).card = 378 := by
  rw [violated_cast_integer]
  exact hoggar_flags_certificate

end HoggarBound

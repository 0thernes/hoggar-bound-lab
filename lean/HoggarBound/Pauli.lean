/-
Hoggar Bound Lab — the N-qubit Pauli operators as explicit complex matrices.

A *point* is a pair `u = (a, c)` of bit vectors of length `N`; it labels the Hermitian operator

    pauli u = i^{|a ∧ c|} · X^a Z^c        (a tensor product of I, X, Y, Z).

The matrices act on `ℂ^(2^N)`, with basis indexed by bit vectors `Fin N → ZMod 2`.
Everything is proved for arbitrary `N`.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open Finset Matrix

namespace HoggarBound

/-- Bit vectors of length `N`. -/
abbrev Vec (N : ℕ) := Fin N → ZMod 2

/-- A point `(a, c)`: the X-part and the Z-part of a Pauli operator. -/
abbrev Pt (N : ℕ) := Vec N × Vec N

variable {N : ℕ}

/-! ### The sign character of `ZMod 2` -/

lemma zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by revert t; decide

lemma zmod2_add_self (t : ZMod 2) : t + t = 0 := by revert t; decide

/-- The character `0 ↦ 1`, `1 ↦ -1`. -/
def eps (t : ZMod 2) : ℂ := if t = 0 then 1 else -1

@[simp] lemma eps_zero : eps 0 = 1 := by simp [eps]

@[simp] lemma eps_one : eps 1 = -1 := by
  have h : (1 : ZMod 2) ≠ 0 := by decide
  simp [eps, h]

lemma eps_add (s t : ZMod 2) : eps (s + t) = eps s * eps t := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl <;> simp [h11]

lemma eps_mul_self (t : ZMod 2) : eps t * eps t = 1 := by
  rw [← eps_add, zmod2_add_self, eps_zero]

lemma star_eps (t : ZMod 2) : star (eps t) = eps t := by
  rcases zmod2_cases t with rfl | rfl <;> simp

lemma eps_natCast (k : ℕ) : eps ((k : ℕ) : ZMod 2) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, eps_add, ih, pow_succ, eps_one]

/-! ### Bit vectors -/

lemma vec_add_self (a : Vec N) : a + a = 0 := by
  funext i
  exact zmod2_add_self (a i)

lemma pt_add_self (u : Pt N) : u + u = 0 :=
  Prod.ext (vec_add_self u.1) (vec_add_self u.2)

lemma pt_eq_of_add_eq_zero {u v : Pt N} (h : u + v = 0) : u = v := by
  calc u = u + (v + v) := by rw [pt_add_self, add_zero]
    _ = (u + v) + v := by abel
    _ = v := by rw [h, zero_add]

/-- The bicharacter `(c, y) ↦ (-1)^{c·y}`. -/
def chi (c y : Vec N) : ℂ := eps (c ⬝ᵥ y)

lemma chi_add_right (c y y' : Vec N) : chi c (y + y') = chi c y * chi c y' := by
  simp [chi, dotProduct_add, eps_add]

lemma chi_add_left (c c' y : Vec N) : chi (c + c') y = chi c y * chi c' y := by
  simp [chi, add_dotProduct, eps_add]

@[simp] lemma chi_zero_left (y : Vec N) : chi 0 y = 1 := by simp [chi]

@[simp] lemma chi_zero_right (c : Vec N) : chi c 0 = 1 := by simp [chi]

lemma chi_mul_self (c y : Vec N) : chi c y * chi c y = 1 := eps_mul_self _

lemma star_chi (c y : Vec N) : star (chi c y) = chi c y := star_eps _

/-- Orthogonality of characters. -/
lemma sum_chi (c : Vec N) : ∑ x : Vec N, chi c x = if c = 0 then (2 : ℂ) ^ N else 0 := by
  split_ifs with h
  · subst h
    simp [ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra hc
      exact h (funext fun i => by simpa using not_not.1 (not_exists.1 hc i))
    have hci : c i = 1 := (zmod2_cases (c i)).resolve_left hi
    have hneg : ∀ x : Vec N, chi c (x + Pi.single i 1) = - chi c x := by
      intro x
      rw [chi_add_right]
      simp [chi, dotProduct_single, hci]
    refine Finset.sum_ninvolution (fun x : Vec N => x + Pi.single i 1) ?_ ?_ ?_ ?_
    · intro x
      rw [hneg]
      ring
    · intro x _ hx
      simp at hx
    · intro x
      exact mem_univ _
    · intro x
      rw [add_assoc, vec_add_self, add_zero]

/-! ### Weyl operators `X^a Z^c` -/

/-- The Weyl operator `X^a Z^c`: `|y⟩ ↦ (-1)^{c·y} |y + a⟩`. -/
def weyl (u : Pt N) : Matrix (Vec N) (Vec N) ℂ :=
  fun x y => if x = y + u.1 then chi u.2 y else 0

lemma weyl_mul (u v : Pt N) : weyl u * weyl v = chi u.2 v.1 • weyl (u + v) := by
  ext x z
  simp only [Matrix.mul_apply, weyl, Matrix.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [Finset.sum_eq_single (z + v.1)]
  · by_cases h : x = z + v.1 + u.1
    · have h' : x = z + (u.1 + v.1) := by rw [h]; abel
      rw [ite_eq_left h, ite_eq_left rfl, ite_eq_left h', chi_add_right, chi_add_left]
      ring
    · have h' : ¬ x = z + (u.1 + v.1) := fun h'' => h (by rw [h'']; abel)
      rw [ite_eq_right h, ite_eq_right h']
      simp
  · intro y _ hy
    rw [ite_eq_right hy, mul_zero]
  · intro h
    exact absurd (mem_univ _) h

lemma weyl_zero : weyl (0 : Pt N) = 1 := by
  ext x y
  simp [weyl, Matrix.one_apply]

lemma trace_weyl (u : Pt N) : (weyl u).trace = if u = 0 then (2 : ℂ) ^ N else 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, weyl]
  by_cases ha : u.1 = 0
  · have h1 : ∀ x : Vec N, (if x = x + u.1 then chi u.2 x else 0) = chi u.2 x := by
      intro x
      rw [ite_eq_left (by rw [ha, add_zero])]
    simp only [h1]
    rw [sum_chi]
    by_cases hc : u.2 = 0
    · rw [ite_eq_left hc, ite_eq_left (Prod.ext ha hc)]
    · have hu : u ≠ 0 := fun h => hc (by rw [h]; rfl)
      rw [ite_eq_right hc, ite_eq_right hu]
  · have h1 : ∀ x : Vec N, (if x = x + u.1 then chi u.2 x else 0) = 0 := by
      intro x
      rw [ite_eq_right]
      intro h
      exact ha (by simpa using h)
    have hu : u ≠ 0 := fun h => ha (by rw [h]; rfl)
    simp only [h1, Finset.sum_const_zero]
    rw [ite_eq_right hu]

lemma weyl_conjTranspose (u : Pt N) : (weyl u)ᴴ = chi u.2 u.1 • weyl u := by
  ext x y
  simp only [Matrix.conjTranspose_apply, weyl, Matrix.smul_apply, smul_eq_mul]
  by_cases h : x = y + u.1
  · subst h
    have h2 : y = y + u.1 + u.1 := by rw [add_assoc, vec_add_self, add_zero]
    rw [ite_eq_left h2, ite_eq_left rfl, star_chi, chi_add_right]
    ring
  · have h2 : ¬ y = x + u.1 := fun h' => h (by rw [h', add_assoc, vec_add_self, add_zero])
    rw [ite_eq_right h2, ite_eq_right h]
    simp

/-! ### Hermitian Pauli operators -/

/-- Number of tensor factors equal to `Y`. -/
def ycount (u : Pt N) : ℕ := (univ.filter fun i => u.1 i = 1 ∧ u.2 i = 1).card

lemma ycount_zero : ycount (0 : Pt N) = 0 := by
  have h : (0 : ZMod 2) ≠ 1 := by decide
  simp [ycount, h]

lemma dot_eq_ycount (u : Pt N) : u.2 ⬝ᵥ u.1 = ((ycount u : ℕ) : ZMod 2) := by
  simp only [dotProduct, ycount]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  rcases zmod2_cases (u.1 i) with h1 | h1 <;> rcases zmod2_cases (u.2 i) with h2 | h2 <;>
    simp [h1, h2, h01]

lemma chi_self (u : Pt N) : chi u.2 u.1 = (-1) ^ ycount u := by
  rw [chi, dot_eq_ycount, eps_natCast]

/-- The Hermitian Pauli operator labelled by `u = (a, c)`: `i^{#Y} X^a Z^c`. -/
def pauli (u : Pt N) : Matrix (Vec N) (Vec N) ℂ := (Complex.I ^ ycount u) • weyl u

lemma pauli_zero : pauli (0 : Pt N) = 1 := by
  simp [pauli, ycount_zero, weyl_zero]

lemma pauli_isHermitian (u : Pt N) : (pauli u).IsHermitian := by
  unfold Matrix.IsHermitian pauli
  rw [Matrix.conjTranspose_smul, weyl_conjTranspose, smul_smul, chi_self]
  congr 1
  rw [star_pow, Complex.star_def, Complex.conj_I, ← mul_pow]
  simp

/-- The phase of a product of two Pauli operators: `pauli u * pauli v = tau u v • pauli (u + v)`. -/
def tau (u v : Pt N) : ℂ := Complex.I ^ (ycount u + ycount v + 3 * ycount (u + v)) * chi u.2 v.1

lemma pauli_mul (u v : Pt N) : pauli u * pauli v = tau u v • pauli (u + v) := by
  simp only [pauli, Matrix.smul_mul, Matrix.mul_smul, weyl_mul, smul_smul, tau]
  congr 1
  have h4 : Complex.I ^ (3 * ycount (u + v)) * Complex.I ^ ycount (u + v) = 1 := by
    rw [← pow_add, show 3 * ycount (u + v) + ycount (u + v) = 4 * ycount (u + v) by ring,
      pow_mul, Complex.I_pow_four, one_pow]
  rw [pow_add (Complex.I) (ycount u + ycount v), pow_add (Complex.I) (ycount u)]
  linear_combination
    (-(Complex.I ^ ycount u * Complex.I ^ ycount v * chi u.2 v.1)) * h4

lemma tau_self (u : Pt N) : tau u u = 1 := by
  simp only [tau, pt_add_self, ycount_zero, mul_zero, add_zero, chi_self]
  rw [← two_mul, pow_mul, Complex.I_sq, ← mul_pow]
  simp

lemma pauli_mul_self (u : Pt N) : pauli u * pauli u = 1 := by
  rw [pauli_mul, tau_self, one_smul, pt_add_self, pauli_zero]

/-- **The sign of a context.**  For any two points, the product of the three operators
`pauli u`, `pauli v`, `pauli (u + v)` is the scalar `tau u v`. -/
theorem context_product (u v : Pt N) : pauli u * pauli v * pauli (u + v) = tau u v • 1 := by
  rw [pauli_mul, Matrix.smul_mul, pauli_mul_self]

lemma trace_pauli (u : Pt N) : (pauli u).trace = if u = 0 then (2 : ℂ) ^ N else 0 := by
  rw [pauli, Matrix.trace_smul, trace_weyl]
  by_cases h : u = 0
  · subst h
    simp [ycount_zero]
  · simp [h]

lemma trace_pauli_mul (u v : Pt N) :
    (pauli u * pauli v).trace = if u = v then (2 : ℂ) ^ N else 0 := by
  rw [pauli_mul, Matrix.trace_smul, trace_pauli]
  by_cases h : u = v
  · subst h
    rw [ite_eq_left (pt_add_self u), ite_eq_left rfl, tau_self, one_smul]
  · have h' : u + v ≠ 0 := fun h0 => h (pt_eq_of_add_eq_zero h0)
    rw [ite_eq_right h', ite_eq_right h, smul_zero]

lemma trace_pauli_triple (u v w : Pt N) :
    (pauli u * pauli v * pauli w).trace = if u + v = w then (2 : ℂ) ^ N * tau u v else 0 := by
  rw [pauli_mul, Matrix.smul_mul, Matrix.trace_smul, trace_pauli_mul, smul_eq_mul]
  by_cases h : u + v = w
  · rw [ite_eq_left h, ite_eq_left h, mul_comm]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-! ### Commutation and the reality of context signs -/

/-- The symplectic form: `0` iff the two operators commute. -/
def symp (u v : Pt N) : ZMod 2 := u.2 ⬝ᵥ v.1 + v.2 ⬝ᵥ u.1

lemma symp_comm (u v : Pt N) : symp u v = symp v u := by
  simp only [symp]; ring

lemma tau_swap (u v : Pt N) : tau v u = eps (symp u v) * tau u v := by
  have hy : ycount v + ycount u + 3 * ycount (v + u) = ycount u + ycount v + 3 * ycount (u + v) := by
    rw [add_comm v u]; ring
  have hchi : chi v.2 u.1 = eps (symp u v) * chi u.2 v.1 := by
    simp only [chi, symp, eps_add]
    rw [mul_comm (eps (u.2 ⬝ᵥ v.1)), mul_assoc, eps_mul_self, mul_one]
  simp only [tau, hy, hchi]
  ring

/-- Operators commute or anticommute according to the symplectic form. -/
theorem pauli_comm (u v : Pt N) : pauli v * pauli u = eps (symp u v) • (pauli u * pauli v) := by
  rw [pauli_mul, pauli_mul, tau_swap, add_comm v u, smul_smul]

lemma ycount_add_cast (u v : Pt N) :
    ((ycount (u + v) : ℕ) : ZMod 2) = (ycount u : ZMod 2) + (ycount v : ZMod 2) + symp u v := by
  rw [← dot_eq_ycount, ← dot_eq_ycount, ← dot_eq_ycount]
  simp only [symp, Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
  ring

lemma tau_sq (u v : Pt N) : tau u v ^ 2 = eps (symp u v) := by
  have h1 : tau u v ^ 2 = (-1) ^ (ycount u + ycount v + 3 * ycount (u + v)) := by
    simp only [tau, mul_pow]
    rw [← pow_mul, mul_comm _ 2, pow_mul, Complex.I_sq, sq, chi_mul_self, mul_one]
  rw [h1, ← eps_natCast]
  congr 1
  push_cast
  rw [ycount_add_cast]
  have h2 : ∀ t : ZMod 2, t + t = 0 := zmod2_add_self
  have h3 : (3 : ZMod 2) = 1 := by decide
  rw [h3, one_mul]
  have := h2 (ycount u : ZMod 2)
  have := h2 (ycount v : ZMod 2)
  linear_combination h2 (ycount u : ZMod 2) + h2 (ycount v : ZMod 2)

/-- For commuting operators the context sign is `+1` or `-1`. -/
theorem tau_eq_one_or_neg_one {u v : Pt N} (h : symp u v = 0) : tau u v = 1 ∨ tau u v = -1 := by
  have h2 : tau u v * tau u v = 1 := by rw [← sq, tau_sq, h, eps_zero]
  exact mul_self_eq_one_iff.mp h2

end HoggarBound

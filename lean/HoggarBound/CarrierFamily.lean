/-
Hoggar Bound Lab - case C3 for every number of qubits.

For every number of qubits `N ≥ 4` there are two sign carriers on the section of case C3 whose carrier
operators have the same characteristic polynomial and whose completion matrices have different
characteristic polynomials: the strict law fails.  Mathematics: publication/ADDENDUM-c3-all-qubits.md
(Theorem 17).  The framework (carriers, completion matrices, the strict law, the cases) is B. W. Jonah's,
"The reach of the section-square law", doi:10.5281/zenodo.23524332; case C3 is reported open there for
`N ≥ 4`.  The construction (Parts 3 and 4) is the addendum's.

`m` is the number of block qubits, `N = m + 1` the number of qubits and `n = 2^m`.  Main statements:

  `c3_strict_law_fails_general`  (Part 7)  for every `m ≥ 3`: on the real quadric of `m + 1` qubits, with
        the polar point `Z` on one qubit, there are two carriers with values `±1` whose carrier operators
        over the section have the same characteristic polynomial and whose completion matrices, defined
        from the contexts and their signs, have different characteristic polynomials;
  `c3_strict_law_fails`          (Part 6)  the same in coordinates, over the integers;
  `c3_all_qubits_completion`     (Part 6)  the cubic traces of the two completion matrices differ by
        exactly `-(3/2) n³`.

  Part 1  block algebra for integer matrices of any size: the operator `M ↦ C * M + M * D`, the trace
          of its cube, and two carriers that differ by moving one diagonal block from `C` to `D`
  Part 2  the same for two parts `A₁`, `A₂` on one index set with `A₁ * A₂ = 0 = A₂ * A₁`
  Part 3  the two character sums over `F_2^m` and the block of the first carrier (Steps 2 and 3)
  Part 4  the two carriers of the family as sign tables, their blocks, and the two main statements for
          a separated set of edges; the instance of the addendum for every `m ≥ 3`
  Part 5  the carrier operator on `N` qubits as a sum of Kronecker products (Step 1)
  Part 6  the outside observables, the completion matrix as a sum of normalised traces
          `tr (S O_q O_p) / 2n` over the section, and the trace of its cube (Step 5)
  Part 7  the section, the outside points, the contexts and the completion matrix in the language of
          `HoggarBound/Pauli.lean`, `Bound.lean` and `Quadric.lean`; the transfer of Part 6 to them;
          sizes, and symmetry of the completion matrix

Parts 1 to 6 use Mathlib only.  Part 7 uses the Pauli matrices of the library, whose product rule,
commutation rule and context signs are theorems there.  The statements were fixed first and tested
numerically; the proofs were then written and audited by separate automated passes (see the review
record in the addendum).  No `sorry`, no `native_decide`; the list of `#print axioms` at the end must
show only `propext`, `Classical.choice` and `Quot.sound`.

  check:  cd lean && lake build HoggarBound.Bound HoggarBound.Quadric && lake env lean HoggarBound/CarrierFamily.lean
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic
import HoggarBound.Bound
import HoggarBound.Quadric

open Matrix
open scoped Kronecker

namespace HoggarBound.C3AllQubits

/-! ### Part 1. Block algebra -/

section blocks

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The matrix, in the basis of matrix units indexed by `(i, j)`, of the linear map
`M ↦ C * M + M * D` on square matrices.  Twice the completion operator of a carrier with blocks
`C` and `D`. -/
def sylvester (C D : Matrix ι ι ℤ) : Matrix (ι × ι) (ι × ι) ℤ :=
  C ⊗ₖ (1 : Matrix ι ι ℤ) + (1 : Matrix ι ι ℤ) ⊗ₖ Dᵀ

/-- `sylvester C D` is the matrix of `M ↦ C * M + M * D`. -/
theorem sylvester_apply (C D M : Matrix ι ι ℤ) (i j : ι) :
    ∑ p : ι × ι, sylvester C D (i, j) p * M p.1 p.2 = (C * M + M * D) i j := by
  simp only [sylvester, Fintype.sum_prod_type, Matrix.add_apply, kroneckerMap_apply, one_apply,
    Matrix.mul_apply, transpose_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp
  · simp [mul_comm]

/-- Trace formula of Step 5, for all square integer matrices of any size. -/
theorem trace_sylvester_cube (C D : Matrix ι ι ℤ) :
    trace (sylvester C D ^ 3) =
      (Fintype.card ι : ℤ) * trace (C ^ 3) + 3 * (trace (C ^ 2) * trace D)
        + 3 * (trace C * trace (D ^ 2)) + (Fintype.card ι : ℤ) * trace (D ^ 3) := by
  have h2 : trace (Dᵀ * Dᵀ) = trace (D * D) := by
    rw [← transpose_mul, trace_transpose]
  have h3 : trace (Dᵀ * (Dᵀ * Dᵀ)) = trace (D * (D * D)) := by
    rw [← transpose_mul, ← transpose_mul, trace_transpose, mul_assoc]
  unfold sylvester
  rw [pow_three]
  simp only [mul_add, add_mul, ← mul_kronecker_mul, mul_one, one_mul, trace_add, trace_kronecker,
    trace_one, trace_transpose, h2, h3]
  rw [pow_three, pow_two, pow_three, pow_two]
  ring

/-- The carrier operator with blocks `C` and `D`. -/
def carrier (C D : Matrix ι ι ℤ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ :=
  fromBlocks C 0 0 D

/-- First carrier: both parts `M₁` and `M₂` sit in the block `C`. -/
def Cσ (M₁ : Matrix ι ι ℤ) (M₂ : Matrix κ κ ℤ) (k : ℤ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℤ :=
  fromBlocks (-1 + k • M₁) 0 0 (-1 + k • M₂)

/-- First carrier: the block `D` is `-1`. -/
def Dσ (_M₁ : Matrix ι ι ℤ) (_M₂ : Matrix κ κ ℤ) (_k : ℤ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℤ :=
  -1

/-- Second carrier: the part `M₂` has left the block `C`. -/
def Cτ (M₁ : Matrix ι ι ℤ) (_M₂ : Matrix κ κ ℤ) (k : ℤ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℤ :=
  fromBlocks (-1 + k • M₁) 0 0 (-1)

/-- Second carrier: the part `M₂` sits in the block `D`. -/
def Dτ (_M₁ : Matrix ι ι ℤ) (M₂ : Matrix κ κ ℤ) (k : ℤ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℤ :=
  fromBlocks (-1) 0 0 (-1 + k • M₂)

/-- Step 4: the two carrier operators have the same characteristic polynomial. -/
theorem carrier_charpoly_eq (M₁ : Matrix ι ι ℤ) (M₂ : Matrix κ κ ℤ) (k : ℤ) :
    (carrier (Cσ M₁ M₂ k) (Dσ M₁ M₂ k)).charpoly = (carrier (Cτ M₁ M₂ k) (Dτ M₁ M₂ k)).charpoly := by
  have hneg : (-1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℤ) = fromBlocks (-1) 0 0 (-1) := by
    rw [← fromBlocks_one, fromBlocks_neg]
    simp only [neg_zero]
  unfold carrier Cσ Dσ Cτ Dτ
  rw [hneg]
  simp only [charpoly_fromBlocks_zero₁₂]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
/-- Trace of a block matrix: the sum of the traces of the diagonal blocks. -/
theorem trace_fromBlocks_aux (A : Matrix ι ι ℤ) (B : Matrix ι κ ℤ) (C : Matrix κ ι ℤ)
    (D : Matrix κ κ ℤ) : trace (fromBlocks A B C D) = trace A + trace D := by
  simp [trace, Fintype.sum_sum_type]

theorem trace_neg_one_aux : trace (-1 : Matrix ι ι ℤ) = -(Fintype.card ι : ℤ) := by
  rw [trace_neg, trace_one]

theorem trace_neg_one_sq_aux : trace ((-1 : Matrix ι ι ℤ) ^ 2) = (Fintype.card ι : ℤ) := by
  rw [neg_one_sq, trace_one]

theorem trace_neg_one_cube_aux : trace ((-1 : Matrix ι ι ℤ) ^ 3) = -(Fintype.card ι : ℤ) := by
  rw [pow_succ, neg_one_sq, one_mul, trace_neg, trace_one]

theorem trace_neg_one_add_smul_aux (M : Matrix ι ι ℤ) (k : ℤ) :
    trace (-1 + k • M) = -(Fintype.card ι : ℤ) + k * trace M := by
  rw [trace_add, trace_neg, trace_one, trace_smul, smul_eq_mul]

theorem trace_neg_one_add_smul_sq_aux (M : Matrix ι ι ℤ) (k : ℤ) :
    trace ((-1 + k • M) ^ 2) =
      (Fintype.card ι : ℤ) - 2 * k * trace M + k ^ 2 * trace (M ^ 2) := by
  rw [pow_two, pow_two M]
  simp only [add_mul, mul_add, neg_mul, mul_neg, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    trace_add, trace_neg, trace_smul, trace_one, smul_eq_mul]
  ring

/-- Step 6 in general form: the gap between the cubic traces of the two completion operators. -/
theorem sylvester_cube_gap (M₁ : Matrix ι ι ℤ) (M₂ : Matrix κ κ ℤ) (k : ℤ) (h : trace M₂ = 0) :
    trace (sylvester (Cσ M₁ M₂ k) (Dσ M₁ M₂ k) ^ 3) - trace (sylvester (Cτ M₁ M₂ k) (Dτ M₁ M₂ k) ^ 3)
      = -3 * k ^ 3 * trace M₁ * trace (M₂ ^ 2) := by
  rw [trace_sylvester_cube, trace_sylvester_cube]
  unfold Cσ Dσ Cτ Dτ
  simp only [fromBlocks_diagonal_pow, trace_fromBlocks_aux, Fintype.card_sum, Nat.cast_add,
    trace_neg_one_aux, trace_neg_one_sq_aux, trace_neg_one_cube_aux, trace_neg_one_add_smul_aux,
    trace_neg_one_add_smul_sq_aux, h]
  ring

/-- The family of the addendum: `M₁` has trace 2 (the loop at `t`), `M₂` is the adjacency matrix of
`e` edges, and `k = n` is the size of the blocks.  The gap is `-12 n³ e`, that is `-(3/2) n³ e` for
the completion matrices, which carry the factor `1/2`. -/
theorem c3_family_gap (M₁ : Matrix ι ι ℤ) (M₂ : Matrix κ κ ℤ) (k e : ℤ)
    (h₀ : trace M₂ = 0) (h₁ : trace M₁ = 2) (h₂ : trace (M₂ ^ 2) = 2 * e) :
    trace (sylvester (Cσ M₁ M₂ k) (Dσ M₁ M₂ k) ^ 3) - trace (sylvester (Cτ M₁ M₂ k) (Dτ M₁ M₂ k) ^ 3)
      = -12 * k ^ 3 * e := by
  rw [sylvester_cube_gap M₁ M₂ k h₀, h₁, h₂]
  ring

/-- With at least one edge and `k ≠ 0` the two cubic traces differ. -/
theorem c3_family_cube_traces_ne (M₁ : Matrix ι ι ℤ) (M₂ : Matrix κ κ ℤ) (k e : ℤ)
    (h₀ : trace M₂ = 0) (h₁ : trace M₁ = 2) (h₂ : trace (M₂ ^ 2) = 2 * e) (hk : k ≠ 0) (he : e ≠ 0) :
    trace (sylvester (Cσ M₁ M₂ k) (Dσ M₁ M₂ k) ^ 3) ≠ trace (sylvester (Cτ M₁ M₂ k) (Dτ M₁ M₂ k) ^ 3) := by
  intro heq
  have hgap := c3_family_gap M₁ M₂ k e h₀ h₁ h₂
  rw [heq, sub_self] at hgap
  have hne : (-12 : ℤ) * k ^ 3 * e ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hk)) he
  exact hne hgap.symm

/-! ### Part 2. The same statements for two parts on one index set

Two matrices `A₁`, `A₂` with `A₁ * A₂ = 0` and `A₂ * A₁ = 0`: for adjacency matrices this says that no
vertex of the first part is joined to, or equal to, a vertex of the second part.  The first carrier has
both parts in the block `C`; the second has `A₂` in the block `D`. -/

section split

open Polynomial

variable (A₁ A₂ : Matrix ι ι ℤ) (k : ℤ)

theorem add_sq_of_mul_eq_zero (h12 : A₁ * A₂ = 0) (h21 : A₂ * A₁ = 0) :
    (A₁ + A₂) ^ 2 = A₁ ^ 2 + A₂ ^ 2 := by
  rw [pow_two, pow_two, pow_two, add_mul, mul_add, mul_add, h12, h21, add_zero, zero_add]

theorem add_cube_of_mul_eq_zero (h12 : A₁ * A₂ = 0) (h21 : A₂ * A₁ = 0) :
    (A₁ + A₂) ^ 3 = A₁ ^ 3 + A₂ ^ 3 := by
  rw [pow_succ, add_sq_of_mul_eq_zero A₁ A₂ h12 h21, pow_succ A₁ 2, pow_succ A₂ 2, add_mul, mul_add,
    mul_add, pow_two, pow_two, mul_assoc A₁ A₁ A₂, h12, mul_zero, mul_assoc A₂ A₂ A₁, h21, mul_zero,
    add_zero, zero_add]

theorem charmatrix_neg_one_add (B : Matrix ι ι ℤ) :
    charmatrix (-1 + B) = charmatrix (-1 : Matrix ι ι ℤ) - (C : ℤ →+* ℤ[X]).mapMatrix B := by
  simp only [charmatrix, map_add]
  abel

theorem charmatrix_neg_one_commute (M : Matrix ι ι ℤ[X]) :
    M * charmatrix (-1 : Matrix ι ι ℤ) = charmatrix (-1 : Matrix ι ι ℤ) * M := by
  have h1 : charmatrix (-1 : Matrix ι ι ℤ) = Matrix.scalar ι (X : ℤ[X]) + 1 := by
    simp only [charmatrix, map_neg, map_one, sub_neg_eq_add]
  rw [h1]
  exact (((Matrix.scalar_commute (X : ℤ[X]) (fun r => Commute.all _ _) M).add_left
    (Commute.one_left M)).eq).symm

theorem charmatrix_split (B₁ B₂ : Matrix ι ι ℤ) (h : B₁ * B₂ = 0) :
    charmatrix (-1 + B₁) * charmatrix (-1 + B₂)
      = charmatrix (-1 : Matrix ι ι ℤ) * charmatrix (-1 + (B₁ + B₂)) := by
  have hφ : (C : ℤ →+* ℤ[X]).mapMatrix B₁ * (C : ℤ →+* ℤ[X]).mapMatrix B₂ = 0 := by
    rw [← map_mul, h, map_zero]
  rw [charmatrix_neg_one_add, charmatrix_neg_one_add, charmatrix_neg_one_add, map_add, sub_mul,
    mul_sub, mul_sub, charmatrix_neg_one_commute ((C : ℤ →+* ℤ[X]).mapMatrix B₁), hφ, mul_sub, mul_add]
  abel

/-- Step 4 on one index set. -/
theorem charpoly_split (h12 : A₁ * A₂ = 0) :
    (-1 + k • (A₁ + A₂)).charpoly * (-1 : Matrix ι ι ℤ).charpoly
      = (-1 + k • A₁).charpoly * (-1 + k • A₂).charpoly := by
  have h : (k • A₁) * (k • A₂) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, h12, smul_zero, smul_zero]
  have key := charmatrix_split (k • A₁) (k • A₂) h
  rw [← smul_add] at key
  simp only [charpoly]
  rw [mul_comm, ← det_mul, ← key, det_mul]

/-- Step 4 on one index set: the two carrier operators have the same characteristic polynomial. -/
theorem carrier_charpoly_split (h12 : A₁ * A₂ = 0) :
    (carrier (-1 + k • (A₁ + A₂)) (-1)).charpoly
      = (carrier (-1 + k • A₁) (-1 + k • A₂)).charpoly := by
  unfold carrier
  rw [charpoly_fromBlocks_zero₁₂, charpoly_fromBlocks_zero₁₂]
  exact charpoly_split A₁ A₂ k h12

theorem trace_neg_one_add_smul_cube_aux (M : Matrix ι ι ℤ) (k : ℤ) :
    trace ((-1 + k • M) ^ 3) =
      -(Fintype.card ι : ℤ) + 3 * k * trace M - 3 * k ^ 2 * trace (M ^ 2)
        + k ^ 3 * trace (M ^ 3) := by
  rw [pow_three, pow_two M, pow_three M]
  simp only [add_mul, mul_add, neg_mul, mul_neg, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_neg, smul_add, trace_add, trace_neg, trace_smul, trace_one, smul_eq_mul]
  ring

/-- Step 6 on one index set. -/
theorem sylvester_cube_gap_split (h12 : A₁ * A₂ = 0) (h21 : A₂ * A₁ = 0) (h : trace A₂ = 0) :
    trace (sylvester (-1 + k • (A₁ + A₂)) (-1) ^ 3)
        - trace (sylvester (-1 + k • A₁) (-1 + k • A₂) ^ 3)
      = -3 * k ^ 3 * trace A₁ * trace (A₂ ^ 2) := by
  rw [trace_sylvester_cube, trace_sylvester_cube]
  simp only [trace_neg_one_sq_aux, trace_neg_one_cube_aux,
    trace_neg_one_add_smul_sq_aux, trace_neg_one_add_smul_cube_aux,
    add_sq_of_mul_eq_zero A₁ A₂ h12 h21, add_cube_of_mul_eq_zero A₁ A₂ h12 h21, trace_add, trace_neg,
    trace_one, trace_smul, smul_eq_mul, h]
  ring

end split

end blocks

/-! ### Part 3. Character sums and the block of the first carrier -/

section sums

/-- Vectors of `F_2^m`. -/
abbrev V (m : ℕ) := Fin m → ZMod 2

variable {m : ℕ}

/-- The sign `(-1)^z` of a bit. -/
def sgn (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

/-- The matrix unit `|i⟩⟨j|`. -/
def unit (i j : V m) : Matrix (V m) (V m) ℤ := fun i' j' => if i' = i ∧ j' = j then 1 else 0

/-- `X^a Z^c` in the computational basis: `|b⟩ ↦ (-1)^(c·b) |b + a⟩`. -/
def xz (a c : V m) : Matrix (V m) (V m) ℤ := fun b' b => if b' = b + a then sgn (c ⬝ᵥ b) else 0

/-- Number of positions where `a` and `c` are both 1. -/
def overlap (a c : V m) : ℕ := (Finset.univ.filter fun i => a i = 1 ∧ c i = 1).card

/-- The real Pauli observable `P_{a,c} = i^(a·c) X^a Z^c`, for `a·c` even. -/
def pauli (a c : V m) : Matrix (V m) (V m) ℤ := (-1 : ℤ) ^ (overlap a c / 2) • xz a c

/-- The sign `ε(P_{a,c}) = (-1)^(c·w) (-1)^((a·c)/2)` of the family, `w = u_a` or `w = t`. -/
def eps (w a c : V m) : ℤ := sgn (c ⬝ᵥ w) * (-1 : ℤ) ^ (overlap a c / 2)

/-! ### Auxiliary lemmas -/

/-- The sign is multiplicative. -/
theorem sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by
  revert x y
  unfold sgn
  decide

theorem sgn_zero : sgn 0 = 1 := by
  simp [sgn]

theorem sgn_one : sgn 1 = -1 := by
  unfold sgn
  decide

/-- Characteristic 2: every vector is its own negative. -/
theorem V_add_self (x : V m) : x + x = 0 := by
  funext i
  have h : ∀ z : ZMod 2, z + z = 0 := by decide
  exact h _

theorem V_add_add_cancel (u a : V m) : u + a + a = u := by
  rw [add_assoc, V_add_self, add_zero]

theorem V_add_add_cancel_left (u a : V m) : u + (u + a) = a := by
  rw [← add_assoc, V_add_self, zero_add]

theorem V_add_eq_zero_iff (w a : V m) : w + a = 0 ↔ w = a := by
  constructor
  · intro h
    calc w = w + a + a := (V_add_add_cancel w a).symm
      _ = a := by rw [h, zero_add]
  · rintro rfl
    exact V_add_self _

/-- The full character sum over `F_2^m`. -/
theorem sum_sgn_dot (w : V m) :
    ∑ c : V m, sgn (c ⬝ᵥ w) = if w = 0 then (2 : ℤ) ^ m else 0 := by
  split_ifs with h
  · subst h
    simp [sgn_zero]
  · obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    have hi1 : w i = 1 := by
      have h2 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
      exact h2 _ hi
    have key : ∑ c : V m, sgn (c ⬝ᵥ w) = - ∑ c : V m, sgn (c ⬝ᵥ w) := by
      rw [← Finset.sum_neg_distrib]
      apply Fintype.sum_equiv (Equiv.addRight (Pi.single i (1 : ZMod 2)))
      intro c
      simp [add_dotProduct, sgn_add, single_dotProduct, hi1, sgn_one]
    linarith

/-- Twice the character sum over the hyperplane orthogonal to `a`. -/
theorem two_mul_sum_sgn_hyperplane (a w : V m) :
    2 * ∑ c ∈ Finset.univ.filter (fun c : V m => c ⬝ᵥ a = 0), sgn (c ⬝ᵥ w)
      = ∑ c : V m, sgn (c ⬝ᵥ w) + ∑ c : V m, sgn (c ⬝ᵥ (w + a)) := by
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [dotProduct_add, sgn_add]
  have h : ∀ x y : ZMod 2, 2 * (if y = 0 then sgn x else 0) = sgn x + sgn x * sgn y := by
    unfold sgn
    decide
  exact h _ _

/-- The character sum over the hyperplane orthogonal to a non-zero `a`. -/
theorem sum_sgn_hyperplane (a w : V m) (ha : a ≠ 0) :
    ∑ c ∈ Finset.univ.filter (fun c : V m => c ⬝ᵥ a = 0), sgn (c ⬝ᵥ w)
      = if w = 0 ∨ w = a then (2 : ℤ) ^ (m - 1) else 0 := by
  have hm : 1 ≤ m := by
    obtain ⟨i, -⟩ : ∃ i, a i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact ha (funext hc)
    exact Nat.succ_le_of_lt i.pos
  have hp : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 := two_mul_sum_sgn_hyperplane a w
  rw [sum_sgn_dot, sum_sgn_dot, hp] at h2
  simp only [V_add_eq_zero_iff] at h2
  by_cases h0 : w = 0
  · have hne : ¬ w = a := by
      rintro rfl
      exact ha h0
    simp only [eq_true h0, eq_false hne, ite_true, ite_false] at h2
    simp only [eq_true h0, true_or, ite_true]
    linarith
  · by_cases h1 : w = a
    · simp only [eq_false h0, eq_true h1, ite_true, ite_false] at h2
      simp only [eq_true h1, or_true, ite_true]
      linarith
    · simp only [eq_false h0, eq_false h1, ite_false] at h2
      simp only [eq_false h0, eq_false h1, or_self, ite_false]
      linarith

/-- The full sum of `(-1)^(c·t) Z^c` is `2^m |t⟩⟨t|`. -/
theorem sum_xz_zero_full (t : V m) :
    ∑ c : V m, sgn (c ⬝ᵥ t) • xz 0 c = (2 : ℤ) ^ m • unit t t := by
  ext b' b
  simp only [Matrix.sum_apply, Matrix.smul_apply, xz, unit, smul_eq_mul, add_zero]
  by_cases hb : b' = b
  · subst hb
    have hc : ∀ c : V m, sgn (c ⬝ᵥ t) * sgn (c ⬝ᵥ b') = sgn (c ⬝ᵥ (t + b')) := fun c => by
      rw [dotProduct_add, sgn_add]
    simp only [ite_true, hc, and_self]
    rw [sum_sgn_dot]
    simp only [V_add_eq_zero_iff]
    by_cases h : b' = t
    · subst h
      simp
    · have h' : ¬ t = b' := fun e => h e.symm
      simp [h, h']
  · have e : ¬ (b' = t ∧ b = t) := by
      rintro ⟨rfl, rfl⟩
      exact hb rfl
    simp [hb, e]

theorem xz_zero_zero : xz (0 : V m) 0 = 1 := by
  ext b' b
  simp [xz, Matrix.one_apply, sgn_zero]

/-! ### The statements -/

/-- `ε(P) P = (-1)^(c·w) X^a Z^c`. -/
theorem eps_smul_pauli (w a c : V m) : eps w a c • pauli a c = sgn (c ⬝ᵥ w) • xz a c := by
  unfold eps pauli
  rw [smul_smul, mul_assoc, ← mul_pow]
  norm_num

/-- Step 2, first sum: over the hyperplane orthogonal to a non-zero `a`. -/
theorem sum_xz_hyperplane (a u : V m) (ha : a ≠ 0) :
    ∑ c ∈ Finset.univ.filter (fun c : V m => c ⬝ᵥ a = 0), sgn (c ⬝ᵥ u) • xz a c
      = (2 : ℤ) ^ (m - 1) • (unit (u + a) u + unit u (u + a)) := by
  ext b' b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply, xz, unit, smul_eq_mul]
  by_cases hb : b' = b + a
  · subst hb
    have hc : ∀ c : V m, sgn (c ⬝ᵥ u) * sgn (c ⬝ᵥ b) = sgn (c ⬝ᵥ (u + b)) := fun c => by
      rw [dotProduct_add, sgn_add]
    simp only [ite_true, hc]
    rw [sum_sgn_hyperplane a (u + b) ha]
    have hab : ¬ b + a = b := by
      intro e
      exact ha (by simpa using e)
    by_cases h1 : b = u
    · subst h1
      simp [V_add_self, ha]
    · by_cases h2 : b = u + a
      · subst h2
        simp [V_add_add_cancel, V_add_add_cancel_left, ha]
      · have c1 : ¬ (u + b = 0 ∨ u + b = a) := by
          rintro (e | e)
          · exact h1 ((V_add_eq_zero_iff u b).1 e).symm
          · apply h2
            rw [← e, V_add_add_cancel_left]
        have e2 : ¬ (b + a = u ∧ b = u + a) := fun e => h2 e.2
        simp [c1, h1, e2]
  · have e1 : ¬ (b' = u + a ∧ b = u) := by
      rintro ⟨rfl, rfl⟩
      exact hb rfl
    have e2 : ¬ (b' = u ∧ b = u + a) := by
      rintro ⟨rfl, rfl⟩
      exact hb (V_add_add_cancel _ _).symm
    simp [hb, e1, e2]

/-- Step 2, second sum: over all non-zero `c`, for `a = 0`. -/
theorem sum_xz_diagonal (t : V m) :
    ∑ c ∈ Finset.univ.filter (fun c : V m => c ≠ 0), sgn (c ⬝ᵥ t) • xz 0 c
      = (2 : ℤ) ^ m • unit t t - 1 := by
  rw [Finset.filter_ne', Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_xz_zero_full,
    zero_dotProduct, sgn_zero, one_smul, xz_zero_zero]

/-- The block `C` of the first carrier: `1 + 2 Σ ε(P) P` over all real non-identity Pauli
observables `P_{a,c}` (`c·a = 0` and `(a, c) ≠ (0, 0)`), with the signs of the family given by a
vertex `t` and vertices `u a`. -/
def familyC (t : V m) (u : V m → V m) : Matrix (V m) (V m) ℤ :=
  1 + (2 : ℤ) • (∑ c ∈ Finset.univ.filter (fun c : V m => c ≠ 0), eps t 0 c • pauli 0 c
    + ∑ a ∈ Finset.univ.filter (fun a : V m => a ≠ 0),
        ∑ c ∈ Finset.univ.filter (fun c : V m => c ⬝ᵥ a = 0), eps (u a) a c • pauli a c)

/-- Step 3: the block is `-1 + 2n |t⟩⟨t| + n Adj(G)`, where `n = 2^m` and `G` has the edges
`{u a, u a + a}`, one for each non-zero `a`. -/
theorem familyC_eq (hm : 1 ≤ m) (t : V m) (u : V m → V m) :
    familyC t u = -1 + (2 : ℤ) ^ (m + 1) • unit t t
      + (2 : ℤ) ^ m • ∑ a ∈ Finset.univ.filter (fun a : V m => a ≠ 0),
          (unit (u a + a) (u a) + unit (u a) (u a + a)) := by
  unfold familyC
  have h0 : ∑ c ∈ Finset.univ.filter (fun c : V m => c ≠ 0), eps t 0 c • pauli 0 c
      = (2 : ℤ) ^ m • unit t t - 1 := by
    rw [← sum_xz_diagonal t]
    exact Finset.sum_congr rfl (fun c _ => eps_smul_pauli t 0 c)
  have h1 : ∑ a ∈ Finset.univ.filter (fun a : V m => a ≠ 0),
        ∑ c ∈ Finset.univ.filter (fun c : V m => c ⬝ᵥ a = 0), eps (u a) a c • pauli a c
      = (2 : ℤ) ^ (m - 1) • ∑ a ∈ Finset.univ.filter (fun a : V m => a ≠ 0),
          (unit (u a + a) (u a) + unit (u a) (u a + a)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← sum_xz_hyperplane a (u a) (Finset.mem_filter.1 ha).2]
    exact Finset.sum_congr rfl (fun c _ => eps_smul_pauli (u a) a c)
  have hp : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h0, h1, pow_succ, hp]
  module

/-! ### Bonus: the observables with `c·a = 0` are symmetric involutions -/

theorem sgn_mul_self (x : ZMod 2) : sgn x * sgn x = 1 := by
  revert x
  unfold sgn
  decide

theorem xz_transpose (a c : V m) (h : c ⬝ᵥ a = 0) : (xz a c)ᵀ = xz a c := by
  ext b' b
  simp only [Matrix.transpose_apply, xz]
  by_cases hb : b' = b + a
  · subst hb
    simp [V_add_add_cancel, dotProduct_add, h]
  · have hb' : ¬ b = b' + a := by
      rintro rfl
      exact hb (V_add_add_cancel _ _).symm
    simp [hb, hb']

theorem xz_mul_self (a c : V m) (h : c ⬝ᵥ a = 0) : xz a c * xz a c = 1 := by
  ext b'' b
  simp only [Matrix.mul_apply, xz, Matrix.one_apply]
  rw [Finset.sum_eq_single (b + a)]
  · by_cases hb : b'' = b
    · subst hb
      simp [V_add_add_cancel, dotProduct_add, h, sgn_mul_self]
    · simp [V_add_add_cancel, hb]
  · intro x _ hx
    simp [hx]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

/-- For `c·a = 0` the observable `P_{a,c}` is symmetric. -/
theorem pauli_transpose (a c : V m) (h : c ⬝ᵥ a = 0) : (pauli a c)ᵀ = pauli a c := by
  unfold pauli
  rw [Matrix.transpose_smul, xz_transpose a c h]

/-- For `c·a = 0` the observable `P_{a,c}` squares to the identity. -/
theorem pauli_mul_self (a c : V m) (h : c ⬝ᵥ a = 0) : pauli a c * pauli a c = 1 := by
  unfold pauli
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, xz_mul_self a c h, ← mul_pow]
  norm_num

end sums

/-! ### Part 4. The two carriers of the family

Fixed definitions.  A carrier is given by its value `s` at the polar point `Z ⊗ 1` and its values
`σI p` at `1 ⊗ P_p` and `σZ p` at `Z ⊗ P_p`, where `p = (a, c)` runs over the labels of the real
non-identity block observables. -/

section family

variable {m : ℕ}

/-- Labels `(a, c)` of the real non-identity block observables `P_{a,c}`: `c·a = 0`, not both zero. -/
def realLabels (m : ℕ) : Finset (V m × V m) :=
  Finset.univ.filter fun p => p.2 ⬝ᵥ p.1 = 0 ∧ p ≠ 0

/-- Step 1: the block `C` of the carrier operator. -/
def blockC (s : ℤ) (σI σZ : V m × V m → ℤ) : Matrix (V m) (V m) ℤ :=
  s • (1 : Matrix (V m) (V m) ℤ) + ∑ p ∈ realLabels m, (σI p + σZ p) • pauli p.1 p.2

/-- Step 1: the block `D` of the carrier operator. -/
def blockD (s : ℤ) (σI σZ : V m × V m → ℤ) : Matrix (V m) (V m) ℤ :=
  (-s) • (1 : Matrix (V m) (V m) ℤ) + ∑ p ∈ realLabels m, (σI p - σZ p) • pauli p.1 p.2

/-- The signs of the family on the block observables: `ε(P_{0,c}) = (-1)^(c·t)` and, for `a ≠ 0`,
`ε(P_{a,c}) = (-1)^(c·u a) (-1)^((a·c)/2)`. -/
def famSign (t : V m) (u : V m → V m) (p : V m × V m) : ℤ :=
  if p.1 = 0 then eps t 0 p.2 else eps (u p.1) p.1 p.2

/-- The second carrier at `Z ⊗ P_{a,c}`: the opposite sign when the direction `a` lies in `F`. -/
def famSignZ (t : V m) (u : V m → V m) (F : Finset (V m)) (p : V m × V m) : ℤ :=
  if p.1 ∈ F then -famSign t u p else famSign t u p

/-- The edge of the direction `a`, as a matrix: `|u a + a⟩⟨u a| + |u a⟩⟨u a + a|`. -/
def edge (u : V m → V m) (a : V m) : Matrix (V m) (V m) ℤ :=
  unit (u a + a) (u a) + unit (u a) (u a + a)

/-- The edges of the directions in `F` touch neither the loop vertex `t` nor any other edge: `F` is a
union of connected components of the graph, and `t` is not on it. -/
structure Separated (t : V m) (u : V m → V m) (F : Finset (V m)) : Prop where
  ne_zero : ∀ b ∈ F, b ≠ 0
  loop : ∀ b ∈ F, t ≠ u b ∧ t ≠ u b + b
  apart : ∀ a, a ≠ 0 → a ∉ F → ∀ b ∈ F,
    u a ≠ u b ∧ u a ≠ u b + b ∧ u a + a ≠ u b ∧ u a + a ≠ u b + b

/-! #### 4a. Both carriers have values `±1`, and their blocks are graph matrices -/

theorem aux4a_sgn_eq_one_or (z : ZMod 2) : sgn z = 1 ∨ sgn z = -1 := by
  revert z
  unfold sgn
  decide

theorem aux4a_eps_eq_one_or (w a c : V m) : eps w a c = 1 ∨ eps w a c = -1 := by
  unfold eps
  rcases aux4a_sgn_eq_one_or (c ⬝ᵥ w) with h | h <;>
    rcases neg_one_pow_eq_or ℤ (overlap a c / 2) with h' | h' <;>
    rw [h, h'] <;> simp

/-- Sums over the labels split into the part `a = 0` and the hyperplanes of the directions `a ≠ 0`. -/
theorem aux4a_sum_realLabels (f : V m × V m → Matrix (V m) (V m) ℤ) :
    ∑ p ∈ realLabels m, f p
      = ∑ c ∈ Finset.univ.filter (fun c : V m => c ≠ 0), f (0, c)
        + ∑ a ∈ Finset.univ.filter (fun a : V m => a ≠ 0),
            ∑ c ∈ Finset.univ.filter (fun c : V m => c ⬝ᵥ a = 0), f (a, c) := by
  unfold realLabels
  rw [Finset.sum_filter, Fintype.sum_prod_type,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : V m => a = 0)]
  congr 1
  · rw [Finset.filter_eq' Finset.univ (0 : V m), ite_eq_left (Finset.mem_univ _), Finset.sum_singleton,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : c = 0
    · simp [hc]
    · simp [hc]
  · apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≠ 0 := (Finset.mem_filter.1 ha).2
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : c ⬝ᵥ a = 0
    · simp [hc, ha']
    · simp [hc]

/-- The character sums of Part 3 with a weight `κ a` on each direction. -/
theorem aux4a_sum_weighted (t : V m) (u : V m → V m) (κ : V m → ℤ) :
    ∑ p ∈ realLabels m, (κ p.1 * famSign t u p) • pauli p.1 p.2
      = κ 0 • ((2 : ℤ) ^ m • unit t t - 1)
        + ∑ a ∈ Finset.univ.filter (fun a : V m => a ≠ 0),
            (κ a * (2 : ℤ) ^ (m - 1)) • edge u a := by
  rw [aux4a_sum_realLabels]
  congr 1
  · rw [← sum_xz_diagonal t, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c _
    simp only [famSign, ite_true]
    rw [mul_smul, eps_smul_pauli]
  · apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≠ 0 := (Finset.mem_filter.1 ha).2
    unfold edge
    rw [mul_smul, ← sum_xz_hyperplane a (u a) ha', Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c _
    simp only [famSign, ite_eq_right ha']
    rw [mul_smul, eps_smul_pauli]

theorem aux4a_two_pow (hm : 1 ≤ m) : (2 : ℤ) * 2 ^ (m - 1) = 2 ^ m := by
  rw [← pow_succ']
  congr 1
  omega

theorem famSign_eq_one_or (t : V m) (u : V m → V m) (p : V m × V m) :
    famSign t u p = 1 ∨ famSign t u p = -1 := by
  unfold famSign
  split_ifs
  · exact aux4a_eps_eq_one_or _ _ _
  · exact aux4a_eps_eq_one_or _ _ _

theorem famSignZ_eq_one_or (t : V m) (u : V m → V m) (F : Finset (V m)) (p : V m × V m) :
    famSignZ t u F p = 1 ∨ famSignZ t u F p = -1 := by
  unfold famSignZ
  rcases famSign_eq_one_or t u p with h | h <;> split_ifs <;> rw [h] <;> simp

/-- Step 3, first carrier: `C = -1 + 2n |t⟩⟨t| + n Adj(G)` with `n = 2^m`. -/
theorem blockC_sigma (hm : 1 ≤ m) (t : V m) (u : V m → V m) :
    blockC 1 (famSign t u) (famSign t u)
      = -1 + (2 : ℤ) ^ m • ((2 : ℤ) • unit t t
          + ∑ a ∈ Finset.univ.filter (fun a : V m => a ≠ 0), edge u a) := by
  unfold blockC
  have e : ∑ p ∈ realLabels m, (famSign t u p + famSign t u p) • pauli p.1 p.2
      = ∑ p ∈ realLabels m, ((fun _ : V m => (2 : ℤ)) p.1 * famSign t u p) • pauli p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    ring
  rw [e, aux4a_sum_weighted t u (fun _ => 2)]
  simp only [aux4a_two_pow hm]
  rw [← Finset.smul_sum]
  module

/-- Step 3, first carrier: `D = -1`. -/
theorem blockD_sigma (t : V m) (u : V m → V m) :
    blockD 1 (famSign t u) (famSign t u) = -1 := by
  unfold blockD
  simp

/-- Step 3, second carrier: the edges of `F` are missing from `C`. -/
theorem blockC_tau (hm : 1 ≤ m) (t : V m) (u : V m → V m) (F : Finset (V m))
    (hF : ∀ b ∈ F, b ≠ 0) :
    blockC 1 (famSign t u) (famSignZ t u F)
      = -1 + (2 : ℤ) ^ m • ((2 : ℤ) • unit t t
          + ∑ a ∈ (Finset.univ.filter (fun a : V m => a ≠ 0)) \ F, edge u a) := by
  unfold blockC
  have h0 : (0 : V m) ∉ F := fun h => hF 0 h rfl
  have hFS : F ⊆ Finset.univ.filter (fun a : V m => a ≠ 0) := fun b hb =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hF b hb⟩
  have e : ∑ p ∈ realLabels m, (famSign t u p + famSignZ t u F p) • pauli p.1 p.2
      = ∑ p ∈ realLabels m,
          ((fun a : V m => if a ∈ F then (0 : ℤ) else 2) p.1 * famSign t u p) • pauli p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    unfold famSignZ
    beta_reduce
    split_ifs <;> ring
  have e1 : ∑ a ∈ (Finset.univ.filter (fun a : V m => a ≠ 0)) \ F,
        ((if a ∈ F then (0 : ℤ) else 2) * (2 : ℤ) ^ (m - 1)) • edge u a
      = (2 : ℤ) ^ m • ∑ a ∈ (Finset.univ.filter (fun a : V m => a ≠ 0)) \ F, edge u a := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [ite_eq_right (Finset.mem_sdiff.1 ha).2, aux4a_two_pow hm]
  have e2 : ∑ a ∈ F, ((if a ∈ F then (0 : ℤ) else 2) * (2 : ℤ) ^ (m - 1)) • edge u a = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [ite_eq_left ha, zero_mul, zero_smul]
  rw [e, aux4a_sum_weighted t u (fun a => if a ∈ F then (0 : ℤ) else 2), ← Finset.sum_sdiff hFS,
    e1, e2]
  simp only [ite_eq_right h0]
  module

/-- Step 3, second carrier: the edges of `F` are in `D`. -/
theorem blockD_tau (hm : 1 ≤ m) (t : V m) (u : V m → V m) (F : Finset (V m))
    (hF : ∀ b ∈ F, b ≠ 0) :
    blockD 1 (famSign t u) (famSignZ t u F) = -1 + (2 : ℤ) ^ m • ∑ a ∈ F, edge u a := by
  unfold blockD
  have h0 : (0 : V m) ∉ F := fun h => hF 0 h rfl
  have hFS : F ⊆ Finset.univ.filter (fun a : V m => a ≠ 0) := fun b hb =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hF b hb⟩
  have e : ∑ p ∈ realLabels m, (famSign t u p - famSignZ t u F p) • pauli p.1 p.2
      = ∑ p ∈ realLabels m,
          ((fun a : V m => if a ∈ F then (2 : ℤ) else 0) p.1 * famSign t u p) • pauli p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    unfold famSignZ
    beta_reduce
    split_ifs <;> ring
  have e1 : ∑ a ∈ (Finset.univ.filter (fun a : V m => a ≠ 0)) \ F,
        ((if a ∈ F then (2 : ℤ) else 0) * (2 : ℤ) ^ (m - 1)) • edge u a = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [ite_eq_right (Finset.mem_sdiff.1 ha).2, zero_mul, zero_smul]
  have e2 : ∑ a ∈ F, ((if a ∈ F then (2 : ℤ) else 0) * (2 : ℤ) ^ (m - 1)) • edge u a
      = (2 : ℤ) ^ m • ∑ a ∈ F, edge u a := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [ite_eq_left ha, aux4a_two_pow hm]
  rw [e, aux4a_sum_weighted t u (fun a => if a ∈ F then (2 : ℤ) else 0), ← Finset.sum_sdiff hFS,
    e1, e2]
  simp only [ite_eq_right h0]
  module

/-! #### 4b. The two main statements for a separated set of directions -/

theorem aux4b_unit_apply (i j x y : V m) :
    unit i j x y = if x = i ∧ y = j then 1 else 0 := rfl

/-- Product of two matrix units. -/
theorem aux4b_unit_mul (i j k l : V m) :
    unit i j * unit k l = if j = k then unit i l else 0 := by
  ext x y
  rw [Matrix.mul_apply]
  by_cases h : j = k
  · subst h
    rw [ite_eq_left rfl, Finset.sum_eq_single j]
    · simp only [aux4b_unit_apply]
      by_cases hx : x = i <;> by_cases hy : y = l <;> simp [hx, hy]
    · intro z _ hz
      simp [aux4b_unit_apply, hz]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [ite_eq_right h, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro z _
    simp only [aux4b_unit_apply]
    by_cases h1 : z = j
    · have h2 : ¬ z = k := fun e => h (h1.symm.trans e)
      simp [h2]
    · simp [h1]

/-- Trace of a matrix unit. -/
theorem aux4b_trace_unit (i j : V m) : trace (unit i j) = if i = j then 1 else 0 := by
  simp only [trace, Matrix.diag_apply, aux4b_unit_apply]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, Finset.sum_eq_single i]
    · simp
    · intro z _ hz
      simp [hz]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro z _
    have h3 : ¬ (z = i ∧ z = j) := by
      rintro ⟨rfl, rfl⟩
      exact h rfl
    simp [h3]

/-- Two edges without a common vertex multiply to zero. -/
theorem aux4b_pair_mul_zero (p q r s : V m) (h1 : p ≠ r) (h2 : p ≠ s) (h3 : q ≠ r) (h4 : q ≠ s) :
    (unit p q + unit q p) * (unit r s + unit s r) = 0 := by
  simp only [add_mul, mul_add, aux4b_unit_mul, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, add_zero]

theorem aux4b_edge_mul_edge (u : V m → V m) (a b : V m)
    (h : u a ≠ u b ∧ u a ≠ u b + b ∧ u a + a ≠ u b ∧ u a + a ≠ u b + b) :
    edge u a * edge u b = 0 :=
  aux4b_pair_mul_zero _ _ _ _ h.2.2.2 h.2.2.1 h.2.1 h.1

theorem aux4b_edge_mul_edge' (u : V m → V m) (a b : V m)
    (h : u a ≠ u b ∧ u a ≠ u b + b ∧ u a + a ≠ u b ∧ u a + a ≠ u b + b) :
    edge u b * edge u a = 0 :=
  aux4b_pair_mul_zero _ _ _ _ h.2.2.2.symm h.2.1.symm h.2.2.1.symm h.1.symm

theorem aux4b_loop_mul_edge (t : V m) (u : V m → V m) (b : V m)
    (h : t ≠ u b ∧ t ≠ u b + b) : unit t t * edge u b = 0 := by
  simp only [edge, mul_add, aux4b_unit_mul, ite_eq_right h.1, ite_eq_right h.2, add_zero]

theorem aux4b_edge_mul_loop (t : V m) (u : V m → V m) (b : V m)
    (h : t ≠ u b ∧ t ≠ u b + b) : edge u b * unit t t = 0 := by
  simp only [edge, add_mul, aux4b_unit_mul, ite_eq_right h.1.symm, ite_eq_right h.2.symm, add_zero]

theorem aux4b_add_ne (x a : V m) (ha : a ≠ 0) : ¬ x + a = x := by
  intro e
  exact ha (by simpa using e)

theorem aux4b_ne_add (x a : V m) (ha : a ≠ 0) : ¬ x = x + a := by
  intro e
  exact ha (by simpa using e)

/-- An edge has no diagonal entry. -/
theorem aux4b_trace_edge (u : V m → V m) (a : V m) (ha : a ≠ 0) : trace (edge u a) = 0 := by
  unfold edge
  rw [trace_add, aux4b_trace_unit, aux4b_trace_unit, ite_eq_right (aux4b_add_ne _ _ ha),
    ite_eq_right (aux4b_ne_add _ _ ha), add_zero]

theorem aux4b_trace_ite_unit (c : Prop) [Decidable c] (i j : V m) :
    trace (if c then unit i j else 0) = if c ∧ i = j then 1 else 0 := by
  by_cases hc : c
  · rw [ite_eq_left hc, aux4b_trace_unit]
    simp [hc]
  · rw [ite_eq_right hc, trace_zero, ite_eq_right (fun h => hc h.1)]

/-- Two edges of different directions are different edges. -/
theorem aux4b_trace_edge_mul (u : V m → V m) (a b : V m) (ha : a ≠ 0) :
    trace (edge u a * edge u b) = if a = b then 2 else 0 := by
  unfold edge
  simp only [add_mul, mul_add, aux4b_unit_mul, trace_add, aux4b_trace_ite_unit]
  by_cases hab : a = b
  · subst hab
    have h1 := aux4b_ne_add (u a) a ha
    have h2 := aux4b_add_ne (u a) a ha
    simp [h1, h2]
  · have c1 : ¬ (u a = u b ∧ u a + a = u b + b) := by
      rintro ⟨e1, e2⟩
      rw [e1] at e2
      exact hab (add_left_cancel e2)
    have c2 : ¬ (u a = u b + b ∧ u a + a = u b) := by
      rintro ⟨e1, e2⟩
      apply hab
      rw [e1, add_assoc] at e2
      have e3 : b + a = 0 := by simpa using e2
      exact ((V_add_eq_zero_iff b a).1 e3).symm
    have c3 : ¬ (u a + a = u b + b ∧ u a = u b) := fun h => c1 h.symm
    have c4 : ¬ (u a + a = u b ∧ u a = u b + b) := fun h => c2 h.symm
    simp only [ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right hab, add_zero]

/-- Splitting the edges into those outside `F` and those of `F`. -/
theorem aux4b_split (t : V m) (u : V m → V m) (F : Finset (V m)) (hF : ∀ b ∈ F, b ≠ 0) :
    (2 : ℤ) • unit t t + ∑ a ∈ Finset.univ.filter (fun a : V m => a ≠ 0), edge u a
      = ((2 : ℤ) • unit t t + ∑ a ∈ (Finset.univ.filter (fun a : V m => a ≠ 0)) \ F, edge u a)
        + ∑ a ∈ F, edge u a := by
  have hsub : F ⊆ Finset.univ.filter (fun a : V m => a ≠ 0) := fun b hb =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hF b hb⟩
  rw [add_assoc, Finset.sum_sdiff hsub]

theorem aux4b_mul12 (t : V m) (u : V m → V m) (F : Finset (V m)) (sep : Separated t u F) :
    ((2 : ℤ) • unit t t + ∑ a ∈ (Finset.univ.filter (fun a : V m => a ≠ 0)) \ F, edge u a)
      * ∑ a ∈ F, edge u a = 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro b hb
  rw [add_mul, smul_mul_assoc, aux4b_loop_mul_edge t u b (sep.loop b hb), smul_zero, zero_add,
    Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro a ha
  rw [Finset.mem_sdiff, Finset.mem_filter] at ha
  exact aux4b_edge_mul_edge u a b (sep.apart a ha.1.2 ha.2 b hb)

theorem aux4b_mul21 (t : V m) (u : V m → V m) (F : Finset (V m)) (sep : Separated t u F) :
    (∑ a ∈ F, edge u a)
      * ((2 : ℤ) • unit t t + ∑ a ∈ (Finset.univ.filter (fun a : V m => a ≠ 0)) \ F, edge u a)
      = 0 := by
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro b hb
  rw [mul_add, mul_smul_comm, aux4b_edge_mul_loop t u b (sep.loop b hb), smul_zero, zero_add,
    Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro a ha
  rw [Finset.mem_sdiff, Finset.mem_filter] at ha
  exact aux4b_edge_mul_edge' u a b (sep.apart a ha.1.2 ha.2 b hb)

theorem aux4b_trace1 (t : V m) (u : V m → V m) (F : Finset (V m)) :
    trace ((2 : ℤ) • unit t t
      + ∑ a ∈ (Finset.univ.filter (fun a : V m => a ≠ 0)) \ F, edge u a) = 2 := by
  have h0 : ∑ a ∈ (Finset.univ.filter (fun a : V m => a ≠ 0)) \ F, trace (edge u a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    exact aux4b_trace_edge u a (Finset.mem_filter.1 (Finset.mem_sdiff.1 ha).1).2
  rw [trace_add, trace_smul, aux4b_trace_unit, ite_eq_left rfl, trace_sum, h0]
  norm_num

theorem aux4b_trace2 (u : V m → V m) (F : Finset (V m)) (hF : ∀ b ∈ F, b ≠ 0) :
    trace (∑ a ∈ F, edge u a) = 0 := by
  rw [trace_sum]
  apply Finset.sum_eq_zero
  intro a ha
  exact aux4b_trace_edge u a (hF a ha)

theorem aux4b_trace2_sq (u : V m → V m) (F : Finset (V m)) (hF : ∀ b ∈ F, b ≠ 0) :
    trace ((∑ a ∈ F, edge u a) ^ 2) = 2 * (F.card : ℤ) := by
  rw [pow_two, Finset.sum_mul, trace_sum]
  have h : ∀ a ∈ F, trace (edge u a * ∑ b ∈ F, edge u b) = 2 := by
    intro a ha
    rw [Finset.mul_sum, trace_sum,
      Finset.sum_congr rfl (fun b _ => aux4b_trace_edge_mul u a b (hF a ha))]
    simp [ha]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Step 4 for the family: the two carrier operators have the same characteristic polynomial. -/
theorem c3_family_charpoly (hm : 1 ≤ m) (t : V m) (u : V m → V m) (F : Finset (V m))
    (sep : Separated t u F) :
    (carrier (blockC 1 (famSign t u) (famSign t u)) (blockD 1 (famSign t u) (famSign t u))).charpoly
      = (carrier (blockC 1 (famSign t u) (famSignZ t u F))
          (blockD 1 (famSign t u) (famSignZ t u F))).charpoly := by
  rw [blockC_sigma hm, blockD_sigma, blockC_tau hm t u F sep.ne_zero,
    blockD_tau hm t u F sep.ne_zero, aux4b_split t u F sep.ne_zero]
  exact carrier_charpoly_split _ _ _ (aux4b_mul12 t u F sep)

/-- Step 6 for the family: the cubic traces of the two completion operators differ by
`-12 n³ |F|` (that is `-(3/2) n³ |F|` for the completion matrices), `n = 2^m`. -/
theorem c3_family_cube_gap (hm : 1 ≤ m) (t : V m) (u : V m → V m) (F : Finset (V m))
    (sep : Separated t u F) :
    trace (sylvester (blockC 1 (famSign t u) (famSign t u))
          (blockD 1 (famSign t u) (famSign t u)) ^ 3)
        - trace (sylvester (blockC 1 (famSign t u) (famSignZ t u F))
          (blockD 1 (famSign t u) (famSignZ t u F)) ^ 3)
      = -12 * ((2 : ℤ) ^ m) ^ 3 * (F.card : ℤ) := by
  rw [blockC_sigma hm, blockD_sigma, blockC_tau hm t u F sep.ne_zero,
    blockD_tau hm t u F sep.ne_zero, aux4b_split t u F sep.ne_zero,
    sylvester_cube_gap_split _ _ _ (aux4b_mul12 t u F sep) (aux4b_mul21 t u F sep)
      (aux4b_trace2 u F sep.ne_zero),
    aux4b_trace1, aux4b_trace2_sq u F sep.ne_zero]
  ring

/-! #### 4c. The instance of the addendum, for every `m ≥ 3`

In the addendum vectors are written as integers: `1`, `2`, `4` are the basis vectors `e₀`, `e₁`, `e₂`
and `3 = e₀ + e₁`.  The instance is `u_1 = 0`, `u_2 = u_3 = 4`, `u_a = 2` for all other `a ≠ 0`,
`t = 2`, and the moved component is the single edge `{0, 1}` of the direction `1`. -/

/-- The basis vector `e_j` of `F_2^m`. -/
def basisVec (m : ℕ) (j : ℕ) (h : j < m) : V m := Pi.single (⟨j, h⟩ : Fin m) (1 : ZMod 2)

/-- The loop vertex `t = e₁`. -/
def defaultT (hm : 3 ≤ m) : V m := basisVec m 1 (by omega)

/-- The vertices `u a`. -/
def defaultU (hm : 3 ≤ m) (a : V m) : V m :=
  if a = basisVec m 0 (by omega) then 0
  else if a = basisVec m 1 (by omega) ∨ a = basisVec m 0 (by omega) + basisVec m 1 (by omega) then
    basisVec m 2 (by omega)
  else basisVec m 1 (by omega)

/-- The moved directions: only `e₀`. -/
def defaultF (hm : 3 ≤ m) : Finset (V m) := {basisVec m 0 (by omega)}

/-- Coordinates of a basis vector. -/
theorem aux4c_basisVec_apply (m j : ℕ) (h : j < m) (i : Fin m) :
    basisVec m j h i = if i = ⟨j, h⟩ then 1 else 0 := by
  unfold basisVec
  rw [Pi.single_apply]

/-- Two vectors that differ at one coordinate are different. -/
theorem aux4c_ne_of_coord {x y : V m} (i : Fin m) (h : x i ≠ y i) : x ≠ y :=
  fun e => h (congrFun e i)

theorem aux4c_e0_ne_zero (hm : 3 ≤ m) : basisVec m 0 (by omega) ≠ 0 := by
  apply aux4c_ne_of_coord ⟨0, by omega⟩
  simp [aux4c_basisVec_apply]

theorem aux4c_e1_ne_zero (hm : 3 ≤ m) : basisVec m 1 (by omega) ≠ 0 := by
  apply aux4c_ne_of_coord ⟨1, by omega⟩
  simp [aux4c_basisVec_apply]

theorem aux4c_e1_ne_e0 (hm : 3 ≤ m) : basisVec m 1 (by omega) ≠ basisVec m 0 (by omega) := by
  apply aux4c_ne_of_coord ⟨1, by omega⟩
  simp [aux4c_basisVec_apply]

theorem aux4c_e01_ne_e0 (hm : 3 ≤ m) :
    basisVec m 0 (by omega) + basisVec m 1 (by omega) ≠ basisVec m 0 (by omega) := by
  apply aux4c_ne_of_coord ⟨1, by omega⟩
  simp [aux4c_basisVec_apply]

theorem aux4c_U_e0 (hm : 3 ≤ m) : defaultU hm (basisVec m 0 (by omega)) = 0 := by
  unfold defaultU
  rw [ite_eq_left rfl]

theorem aux4c_U_e1 (hm : 3 ≤ m) :
    defaultU hm (basisVec m 1 (by omega)) = basisVec m 2 (by omega) := by
  unfold defaultU
  rw [ite_eq_right (aux4c_e1_ne_e0 hm), ite_eq_left (Or.inl rfl)]

theorem aux4c_U_e01 (hm : 3 ≤ m) :
    defaultU hm (basisVec m 0 (by omega) + basisVec m 1 (by omega)) = basisVec m 2 (by omega) := by
  unfold defaultU
  rw [ite_eq_right (aux4c_e01_ne_e0 hm), ite_eq_left (Or.inr rfl)]

theorem aux4c_U_other (hm : 3 ≤ m) (a : V m) (h0 : a ≠ basisVec m 0 (by omega))
    (h1 : a ≠ basisVec m 1 (by omega))
    (h01 : a ≠ basisVec m 0 (by omega) + basisVec m 1 (by omega)) :
    defaultU hm a = basisVec m 1 (by omega) := by
  unfold defaultU
  rw [ite_eq_right h0, ite_eq_right (by rintro (h | h); exacts [h1 h, h01 h])]

theorem defaultF_card (hm : 3 ≤ m) : (defaultF hm).card = 1 := by
  unfold defaultF
  exact Finset.card_singleton _

/-- The edge `{0, e₀}` is a connected component of the graph and does not contain `t`. -/
theorem default_separated (hm : 3 ≤ m) : Separated (defaultT hm) (defaultU hm) (defaultF hm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    rw [defaultF, Finset.mem_singleton] at hb
    subst hb
    exact aux4c_e0_ne_zero hm
  · intro b hb
    rw [defaultF, Finset.mem_singleton] at hb
    subst hb
    rw [aux4c_U_e0, zero_add]
    exact ⟨aux4c_e1_ne_zero hm, aux4c_e1_ne_e0 hm⟩
  · intro a _ haF b hb
    rw [defaultF, Finset.mem_singleton] at hb haF
    subst hb
    rw [aux4c_U_e0, zero_add]
    by_cases h1 : a = basisVec m 1 (by omega)
    · subst h1
      rw [aux4c_U_e1]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        (apply aux4c_ne_of_coord ⟨2, by omega⟩; simp [aux4c_basisVec_apply])
    · by_cases h01 : a = basisVec m 0 (by omega) + basisVec m 1 (by omega)
      · subst h01
        rw [aux4c_U_e01]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          (apply aux4c_ne_of_coord ⟨2, by omega⟩; simp [aux4c_basisVec_apply])
      · rw [aux4c_U_other hm a haF h1 h01]
        refine ⟨aux4c_e1_ne_zero hm, aux4c_e1_ne_e0 hm, ?_, ?_⟩
        · intro h
          exact h1 ((V_add_eq_zero_iff _ _).1 h).symm
        · intro h
          have ha : a = basisVec m 1 (by omega) + basisVec m 0 (by omega) := by
            rw [← h, V_add_add_cancel_left]
          exact h01 (ha.trans (add_comm _ _))

/-- **Case C3 for every number of qubits, block form.**  For every `m ≥ 3`, that is for every number
of qubits `N = m + 1 ≥ 4`, the two carriers of the instance have the same carrier characteristic
polynomial, and the cubic traces of their completion operators differ by `-12 n³`, `n = 2^m`. -/
theorem c3_all_qubits (hm : 3 ≤ m) :
    (carrier (blockC 1 (famSign (defaultT hm) (defaultU hm)) (famSign (defaultT hm) (defaultU hm)))
        (blockD 1 (famSign (defaultT hm) (defaultU hm)) (famSign (defaultT hm) (defaultU hm)))).charpoly
      = (carrier
          (blockC 1 (famSign (defaultT hm) (defaultU hm))
            (famSignZ (defaultT hm) (defaultU hm) (defaultF hm)))
          (blockD 1 (famSign (defaultT hm) (defaultU hm))
            (famSignZ (defaultT hm) (defaultU hm) (defaultF hm)))).charpoly
    ∧ trace (sylvester
          (blockC 1 (famSign (defaultT hm) (defaultU hm)) (famSign (defaultT hm) (defaultU hm)))
          (blockD 1 (famSign (defaultT hm) (defaultU hm)) (famSign (defaultT hm) (defaultU hm))) ^ 3)
        - trace (sylvester
          (blockC 1 (famSign (defaultT hm) (defaultU hm))
            (famSignZ (defaultT hm) (defaultU hm) (defaultF hm)))
          (blockD 1 (famSign (defaultT hm) (defaultU hm))
            (famSignZ (defaultT hm) (defaultU hm) (defaultF hm))) ^ 3)
      = -12 * ((2 : ℤ) ^ m) ^ 3 := by
  have hm1 : 1 ≤ m := by omega
  refine ⟨c3_family_charpoly hm1 _ _ _ (default_separated hm), ?_⟩
  rw [c3_family_cube_gap hm1 _ _ _ (default_separated hm), defaultF_card, Nat.cast_one, mul_one]

/-- The two carriers of the instance differ exactly at `Z ⊗ P_{a,c}` with `a = e₀`. -/
theorem default_differ (hm : 3 ≤ m) (p : V m × V m) :
    famSignZ (defaultT hm) (defaultU hm) (defaultF hm) p ≠ famSign (defaultT hm) (defaultU hm) p
      ↔ p.1 = basisVec m 0 (by omega) := by
  unfold famSignZ
  have hmem : p.1 ∈ defaultF hm ↔ p.1 = basisVec m 0 (by omega) := by
    unfold defaultF
    exact Finset.mem_singleton
  by_cases h : p.1 = basisVec m 0 (by omega)
  · rw [ite_eq_left (hmem.2 h)]
    refine ⟨fun _ => h, fun _ => ?_⟩
    rcases famSign_eq_one_or (defaultT hm) (defaultU hm) p with h1 | h1 <;> rw [h1] <;> decide
  · rw [ite_eq_right (fun hc => h (hmem.1 hc))]
    exact ⟨fun hne => absurd rfl hne, fun hp => absurd hp h⟩

/-! ### Part 5. The carrier operator on `N = m + 1` qubits

The first tensor factor is the qubit of the polar point `p⋆ = Z ⊗ 1`.  The section consists of
`Z ⊗ 1`, `1 ⊗ P_p` and `Z ⊗ P_p`, with `p` running over the real non-identity block observables. -/

/-- The Pauli matrix `Z`. -/
def Zmat : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

/-- The carrier operator `Σ σ(s) P_s` over the section, as a matrix on `N = m + 1` qubits. -/
def carrierOp (s : ℤ) (σI σZ : V m × V m → ℤ) : Matrix (Fin 2 × V m) (Fin 2 × V m) ℤ :=
  s • (Zmat ⊗ₖ (1 : Matrix (V m) (V m) ℤ))
    + ∑ p ∈ realLabels m, (σI p • ((1 : Matrix (Fin 2) (Fin 2) ℤ) ⊗ₖ pauli p.1 p.2)
        + σZ p • (Zmat ⊗ₖ pauli p.1 p.2))

/-- The index equivalence that sends the first qubit `0` to the left block and `1` to the right. -/
def aux5_equiv (m : ℕ) : Fin 2 × V m ≃ V m ⊕ V m where
  toFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  invFun := Sum.elim (fun x => (0, x)) (fun x => (1, x))
  left_inv := by
    rintro ⟨i, x⟩
    fin_cases i <;> simp
  right_inv := by
    rintro (x | x) <;> simp

/-- The carrier operator is the block matrix `carrier (blockC ..) (blockD ..)`, reindexed. -/
theorem aux5_carrierOp_eq (s : ℤ) (σI σZ : V m × V m → ℤ) :
    carrierOp s σI σZ
      = Matrix.reindex (aux5_equiv m).symm (aux5_equiv m).symm
          (carrier (blockC s σI σZ) (blockD s σI σZ)) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  simp only [carrierOp, carrier, blockC, blockD, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, kroneckerMap_apply,
    smul_eq_mul]
  fin_cases i <;> fin_cases j
  · simp only [aux5_equiv, Zmat, Equiv.coe_fn_mk, Fin.zero_eta, Fin.isValue, ite_true,
      fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      Matrix.one_apply_eq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, one_mul]
    refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun p _ => ?_) <;> ring
  · simp [aux5_equiv, Zmat]
  · simp [aux5_equiv, Zmat]
  · simp only [aux5_equiv, Zmat, Equiv.coe_fn_mk, Fin.mk_one, Fin.isValue, one_ne_zero, ite_false,
      fromBlocks_apply₂₂, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      Matrix.one_apply_eq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, one_mul]
    refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun p _ => ?_) <;> ring

/-- Step 1: the carrier operator has the blocks `blockC` and `blockD`. -/
theorem carrierOp_charpoly (s : ℤ) (σI σZ : V m × V m → ℤ) :
    (carrierOp s σI σZ).charpoly = (carrier (blockC s σI σZ) (blockD s σI σZ)).charpoly := by
  rw [aux5_carrierOp_eq, Matrix.charpoly_reindex]

/-- **Case C3 for every number of qubits.**  For every `m ≥ 3`, that is `N = m + 1 ≥ 4` qubits, there
are two carriers with values `±1` on the section whose carrier operators have the same characteristic
polynomial, while the cubic traces of the operators `M ↦ C * M + M * D` built from their blocks
differ. -/
theorem c3_all_qubits_carrierOp (hm : 3 ≤ m) :
    ∃ (σI σZ τI τZ : V m × V m → ℤ),
      (∀ p, σI p = 1 ∨ σI p = -1) ∧ (∀ p, σZ p = 1 ∨ σZ p = -1) ∧
      (∀ p, τI p = 1 ∨ τI p = -1) ∧ (∀ p, τZ p = 1 ∨ τZ p = -1) ∧
      (carrierOp 1 σI σZ).charpoly = (carrierOp 1 τI τZ).charpoly ∧
      trace (sylvester (blockC 1 σI σZ) (blockD 1 σI σZ) ^ 3)
        ≠ trace (sylvester (blockC 1 τI τZ) (blockD 1 τI τZ) ^ 3) := by
  obtain ⟨h1, h2⟩ := c3_all_qubits hm
  refine ⟨famSign (defaultT hm) (defaultU hm), famSign (defaultT hm) (defaultU hm),
    famSign (defaultT hm) (defaultU hm), famSignZ (defaultT hm) (defaultU hm) (defaultF hm),
    famSign_eq_one_or _ _, famSign_eq_one_or _ _, famSign_eq_one_or _ _,
    famSignZ_eq_one_or _ _ _, ?_, ?_⟩
  · rw [carrierOp_charpoly, carrierOp_charpoly]
    exact h1
  · intro heq
    rw [heq, sub_self] at h2
    have hne : (-12 : ℤ) * ((2 : ℤ) ^ m) ^ 3 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 3 (pow_ne_zero m (by norm_num)))
    exact hne h2.symm

end family

/-! ### Part 6. The completion matrix, defined from the contexts (Step 5)

Fixed definitions.  The outside observables are the real observables on `N = m + 1` qubits that
anticommute with the polar point `Z ⊗ 1`.  They are labelled by all pairs `q = (a, c)`:
`X ⊗ P_q` when `P_q` is real (`c·a = 0`), and `Y ⊗ P_q` when `P_q` is imaginary (`c·a = 1`).  In the
second case `P_q = i w` with the real matrix `w = pauli a c`, so `Y ⊗ P_q = (i Y) ⊗ w`. -/

section completion

variable {m : ℕ}

/-- The Pauli matrix `X`. -/
def Xmat : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- The real matrix `i Y`. -/
def Jmat : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

/-- The outside observable with the label `q = (a, c)`. -/
def outsideOp (q : V m × V m) : Matrix (Fin 2 × V m) (Fin 2 × V m) ℤ :=
  if q.2 ⬝ᵥ q.1 = 0 then Xmat ⊗ₖ pauli q.1 q.2 else Jmat ⊗ₖ pauli q.1 q.2

/-- The sign of the context formed by a section observable `S` and the outside observables with the
labels `q` and `p`: the number `tr (S O_q O_p) / 2n`, `n = 2^m`.  For three observables that commute
pairwise and multiply to `±1` it is that sign; for all other triples it is `0`. -/
def ctxSign (S : Matrix (Fin 2 × V m) (Fin 2 × V m) ℤ) (q p : V m × V m) : ℚ :=
  ((trace (S * outsideOp q * outsideOp p) : ℤ) : ℚ) / (2 * 2 ^ m)

/-- The completion matrix of a carrier.  Its entry at `(p, q)` is the sum, over the observables `s`
of the section, of the value of the carrier at `s` times the sign of the context `{s, q, p}`: the
polar point `Z ⊗ 1` with value `s₀`, and `1 ⊗ P_r`, `Z ⊗ P_r` with values `σI r`, `σZ r`. -/
def completion (s₀ : ℤ) (σI σZ : V m × V m → ℤ) : Matrix (V m × V m) (V m × V m) ℚ :=
  fun p q => (s₀ : ℚ) * ctxSign (Zmat ⊗ₖ (1 : Matrix (V m) (V m) ℤ)) q p
    + ∑ r ∈ realLabels m,
        ((σI r : ℚ) * ctxSign ((1 : Matrix (Fin 2) (Fin 2) ℤ) ⊗ₖ pauli r.1 r.2) q p
          + (σZ r : ℚ) * ctxSign (Zmat ⊗ₖ pauli r.1 r.2) q p)

/-! #### 6a. The outside observables -/

/-- `(X^a Z^c)ᵀ = (-1)^(c·a) X^a Z^c`. -/
theorem xz_transpose_sgn (a c : V m) : (xz a c)ᵀ = sgn (c ⬝ᵥ a) • xz a c := by
  ext b' b
  simp only [Matrix.transpose_apply, Matrix.smul_apply, xz, smul_eq_mul]
  by_cases hb : b' = b + a
  · subst hb
    simp [V_add_add_cancel, dotProduct_add, sgn_add, mul_comm]
  · have hb' : ¬ b = b' + a := by
      rintro rfl
      exact hb (V_add_add_cancel _ _).symm
    simp [hb, hb']

/-- `(X^a Z^c)² = (-1)^(c·a)`, without a hypothesis on the label. -/
theorem aux6a_xz_mul_self (a c : V m) : xz a c * xz a c = sgn (c ⬝ᵥ a) • 1 := by
  have hs : ∀ x y : ZMod 2, sgn (x + y) * sgn x = sgn y := by
    unfold sgn
    decide
  ext b'' b
  simp only [Matrix.mul_apply, xz, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (b + a)]
  · by_cases hb : b'' = b
    · subst hb
      simp [V_add_add_cancel, dotProduct_add, hs]
    · simp [V_add_add_cancel, hb]
  · intro x _ hx
    simp [hx]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem pauli_transpose_sgn (a c : V m) : (pauli a c)ᵀ = sgn (c ⬝ᵥ a) • pauli a c := by
  unfold pauli
  rw [Matrix.transpose_smul, xz_transpose_sgn, smul_comm]

/-- `w_q * w_q = (-1)^(c·a)`, without a hypothesis on the label. -/
theorem aux6a_pauli_mul_self (a c : V m) : pauli a c * pauli a c = sgn (c ⬝ᵥ a) • 1 := by
  unfold pauli
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, aux6a_xz_mul_self, ← mul_pow]
  norm_num

/-- For every label, `w_q * w_qᵀ = 1`. -/
theorem pauli_mul_transpose (a c : V m) : pauli a c * (pauli a c)ᵀ = 1 := by
  rw [pauli_transpose_sgn, Matrix.mul_smul, aux6a_pauli_mul_self, smul_smul, sgn_mul_self,
    one_smul]

theorem aux6a_Xmat_transpose : Xmatᵀ = Xmat := by
  unfold Xmat
  decide

theorem aux6a_Jmat_transpose : Jmatᵀ = (-1 : ℤ) • Jmat := by
  unfold Jmat
  decide

theorem aux6a_Xmat_mul_self : Xmat * Xmat = 1 := by
  unfold Xmat
  decide

theorem aux6a_Jmat_mul_self : Jmat * Jmat = (-1 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  unfold Jmat
  decide

theorem aux6a_Zmat_mul_Xmat : Zmat * Xmat = (-1 : ℤ) • (Xmat * Zmat) := by
  unfold Zmat Xmat
  decide

theorem aux6a_Zmat_mul_Jmat : Zmat * Jmat = (-1 : ℤ) • (Jmat * Zmat) := by
  unfold Zmat Jmat
  decide

theorem aux6a_eq_one_of_ne_zero (z : ZMod 2) (h : ¬ z = 0) : z = 1 := by
  revert z
  decide

/-- The outside observables are symmetric. -/
theorem outsideOp_transpose (q : V m × V m) : (outsideOp q)ᵀ = outsideOp q := by
  unfold outsideOp
  split_ifs with h
  · rw [← kroneckerMap_transpose, aux6a_Xmat_transpose, pauli_transpose_sgn, h, sgn_zero,
      one_smul]
  · rw [← kroneckerMap_transpose, aux6a_Jmat_transpose, pauli_transpose_sgn,
      aux6a_eq_one_of_ne_zero _ h, sgn_one, smul_kronecker, kronecker_smul, smul_smul]
    norm_num

/-- The outside observables square to the identity. -/
theorem outsideOp_mul_self (q : V m × V m) : outsideOp q * outsideOp q = 1 := by
  unfold outsideOp
  split_ifs with h
  · rw [← mul_kronecker_mul, aux6a_Xmat_mul_self, pauli_mul_self _ _ h, one_kronecker_one]
  · rw [← mul_kronecker_mul, aux6a_Jmat_mul_self, aux6a_pauli_mul_self,
      aux6a_eq_one_of_ne_zero _ h, sgn_one, smul_kronecker, kronecker_smul, smul_smul,
      one_kronecker_one]
    norm_num

/-- The outside observables anticommute with the polar point `Z ⊗ 1`. -/
theorem outsideOp_anticomm (q : V m × V m) :
    (Zmat ⊗ₖ (1 : Matrix (V m) (V m) ℤ)) * outsideOp q
      = -(outsideOp q * (Zmat ⊗ₖ (1 : Matrix (V m) (V m) ℤ))) := by
  unfold outsideOp
  split_ifs with h
  · rw [← mul_kronecker_mul, ← mul_kronecker_mul, aux6a_Zmat_mul_Xmat, smul_kronecker, one_mul,
      mul_one, neg_smul, one_smul]
  · rw [← mul_kronecker_mul, ← mul_kronecker_mul, aux6a_Zmat_mul_Jmat, smul_kronecker, one_mul,
      mul_one, neg_smul, one_smul]

/-- Completeness of the `n²` real matrices `w_q`: they form an orthogonal basis of all matrices. -/
theorem sum_pauli_mul_pauli (x y x' y' : V m) :
    ∑ q : V m × V m, pauli q.1 q.2 x y * pauli q.1 q.2 x' y'
      = if x = x' ∧ y = y' then (2 : ℤ) ^ m else 0 := by
  have hp : ∀ a c : V m, pauli a c x y * pauli a c x' y'
      = if a = x + y then (if x' = y' + a then sgn (c ⬝ᵥ (y + y')) else 0) else 0 := by
    intro a c
    have hs : ((-1 : ℤ) ^ (overlap a c / 2)) * ((-1 : ℤ) ^ (overlap a c / 2)) = 1 := by
      rw [← mul_pow]
      norm_num
    have hx : (x = y + a) ↔ (a = x + y) := by
      constructor
      · rintro rfl
        rw [add_comm y a, V_add_add_cancel]
      · rintro rfl
        rw [add_comm x y, V_add_add_cancel_left]
    simp only [pauli, Matrix.smul_apply, xz, smul_eq_mul, hx]
    rw [dotProduct_add, sgn_add]
    split_ifs
    · linear_combination (sgn (c ⬝ᵥ y) * sgn (c ⬝ᵥ y')) * hs
    · simp
    · simp
    · simp
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (x + y)]
  · simp only [hp, ite_true]
    by_cases h1 : x' = y' + (x + y)
    · simp only [eq_true h1, ite_true]
      rw [sum_sgn_dot]
      simp only [V_add_eq_zero_iff]
      by_cases h2 : y = y'
      · subst h2
        have hxx : x = x' := by
          rw [h1, add_comm x y, V_add_add_cancel_left]
        simp [hxx]
      · simp [h2]
    · simp only [eq_false h1, ite_false, Finset.sum_const_zero]
      have hn : ¬ (x = x' ∧ y = y') := by
        rintro ⟨rfl, rfl⟩
        apply h1
        rw [add_comm x y, V_add_add_cancel_left]
      simp only [eq_false hn, ite_false]
  · intro a _ ha
    simp only [hp, eq_false ha, ite_false, Finset.sum_const_zero]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

/-! #### 6b. The entries of the completion matrix -/

/-- By linearity, the entry of the completion matrix is `tr (A O_q O_p) / 2n`, with `A` the carrier
operator. -/
theorem completion_apply (s₀ : ℤ) (σI σZ : V m × V m → ℤ) (p q : V m × V m) :
    completion s₀ σI σZ p q
      = ((trace (carrierOp s₀ σI σZ * outsideOp q * outsideOp p) : ℤ) : ℚ) / (2 * 2 ^ m) := by
  unfold completion ctxSign carrierOp
  simp only [add_mul, Finset.sum_mul, Matrix.smul_mul, trace_add, trace_sum, trace_smul,
    smul_eq_mul]
  push_cast
  rw [add_div, Finset.sum_div]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun r _ => ?_
    ring

/-- The outside observable in blocks: `[[0, w_q], [w_qᵀ, 0]]`, reindexed. -/
theorem aux6b_outsideOp_eq (q : V m × V m) :
    outsideOp q
      = Matrix.reindex (aux5_equiv m).symm (aux5_equiv m).symm
          (fromBlocks 0 (pauli q.1 q.2) (pauli q.1 q.2)ᵀ 0) := by
  have hz : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  ext ⟨i, x⟩ ⟨j, y⟩
  unfold outsideOp
  rw [pauli_transpose_sgn]
  split_ifs with h
  · rw [h, sgn_zero, one_smul]
    fin_cases i <;> fin_cases j <;> simp [aux5_equiv, Xmat]
  · rw [hz _ h, sgn_one]
    fin_cases i <;> fin_cases j <;> simp [aux5_equiv, Jmat]

/-- The trace does not change under reindexing by an equivalence. -/
theorem aux6b_trace_reindex (M : Matrix (V m ⊕ V m) (V m ⊕ V m) ℤ) :
    trace (Matrix.reindex (aux5_equiv m).symm (aux5_equiv m).symm M) = trace M := by
  simp only [trace, Matrix.reindex_apply, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp ((aux5_equiv m).symm.symm) fun i => M i i

/-- `tr (M Nᵀ)` is the entrywise inner product. -/
theorem aux6b_trace_mul_transpose (M N : Matrix (V m) (V m) ℤ) :
    trace (M * Nᵀ) = ∑ x : V m, ∑ y : V m, N x y * M x y := by
  simp only [trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- In blocks: `tr (A O_q O_p)` is the inner product of `w_p` with `C w_q + w_q Dᵀ`. -/
theorem trace_carrierOp_outside (s₀ : ℤ) (σI σZ : V m × V m → ℤ) (p q : V m × V m) :
    trace (carrierOp s₀ σI σZ * outsideOp q * outsideOp p)
      = ∑ x : V m, ∑ y : V m, pauli p.1 p.2 x y
          * (blockC s₀ σI σZ * pauli q.1 q.2 + pauli q.1 q.2 * (blockD s₀ σI σZ)ᵀ) x y := by
  have h2 : trace (blockD s₀ σI σZ * (pauli q.1 q.2)ᵀ * pauli p.1 p.2)
      = trace (pauli q.1 q.2 * (blockD s₀ σI σZ)ᵀ * (pauli p.1 p.2)ᵀ) := by
    rw [← trace_transpose, transpose_mul, transpose_mul, transpose_transpose, trace_mul_comm]
  rw [aux5_carrierOp_eq, aux6b_outsideOp_eq q, aux6b_outsideOp_eq p]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [← Matrix.reindex_apply, aux6b_trace_reindex]
  unfold carrier
  rw [fromBlocks_multiply, fromBlocks_multiply, trace_fromBlocks_aux]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [h2, aux6b_trace_mul_transpose, aux6b_trace_mul_transpose, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.add_apply, mul_add]

/-! #### 6c. The cubic trace of the completion matrix, and the theorem -/

/-- The matrix whose column `q` is the matrix `w_q = pauli q.1 q.2`, written as a vector indexed by
the pairs `(x, y)`, with rational entries. -/
def aux6c_W (m : ℕ) : Matrix (V m × V m) (V m × V m) ℚ :=
  fun xy q => ((pauli q.1 q.2 xy.1 xy.2 : ℤ) : ℚ)

/-- Completeness of the matrices `w_q`, in matrix form: `W * Wᵀ = n • 1`. -/
theorem aux6c_W_mul_transpose :
    aux6c_W m * (aux6c_W m)ᵀ = ((2 : ℚ) ^ m) • (1 : Matrix (V m × V m) (V m × V m) ℚ) := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp only [Matrix.mul_apply, transpose_apply, aux6c_W, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, Prod.mk.injEq]
  have h2 := congrArg (Int.cast : ℤ → ℚ) (sum_pauli_mul_pauli x y x' y')
  push_cast at h2
  rw [h2]
  split_ifs <;> simp

/-- If `W * Wᵀ = n • 1`, the cubic trace of `Wᵀ * S * W` is `n³` times that of `S`. -/
theorem aux6c_trace_conj_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (W S : Matrix ι ι ℚ) (n : ℚ)
    (h : W * Wᵀ = n • (1 : Matrix ι ι ℚ)) :
    trace ((Wᵀ * (S * W)) ^ 3) = n ^ 3 * trace (S ^ 3) := by
  have e : (Wᵀ * (S * W)) ^ 3 = Wᵀ * (S * (W * Wᵀ) * (S * (W * Wᵀ)) * S * W) := by
    rw [pow_three]
    simp only [Matrix.mul_assoc]
  rw [e, trace_mul_comm, Matrix.mul_assoc _ W Wᵀ, h]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, trace_smul, smul_eq_mul, pow_three,
    Matrix.mul_assoc]
  ring

/-- The entrywise cast commutes with the trace of the cube. -/
theorem aux6c_trace_map_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) :
    trace ((M.map (Int.cast : ℤ → ℚ)) ^ 3) = ((trace (M ^ 3) : ℤ) : ℚ) := by
  have h : M.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix M := rfl
  rw [h, ← map_pow]
  simp [Matrix.trace]

/-- The cubic trace of `sylvester C D` does not change when `D` is transposed. -/
theorem aux6c_trace_sylvester_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C D : Matrix ι ι ℤ) :
    trace (sylvester C Dᵀ ^ 3) = trace (sylvester C D ^ 3) := by
  rw [trace_sylvester_cube, trace_sylvester_cube, ← transpose_pow, ← transpose_pow,
    trace_transpose, trace_transpose, trace_transpose]

/-- The completion matrix is `(1 / 2n) • Wᵀ * S * W`, with `S` the matrix of `M ↦ C * M + M * Dᵀ`. -/
theorem aux6c_completion_eq (s₀ : ℤ) (σI σZ : V m × V m → ℤ) :
    completion s₀ σI σZ
      = (1 / (2 * 2 ^ m) : ℚ) • ((aux6c_W m)ᵀ *
          ((sylvester (blockC s₀ σI σZ) (blockD s₀ σI σZ)ᵀ).map (Int.cast : ℤ → ℚ)
            * aux6c_W m)) := by
  ext p q
  have hs : ∀ x y : V m,
      (blockC s₀ σI σZ * pauli q.1 q.2 + pauli q.1 q.2 * (blockD s₀ σI σZ)ᵀ) x y
        = ∑ r : V m × V m,
            sylvester (blockC s₀ σI σZ) (blockD s₀ σI σZ)ᵀ (x, y) r * pauli q.1 q.2 r.1 r.2 :=
    fun x y => (sylvester_apply _ _ _ x y).symm
  rw [completion_apply, trace_carrierOp_outside]
  simp only [hs, Matrix.smul_apply, Matrix.mul_apply, transpose_apply, aux6c_W, Matrix.map_apply,
    smul_eq_mul]
  rw [Fintype.sum_prod_type]
  push_cast
  ring

/-- Step 5.  The completion matrix is the matrix of `M ↦ (C * M + M * Dᵀ) / 2` in the orthogonal
basis of the matrices `w_q`; so the trace of its cube is one eighth of that of `sylvester C D`. -/
theorem trace_completion_cube (s₀ : ℤ) (σI σZ : V m × V m → ℤ) :
    trace (completion s₀ σI σZ ^ 3)
      = ((trace (sylvester (blockC s₀ σI σZ) (blockD s₀ σI σZ) ^ 3) : ℤ) : ℚ) / 8 := by
  have hn : (2 : ℚ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [aux6c_completion_eq, smul_pow, trace_smul, smul_eq_mul,
    aux6c_trace_conj_cube _ _ _ aux6c_W_mul_transpose, aux6c_trace_map_cube,
    aux6c_trace_sylvester_transpose]
  field_simp
  ring

/-- **Theorem 17, case C3 for every number of qubits.**  For every `m ≥ 3`, that is for every number
of qubits `N = m + 1 ≥ 4`, there are two carriers with values `±1` on the section, both with value
`+1` at the polar point, whose carrier operators have the same characteristic polynomial, while the
cubic traces of their completion matrices differ by `-(3/2) n³`, `n = 2^m`. -/
theorem c3_all_qubits_completion (hm : 3 ≤ m) :
    ∃ (σI σZ τI τZ : V m × V m → ℤ),
      (∀ p, σI p = 1 ∨ σI p = -1) ∧ (∀ p, σZ p = 1 ∨ σZ p = -1) ∧
      (∀ p, τI p = 1 ∨ τI p = -1) ∧ (∀ p, τZ p = 1 ∨ τZ p = -1) ∧
      (carrierOp 1 σI σZ).charpoly = (carrierOp 1 τI τZ).charpoly ∧
      trace (completion 1 σI σZ ^ 3) - trace (completion 1 τI τZ ^ 3)
        = -(3 / 2 : ℚ) * ((2 : ℚ) ^ m) ^ 3 := by
  obtain ⟨h1, h2⟩ := c3_all_qubits hm
  refine ⟨famSign (defaultT hm) (defaultU hm), famSign (defaultT hm) (defaultU hm),
    famSign (defaultT hm) (defaultU hm), famSignZ (defaultT hm) (defaultU hm) (defaultF hm),
    famSign_eq_one_or _ _, famSign_eq_one_or _ _, famSign_eq_one_or _ _,
    famSignZ_eq_one_or _ _ _, ?_, ?_⟩
  · rw [carrierOp_charpoly, carrierOp_charpoly]
    exact h1
  · rw [trace_completion_cube, trace_completion_cube]
    have h3 := congrArg (Int.cast : ℤ → ℚ) h2
    push_cast at h3
    linear_combination h3 / 8

/-! #### 6d. Different completion spectra: the strict law fails -/

/-- The Pauli matrix `Z` is symmetric. -/
theorem aux6d_Zmat_transpose : Zmatᵀ = Zmat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Zmat]

/-- The carrier operator is symmetric. -/
theorem aux6d_carrierOp_transpose (s : ℤ) (σI σZ : V m × V m → ℤ) :
    (carrierOp s σI σZ)ᵀ = carrierOp s σI σZ := by
  unfold carrierOp
  rw [transpose_add, transpose_smul, transpose_sum, ← kroneckerMap_transpose,
    aux6d_Zmat_transpose, transpose_one]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun r hr => ?_)
  have hr0 : r.2 ⬝ᵥ r.1 = 0 := (Finset.mem_filter.1 hr).2.1
  rw [transpose_add, transpose_smul, transpose_smul, ← kroneckerMap_transpose,
    ← kroneckerMap_transpose, aux6d_Zmat_transpose, transpose_one, pauli_transpose _ _ hr0]

/-- The completion matrix is symmetric. -/
theorem completion_transpose (s₀ : ℤ) (σI σZ : V m × V m → ℤ) :
    (completion s₀ σI σZ)ᵀ = completion s₀ σI σZ := by
  ext p q
  rw [transpose_apply, completion_apply, completion_apply]
  have hA : (carrierOp s₀ σI σZ)ᵀ = carrierOp s₀ σI σZ := aux6d_carrierOp_transpose s₀ σI σZ
  have h : trace (carrierOp s₀ σI σZ * outsideOp p * outsideOp q)
      = trace (carrierOp s₀ σI σZ * outsideOp q * outsideOp p) := by
    calc trace (carrierOp s₀ σI σZ * outsideOp p * outsideOp q)
        = trace ((carrierOp s₀ σI σZ * outsideOp p * outsideOp q)ᵀ) := (trace_transpose _).symm
      _ = trace (outsideOp q * (outsideOp p * carrierOp s₀ σI σZ)) := by
          rw [transpose_mul, transpose_mul, outsideOp_transpose, outsideOp_transpose, hA]
      _ = trace (carrierOp s₀ σI σZ * outsideOp q * outsideOp p) := by
          rw [trace_mul_comm (outsideOp q) (outsideOp p * carrierOp s₀ σI σZ),
            trace_mul_cycle (carrierOp s₀ σI σZ) (outsideOp q) (outsideOp p)]
  rw [h]

/-- Power sums of the eigenvalues of a Hermitian matrix are the traces of its powers. -/
theorem aux6d_trace_pow_eq_sum_eigenvalues_pow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) ^ k := by
  have hU := hA.spectral_theorem
  have hpow : A ^ k = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues) ^ k) := by
    conv_lhs => rw [hU]
    rw [map_pow]
  rw [hpow, Unitary.conjStarAlgAut_apply, Matrix.diagonal_pow, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp]

/-- A symmetric rational matrix is Hermitian as a complex matrix. -/
theorem aux6d_isHermitian_map {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ)
    (hA : Aᵀ = A) : (A.map (algebraMap ℚ ℂ)).IsHermitian := by
  show (A.map (algebraMap ℚ ℂ))ᴴ = A.map (algebraMap ℚ ℂ)
  ext i j
  have hij : A j i = A i j := congrFun (congrFun hA i) j
  rw [conjTranspose_apply, map_apply, map_apply, hij]
  simp

/-- The cubic trace commutes with the cast of a rational matrix to the complex numbers. -/
theorem aux6d_trace_map_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ) :
    trace ((M.map (algebraMap ℚ ℂ)) ^ 3) = algebraMap ℚ ℂ (trace (M ^ 3)) := by
  have h : M.map (algebraMap ℚ ℂ) = (algebraMap ℚ ℂ).mapMatrix M := rfl
  rw [h, ← map_pow, RingHom.mapMatrix_apply, AddMonoidHom.map_trace]

/-- Two symmetric rational matrices with the same characteristic polynomial have the same trace of
the cube: the characteristic polynomial determines the eigenvalues with their multiplicities. -/
theorem trace_cube_eq_of_charpoly_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℚ)
    (hA : Aᵀ = A) (hB : Bᵀ = B) (h : A.charpoly = B.charpoly) :
    trace (A ^ 3) = trace (B ^ 3) := by
  have hA' := aux6d_isHermitian_map A hA
  have hB' := aux6d_isHermitian_map B hB
  have hch : (A.map (algebraMap ℚ ℂ)).charpoly = (B.map (algebraMap ℚ ℂ)).charpoly := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, h]
  have hev : hA'.eigenvalues = hB'.eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hA' hB').2 hch
  have htr : trace ((A.map (algebraMap ℚ ℂ)) ^ 3) = trace ((B.map (algebraMap ℚ ℂ)) ^ 3) := by
    rw [aux6d_trace_pow_eq_sum_eigenvalues_pow hA' 3, aux6d_trace_pow_eq_sum_eigenvalues_pow hB' 3,
      hev]
  rw [aux6d_trace_map_cube, aux6d_trace_map_cube] at htr
  exact (algebraMap ℚ ℂ).injective htr

/-- **The strict law fails in case C3 for every number of qubits `N = m + 1 ≥ 4`.**  There are two
carriers with values `±1` on the section whose carrier operators have the same characteristic
polynomial and whose completion matrices have different characteristic polynomials. -/
theorem c3_strict_law_fails (hm : 3 ≤ m) :
    ∃ (σI σZ τI τZ : V m × V m → ℤ),
      (∀ p, σI p = 1 ∨ σI p = -1) ∧ (∀ p, σZ p = 1 ∨ σZ p = -1) ∧
      (∀ p, τI p = 1 ∨ τI p = -1) ∧ (∀ p, τZ p = 1 ∨ τZ p = -1) ∧
      (carrierOp 1 σI σZ).charpoly = (carrierOp 1 τI τZ).charpoly ∧
      (completion 1 σI σZ).charpoly ≠ (completion 1 τI τZ).charpoly := by
  obtain ⟨σI, σZ, τI, τZ, h1, h2, h3, h4, h5, h6⟩ := c3_all_qubits_completion hm
  refine ⟨σI, σZ, τI, τZ, h1, h2, h3, h4, h5, ?_⟩
  intro heq
  have htr := trace_cube_eq_of_charpoly_eq _ _ (completion_transpose 1 σI σZ)
    (completion_transpose 1 τI τZ) heq
  rw [htr, sub_self] at h6
  have hne : -(3 / 2 : ℚ) * ((2 : ℚ) ^ m) ^ 3 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 3 (pow_ne_zero m (by norm_num)))
  exact hne h6.symm

end completion

/-! ### Part 7. The theorem in the language of the library

Fixed definitions.  The library (`HoggarBound/Pauli.lean`, `Bound.lean`, `Quadric.lean`) has, for every
number of qubits: the points `Pt N` (pairs of bit vectors), the Hermitian Pauli matrices
`HoggarBound.pauli u` over `ℂ` with their product rule `pauli u * pauli v = tau u v • pauli (u + v)`, the
symplectic form `symp` (`0` exactly for commuting observables), the quadratic form `qform`, the real
quadric `realPoints N` (non-identity observables with an even number of factors `Y`), the sign
`lineSign u v` of the context `{u, v, u + v}`, and the operator `opA S f = ∑_{u ∈ S} f u • pauli u`.

Here the configuration of case C3 on `N = m + 1` qubits is defined with these objects, and the theorem
of Part 6 is transferred to it. -/

section general

variable {m : ℕ}

/-- The polar point `p⋆`: `Z` on qubit 0. -/
def polar (m : ℕ) : Pt (m + 1) := (0, Pi.single 0 1)

/-- The section: the points of the real quadric that commute with the polar point. -/
def sectionPts (m : ℕ) : Finset (Pt (m + 1)) :=
  (realPoints (m + 1)).filter fun s => symp s (polar m) = 0

/-- The outside points: the points of the real quadric that anticommute with the polar point. -/
def outsidePts (m : ℕ) : Finset (Pt (m + 1)) :=
  (realPoints (m + 1)).filter fun s => symp s (polar m) = 1

/-- The completion matrix of a carrier `σ`, indexed by the outside points.  If `p ≠ q` are commuting
outside points, then `{p + q, p, q}` is a context whose third point `p + q` lies in the section, and
the entry is the sign of this context, `P_{p+q} P_q P_p = lineSign (p + q) q • 1`, times the value of
the carrier at `p + q`.  All other entries are zero. -/
noncomputable def completionMatrix (m : ℕ) (σ : Pt (m + 1) → ℝ) :
    Matrix {p // p ∈ outsidePts m} {p // p ∈ outsidePts m} ℝ :=
  fun p q => if p.1 ≠ q.1 ∧ symp p.1 q.1 = 0 then lineSign (p.1 + q.1) q.1 * σ (p.1 + q.1) else 0

/-- The outside point with the block label `q = (a, c)`: `X ⊗ P_q` or `Y ⊗ P_q`. -/
def outPt (q : V m × V m) : Pt (m + 1) :=
  ((Fin.cons (1 : ZMod 2) q.1 : Fin (m + 1) → ZMod 2), (Fin.cons (q.2 ⬝ᵥ q.1) q.2 : Fin (m + 1) → ZMod 2))

/-- The section points `1 ⊗ P_r` (`z = 0`) and `Z ⊗ P_r` (`z = 1`). -/
def secPt (z : ZMod 2) (r : V m × V m) : Pt (m + 1) :=
  ((Fin.cons (0 : ZMod 2) r.1 : Fin (m + 1) → ZMod 2), (Fin.cons z r.2 : Fin (m + 1) → ZMod 2))

/-- The carrier on `m + 1` qubits with the value `1` at the polar point and the sign tables `σI`, `σZ`
at `1 ⊗ P_r`, `Z ⊗ P_r`. -/
def liftCarrier (σI σZ : V m × V m → ℤ) (u : Pt (m + 1)) : ℝ :=
  if u = polar m then 1
  else if u.2 0 = 0 then ((σI (Fin.tail u.1, Fin.tail u.2) : ℤ) : ℝ)
  else ((σZ (Fin.tail u.1, Fin.tail u.2) : ℤ) : ℝ)

/-- Splitting off qubit 0: basis states of `m + 1` qubits as pairs. -/
def splitEquiv (m : ℕ) : (Fin (m + 1) → ZMod 2) ≃ Fin 2 × V m where
  toFun x := (x 0, Fin.tail x)
  invFun y := Fin.cons y.1 y.2
  left_inv x := Fin.cons_self_tail x
  right_inv y := by
    rcases y with ⟨i, x⟩
    exact Prod.ext rfl (Fin.tail_cons (α := fun _ => ZMod 2) i x)

/-! #### 7a. The section and the outside points -/

theorem aux7a_dot_split (x y : Fin (m + 1) → ZMod 2) :
    x ⬝ᵥ y = x 0 * y 0 + Fin.tail x ⬝ᵥ Fin.tail y := by
  simp only [dotProduct, Fin.sum_univ_succ, Fin.tail]

theorem aux7a_cons_dot (a₀ b₀ : ZMod 2) (a b : V m) :
    (Fin.cons a₀ a : Fin (m + 1) → ZMod 2) ⬝ᵥ (Fin.cons b₀ b : Fin (m + 1) → ZMod 2)
      = a₀ * b₀ + a ⬝ᵥ b := by
  simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem aux7a_symp_polar (s : Pt (m + 1)) : symp s (polar m) = s.1 0 := by
  simp [symp, polar]

theorem aux7a_symp_zero_left (v : Pt (m + 1)) : symp 0 v = 0 := by
  rw [symp_comm]; exact symp_zero_right v

theorem aux7a_symp_add_left (u v w : Pt (m + 1)) : symp (u + v) w = symp u w + symp v w := by
  rw [symp_comm, symp_add_right, symp_comm w u, symp_comm w v]

theorem aux7a_mem_section (u : Pt (m + 1)) :
    u ∈ sectionPts m ↔ (u ≠ 0 ∧ qform u = 0) ∧ symp u (polar m) = 0 := by
  simp [sectionPts, realPoints]

theorem aux7a_mem_outside (u : Pt (m + 1)) :
    u ∈ outsidePts m ↔ (u ≠ 0 ∧ qform u = 0) ∧ symp u (polar m) = 1 := by
  simp [outsidePts, realPoints]

theorem aux7a_zmod2_eq_of_add (a b : ZMod 2) (h : a + b = 0) : b = a := by
  revert a b; decide

theorem aux7a_secPt_inj {z z' : ZMod 2} {r r' : V m × V m} (h : secPt z r = secPt z' r') :
    z = z' ∧ r = r' := by
  have h1 : (Fin.cons (0 : ZMod 2) r.1 : Fin (m + 1) → ZMod 2) = Fin.cons 0 r'.1 :=
    congrArg Prod.fst h
  have h2 : (Fin.cons z r.2 : Fin (m + 1) → ZMod 2) = Fin.cons z' r'.2 := congrArg Prod.snd h
  exact ⟨(Fin.cons_inj.1 h2).1, Prod.ext (Fin.cons_inj.1 h1).2 (Fin.cons_inj.1 h2).2⟩

theorem aux7a_cons_zero_zero :
    (Fin.cons (0 : ZMod 2) (0 : V m) : Fin (m + 1) → ZMod 2) = 0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

theorem aux7a_polar_eq : polar m = secPt 1 (0 : V m × V m) := by
  refine Prod.ext ?_ ?_
  · exact aux7a_cons_zero_zero.symm
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [polar, secPt]
    · simp [polar, secPt, Fin.succ_ne_zero]

theorem aux7a_secPt_ne_zero (z : ZMod 2) {r : V m × V m} (hr : r ≠ 0) : secPt z r ≠ 0 := by
  intro h
  apply hr
  have h1 : (Fin.cons (0 : ZMod 2) r.1 : Fin (m + 1) → ZMod 2) = 0 := congrArg Prod.fst h
  have h2 : (Fin.cons z r.2 : Fin (m + 1) → ZMod 2) = 0 := congrArg Prod.snd h
  refine Prod.ext ?_ ?_
  · funext i
    have := congrFun h1 i.succ
    simpa using this
  · funext i
    have := congrFun h2 i.succ
    simpa using this

theorem aux7a_polar_ne_zero : polar m ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg Prod.snd h) 0
  simp [polar] at h2

/-- The polar point lies on the quadric and in the section. -/
theorem polar_mem_sectionPts : polar m ∈ sectionPts m := by
  rw [aux7a_mem_section]
  refine ⟨⟨aux7a_polar_ne_zero, ?_⟩, ?_⟩
  · simp [qform, polar]
  · rw [aux7a_symp_polar]; rfl

theorem secPt_mem_sectionPts (z : ZMod 2) (r : V m × V m) (hr : r ∈ realLabels m) :
    secPt z r ∈ sectionPts m := by
  have hr' : r.2 ⬝ᵥ r.1 = 0 ∧ r ≠ 0 := by simpa [realLabels] using hr
  rw [aux7a_mem_section]
  refine ⟨⟨aux7a_secPt_ne_zero z hr'.2, ?_⟩, ?_⟩
  · show (Fin.cons z r.2 : Fin (m + 1) → ZMod 2) ⬝ᵥ (Fin.cons 0 r.1 : Fin (m + 1) → ZMod 2) = 0
    rw [aux7a_cons_dot, hr'.1, mul_zero, add_zero]
  · rw [aux7a_symp_polar]; rfl

theorem outPt_mem_outsidePts (q : V m × V m) : outPt q ∈ outsidePts m := by
  have h0 : symp (outPt q) (polar m) = 1 := by rw [aux7a_symp_polar]; rfl
  rw [aux7a_mem_outside]
  refine ⟨⟨?_, ?_⟩, h0⟩
  · intro h
    rw [h, aux7a_symp_zero_left] at h0
    exact absurd h0 (by decide)
  · show (Fin.cons (q.2 ⬝ᵥ q.1) q.2 : Fin (m + 1) → ZMod 2) ⬝ᵥ
        (Fin.cons 1 q.1 : Fin (m + 1) → ZMod 2) = 0
    rw [aux7a_cons_dot, mul_one]
    exact zmod2_add_self _

theorem outPt_injective : Function.Injective (outPt : V m × V m → Pt (m + 1)) := by
  intro p q h
  have h1 : (Fin.cons (1 : ZMod 2) p.1 : Fin (m + 1) → ZMod 2) = Fin.cons 1 q.1 :=
    congrArg Prod.fst h
  have h2 : (Fin.cons (p.2 ⬝ᵥ p.1) p.2 : Fin (m + 1) → ZMod 2) = Fin.cons (q.2 ⬝ᵥ q.1) q.2 :=
    congrArg Prod.snd h
  exact Prod.ext (Fin.cons_inj.1 h1).2 (Fin.cons_inj.1 h2).2

/-- Every outside point is `outPt q` for a label `q`. -/
theorem mem_outsidePts_iff (u : Pt (m + 1)) : u ∈ outsidePts m ↔ ∃ q : V m × V m, outPt q = u := by
  constructor
  · intro hu
    obtain ⟨⟨-, hq⟩, hs⟩ := (aux7a_mem_outside u).1 hu
    rw [aux7a_symp_polar] at hs
    have hq' : u.2 ⬝ᵥ u.1 = 0 := hq
    rw [aux7a_dot_split, hs, mul_one] at hq'
    have ht : Fin.tail u.2 ⬝ᵥ Fin.tail u.1 = u.2 0 := aux7a_zmod2_eq_of_add _ _ hq'
    refine ⟨(Fin.tail u.1, Fin.tail u.2), Prod.ext ?_ ?_⟩
    · show (Fin.cons (1 : ZMod 2) (Fin.tail u.1) : Fin (m + 1) → ZMod 2) = u.1
      rw [← hs]; exact Fin.cons_self_tail u.1
    · show (Fin.cons (Fin.tail u.2 ⬝ᵥ Fin.tail u.1) (Fin.tail u.2) : Fin (m + 1) → ZMod 2) = u.2
      rw [ht]; exact Fin.cons_self_tail u.2
  · rintro ⟨q, rfl⟩
    exact outPt_mem_outsidePts q

theorem aux7a_secPt_tail (u : Pt (m + 1)) (h : u.1 0 = 0) :
    secPt (u.2 0) (Fin.tail u.1, Fin.tail u.2) = u := by
  refine Prod.ext ?_ ?_
  · show (Fin.cons (0 : ZMod 2) (Fin.tail u.1) : Fin (m + 1) → ZMod 2) = u.1
    rw [← h]; exact Fin.cons_self_tail u.1
  · exact Fin.cons_self_tail u.2

/-- The section is the polar point together with the points `1 ⊗ P_r` and `Z ⊗ P_r`, `r` a real
non-identity block label. -/
theorem mem_sectionPts_iff (u : Pt (m + 1)) :
    u ∈ sectionPts m ↔ u = polar m ∨ ∃ z : ZMod 2, ∃ r ∈ realLabels m, secPt z r = u := by
  constructor
  · intro hu
    obtain ⟨⟨hne, hq⟩, hs⟩ := (aux7a_mem_section u).1 hu
    rw [aux7a_symp_polar] at hs
    have hq' : u.2 ⬝ᵥ u.1 = 0 := hq
    rw [aux7a_dot_split, hs, mul_zero, zero_add] at hq'
    have hu' := aux7a_secPt_tail u hs
    by_cases h0 : ((Fin.tail u.1, Fin.tail u.2) : V m × V m) = 0
    · left
      rw [h0] at hu'
      rcases zmod2_cases (u.2 0) with hz | hz
      · exfalso
        apply hne
        rw [← hu', hz]
        exact Prod.ext aux7a_cons_zero_zero aux7a_cons_zero_zero
      · rw [← hu', hz, aux7a_polar_eq]
    · right
      refine ⟨u.2 0, (Fin.tail u.1, Fin.tail u.2), ?_, hu'⟩
      simp only [realLabels, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hq', h0⟩
  · rintro (rfl | ⟨z, r, hr, rfl⟩)
    · exact polar_mem_sectionPts
    · exact secPt_mem_sectionPts z r hr

/-- Sums over the section. -/
theorem sum_sectionPts {M : Type*} [AddCommMonoid M] (f : Pt (m + 1) → M) :
    ∑ u ∈ sectionPts m, f u = f (polar m) + ∑ r ∈ realLabels m, (f (secPt 0 r) + f (secPt 1 r)) := by
  classical
  have hS : sectionPts m
      = insert (polar m) ((realLabels m).image (secPt 0) ∪ (realLabels m).image (secPt 1)) := by
    ext u
    rw [mem_sectionPts_iff]
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (h | ⟨z, r, hr, rfl⟩)
      · exact Or.inl h
      · rcases zmod2_cases z with rfl | rfl
        · exact Or.inr (Or.inl ⟨r, hr, rfl⟩)
        · exact Or.inr (Or.inr ⟨r, hr, rfl⟩)
    · rintro (h | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨0, r, hr, rfl⟩
      · exact Or.inr ⟨1, r, hr, rfl⟩
  have hpol : polar m ∉ (realLabels m).image (secPt 0) ∪ (realLabels m).image (secPt 1) := by
    simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
    refine ⟨fun r _ h => ?_, fun r hr h => ?_⟩
    · rw [aux7a_polar_eq] at h
      exact absurd (aux7a_secPt_inj h).1 (by decide)
    · rw [aux7a_polar_eq] at h
      have hr' : r.2 ⬝ᵥ r.1 = 0 ∧ r ≠ 0 := by simpa [realLabels] using hr
      exact hr'.2 (aux7a_secPt_inj h).2
  have hdisj : Disjoint ((realLabels m).image (secPt 0)) ((realLabels m).image (secPt 1)) := by
    rw [Finset.disjoint_left]
    intro u h0 h1
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 h0
    obtain ⟨r', -, h⟩ := Finset.mem_image.1 h1
    exact absurd (aux7a_secPt_inj h).1 (by decide)
  rw [hS, Finset.sum_insert hpol, Finset.sum_union hdisj, Finset.sum_image, Finset.sum_image,
    Finset.sum_add_distrib]
  · intro r _ r' _ h
    exact (aux7a_secPt_inj h).2
  · intro r _ r' _ h
    exact (aux7a_secPt_inj h).2

/-- Two different commuting outside points span a context whose third point is in the section. -/
theorem add_mem_sectionPts {p q : Pt (m + 1)} (hp : p ∈ outsidePts m) (hq : q ∈ outsidePts m)
    (hne : p ≠ q) (hc : symp p q = 0) : p + q ∈ sectionPts m := by
  obtain ⟨⟨-, hp2⟩, hp3⟩ := (aux7a_mem_outside p).1 hp
  obtain ⟨⟨-, hq2⟩, hq3⟩ := (aux7a_mem_outside q).1 hq
  rw [aux7a_mem_section]
  refine ⟨⟨fun h => hne (pt_eq_of_add_eq_zero h), ?_⟩, ?_⟩
  · rw [qform_add, hp2, hq2, hc]; rfl
  · rw [aux7a_symp_add_left, hp3, hq3]; rfl

/-- Conversely the sum of two outside points lies in the section only in that case. -/
theorem add_mem_sectionPts_iff {p q : Pt (m + 1)} (hp : p ∈ outsidePts m) (hq : q ∈ outsidePts m) :
    p + q ∈ sectionPts m ↔ p ≠ q ∧ symp p q = 0 := by
  constructor
  · intro h
    obtain ⟨⟨-, hp2⟩, -⟩ := (aux7a_mem_outside p).1 hp
    obtain ⟨⟨-, hq2⟩, -⟩ := (aux7a_mem_outside q).1 hq
    obtain ⟨⟨hne, hq'⟩, -⟩ := (aux7a_mem_section (p + q)).1 h
    refine ⟨fun hpq => hne ?_, ?_⟩
    · rw [hpq]; exact pt_add_self q
    · rw [qform_add, hp2, hq2, zero_add, zero_add] at hq'
      exact hq'
  · rintro ⟨hne, hc⟩
    exact add_mem_sectionPts hp hq hne hc

/-- A section point and an outside point that commute span a context whose third point is another
outside point. -/
theorem add_mem_outsidePts {s p : Pt (m + 1)} (hs : s ∈ sectionPts m) (hp : p ∈ outsidePts m)
    (hc : symp s p = 0) : s + p ∈ outsidePts m ∧ s + p ≠ p := by
  obtain ⟨⟨hs1, hs2⟩, hs3⟩ := (aux7a_mem_section s).1 hs
  obtain ⟨⟨-, hp2⟩, hp3⟩ := (aux7a_mem_outside p).1 hp
  have h0 : symp (s + p) (polar m) = 1 := by
    rw [aux7a_symp_add_left, hs3, hp3]; rfl
  refine ⟨?_, ?_⟩
  · rw [aux7a_mem_outside]
    refine ⟨⟨?_, ?_⟩, h0⟩
    · intro h
      rw [h, aux7a_symp_zero_left] at h0
      exact absurd h0 (by decide)
    · rw [qform_add, hs2, hp2, hc]; rfl
  · intro h
    apply hs1
    calc s = (s + p) + p := by rw [add_assoc, pt_add_self, add_zero]
      _ = p + p := by rw [h]
      _ = 0 := pt_add_self p

/-- The polar point commutes with no outside point. -/
theorem symp_polar_outside {p : Pt (m + 1)} (hp : p ∈ outsidePts m) : symp (polar m) p = 1 := by
  rw [symp_comm]
  exact ((aux7a_mem_outside p).1 hp).2

/-- The outside points are exactly the points `outPt q`: an equivalence with the block labels. -/
noncomputable def outEquiv (m : ℕ) : V m × V m ≃ {p // p ∈ outsidePts m} :=
  Equiv.ofBijective (fun q => ⟨outPt q, outPt_mem_outsidePts q⟩)
    ⟨fun _ _ h => outPt_injective (congrArg Subtype.val h), fun p => by
      obtain ⟨q, hq⟩ := (mem_outsidePts_iff p.1).1 p.2
      exact ⟨q, Subtype.ext hq⟩⟩

/-- There are `n² = 4^m` outside points. -/
theorem card_outsidePts : (outsidePts m).card = 4 ^ m := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (outEquiv m), Fintype.card_prod, Fintype.card_fun,
    ZMod.card, Fintype.card_fin, ← mul_pow]
  norm_num

/-- There are `1 + 2 |R|` section points. -/
theorem card_sectionPts : (sectionPts m).card = 1 + 2 * (realLabels m).card := by
  have h := sum_sectionPts (m := m) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  omega

/-! #### 7b. The Pauli matrices of the library are the Kronecker products of Parts 5 and 6 -/

/-- The sign character of the library is the integer sign of Part 3. -/
theorem aux7b_eps_cast (z : ZMod 2) : HoggarBound.eps z = ((sgn z : ℤ) : ℂ) := by
  rcases zmod2_cases z with rfl | rfl
  · rw [HoggarBound.eps_zero, sgn_zero]
    norm_num
  · rw [HoggarBound.eps_one, sgn_one]
    norm_num

theorem aux7b_cons_eq_iff (a₀ : ZMod 2) (a : V m) (x y : Fin (m + 1) → ZMod 2) :
    x = y + (Fin.cons a₀ a : Fin (m + 1) → ZMod 2)
      ↔ x 0 = y 0 + a₀ ∧ Fin.tail x = Fin.tail y + a := by
  constructor
  · intro h
    subst h
    refine ⟨by simp, ?_⟩
    funext i
    simp [Fin.tail]
  · rintro ⟨h0, ht⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h0
    · have := congrFun ht j
      simpa [Fin.tail] using this

theorem aux7b_cons_dot (c₀ : ZMod 2) (c : V m) (y : Fin (m + 1) → ZMod 2) :
    (Fin.cons c₀ c : Fin (m + 1) → ZMod 2) ⬝ᵥ y = c₀ * y 0 + c ⬝ᵥ Fin.tail y := by
  simp [dotProduct, Fin.sum_univ_succ, Fin.tail]

/-- The Weyl operator with qubit 0 split off. -/
theorem aux7b_weyl_cons (a₀ c₀ : ZMod 2) (a c : V m) (x y : Fin (m + 1) → ZMod 2) :
    weyl (((Fin.cons a₀ a : Fin (m + 1) → ZMod 2), (Fin.cons c₀ c : Fin (m + 1) → ZMod 2)) : Pt (m + 1))
        x y
      = (if x 0 = y 0 + a₀ then ((sgn (c₀ * y 0) : ℤ) : ℂ) else 0)
          * (((xz a c (Fin.tail x) (Fin.tail y) : ℤ)) : ℂ) := by
  simp only [weyl, chi, xz, aux7b_cons_dot, aux7b_eps_cast, aux7b_cons_eq_iff, sgn_add]
  by_cases h0 : x 0 = y 0 + a₀ <;> by_cases ht : Fin.tail x = Fin.tail y + a <;> simp [h0, ht]

/-- The number of factors `Y` with qubit 0 split off. -/
theorem aux7b_ycount_cons (a₀ c₀ : ZMod 2) (a c : V m) :
    ycount (((Fin.cons a₀ a : Fin (m + 1) → ZMod 2), (Fin.cons c₀ c : Fin (m + 1) → ZMod 2)) : Pt (m + 1))
      = (if a₀ = 1 ∧ c₀ = 1 then 1 else 0) + overlap a c := by
  unfold ycount overlap
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp

theorem aux7b_overlap_cast (a c : V m) : ((overlap a c : ℕ) : ZMod 2) = c ⬝ᵥ a :=
  (dot_eq_ycount ((a, c) : Pt m)).symm

theorem aux7b_I_pow_even (a c : V m) (h : c ⬝ᵥ a = 0) :
    Complex.I ^ overlap a c = (((-1 : ℤ) ^ (overlap a c / 2) : ℤ) : ℂ) := by
  have hc := aux7b_overlap_cast a c
  rw [h] at hc
  generalize overlap a c = k at hc ⊢
  have h2 : k % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
    · exact h2
    · exfalso
      rw [← ZMod.natCast_mod k 2, h2] at hc
      simp at hc
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  have e2 : (2 * j) / 2 = j := by omega
  rw [e2, pow_mul, Complex.I_sq]
  push_cast
  rfl

theorem aux7b_I_pow_odd (a c : V m) (h : ¬ c ⬝ᵥ a = 0) :
    Complex.I ^ (1 + overlap a c) = ((-1 : ℤ) : ℂ) * (((-1 : ℤ) ^ (overlap a c / 2) : ℤ) : ℂ) := by
  have hc := aux7b_overlap_cast a c
  generalize overlap a c = k at hc ⊢
  have h2 : k % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
    · exfalso
      rw [← ZMod.natCast_mod k 2, h2] at hc
      exact h (by rw [← hc]; simp)
    · exact h2
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  have e1 : 1 + (2 * j + 1) = 2 * (j + 1) := by ring
  have e2 : (2 * j + 1) / 2 = j := by omega
  rw [e1, e2, pow_mul, Complex.I_sq]
  push_cast
  ring

/-- The general statement: the Pauli matrix of a point with qubit 0 split off is a Kronecker product,
if the factor `A` of qubit 0 is `s` times the Weyl factor and the phase is `s` times the block phase. -/
theorem aux7b_pauli_cons (a₀ c₀ : ZMod 2) (a c : V m) (A : Matrix (Fin 2) (Fin 2) ℤ) (s : ℤ)
    (hA : ∀ i j : ZMod 2, A i j = s * (if i = j + a₀ then sgn (c₀ * j) else 0))
    (hI : Complex.I ^ ((if a₀ = 1 ∧ c₀ = 1 then 1 else 0) + overlap a c)
        = (s : ℂ) * (((-1 : ℤ) ^ (overlap a c / 2) : ℤ) : ℂ)) :
    HoggarBound.pauli
        (((Fin.cons a₀ a : Fin (m + 1) → ZMod 2), (Fin.cons c₀ c : Fin (m + 1) → ZMod 2)) : Pt (m + 1))
      = Matrix.reindex (splitEquiv m).symm (splitEquiv m).symm
          ((A ⊗ₖ pauli a c).map (Int.cast : ℤ → ℂ)) := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.kroneckerMap_apply,
    Equiv.symm_symm, splitEquiv, Equiv.coe_fn_mk]
  rw [hA (x 0) (y 0)]
  unfold HoggarBound.pauli pauli
  rw [Matrix.smul_apply, Matrix.smul_apply, aux7b_ycount_cons, hI, aux7b_weyl_cons]
  by_cases h0 : x 0 = y 0 + a₀
  · simp only [h0, ite_true, smul_eq_mul]
    push_cast
    ring
  · simp [h0]

theorem aux7b_polar_eq :
    polar m = (((Fin.cons (0 : ZMod 2) (0 : V m) : Fin (m + 1) → ZMod 2),
      (Fin.cons (1 : ZMod 2) (0 : V m) : Fin (m + 1) → ZMod 2)) : Pt (m + 1)) := by
  unfold polar
  refine Prod.ext ?_ ?_
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.succ_ne_zero]

theorem aux7b_one_entry : ∀ i j : ZMod 2,
    (1 : Matrix (Fin 2) (Fin 2) ℤ) i j = 1 * (if i = j + 0 then sgn (0 * j) else 0) := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem aux7b_Zmat_entry : ∀ i j : ZMod 2,
    Zmat i j = 1 * (if i = j + 0 then sgn (1 * j) else 0) := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem aux7b_Xmat_entry : ∀ i j : ZMod 2,
    Xmat i j = 1 * (if i = j + 1 then sgn (0 * j) else 0) := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem aux7b_Jmat_entry : ∀ i j : ZMod 2,
    Jmat i j = (-1) * (if i = j + 1 then sgn (1 * j) else 0) := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem pauli_polar :
    HoggarBound.pauli (polar m)
      = Matrix.reindex (splitEquiv m).symm (splitEquiv m).symm
          ((Zmat ⊗ₖ (1 : Matrix (V m) (V m) ℤ)).map (Int.cast : ℤ → ℂ)) := by
  have h01 : ¬ ((0 : ZMod 2) = 1) := by decide
  have hp : pauli (0 : V m) 0 = 1 := by
    have ho : overlap (0 : V m) 0 = 0 := by simp [overlap, h01]
    simp [pauli, ho, xz_zero_zero]
  have key := aux7b_pauli_cons 0 1 (0 : V m) 0 Zmat 1 aux7b_Zmat_entry (by
    rw [ite_eq_right (fun h => h01 h.1), zero_add, aux7b_I_pow_even _ _ (by simp)]
    simp)
  rw [aux7b_polar_eq, key, hp]

theorem pauli_secPt_zero (r : V m × V m) (hr : r.2 ⬝ᵥ r.1 = 0) :
    HoggarBound.pauli (secPt 0 r)
      = Matrix.reindex (splitEquiv m).symm (splitEquiv m).symm
          (((1 : Matrix (Fin 2) (Fin 2) ℤ) ⊗ₖ pauli r.1 r.2).map (Int.cast : ℤ → ℂ)) := by
  have h01 : ¬ ((0 : ZMod 2) = 1) := by decide
  exact aux7b_pauli_cons 0 0 r.1 r.2 1 1 aux7b_one_entry (by
    rw [ite_eq_right (fun h => h01 h.1), zero_add, aux7b_I_pow_even _ _ hr]
    simp)

theorem pauli_secPt_one (r : V m × V m) (hr : r.2 ⬝ᵥ r.1 = 0) :
    HoggarBound.pauli (secPt 1 r)
      = Matrix.reindex (splitEquiv m).symm (splitEquiv m).symm
          ((Zmat ⊗ₖ pauli r.1 r.2).map (Int.cast : ℤ → ℂ)) := by
  have h01 : ¬ ((0 : ZMod 2) = 1) := by decide
  exact aux7b_pauli_cons 0 1 r.1 r.2 Zmat 1 aux7b_Zmat_entry (by
    rw [ite_eq_right (fun h => h01 h.1), zero_add, aux7b_I_pow_even _ _ hr]
    simp)

/-- The outside observables of Part 6 are the Pauli matrices of the outside points. -/
theorem pauli_outPt (q : V m × V m) :
    HoggarBound.pauli (outPt q)
      = Matrix.reindex (splitEquiv m).symm (splitEquiv m).symm
          ((outsideOp q).map (Int.cast : ℤ → ℂ)) := by
  have h01 : ¬ ((0 : ZMod 2) = 1) := by decide
  unfold outsideOp outPt
  split_ifs with h
  · rw [h]
    exact aux7b_pauli_cons 1 0 q.1 q.2 Xmat 1 aux7b_Xmat_entry (by
      rw [ite_eq_right (fun hh => h01 hh.2), zero_add, aux7b_I_pow_even _ _ h]
      simp)
  · have h1 : q.2 ⬝ᵥ q.1 = 1 := (zmod2_cases _).resolve_left h
    rw [h1]
    exact aux7b_pauli_cons 1 1 q.1 q.2 Jmat (-1) aux7b_Jmat_entry (by
      rw [ite_eq_left ⟨rfl, rfl⟩, aux7b_I_pow_odd _ _ h])

/-! #### 7c. The carrier operator -/

theorem liftCarrier_eq_one_or (σI σZ : V m × V m → ℤ) (hI : ∀ p, σI p = 1 ∨ σI p = -1)
    (hZ : ∀ p, σZ p = 1 ∨ σZ p = -1) (u : Pt (m + 1)) :
    liftCarrier σI σZ u = 1 ∨ liftCarrier σI σZ u = -1 := by
  unfold liftCarrier
  split_ifs
  · exact Or.inl rfl
  · rcases hI (Fin.tail u.1, Fin.tail u.2) with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  · rcases hZ (Fin.tail u.1, Fin.tail u.2) with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num

theorem liftCarrier_polar (σI σZ : V m × V m → ℤ) : liftCarrier σI σZ (polar m) = 1 := by
  unfold liftCarrier
  rw [ite_eq_left rfl]

/-- A section point `1 ⊗ P_r` or `Z ⊗ P_r` with `r ≠ 0` is not the polar point. -/
theorem aux7c_secPt_ne_polar (z : ZMod 2) (r : V m × V m) (hr : r ≠ 0) : secPt z r ≠ polar m := by
  intro h
  apply hr
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have h1 := congrFun (congrArg Prod.fst h) i.succ
    simpa [secPt, polar] using h1
  · have h2 := congrFun (congrArg Prod.snd h) i.succ
    simpa [secPt, polar, Fin.succ_ne_zero] using h2

theorem aux7c_secPt_snd_zero (z : ZMod 2) (r : V m × V m) : (secPt z r).2 0 = z := by
  simp [secPt]

theorem aux7c_secPt_tail (z : ZMod 2) (r : V m × V m) :
    ((Fin.tail (secPt z r).1 : V m), (Fin.tail (secPt z r).2 : V m)) = r := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp [secPt, Fin.tail]
  · simp [secPt, Fin.tail]

theorem liftCarrier_secPt_zero (σI σZ : V m × V m → ℤ) (r : V m × V m) (hr : r ∈ realLabels m) :
    liftCarrier σI σZ (secPt 0 r) = ((σI r : ℤ) : ℝ) := by
  have hr0 : r ≠ 0 := (Finset.mem_filter.1 hr).2.2
  unfold liftCarrier
  rw [ite_eq_right (aux7c_secPt_ne_polar 0 r hr0), ite_eq_left (aux7c_secPt_snd_zero 0 r), aux7c_secPt_tail]

theorem liftCarrier_secPt_one (σI σZ : V m × V m → ℤ) (r : V m × V m) (hr : r ∈ realLabels m) :
    liftCarrier σI σZ (secPt 1 r) = ((σZ r : ℤ) : ℝ) := by
  have hr0 : r ≠ 0 := (Finset.mem_filter.1 hr).2.2
  have h1 : ¬ (secPt 1 r).2 0 = 0 := by
    rw [aux7c_secPt_snd_zero]; exact one_ne_zero
  unfold liftCarrier
  rw [ite_eq_right (aux7c_secPt_ne_polar 1 r hr0), ite_eq_right h1, aux7c_secPt_tail]

/-- Entrywise cast to `ℂ` followed by the reindexing along `splitEquiv`, as an additive map. -/
noncomputable def aux7c_lift (m : ℕ) :
    Matrix (Fin 2 × V m) (Fin 2 × V m) ℤ →+ Matrix (Vec (m + 1)) (Vec (m + 1)) ℂ where
  toFun M := Matrix.reindex (splitEquiv m).symm (splitEquiv m).symm (M.map (Int.cast : ℤ → ℂ))
  map_zero' := by
    ext x y
    simp
  map_add' A B := by
    ext x y
    simp

theorem aux7c_lift_apply (M : Matrix (Fin 2 × V m) (Fin 2 × V m) ℤ) :
    aux7c_lift m M
      = Matrix.reindex (splitEquiv m).symm (splitEquiv m).symm (M.map (Int.cast : ℤ → ℂ)) := rfl

theorem aux7c_lift_smul (k : ℤ) (M : Matrix (Fin 2 × V m) (Fin 2 × V m) ℤ) :
    aux7c_lift m (k • M) = (((k : ℤ) : ℝ) : ℂ) • aux7c_lift m M := by
  ext x y
  simp only [aux7c_lift_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.smul_apply]
  simp

/-- The carrier operator of the library, over the section, is the carrier operator of Part 5. -/
theorem opA_liftCarrier (σI σZ : V m × V m → ℤ) :
    opA (sectionPts m) (liftCarrier σI σZ)
      = Matrix.reindex (splitEquiv m).symm (splitEquiv m).symm
          ((carrierOp 1 σI σZ).map (Int.cast : ℤ → ℂ)) := by
  rw [← aux7c_lift_apply]
  unfold opA carrierOp
  rw [sum_sectionPts, liftCarrier_polar, pauli_polar, ← aux7c_lift_apply, map_add, map_sum,
    aux7c_lift_smul]
  congr 1
  · norm_num
  · refine Finset.sum_congr rfl fun r hr => ?_
    have hq : r.2 ⬝ᵥ r.1 = 0 := (Finset.mem_filter.1 hr).2.1
    rw [liftCarrier_secPt_zero σI σZ r hr, liftCarrier_secPt_one σI σZ r hr,
      pauli_secPt_zero r hq, pauli_secPt_one r hq, ← aux7c_lift_apply, ← aux7c_lift_apply,
      map_add, aux7c_lift_smul, aux7c_lift_smul]

theorem charpoly_opA_liftCarrier (σI σZ : V m × V m → ℤ) :
    (opA (sectionPts m) (liftCarrier σI σZ)).charpoly
      = (carrierOp 1 σI σZ).charpoly.map (Int.castRingHom ℂ) := by
  rw [opA_liftCarrier, Matrix.charpoly_reindex]
  exact Matrix.charpoly_map (carrierOp 1 σI σZ) (Int.castRingHom ℂ)

/-! #### 7d. The completion matrix, and the theorem -/

/-- The trace of `A Q P`, with `A` the carrier operator over a set `S` of points: only the point
`P + Q` contributes. -/
theorem aux7d_trace_opA_mul {N : ℕ} (S : Finset (Pt N)) (f : Pt N → ℝ) (P Q : Pt N) :
    (opA S f * HoggarBound.pauli Q * HoggarBound.pauli P).trace
      = if P + Q ∈ S then ((f (P + Q) : ℝ) : ℂ) * ((2 : ℂ) ^ N * tau (P + Q) Q) else 0 := by
  have hterm : ∀ s ∈ S,
      (((f s : ℝ) : ℂ) • HoggarBound.pauli s * HoggarBound.pauli Q * HoggarBound.pauli P).trace
        = if s = P + Q then ((f (P + Q) : ℝ) : ℂ) * ((2 : ℂ) ^ N * tau (P + Q) Q) else 0 := by
    intro s _
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, trace_pauli_triple, smul_eq_mul]
    by_cases h : s = P + Q
    · subst h
      have h' : P + Q + Q = P := by rw [add_assoc, pt_add_self, add_zero]
      rw [ite_eq_left h', ite_eq_left rfl]
    · have h' : ¬ s + Q = P := by
        intro h2
        apply h
        rw [← h2, add_assoc, pt_add_self, add_zero]
      rw [ite_eq_right h', ite_eq_right h, mul_zero]
  rw [opA, Finset.sum_mul, Finset.sum_mul, Matrix.trace_sum, Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq']

/-- The trace of Part 6, cast to `ℂ`, is the trace of the product of the library matrices. -/
theorem aux7d_trace_cast (σI σZ : V m × V m → ℤ) (p q : V m × V m) :
    ((trace (carrierOp 1 σI σZ * outsideOp q * outsideOp p) : ℤ) : ℂ)
      = (opA (sectionPts m) (liftCarrier σI σZ) * HoggarBound.pauli (outPt q)
          * HoggarBound.pauli (outPt p)).trace := by
  have hmap : ∀ A B : Matrix (Fin 2 × V m) (Fin 2 × V m) ℤ,
      A.map (Int.cast : ℤ → ℂ) * B.map (Int.cast : ℤ → ℂ) = (A * B).map (Int.cast : ℤ → ℂ) := by
    intro A B
    exact (Matrix.map_mul (f := Int.castRingHom ℂ)).symm
  rw [opA_liftCarrier, pauli_outPt, pauli_outPt]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hmap]
  simp only [trace, Matrix.diag_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rw [Int.cast_sum]
  exact (Equiv.sum_comp ((splitEquiv m).symm.symm)
    fun i => (((carrierOp 1 σI σZ * outsideOp q * outsideOp p) i i : ℤ) : ℂ)).symm

/-- The symplectic form is additive in the first argument. -/
theorem aux7d_symp_add_self {N : ℕ} (P Q : Pt N) : symp (P + Q) Q = symp P Q := by
  rw [symp_comm, symp_add_right, symp_self, add_zero, symp_comm]

/-- The entries of the completion matrix of Part 6 are those of the completion matrix defined from the
contexts. -/
theorem completion_eq_context (σI σZ : V m × V m → ℤ) (p q : V m × V m) :
    ((completion 1 σI σZ p q : ℚ) : ℝ)
      = if outPt p ≠ outPt q ∧ symp (outPt p) (outPt q) = 0
          then lineSign (outPt p + outPt q) (outPt q) * liftCarrier σI σZ (outPt p + outPt q)
          else 0 := by
  apply Complex.ofReal_injective
  have h2 : ((2 : ℂ) * 2 ^ m) = 2 ^ (m + 1) := by rw [pow_succ]; ring
  have hL : (((completion 1 σI σZ p q : ℚ) : ℝ) : ℂ)
      = (opA (sectionPts m) (liftCarrier σI σZ) * HoggarBound.pauli (outPt q)
          * HoggarBound.pauli (outPt p)).trace / 2 ^ (m + 1) := by
    rw [completion_apply, ← aux7d_trace_cast, ← h2]
    push_cast
    rfl
  rw [hL, aux7d_trace_opA_mul]
  have hiff := add_mem_sectionPts_iff (outPt_mem_outsidePts p) (outPt_mem_outsidePts q)
  by_cases h : outPt p ≠ outPt q ∧ symp (outPt p) (outPt q) = 0
  · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
    have hs : symp (outPt p + outPt q) (outPt q) = 0 := by
      rw [aux7d_symp_add_self]; exact h.2
    rw [tau_eq_lineSign hs]
    have hne : ((2 : ℂ) ^ (m + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    field_simp
  · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h, zero_div]
    rfl

theorem completionMatrix_liftCarrier (σI σZ : V m × V m → ℤ) :
    completionMatrix m (liftCarrier σI σZ)
      = Matrix.reindex (outEquiv m) (outEquiv m)
          ((completion 1 σI σZ).map (Rat.cast : ℚ → ℝ)) := by
  ext ⟨P, hP⟩ ⟨Q, hQ⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  obtain ⟨p, rfl⟩ := (mem_outsidePts_iff P).1 hP
  obtain ⟨q, rfl⟩ := (mem_outsidePts_iff Q).1 hQ
  have hp : (outEquiv m).symm ⟨outPt p, hP⟩ = p :=
    (Equiv.symm_apply_eq (outEquiv m)).2 (Subtype.ext rfl)
  have hq : (outEquiv m).symm ⟨outPt q, hQ⟩ = q :=
    (Equiv.symm_apply_eq (outEquiv m)).2 (Subtype.ext rfl)
  rw [hp, hq, completion_eq_context]
  rfl

theorem charpoly_completionMatrix_liftCarrier (σI σZ : V m × V m → ℤ) :
    (completionMatrix m (liftCarrier σI σZ)).charpoly
      = (completion 1 σI σZ).charpoly.map (algebraMap ℚ ℝ) := by
  rw [completionMatrix_liftCarrier, Matrix.charpoly_reindex]
  exact Matrix.charpoly_map (completion 1 σI σZ) (algebraMap ℚ ℝ)

/-- **The strict law fails in case C3 for every number of qubits `N = m + 1 ≥ 4`.**

The configuration is the real quadric `realPoints (m + 1)`, the hyperbolic quadric `Q⁺(2N - 1, 2)`; the
polar point is `Z` on one qubit, a point of the quadric; the section consists of the points of the
quadric that commute with it, the outside points of those that do not.  There are two carriers `σ`, `τ`
with values `±1` such that the carrier operators `∑_{s ∈ section} σ(s) P_s` and `∑ τ(s) P_s` have the same
characteristic polynomial, while the two completion matrices have different characteristic
polynomials. -/
theorem c3_strict_law_fails_general (hm : 3 ≤ m) :
    ∃ σ τ : Pt (m + 1) → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionPts m) σ).charpoly = (opA (sectionPts m) τ).charpoly ∧
      (completionMatrix m σ).charpoly ≠ (completionMatrix m τ).charpoly := by
  obtain ⟨σI, σZ, τI, τZ, h1, h2, h3, h4, hA, hL⟩ := c3_strict_law_fails hm
  refine ⟨liftCarrier σI σZ, liftCarrier τI τZ, liftCarrier_eq_one_or σI σZ h1 h2,
    liftCarrier_eq_one_or τI τZ h3 h4, ?_, ?_⟩
  · rw [charpoly_opA_liftCarrier, charpoly_opA_liftCarrier, hA]
  · rw [charpoly_completionMatrix_liftCarrier, charpoly_completionMatrix_liftCarrier]
    intro h
    exact hL (Polynomial.map_injective _ (algebraMap ℚ ℝ).injective h)

end general

/-! #### 7e. Further facts about the configuration

The labels of Parts 3 to 6 are the points of the real quadric on `m` qubits, which gives the sizes; the
sign of a context does not depend on the order of its points, so the completion matrix is symmetric;
and the carrier operator is Hermitian (`opA_isHermitian` in the library).  With these, equal
characteristic polynomials mean equal spectra with multiplicities, for both kinds of matrices. -/

section extras

variable {m : ℕ}

/-- The real non-identity block labels are the points of the real quadric on `m` qubits. -/
theorem realLabels_eq_realPoints : realLabels m = realPoints m := by
  ext p
  unfold realLabels realPoints qform
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨h, h1, h2⟩
    exact ⟨h, h2, h1⟩
  · rintro ⟨h, h1, h2⟩
    exact ⟨h, h2, h1⟩

/-- `|R| = (n - 1)(n + 2) / 2`, in the form `2 |R| + 2 = n² + n`. -/
theorem card_realLabels : 2 * (realLabels m).card + 2 = 4 ^ m + 2 ^ m := by
  rw [realLabels_eq_realPoints]
  exact card_realPoints

/-- The section has `n² + n - 1` points. -/
theorem card_sectionPts_add_one : (sectionPts m).card + 1 = 4 ^ m + 2 ^ m := by
  rw [card_sectionPts]
  have h := card_realLabels (m := m)
  omega

/-- The sign of a context does not depend on the order of its points: for commuting `u`, `v` the
products `P_{u+v} P_v P_u` and `P_{u+v} P_u P_v` are the same multiple of the identity. -/
theorem tau_add_comm {N : ℕ} (u v : Pt N) (h : symp u v = 0) : tau (u + v) v = tau (u + v) u := by
  have e1 : u + v + v = u := by rw [add_assoc, pt_add_self, add_zero]
  have e2 : u + v + u = v := by rw [add_comm u v, add_assoc, pt_add_self, add_zero]
  have h1 : HoggarBound.pauli (u + v) * HoggarBound.pauli v * HoggarBound.pauli u
      = tau (u + v) v • (1 : Matrix (Vec N) (Vec N) ℂ) := by
    rw [pauli_mul, e1, Matrix.smul_mul, HoggarBound.pauli_mul_self]
  have h2 : HoggarBound.pauli (u + v) * HoggarBound.pauli u * HoggarBound.pauli v
      = tau (u + v) u • (1 : Matrix (Vec N) (Vec N) ℂ) := by
    rw [pauli_mul, e2, Matrix.smul_mul, HoggarBound.pauli_mul_self]
  have hc : HoggarBound.pauli v * HoggarBound.pauli u = HoggarBound.pauli u * HoggarBound.pauli v := by
    rw [pauli_comm, h, HoggarBound.eps_zero, one_smul]
  have h3 : tau (u + v) v • (1 : Matrix (Vec N) (Vec N) ℂ) = tau (u + v) u • 1 := by
    rw [← h1, ← h2, Matrix.mul_assoc, hc, ← Matrix.mul_assoc]
  have h4 := congrFun (congrFun h3 0) 0
  simpa using h4

/-- The completion matrix is symmetric. -/
theorem completionMatrix_transpose (σ : Pt (m + 1) → ℝ) :
    (completionMatrix m σ)ᵀ = completionMatrix m σ := by
  ext p q
  simp only [Matrix.transpose_apply, completionMatrix]
  by_cases hpq : p.1 ≠ q.1 ∧ symp p.1 q.1 = 0
  · have hqp : q.1 ≠ p.1 ∧ symp q.1 p.1 = 0 := ⟨fun e => hpq.1 e.symm, by rw [symp_comm]; exact hpq.2⟩
    rw [ite_eq_left hpq, ite_eq_left hqp, add_comm q.1 p.1]
    congr 1
    unfold lineSign
    rw [tau_add_comm p.1 q.1 hpq.2]
  · have hqp : ¬ (q.1 ≠ p.1 ∧ symp q.1 p.1 = 0) := fun hh =>
      hpq ⟨fun e => hh.1 e.symm, by rw [symp_comm]; exact hh.2⟩
    rw [ite_eq_right hpq, ite_eq_right hqp]

end extras

end HoggarBound.C3AllQubits

#print axioms HoggarBound.C3AllQubits.sylvester_apply
#print axioms HoggarBound.C3AllQubits.trace_sylvester_cube
#print axioms HoggarBound.C3AllQubits.carrier_charpoly_eq
#print axioms HoggarBound.C3AllQubits.sylvester_cube_gap
#print axioms HoggarBound.C3AllQubits.c3_family_gap
#print axioms HoggarBound.C3AllQubits.c3_family_cube_traces_ne
#print axioms HoggarBound.C3AllQubits.carrier_charpoly_split
#print axioms HoggarBound.C3AllQubits.sylvester_cube_gap_split
#print axioms HoggarBound.C3AllQubits.eps_smul_pauli
#print axioms HoggarBound.C3AllQubits.sum_xz_hyperplane
#print axioms HoggarBound.C3AllQubits.sum_xz_diagonal
#print axioms HoggarBound.C3AllQubits.familyC_eq
#print axioms HoggarBound.C3AllQubits.pauli_transpose
#print axioms HoggarBound.C3AllQubits.pauli_mul_self
#print axioms HoggarBound.C3AllQubits.famSign_eq_one_or
#print axioms HoggarBound.C3AllQubits.famSignZ_eq_one_or
#print axioms HoggarBound.C3AllQubits.blockC_sigma
#print axioms HoggarBound.C3AllQubits.blockD_sigma
#print axioms HoggarBound.C3AllQubits.blockC_tau
#print axioms HoggarBound.C3AllQubits.blockD_tau
#print axioms HoggarBound.C3AllQubits.c3_family_charpoly
#print axioms HoggarBound.C3AllQubits.c3_family_cube_gap
#print axioms HoggarBound.C3AllQubits.defaultF_card
#print axioms HoggarBound.C3AllQubits.default_separated
#print axioms HoggarBound.C3AllQubits.c3_all_qubits
#print axioms HoggarBound.C3AllQubits.default_differ
#print axioms HoggarBound.C3AllQubits.carrierOp_charpoly
#print axioms HoggarBound.C3AllQubits.c3_all_qubits_carrierOp
#print axioms HoggarBound.C3AllQubits.xz_transpose_sgn
#print axioms HoggarBound.C3AllQubits.pauli_transpose_sgn
#print axioms HoggarBound.C3AllQubits.pauli_mul_transpose
#print axioms HoggarBound.C3AllQubits.outsideOp_transpose
#print axioms HoggarBound.C3AllQubits.outsideOp_mul_self
#print axioms HoggarBound.C3AllQubits.outsideOp_anticomm
#print axioms HoggarBound.C3AllQubits.sum_pauli_mul_pauli
#print axioms HoggarBound.C3AllQubits.completion_apply
#print axioms HoggarBound.C3AllQubits.trace_carrierOp_outside
#print axioms HoggarBound.C3AllQubits.trace_completion_cube
#print axioms HoggarBound.C3AllQubits.c3_all_qubits_completion
#print axioms HoggarBound.C3AllQubits.completion_transpose
#print axioms HoggarBound.C3AllQubits.trace_cube_eq_of_charpoly_eq
#print axioms HoggarBound.C3AllQubits.c3_strict_law_fails
#print axioms HoggarBound.C3AllQubits.polar_mem_sectionPts
#print axioms HoggarBound.C3AllQubits.secPt_mem_sectionPts
#print axioms HoggarBound.C3AllQubits.outPt_mem_outsidePts
#print axioms HoggarBound.C3AllQubits.outPt_injective
#print axioms HoggarBound.C3AllQubits.mem_outsidePts_iff
#print axioms HoggarBound.C3AllQubits.mem_sectionPts_iff
#print axioms HoggarBound.C3AllQubits.sum_sectionPts
#print axioms HoggarBound.C3AllQubits.add_mem_sectionPts
#print axioms HoggarBound.C3AllQubits.add_mem_sectionPts_iff
#print axioms HoggarBound.C3AllQubits.add_mem_outsidePts
#print axioms HoggarBound.C3AllQubits.symp_polar_outside
#print axioms HoggarBound.C3AllQubits.card_outsidePts
#print axioms HoggarBound.C3AllQubits.card_sectionPts
#print axioms HoggarBound.C3AllQubits.pauli_polar
#print axioms HoggarBound.C3AllQubits.pauli_secPt_zero
#print axioms HoggarBound.C3AllQubits.pauli_secPt_one
#print axioms HoggarBound.C3AllQubits.pauli_outPt
#print axioms HoggarBound.C3AllQubits.liftCarrier_eq_one_or
#print axioms HoggarBound.C3AllQubits.liftCarrier_polar
#print axioms HoggarBound.C3AllQubits.liftCarrier_secPt_zero
#print axioms HoggarBound.C3AllQubits.liftCarrier_secPt_one
#print axioms HoggarBound.C3AllQubits.opA_liftCarrier
#print axioms HoggarBound.C3AllQubits.charpoly_opA_liftCarrier
#print axioms HoggarBound.C3AllQubits.completion_eq_context
#print axioms HoggarBound.C3AllQubits.completionMatrix_liftCarrier
#print axioms HoggarBound.C3AllQubits.charpoly_completionMatrix_liftCarrier
#print axioms HoggarBound.C3AllQubits.c3_strict_law_fails_general
#print axioms HoggarBound.C3AllQubits.realLabels_eq_realPoints
#print axioms HoggarBound.C3AllQubits.card_realLabels
#print axioms HoggarBound.C3AllQubits.card_sectionPts_add_one
#print axioms HoggarBound.C3AllQubits.tau_add_comm
#print axioms HoggarBound.C3AllQubits.completionMatrix_transpose

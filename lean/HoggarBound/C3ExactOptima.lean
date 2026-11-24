/-
Exact Global Binary Optima for the Four-Qubit C3 Cospectral Pair (Corollary 16, v1.8.0)

Closes BOTH remaining binary QUBO completion gaps to exact global binary optimality inside
Lean 4's kernel (no `sorry`, no `admit`, no `native_decide`, strictly standard axioms):

  * `corollary16_sigmaA_exact_lower` : ∀ y ∈ {±1}^64, 368 ≤ c3ViolatedOutsideContexts signA y
  * `corollary16_sigmaB_exact_lower` : ∀ y ∈ {±1}^64, 344 ≤ c3ViolatedOutsideContexts signB y
  * `corollary16_exact_binary_optima` :
      min_{y ∈ {±1}^64} F(signA, y) = 368  ∧  min_{y ∈ {±1}^64} F(signB, y) = 344
      (exact global binary separation = 24, closing [347, 368] and [330, 344] to zero width).

Proof architecture (pure integer MET-SDP dual + Gershgorin-shifted integer Cholesky):
  1. For every frustrated triangle cut `c = (i, j, k, s1, s2, s3, w)` with `s1, s2, s3 ∈ {±1}`,
     `s1 * s2 * s3 = -1`, and `w > 0`, every binary vector `y ∈ {±1}^64` satisfies
     `2 * w * (s1 * y i * y j + s2 * y j * y k + s3 * y i * y k) ≤ 2 * w`.
  2. Folding all cuts into the base integer matrix `M₀ = μ·I - diag(d) - Q·Λ` produces a
     symmetric 64×64 integer matrix `M_cert` whose quadratic form satisfies
       `yᵀ M_cert y ≤ 64·μ - ∑ d_i - Q·(yᵀ Λ y) + 2·∑ w_t`.
  3. On the other hand, `K²·M_cert = L·Lᵀ + E` where `L` is lower-triangular integer and `E`
     is strictly diagonally dominant (`∑_{j ≠ i} |E_{ij}| < E_{ii}` for all `i : Fin 64`),
     proved purely in Lean's kernel by linear-pass `decide +kernel`, which implies
     `0 < yᵀ M_cert y` for every nonzero `y` (by `vᵀ (L Lᵀ) v = ∑_k (∑_i L_{ik} v_i)² ≥ 0`
     and AM-GM `2|v_i v_j| ≤ v_i² + v_j²` on `E`).
  4. Combining (2) and (3) with `∑ d_i = 0` and `64·μ + 2·∑ w_t < 4·Q·(560 - (target - 1))`
     yields `target ≤ c3ViolatedOutsideContexts sign y`.
-/

import HoggarBound.AuditUpgrades
import HoggarBound.C3ExactOptimaData

open Finset BigOperators

namespace HoggarBound.C3ExactOptima

open HoggarBound.C3
open HoggarBound.ConjectureE
open HoggarBound.AuditUpgrades
open HoggarBound.C3ExactOptimaData

/-! ### Part 1. General Matrix Quadratic Form and Strictly Diagonally Dominant Gram Positivity -/

/-- Quadratic form `∑ i j, y i * M_{ij} * y j` of a 64×64 integer matrix represented as `List (List ℤ)`. -/
def matQuadForm (M : List (List ℤ)) (y : Fin 64 → ℝ) : ℝ :=
  ∑ i : Fin 64, ∑ j : Fin 64, y i * (((M.getD i.val []).getD j.val 0 : ℤ) : ℝ) * y j

/-- Well-formedness of a 64×64 matrix represented as `List (List ℤ)`. -/
def Mat64WF (M : List (List ℤ)) : Prop :=
  M.length = 64 ∧ ∀ r ∈ M, r.length = 64

/-- Add `v` to element `idx` of a list `xs`. -/
def listAddAt (idx : ℕ) (v : ℤ) : List ℤ → List ℤ
  | [] => []
  | x :: xs =>
    match idx with
    | 0 => (x + v) :: xs
    | n + 1 => x :: listAddAt n v xs

lemma listAddAt_length (idx : ℕ) (v : ℤ) : ∀ xs : List ℤ, (listAddAt idx v xs).length = xs.length
  | [] => by simp [listAddAt]
  | _ :: xs => by
    cases idx with
    | zero => simp [listAddAt]
    | succ n => simp [listAddAt, listAddAt_length n v xs]

lemma listAddAt_getD (idx j : ℕ) (v : ℤ) :
    ∀ xs : List ℤ, idx < xs.length →
      (listAddAt idx v xs).getD j 0 = xs.getD j 0 + (if j = idx then v else 0)
  | [], h => by simp at h
  | x :: xs, h => by
    cases idx with
    | zero =>
      cases j with
      | zero => simp [listAddAt]
      | succ k => simp [listAddAt]
    | succ n =>
      cases j with
      | zero => simp [listAddAt]
      | succ k =>
        have hlt : n < xs.length := Nat.lt_of_succ_lt_succ h
        simpa [listAddAt] using listAddAt_getD n k v xs hlt

/-- Add `v` to entry `(r, c)` of a `List (List ℤ)`. -/
def matAddEntry (r c : ℕ) (v : ℤ) : List (List ℤ) → List (List ℤ)
  | [] => []
  | row :: rows =>
    match r with
    | 0 => listAddAt c v row :: rows
    | n + 1 => row :: matAddEntry n c v rows

lemma matAddEntry_wf (r c : ℕ) (v : ℤ) {M : List (List ℤ)} (hM : Mat64WF M) :
    Mat64WF (matAddEntry r c v M) := by
  rcases hM with ⟨hlen, hrows⟩
  suffices ∀ (M' : List (List ℤ)) (r' : ℕ),
      (∀ row ∈ M', row.length = 64) →
      (matAddEntry r' c v M').length = M'.length ∧
      ∀ row ∈ matAddEntry r' c v M', row.length = 64 by
    have h := this M r hrows
    exact ⟨h.1.trans hlen, h.2⟩
  intro M'
  induction M' with
  | nil => intro r' _; simp [matAddEntry]
  | cons row rows ih =>
    intro r' h
    have hrow : row.length = 64 := h row (List.mem_cons_self ..)
    have hrest : ∀ rw ∈ rows, rw.length = 64 := fun rw hrw => h rw (List.mem_cons_of_mem _ hrw)
    cases r' with
    | zero =>
      refine ⟨rfl, ?_⟩
      intro rw hrw
      rcases List.mem_cons.mp hrw with rfl | hrw'
      · rw [listAddAt_length, hrow]
      · exact hrest rw hrw'
    | succ n =>
      have ihn := ih n hrest
      refine ⟨by simp [matAddEntry, ihn.1], ?_⟩
      intro rw hrw
      rcases List.mem_cons.mp hrw with rfl | hrw'
      · exact hrow
      · exact ihn.2 rw hrw'

lemma matAddEntry_getD (r c i j : ℕ) (v : ℤ) :
    ∀ (M : List (List ℤ)), r < M.length → (∀ row ∈ M, c < row.length) →
      ((matAddEntry r c v M).getD i []).getD j 0 =
        (M.getD i []).getD j 0 + (if i = r ∧ j = c then v else 0)
  | [], hr, _ => by simp at hr
  | row :: rows, hr, hc => by
    have hcr : c < row.length := hc row (List.mem_cons_self ..)
    have hcrest : ∀ rw ∈ rows, c < rw.length := fun rw hrw => hc rw (List.mem_cons_of_mem _ hrw)
    cases r with
    | zero =>
      cases i with
      | zero =>
        simp only [matAddEntry, List.getD_cons_zero, true_and]
        exact listAddAt_getD c j v row hcr
      | succ k =>
        simp [matAddEntry]
    | succ n =>
      cases i with
      | zero =>
        simp [matAddEntry]
      | succ k =>
        have hlt : n < rows.length := Nat.lt_of_succ_lt_succ hr
        simpa [matAddEntry] using matAddEntry_getD n c k j v rows hlt hcrest

lemma matQuadForm_addEntry {M : List (List ℤ)} (hM : Mat64WF M)
    (r c : Fin 64) (v : ℤ) (y : Fin 64 → ℝ) :
    matQuadForm (matAddEntry r.val c.val v M) y =
      matQuadForm M y + (v : ℝ) * y r * y c := by
  have hr : r.val < M.length := by rw [hM.1]; exact r.isLt
  have hc : ∀ row ∈ M, c.val < row.length := fun row hrow => by rw [hM.2 row hrow]; exact c.isLt
  unfold matQuadForm
  have hterm : ∀ i j : Fin 64,
      y i * (((((matAddEntry r.val c.val v M).getD i.val []).getD j.val 0 : ℤ) : ℝ)) * y j
      = y i * (((M.getD i.val []).getD j.val 0 : ℤ) : ℝ) * y j
        + (if i = r ∧ j = c then (v : ℝ) * y r * y c else 0) := by
    intro i j
    rw [matAddEntry_getD r.val c.val i.val j.val v M hr hc]
    by_cases h : i = r ∧ j = c
    · rcases h with ⟨rfl, rfl⟩
      simp only [and_self, ↓reduceIte, Int.cast_add]
      ring
    · have hval : ¬(i.val = r.val ∧ j.val = c.val) := fun ⟨hi, hj⟩ => h ⟨Fin.ext hi, Fin.ext hj⟩
      simp only [h, hval, ↓reduceIte, add_zero]
  simp_rw [hterm, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single r]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro j _ hjc; simp [hjc]
    · intro hc'; exact absurd (mem_univ c) hc'
  · intro i _ hir
    exact Finset.sum_eq_zero fun j _ => by simp [hir]
  · intro hr'; exact absurd (mem_univ r) hr'

lemma matAddEntry_symm {M : List (List ℤ)} (hM : Mat64WF M)
    (hsym : ∀ i j : Fin 64, (M.getD i.val []).getD j.val 0 = (M.getD j.val []).getD i.val 0)
    (r c : Fin 64) (v : ℤ) :
    ∀ i j : Fin 64,
      ((matAddEntry c.val r.val v (matAddEntry r.val c.val v M)).getD i.val []).getD j.val 0 =
      ((matAddEntry c.val r.val v (matAddEntry r.val c.val v M)).getD j.val []).getD i.val 0 := by
  have hM1 : Mat64WF (matAddEntry r.val c.val v M) := matAddEntry_wf r.val c.val v hM
  have hr1 : r.val < M.length := by rw [hM.1]; exact r.isLt
  have hc1 : ∀ row ∈ M, c.val < row.length := fun row h => by rw [hM.2 row h]; exact c.isLt
  have hc2 : c.val < (matAddEntry r.val c.val v M).length := by rw [hM1.1]; exact c.isLt
  have hr2 : ∀ row ∈ matAddEntry r.val c.val v M, r.val < row.length :=
    fun row h => by rw [hM1.2 row h]; exact r.isLt
  intro i j
  rw [matAddEntry_getD c.val r.val i.val j.val v _ hc2 hr2,
      matAddEntry_getD r.val c.val i.val j.val v M hr1 hc1,
      matAddEntry_getD c.val r.val j.val i.val v _ hc2 hr2,
      matAddEntry_getD r.val c.val j.val i.val v M hr1 hc1,
      hsym i j]
  have h1 : (i.val = r.val ∧ j.val = c.val) ↔ (j.val = c.val ∧ i.val = r.val) := and_comm
  have h2 : (i.val = c.val ∧ j.val = r.val) ↔ (j.val = r.val ∧ i.val = c.val) := and_comm
  simp only [h1, h2]
  ring

/-! ### Part 2. Triangle Cut Inequality and Fold Accumulator -/

/-- Valid frustrated triangle cut predicate. -/
def validTriCut (c : TriCut) : Bool :=
  c.i < 64 && c.j < 64 && c.k < 64 &&
  (c.s1 == 1 || c.s1 == -1) &&
  (c.s2 == 1 || c.s2 == -1) &&
  (c.s3 == 1 || c.s3 == -1) &&
  (c.s1 * c.s2 * c.s3 == -1) &&
  (0 < c.w)

/-- Add a symmetric pair `(r, c)` and `(c, r)` with value `v`. -/
def matAddSym (r c : ℕ) (v : ℤ) (M : List (List ℤ)) : List (List ℤ) :=
  matAddEntry c r v (matAddEntry r c v M)

/-- Add a single triangle cut `c` (`w * C_c`) to matrix `M`. -/
def addTriCut (M : List (List ℤ)) (c : TriCut) : List (List ℤ) :=
  matAddSym c.i c.k (c.w * c.s3)
    (matAddSym c.j c.k (c.w * c.s2)
      (matAddSym c.i c.j (c.w * c.s1) M))

/-- Key binary frustrated-triangle inequality:
for `a, b, c ∈ {±1}` and `s1, s2, s3 ∈ {±1}` with `s1 * s2 * s3 = -1`,
`s1 * a * b + s2 * b * c + s3 * a * c ≤ 1`. -/
lemma frustrated_triangle_le_one {a b c s1 s2 s3 : ℝ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1)
    (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1) (hs3 : s3 = 1 ∨ s3 = -1)
    (hodd : s1 * s2 * s3 = -1) :
    s1 * a * b + s2 * b * c + s3 * a * c ≤ 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl <;> rcases hs3 with rfl | rfl <;>
    linarith [hodd]

lemma matAddSym_wf (r c : ℕ) (v : ℤ) {M : List (List ℤ)} (hM : Mat64WF M) :
    Mat64WF (matAddSym r c v M) :=
  matAddEntry_wf c r v (matAddEntry_wf r c v hM)

lemma matAddSym_quadForm {M : List (List ℤ)} (hM : Mat64WF M)
    (r c : Fin 64) (v : ℤ) (y : Fin 64 → ℝ) :
    matQuadForm (matAddSym r.val c.val v M) y =
      matQuadForm M y + 2 * (v : ℝ) * y r * y c := by
  unfold matAddSym
  rw [matQuadForm_addEntry (matAddEntry_wf r.val c.val v hM) c r v y,
      matQuadForm_addEntry hM r c v y]
  ring

lemma addTriCut_spec {M : List (List ℤ)} (hM : Mat64WF M)
    (hsym : ∀ i j : Fin 64, (M.getD i.val []).getD j.val 0 = (M.getD j.val []).getD i.val 0)
    (c : TriCut) (hc : validTriCut c = true)
    (y : Fin 64 → ℝ) (hy : ∀ i : Fin 64, y i = 1 ∨ y i = -1) :
    Mat64WF (addTriCut M c) ∧
    (∀ i j : Fin 64,
      ((addTriCut M c).getD i.val []).getD j.val 0 =
      ((addTriCut M c).getD j.val []).getD i.val 0) ∧
    matQuadForm (addTriCut M c) y ≤ matQuadForm M y + 2 * (c.w : ℝ) := by
  simp only [validTriCut, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, hk⟩, hs1⟩, hs2⟩, hs3⟩, hodd⟩, hw⟩
  let fi : Fin 64 := ⟨c.i, hi⟩
  let fj : Fin 64 := ⟨c.j, hj⟩
  let fk : Fin 64 := ⟨c.k, hk⟩
  have hM1 := matAddSym_wf c.i c.j (c.w * c.s1) hM
  have hM2 := matAddSym_wf c.j c.k (c.w * c.s2) hM1
  have hM3 := matAddSym_wf c.i c.k (c.w * c.s3) hM2
  have hsym1 := matAddEntry_symm hM hsym fi fj (c.w * c.s1)
  have hsym2 := matAddEntry_symm hM1 hsym1 fj fk (c.w * c.s2)
  have hsym3 := matAddEntry_symm hM2 hsym2 fi fk (c.w * c.s3)
  refine ⟨hM3, hsym3, ?_⟩
  unfold addTriCut
  rw [matAddSym_quadForm hM2 fi fk (c.w * c.s3) y,
      matAddSym_quadForm hM1 fj fk (c.w * c.s2) y,
      matAddSym_quadForm hM fi fj (c.w * c.s1) y]
  have hs1R : (c.s1 : ℝ) = 1 ∨ (c.s1 : ℝ) = -1 := by
    rcases hs1 with h | h <;> simp [h]
  have hs2R : (c.s2 : ℝ) = 1 ∨ (c.s2 : ℝ) = -1 := by
    rcases hs2 with h | h <;> simp [h]
  have hs3R : (c.s3 : ℝ) = 1 ∨ (c.s3 : ℝ) = -1 := by
    rcases hs3 with h | h <;> simp [h]
  have hoddR : (c.s1 : ℝ) * (c.s2 : ℝ) * (c.s3 : ℝ) = -1 := by exact_mod_cast hodd
  have hwR : (0 : ℝ) < (c.w : ℝ) := by exact_mod_cast hw
  have htri := frustrated_triangle_le_one (hy fi) (hy fj) (hy fk) hs1R hs2R hs3R hoddR
  have hrew :
      matQuadForm M y + 2 * ((c.w * c.s1 : ℤ) : ℝ) * y fi * y fj
        + 2 * ((c.w * c.s2 : ℤ) : ℝ) * y fj * y fk
        + 2 * ((c.w * c.s3 : ℤ) : ℝ) * y fi * y fk
      = matQuadForm M y + 2 * (c.w : ℝ) *
          ((c.s1 : ℝ) * y fi * y fj + (c.s2 : ℝ) * y fj * y fk + (c.s3 : ℝ) * y fi * y fk) := by
    push_cast; ring
  rw [hrew]
  nlinarith

/-- Sum of integer weights across a list of frustrated-triangle cuts. -/
def sumWeights (cuts : List TriCut) : ℤ :=
  cuts.foldl (fun acc c => acc + c.w) 0

lemma sumWeights_cons (c : TriCut) (cs : List TriCut) :
    sumWeights (c :: cs) = c.w + sumWeights cs := by
  unfold sumWeights
  suffices ∀ (acc : ℤ) (l : List TriCut),
      l.foldl (fun a x => a + x.w) acc = acc + l.foldl (fun a x => a + x.w) 0 by
    simpa [List.foldl] using this c.w cs
  intro acc l
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (acc + x.w), ih (0 + x.w)]
    ring

lemma foldl_addTriCut_spec (cuts : List TriCut) (hcuts : cuts.all validTriCut = true)
    (M : List (List ℤ)) (hM : Mat64WF M)
    (hsym : ∀ i j : Fin 64, (M.getD i.val []).getD j.val 0 = (M.getD j.val []).getD i.val 0)
    (y : Fin 64 → ℝ) (hy : ∀ i : Fin 64, y i = 1 ∨ y i = -1) :
    Mat64WF (cuts.foldl addTriCut M) ∧
    (∀ i j : Fin 64,
      ((cuts.foldl addTriCut M).getD i.val []).getD j.val 0 =
      ((cuts.foldl addTriCut M).getD j.val []).getD i.val 0) ∧
    matQuadForm (cuts.foldl addTriCut M) y ≤ matQuadForm M y + 2 * (sumWeights cuts : ℝ) := by
  induction cuts generalizing M with
  | nil =>
    refine ⟨hM, hsym, ?_⟩
    simp [sumWeights]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hcuts
    obtain ⟨hM1, hsym1, hq1⟩ := addTriCut_spec hM hsym c hcuts.1 y hy
    obtain ⟨hMf, hsymf, hqf⟩ := ih hcuts.2 (addTriCut M c) hM1 hsym1
    refine ⟨hMf, hsymf, ?_⟩
    rw [List.foldl_cons, sumWeights_cons]
    push_cast
    linarith

/-! ### Part 3. Linear-Pass Lower-Triangular Cholesky + Diagonal Dominance Positivity -/

/-- Linear-pass dot product of two integer lists (zero-padded beyond the shorter list). -/
def rowDot : List ℤ → List ℤ → ℤ
  | x :: xs, y :: ys => x * y + rowDot xs ys
  | _, _ => 0

lemma rowDot_eq_sum_range : ∀ (n : ℕ) (a b : List ℤ), a.length ≤ n → b.length ≤ n →
    rowDot a b = ∑ k : Fin n, a.getD k.val 0 * b.getD k.val 0
  | 0, a, b, ha, hb => by
    have ha0 : a = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp ha)
    have hb0 : b = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hb)
    subst ha0; subst hb0; simp [rowDot]
  | n + 1, [], b, _, _ => by
    simp [rowDot]
  | n + 1, a, [], _, _ => by
    simp [rowDot]
  | n + 1, x :: xs, y :: ys, ha, hb => by
    have hxs : xs.length ≤ n := Nat.le_of_succ_le_succ ha
    have hys : ys.length ≤ n := Nat.le_of_succ_le_succ hb
    rw [rowDot, Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
    rw [rowDot_eq_sum_range n xs ys hxs hys]

/-- Linear-pass strict diagonal-dominance checker for row `i` of `E = K² M - L Lᵀ`. -/
def checkRowDomAux (K2 : ℤ) (li : List ℤ) (i : ℕ) :
    ℕ → List ℤ → List (List ℤ) → ℤ → ℤ → Bool
  | j, m :: mrest, lj :: lrest, diag, off =>
    let e := K2 * m - rowDot li lj
    if j == i then checkRowDomAux K2 li i (j + 1) mrest lrest e off
    else checkRowDomAux K2 li i (j + 1) mrest lrest diag (off + (e.natAbs : ℤ))
  | _, [], [], diag, off => decide (off < diag)
  | _, _, _, _, _ => false

/-- Recursive row-wise Gershgorin diagonal-dominance checker for `K² M - L Lᵀ`. -/
def checkMatDomAux (K2 : ℤ) (Lrows : List (List ℤ)) :
    ℕ → List (List ℤ) → List (List ℤ) → Bool
  | i, mRow :: mRest, li :: lRest =>
    checkRowDomAux K2 li i 0 mRow Lrows 0 0 &&
    checkMatDomAux K2 Lrows (i + 1) mRest lRest
  | _, [], [] => true
  | _, _, _ => false

/-- Boolean certificate check asserting `K² M - L Lᵀ` is strictly diagonally dominant. -/
def checkGramDiagDom (K : ℤ) (Mrows Lrows : List (List ℤ)) : Bool :=
  (Lrows.length == 64) &&
  Lrows.all (fun r => r.length ≤ 64) &&
  checkMatDomAux (K * K) Lrows 0 Mrows Lrows

lemma checkRowDomAux_spec (K2 : ℤ) (li : List ℤ) (i : ℕ) :
    ∀ (j : ℕ) (ms : List ℤ) (ls : List (List ℤ)) (diag off : ℤ),
      ms.length = ls.length →
      checkRowDomAux K2 li i j ms ls diag off = true →
      off + (∑ k : Fin ms.length,
        if j + k.val = i then (0 : ℤ)
        else ((K2 * ms.getD k.val 0 - rowDot li (ls.getD k.val [])).natAbs : ℤ))
      < (if i ≥ j ∧ i < j + ms.length
         then K2 * ms.getD (i - j) 0 - rowDot li (ls.getD (i - j) [])
         else diag) := by
  intro j ms
  induction ms generalizing j with
  | nil =>
    intro ls diag off hlen hchk
    cases ls with
    | nil =>
      simp only [checkRowDomAux, decide_eq_true_eq] at hchk
      simp only [List.length_nil, add_zero, Fin.sum_univ_zero, add_zero]
      have hfalse : ¬(i ≥ j ∧ i < j) := by omega
      rw [ite_eq_right hfalse]
      exact hchk
    | cons _ _ => simp at hlen
  | cons m mrest ih =>
    intro ls diag off hlen hchk
    cases ls with
    | nil => simp at hlen
    | cons lj lrest =>
      have hlen' : mrest.length = lrest.length := Nat.succ.inj hlen
      simp only [checkRowDomAux] at hchk
      by_cases hji : j = i
      · subst hji
        simp only [beq_self_eq_true, ↓reduceIte] at hchk
        have hrec := ih (j + 1) lrest (K2 * m - rowDot li lj) off hlen' hchk
        have hnot : ¬(j ≥ j + 1 ∧ j < j + 1 + mrest.length) := by omega
        simp only [hnot, ↓reduceIte] at hrec
        have hlt : j ≥ j ∧ j < j + (m :: mrest).length := by simp
        rw [ite_eq_left hlt]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have hsum_split :
            (∑ k : Fin (m :: mrest).length,
              if j + k.val = j then (0 : ℤ)
              else ((K2 * (m :: mrest).getD k.val 0 - rowDot li ((lj :: lrest).getD k.val [])).natAbs : ℤ))
            = ∑ k : Fin mrest.length,
              if j + 1 + k.val = j then (0 : ℤ)
              else ((K2 * mrest.getD k.val 0 - rowDot li (lrest.getD k.val [])).natAbs : ℤ) := by
          let e : Fin (mrest.length + 1) ≃ Fin (m :: mrest).length := finCongr rfl
          rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fin.sum_univ_succ]
          simp only [Fin.val_zero, add_zero, ↓reduceIte, zero_add,
            Fin.val_succ, List.getD_cons_succ]
          refine Finset.sum_congr rfl fun k _ => ?_
          have heq : (j + (k.val + 1) = j) ↔ (j + 1 + k.val = j) := by omega
          simp only [heq]
        rw [hsum_split]
        exact hrec
      · have hbeq : (j == i) = false := beq_false_of_ne hji
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hchk
        have hrec := ih (j + 1) lrest diag (off + ((K2 * m - rowDot li lj).natAbs : ℤ)) hlen' hchk
        have hsum_split :
            off + (∑ k : Fin (m :: mrest).length,
              if j + k.val = i then (0 : ℤ)
              else ((K2 * (m :: mrest).getD k.val 0 - rowDot li ((lj :: lrest).getD k.val [])).natAbs : ℤ))
            = (off + ((K2 * m - rowDot li lj).natAbs : ℤ)) +
              ∑ k : Fin mrest.length,
                if j + 1 + k.val = i then (0 : ℤ)
                else ((K2 * mrest.getD k.val 0 - rowDot li (lrest.getD k.val [])).natAbs : ℤ) := by
          let e : Fin (mrest.length + 1) ≃ Fin (m :: mrest).length := finCongr rfl
          rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fin.sum_univ_succ]
          simp only [Fin.val_zero, add_zero, hji, ↓reduceIte,
            List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
          rw [add_assoc]
          congr 2
          refine Finset.sum_congr rfl fun k _ => ?_
          have heq : (j + (k.val + 1) = i) ↔ (j + 1 + k.val = i) := by omega
          simp only [heq]
        rw [hsum_split]
        have hcond : (i ≥ j ∧ i < j + (m :: mrest).length) ↔
            (i ≥ j + 1 ∧ i < j + 1 + mrest.length) := by
          simp only [List.length_cons]; omega
        by_cases hc : i ≥ j + 1 ∧ i < j + 1 + mrest.length
        · have hc' : i ≥ j ∧ i < j + (m :: mrest).length := hcond.mpr hc
          rw [ite_eq_left hc] at hrec
          rw [ite_eq_left hc']
          have hsub : i - j = (i - (j + 1)) + 1 := by omega
          rw [hsub, List.getD_cons_succ, List.getD_cons_succ]
          exact hrec
        · have hc' : ¬(i ≥ j ∧ i < j + (m :: mrest).length) := mt hcond.mp hc
          rw [ite_eq_right hc] at hrec
          rw [ite_eq_right hc']
          exact hrec

lemma checkMatDomAux_spec (K2 : ℤ) (Lrows : List (List ℤ)) :
    ∀ (i : ℕ) (ms ls : List (List ℤ)),
      ms.length = ls.length →
      checkMatDomAux K2 Lrows i ms ls = true →
      ∀ k : Fin ms.length,
        checkRowDomAux K2 (ls.getD k.val []) (i + k.val) 0 (ms.getD k.val []) Lrows 0 0 = true := by
  intro i ms
  induction ms generalizing i with
  | nil =>
    intro ls _ _ k
    exact Fin.elim0 k
  | cons mRow mRest ih =>
    intro ls hlen hchk
    cases ls with
    | nil => simp at hlen
    | cons li lRest =>
      have hlen' : mRest.length = lRest.length := Nat.succ.inj hlen
      simp only [checkMatDomAux, Bool.and_eq_true] at hchk
      intro k
      refine Fin.cases ?_ ?_ k
      · simpa using hchk.1
      · intro k'
        have hrec := ih (i + 1) lRest hlen' hchk.2 k'
        have hi : i + 1 + k'.val = i + (k'.val + 1) := by omega
        rw [hi] at hrec
        simpa using hrec

/-- **Gershgorin-shifted Gram positivity theorem:**
If `Mrows` is a symmetric 64×64 integer matrix and `checkGramDiagDom K Mrows Lrows = true`
with `K > 0`, then `0 < matQuadForm Mrows v` for every nonzero `v : Fin 64 → ℝ`. -/
theorem matQuadForm_pos_of_gram_diagDom
    {K : ℤ} (hK : 0 < K)
    {Mrows Lrows : List (List ℤ)}
    (hM : Mat64WF Mrows)
    (hsym : ∀ i j : Fin 64,
      (Mrows.getD i.val []).getD j.val 0 = (Mrows.getD j.val []).getD i.val 0)
    (hchk : checkGramDiagDom K Mrows Lrows = true)
    (v : Fin 64 → ℝ) (hv : ∃ i : Fin 64, v i ≠ 0) :
    0 < matQuadForm Mrows v := by
  simp only [checkGramDiagDom, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨hLlen, hLrow⟩, hmat⟩
  let M : Fin 64 → Fin 64 → ℤ := fun i j => (Mrows.getD i.val []).getD j.val 0
  let L : Fin 64 → Fin 64 → ℤ := fun i k => (Lrows.getD i.val []).getD k.val 0
  let E : Fin 64 → Fin 64 → ℤ := fun i j => K * K * M i j - ∑ k : Fin 64, L i k * L j k
  -- Step 1: Extract strict diagonal dominance of `E` from `hmat`
  have hE_dom : ∀ i : Fin 64,
      (∑ j : Fin 64, if j = i then (0 : ℤ) else ((E i j).natAbs : ℤ)) < E i i := by
    intro i
    have hML : Mrows.length = Lrows.length := by rw [hM.1, hLlen]
    have hrowchk := checkMatDomAux_spec (K * K) Lrows 0 Mrows Lrows hML hmat
      ⟨i.val, by rw [hM.1]; exact i.isLt⟩
    simp only [zero_add] at hrowchk
    have hMrow_len : (Mrows.getD i.val []).length = 64 := by
      have hmem : Mrows.getD i.val [] ∈ Mrows := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hM.1]; exact i.isLt)]
        exact List.getElem_mem _
      exact hM.2 _ hmem
    have hdom_raw := checkRowDomAux_spec (K * K) (Lrows.getD i.val []) i.val 0
      (Mrows.getD i.val []) Lrows 0 0 (by rw [hMrow_len, hLlen]) hrowchk
    have hi_cond : i.val ≥ 0 ∧ i.val < 0 + (Mrows.getD i.val []).length := by
      rw [hMrow_len]; exact ⟨Nat.zero_le _, i.isLt⟩
    rw [ite_eq_left hi_cond] at hdom_raw
    simp only [zero_add, Nat.sub_zero] at hdom_raw
    have hLlen_all : ∀ r : Fin 64, (Lrows.getD r.val []).length ≤ 64 := by
      intro r
      have hmem : Lrows.getD r.val [] ∈ Lrows := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hLlen]; exact r.isLt)]
        exact List.getElem_mem _
      exact hLrow _ hmem
    have hdot : ∀ j : Fin 64, rowDot (Lrows.getD i.val []) (Lrows.getD j.val []) =
        ∑ k : Fin 64, L i k * L j k := fun j =>
      rowDot_eq_sum_range 64 (Lrows.getD i.val []) (Lrows.getD j.val [])
        (hLlen_all i) (hLlen_all j)
    let eFin : Fin (Mrows.getD i.val []).length ≃ Fin 64 := finCongr hMrow_len
    have hsum_eq :
        (∑ k : Fin (Mrows.getD i.val []).length,
          if k.val = i.val then (0 : ℤ)
          else ((K * K * (Mrows.getD i.val []).getD k.val 0
                 - rowDot (Lrows.getD i.val []) (Lrows.getD k.val [])).natAbs : ℤ))
        = ∑ j : Fin 64, if j = i then (0 : ℤ) else ((E i j).natAbs : ℤ) := by
      refine Fintype.sum_equiv eFin _ _ fun k => ?_
      have hv_eq : (eFin k).val = k.val := rfl
      have hji : (k.val = i.val) ↔ (eFin k = i) := by
        constructor
        · intro h; exact Fin.ext h
        · intro h; exact congrArg Fin.val h
      simp only [hji]
      by_cases h : eFin k = i
      · simp [h]
      · simp only [h, ↓reduceIte, E, M]
        rw [← hdot (eFin k), hv_eq]
    rw [hsum_eq, hdot i] at hdom_raw
    exact hdom_raw
  -- Step 2: Symmetry of E
  have hE_sym : ∀ i j : Fin 64, E i j = E j i := by
    intro i j
    simp only [E, M]
    rw [hsym i j]
    congr 1
    refine Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- Step 3: K² * matQuadForm Mrows v = ∑ k, (∑ i, L i k * v i)² + ∑ i j, v i * E i j * v j
  have hdecomp :
      ((K : ℝ) ^ 2) * matQuadForm Mrows v =
        (∑ k : Fin 64, (∑ i : Fin 64, (L i k : ℝ) * v i) ^ 2) +
        (∑ i : Fin 64, ∑ j : Fin 64, v i * (E i j : ℝ) * v j) := by
    have hgram : (∑ k : Fin 64, (∑ i : Fin 64, (L i k : ℝ) * v i) ^ 2) =
        ∑ i : Fin 64, ∑ j : Fin 64, v i * (∑ k : Fin 64, (L i k : ℝ) * (L j k : ℝ)) * v j := by
      have h1 : ∀ k : Fin 64, (∑ i : Fin 64, (L i k : ℝ) * v i) ^ 2 =
          ∑ i : Fin 64, ∑ j : Fin 64, v i * ((L i k : ℝ) * (L j k : ℝ)) * v j := by
        intro k
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hgram, ← Finset.sum_add_distrib]
    unfold matQuadForm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [E, M, Int.cast_sub, Int.cast_mul, Int.cast_sum]
    ring
  -- Step 4: Show 0 < ∑ i j, v i * E i j * v j via AM-GM and strict diagonal dominance
  have hE_pos : 0 < ∑ i : Fin 64, ∑ j : Fin 64, v i * (E i j : ℝ) * v j := by
    have hpair : ∀ i j : Fin 64,
        (if j = i then (0 : ℝ) else -|(E i j : ℝ)| * ((v i ^ 2 + v j ^ 2) / 2))
        ≤ (if j = i then (0 : ℝ) else v i * (E i j : ℝ) * v j) := by
      intro i j
      by_cases h : j = i
      · simp [h]
      · simp only [h, ↓reduceIte]
        have h1 : -( |(E i j : ℝ)| * |v i * v j| ) ≤ v i * (E i j : ℝ) * v j := by
          have hrew : v i * (E i j : ℝ) * v j = (E i j : ℝ) * (v i * v j) := by ring
          rw [hrew, ← abs_mul]
          exact neg_abs_le _
        have h2 : |v i * v j| ≤ (v i ^ 2 + v j ^ 2) / 2 := by
          rw [abs_mul]
          have hsq : 0 ≤ (|v i| - |v j|) ^ 2 := sq_nonneg _
          have habs : |v i| ^ 2 = v i ^ 2 ∧ |v j| ^ 2 = v j ^ 2 := ⟨sq_abs _, sq_abs _⟩
          nlinarith
        have h3 : |(E i j : ℝ)| * |v i * v j| ≤ |(E i j : ℝ)| * ((v i ^ 2 + v j ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        linarith
    have hsplit : (∑ i : Fin 64, ∑ j : Fin 64, v i * (E i j : ℝ) * v j) =
        (∑ i : Fin 64, v i ^ 2 * (E i i : ℝ)) +
        (∑ i : Fin 64, ∑ j : Fin 64, if j = i then (0 : ℝ) else v i * (E i j : ℝ) * v j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.add_sum_erase _ _ (mem_univ i)]
      have h1 : (∑ j : Fin 64, if j = i then (0 : ℝ) else v i * (E i j : ℝ) * v j) =
          ∑ j ∈ univ.erase i, v i * (E i j : ℝ) * v j := by
        rw [← Finset.add_sum_erase _ _ (mem_univ i), ite_eq_left rfl, zero_add]
        refine Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
      rw [h1]; ring
    have hoff_ge :
        -(∑ i : Fin 64, v i ^ 2 * ∑ j : Fin 64, if j = i then (0 : ℝ) else |(E i j : ℝ)|)
        ≤ ∑ i : Fin 64, ∑ j : Fin 64, if j = i then (0 : ℝ) else v i * (E i j : ℝ) * v j := by
      have hle : (∑ i : Fin 64, ∑ j : Fin 64,
            if j = i then (0 : ℝ) else -|(E i j : ℝ)| * ((v i ^ 2 + v j ^ 2) / 2))
          ≤ ∑ i : Fin 64, ∑ j : Fin 64, if j = i then (0 : ℝ) else v i * (E i j : ℝ) * v j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
      have heq : (∑ i : Fin 64, ∑ j : Fin 64,
            if j = i then (0 : ℝ) else -|(E i j : ℝ)| * ((v i ^ 2 + v j ^ 2) / 2))
          = -(∑ i : Fin 64, v i ^ 2 * ∑ j : Fin 64, if j = i then (0 : ℝ) else |(E i j : ℝ)|) := by
        have hpart : ∀ i j : Fin 64,
            (if j = i then (0 : ℝ) else -|(E i j : ℝ)| * ((v i ^ 2 + v j ^ 2) / 2))
            = (if j = i then (0 : ℝ) else -(|(E i j : ℝ)| * v i ^ 2 / 2))
              + (if j = i then (0 : ℝ) else -(|(E i j : ℝ)| * v j ^ 2 / 2)) := by
          intro i j; by_cases h : j = i <;> simp [h]; ring
        simp_rw [hpart, Finset.sum_add_distrib]
        have hswap : (∑ i : Fin 64, ∑ j : Fin 64,
              if j = i then (0 : ℝ) else -(|(E i j : ℝ)| * v j ^ 2 / 2))
            = ∑ i : Fin 64, ∑ j : Fin 64,
              if j = i then (0 : ℝ) else -(|(E i j : ℝ)| * v i ^ 2 / 2) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [hE_sym i j]
          by_cases h : j = i
          · subst h; simp
          · have h' : i ≠ j := Ne.symm h
            simp [h, h']
        rw [hswap, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : j = i <;> simp [h]; ring
      linarith
    have hdiag_pos : ∀ i : Fin 64,
        (0 : ℝ) < (E i i : ℝ) - ∑ j : Fin 64, if j = i then (0 : ℝ) else |(E i j : ℝ)| := by
      intro i
      have hi : ((∑ j : Fin 64, if j = i then (0 : ℤ) else ((E i j).natAbs : ℤ) : ℤ) : ℝ)
          < (E i i : ℝ) := by exact_mod_cast hE_dom i
      have hcast : ((∑ j : Fin 64, if j = i then (0 : ℤ) else ((E i j).natAbs : ℤ) : ℤ) : ℝ)
          = ∑ j : Fin 64, if j = i then (0 : ℝ) else |(E i j : ℝ)| := by
        push_cast
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : j = i
        · simp [h]
        · simp [h]
      linarith
    obtain ⟨i₀, hi₀⟩ := hv
    have hsum_pos : 0 < ∑ i : Fin 64, v i ^ 2 *
        ((E i i : ℝ) - ∑ j : Fin 64, if j = i then (0 : ℝ) else |(E i j : ℝ)|) := by
      refine Finset.sum_pos' (fun i _ => mul_nonneg (sq_nonneg _) (le_of_lt (hdiag_pos i))) ?_
      exact ⟨i₀, mem_univ i₀, mul_pos (sq_pos_of_ne_zero hi₀) (hdiag_pos i₀)⟩
    have hrew : (∑ i : Fin 64, v i ^ 2 *
          ((E i i : ℝ) - ∑ j : Fin 64, if j = i then (0 : ℝ) else |(E i j : ℝ)|))
        = (∑ i : Fin 64, v i ^ 2 * (E i i : ℝ)) -
          (∑ i : Fin 64, v i ^ 2 * ∑ j : Fin 64, if j = i then (0 : ℝ) else |(E i j : ℝ)|) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hgram_nn : 0 ≤ ∑ k : Fin 64, (∑ i : Fin 64, (L i k : ℝ) * v i) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hK2 : (0 : ℝ) < (K : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hK)
  nlinarith

/-! ### Part 4. Connecting `buildBaseMat` to `completionOf` and Master Certificate Theorem -/

/-- Build the 64×64 base integer matrix `M₀ = μ·I - diag(d) - Q·Λ` for `signFast`. -/
def buildBaseMat (signFast : ℕ → ℤ) (Q mu : ℤ) (dList : List ℤ) : List (List ℤ) :=
  (List.range 64).map fun i =>
    let pi := outNatArr.getD i 0
    let di := dList.getD i 0
    (List.range 64).map fun j =>
      let pj := outNatArr.getD j 0
      let lam := if isSectionFast (pi ^^^ pj) && (sympFast pi pj == 0)
                 then signFast (pi ^^^ pj) * lineSignFast pi pj else 0
      (if i == j then mu - di else 0) - Q * lam

lemma buildBaseMat_wf (signFast : ℕ → ℤ) (Q mu : ℤ) (dList : List ℤ) :
    Mat64WF (buildBaseMat signFast Q mu dList) := by
  refine ⟨by simp [buildBaseMat], ?_⟩
  intro r hr
  simp only [buildBaseMat, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨_, _, rfl⟩
  simp

lemma map_outsideLabel_outNatArr_eq :
    (List.finRange 64).map (fun k => (outsideLabel k).val) = outNatArr := by decide +kernel

lemma outNatArr_getD_eq (i : Fin 64) : outNatArr.getD i.val 0 = (outsideLabel i).val := by
  have h := map_outsideLabel_outNatArr_eq
  rw [← h, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by simp)]
  simp

lemma completionOf_eq_fast {sign : Fin 256 → ℤ} {signFast : ℕ → ℤ}
    (hsign : ∀ w : Fin 256, sign w = signFast w.val) (i j : Fin 64) :
    completionOf sign i j =
      if isSectionFast ((outsideLabel i).val ^^^ (outsideLabel j).val) &&
          (sympFast (outsideLabel i).val (outsideLabel j).val == 0)
      then signFast ((outsideLabel i).val ^^^ (outsideLabel j).val) *
            lineSignFast (outsideLabel i).val (outsideLabel j).val
      else 0 := by
  have hlt : Nat.xor (outsideLabel i).val (outsideLabel j).val < 256 :=
    Nat.xor_lt_two_pow (n := 8) (outsideLabel i).isLt (outsideLabel j).isLt
  have haddv : (codeAdd (outsideLabel i) (outsideLabel j)).val =
      (outsideLabel i).val ^^^ (outsideLabel j).val := by
    simp only [codeAdd, Nat.mod_eq_of_lt hlt]; rfl
  unfold completionOf
  simp only [mem_sectionCodes_iff_fast, symp_codePoint_eq_fast, hsign,
    integerLineSign_codePoint_eq_fast, haddv, Bool.and_eq_true, beq_iff_eq]

lemma buildBaseMat_getD {sign : Fin 256 → ℤ} {signFast : ℕ → ℤ}
    (hsign : ∀ w : Fin 256, sign w = signFast w.val)
    (Q mu : ℤ) (dList : List ℤ) (i j : Fin 64) :
    ((buildBaseMat signFast Q mu dList).getD i.val []).getD j.val 0 =
      (if i = j then mu - dList.getD i.val 0 else 0) - Q * completionOf sign i j := by
  have hi : i.val < 64 := i.isLt
  have hj : j.val < 64 := j.isLt
  have h1 : (buildBaseMat signFast Q mu dList).getD i.val [] =
      (List.range 64).map fun k =>
        let pi := outNatArr.getD i.val 0
        let di := dList.getD i.val 0
        let pk := outNatArr.getD k 0
        let lam := if isSectionFast (pi ^^^ pk) && (sympFast pi pk == 0)
                   then signFast (pi ^^^ pk) * lineSignFast pi pk else 0
        (if i.val == k then mu - di else 0) - Q * lam := by
    unfold buildBaseMat
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some]
  rw [outNatArr_getD_eq i, outNatArr_getD_eq j, ← completionOf_eq_fast hsign i j]
  have hij : (i.val == j.val) = decide (i = j) := by
    by_cases h : i = j
    · subst h; simp
    · have hne : i.val ≠ j.val := fun hv => h (Fin.ext hv)
      simp [h, beq_false_of_ne hne]
  simp only [hij, decide_eq_true_eq]

lemma buildBaseMat_quadForm {sign : Fin 256 → ℤ} {signFast : ℕ → ℤ}
    (hsign : ∀ w : Fin 256, sign w = signFast w.val)
    (Q mu : ℤ) (dList : List ℤ)
    (hd0 : (∑ i : Fin 64, dList.getD i.val 0) = 0)
    (y : Fin 64 → ℝ) (hy : ∀ i : Fin 64, y i = 1 ∨ y i = -1) :
    matQuadForm (buildBaseMat signFast Q mu dList) y =
      64 * (mu : ℝ) - (Q : ℝ) * ∑ i : Fin 64, ∑ j : Fin 64, y i * (completionOf sign i j : ℝ) * y j := by
  have hsq : ∀ i : Fin 64, y i * y i = 1 := fun i => by rcases hy i with h | h <;> rw [h] <;> norm_num
  unfold matQuadForm
  simp_rw [buildBaseMat_getD hsign Q mu dList]
  have h1 : ∀ i : Fin 64,
      (∑ j : Fin 64, y i * ((((if i = j then mu - dList.getD i.val 0 else 0) - Q * completionOf sign i j : ℤ) : ℝ)) * y j)
      = ((mu : ℝ) - (dList.getD i.val 0 : ℝ)) -
        (Q : ℝ) * ∑ j : Fin 64, y i * (completionOf sign i j : ℝ) * y j := by
    intro i
    have hsplit : ∀ j : Fin 64,
        y i * ((((if i = j then mu - dList.getD i.val 0 else 0) - Q * completionOf sign i j : ℤ) : ℝ)) * y j
        = (if j = i then (mu : ℝ) - (dList.getD i.val 0 : ℝ) else 0) -
          (Q : ℝ) * (y i * (completionOf sign i j : ℝ) * y j) := by
      intro j
      by_cases h : j = i
      · subst h; simp only [↓reduceIte, Int.cast_sub, Int.cast_mul]
        calc y j * ((mu : ℝ) - (dList.getD j.val 0 : ℝ) - (Q : ℝ) * (completionOf sign j j : ℝ)) * y j
            = ((mu : ℝ) - (dList.getD j.val 0 : ℝ)) * (y j * y j) -
              (Q : ℝ) * (y j * (completionOf sign j j : ℝ) * y j) := by ring
          _ = ((mu : ℝ) - (dList.getD j.val 0 : ℝ)) -
              (Q : ℝ) * (y j * (completionOf sign j j : ℝ) * y j) := by rw [hsq j, mul_one]
      · have h' : i ≠ j := Ne.symm h
        simp only [h, h', ↓reduceIte, zero_sub, Int.cast_neg, Int.cast_mul]
        ring
    simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, ↓reduceIte, ← Finset.mul_sum]
  simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  have hdR : (∑ i : Fin 64, (dList.getD i.val 0 : ℝ)) = 0 := by exact_mod_cast hd0
  rw [hdR]; ring

/-- Master theorem: a single verified MET-SDP + Gershgorin-shifted Cholesky certificate proves
`target ≤ c3ViolatedOutsideContexts sign y` for EVERY binary completion `y ∈ {±1}^64`. -/
theorem c3_lower_of_met_sdp_cert
    {sign : Fin 256 → ℤ} {signFast : ℕ → ℤ}
    (hsign_val : ∀ w : Fin 256, sign w = 1 ∨ sign w = -1)
    (hsign : ∀ w : Fin 256, sign w = signFast w.val)
    (Q mu K : ℤ) (hQ : 0 < Q) (hK : 0 < K)
    (dList : List ℤ) (cuts : List TriCut) (Lrows : List (List ℤ))
    (target : ℕ)
    (hd0 : (∑ i : Fin 64, dList.getD i.val 0) = 0)
    (hbase_sym : ∀ i j : Fin 64,
      ((buildBaseMat signFast Q mu dList).getD i.val []).getD j.val 0 =
      ((buildBaseMat signFast Q mu dList).getD j.val []).getD i.val 0)
    (hcuts : cuts.all validTriCut = true)
    (hdom : checkGramDiagDom K (cuts.foldl addTriCut (buildBaseMat signFast Q mu dList)) Lrows = true)
    (hbound : 64 * mu + 2 * sumWeights cuts < 4 * Q * (560 - ((target : ℤ) - 1)))
    (y : Fin 64 → ℝ) (hy : ∀ i : Fin 64, y i = 1 ∨ y i = -1) :
    target ≤ c3ViolatedOutsideContexts sign y := by
  let M0 := buildBaseMat signFast Q mu dList
  let Mcert := cuts.foldl addTriCut M0
  have hM0_wf : Mat64WF M0 := buildBaseMat_wf signFast Q mu dList
  obtain ⟨hMc_wf, hMc_sym, hMc_le⟩ := foldl_addTriCut_spec cuts hcuts M0 hM0_wf hbase_sym y hy
  have hy_nz : ∃ i : Fin 64, y i ≠ 0 :=
    ⟨⟨0, by norm_num⟩, by rcases hy ⟨0, by norm_num⟩ with h | h <;> rw [h] <;> norm_num⟩
  have hpos : 0 < matQuadForm Mcert y :=
    matQuadForm_pos_of_gram_diagDom hK hMc_wf hMc_sym hdom y hy_nz
  have hbase := buildBaseMat_quadForm hsign Q mu dList hd0 y hy
  have hquad := c3_quadForm_eq sign hsign_val y hy
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hbdR : 64 * (mu : ℝ) + 2 * (sumWeights cuts : ℝ) <
      4 * (Q : ℝ) * (560 - ((target : ℝ) - 1)) := by exact_mod_cast hbound
  -- From 0 < matQuadForm Mcert y ≤ 64*mu - Q*(yᵀ Λ y) + 2*sumWeights:
  -- Q * (yᵀ Λ y) < 64*mu + 2*sumWeights < 4*Q*(560 - (target - 1))
  -- Since yᵀ Λ y = 4 * (560 - F), we get target - 1 < F, hence target ≤ F!
  have hlt : ((target : ℝ) - 1) < (c3ViolatedOutsideContexts sign y : ℝ) := by nlinarith
  have hnat : target < c3ViolatedOutsideContexts sign y + 1 := by
    have : (target : ℝ) < ((c3ViolatedOutsideContexts sign y + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

/-! ### Part 5. Instantiation on `signA` (Exact Minimum 368) and `signB` (Exact Minimum 344) -/

/-- Fast computable lookup encoding `signB` on 8-bit Pauli codes. -/
def signBFast (w : ℕ) : ℤ :=
  if w == 87 || w == 144 || w == 176 || w == 215 then -1 else 1

lemma signB_eq_fast : ∀ w : Fin 256, signB w = signBFast w.val := by decide +kernel

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
lemma certA_base_sym : ∀ i j : Fin 64,
    ((buildBaseMat signAFast certAQ certAMu certAD).getD i.val []).getD j.val 0 =
    ((buildBaseMat signAFast certAQ certAMu certAD).getD j.val []).getD i.val 0 := by
  decide +kernel

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
lemma certA_d0 : (∑ i : Fin 64, certAD.getD i.val 0) = 0 := by decide +kernel

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
lemma certA_cuts_valid : certACuts.all validTriCut = true := by decide +kernel

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
lemma certA_bound : 64 * certAMu + 2 * sumWeights certACuts < 4 * certAQ * (560 - ((368 : ℤ) - 1)) := by
  decide +kernel

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
lemma certA_gram_diagDom :
    checkGramDiagDom certAK
      (certACuts.foldl addTriCut (buildBaseMat signAFast certAQ certAMu certAD)) certAL = true := by
  decide +kernel

/-- **Exact global binary lower bound for `signA` (`σ₀`):**
Every binary completion `y ∈ {±1}^64` of `signA` violates at least **368** outside contexts
(closing the previous `[347, 368]` interval to exact global optimality `368`). -/
theorem corollary16_sigmaA_exact_lower :
    ∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      368 ≤ c3ViolatedOutsideContexts signA y :=
  c3_lower_of_met_sdp_cert signA_values signA_eq_fast
    certAQ certAMu certAK (by decide) (by decide)
    certAD certACuts certAL 368
    certA_d0 certA_base_sym certA_cuts_valid certA_gram_diagDom certA_bound

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
lemma certB_base_sym : ∀ i j : Fin 64,
    ((buildBaseMat signBFast certBQ certBMu certBD).getD i.val []).getD j.val 0 =
    ((buildBaseMat signBFast certBQ certBMu certBD).getD j.val []).getD i.val 0 := by
  decide +kernel

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
lemma certB_d0 : (∑ i : Fin 64, certBD.getD i.val 0) = 0 := by decide +kernel

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
lemma certB_cuts_valid : certBCuts.all validTriCut = true := by decide +kernel

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
lemma certB_bound : 64 * certBMu + 2 * sumWeights certBCuts < 4 * certBQ * (560 - ((344 : ℤ) - 1)) := by
  decide +kernel

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
lemma certB_gram_diagDom :
    checkGramDiagDom certBK
      (certBCuts.foldl addTriCut (buildBaseMat signBFast certBQ certBMu certBD)) certBL = true := by
  decide +kernel

/-- **Exact global binary lower bound for `signB` (`σ₁`):**
Every binary completion `y ∈ {±1}^64` of `signB` violates at least **344** outside contexts
(closing the previous `[330, 344]` interval to exact global optimality `344`). -/
theorem corollary16_sigmaB_exact_lower :
    ∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      344 ≤ c3ViolatedOutsideContexts signB y :=
  c3_lower_of_met_sdp_cert signB_values signB_eq_fast
    certBQ certBMu certBK (by decide) (by decide)
    certBD certBCuts certBL 344
    certB_d0 certB_base_sym certB_cuts_valid certB_gram_diagDom certB_bound

/-- **Exact Corollary 16 (complete resolution of BOTH four-qubit C3 binary completion optima):**
- `min_{y ∈ {±1}^64} F(signA, y) = 368` (attained by `c3WitnessAReal`)
- `min_{y ∈ {±1}^64} F(signB, y) = 344` (attained by `c3WitnessReal`)
- Exact binary completion separation: `368 - 344 = 24`. -/
theorem corollary16_exact_binary_optima :
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) → 368 ≤ c3ViolatedOutsideContexts signA y) ∧
    (∃ y₀ : Fin 64 → ℝ, (∀ i, y₀ i = 1 ∨ y₀ i = -1) ∧ c3ViolatedOutsideContexts signA y₀ = 368) ∧
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) → 344 ≤ c3ViolatedOutsideContexts signB y) ∧
    (∃ y₁ : Fin 64 → ℝ, (∀ i, y₁ i = 1 ∨ y₁ i = -1) ∧ c3ViolatedOutsideContexts signB y₁ = 344) :=
  ⟨corollary16_sigmaA_exact_lower,
   ⟨c3WitnessAReal, c3WitnessAReal_values, corollary16_sigmaA_witness⟩,
   corollary16_sigmaB_exact_lower,
   ⟨c3WitnessReal, c3WitnessReal_values, corollary16_sigmaB_witness⟩⟩

end HoggarBound.C3ExactOptima

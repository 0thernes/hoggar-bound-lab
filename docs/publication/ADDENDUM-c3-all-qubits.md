# Addendum: the strict law fails in case C3 for every number of qubits

**Folded into the combined paper, version 1.3.0 (10 November 2026), Sections 8.6 and 9.3 (Theorem 17, Corollary 18).** This file keeps
the result as first stated. Since version 1.4.0 the paper repeats the proof of the cone lift used in Corollary 18.

**Status.** Originally proposed addition for the next revision of the combined paper
([paper/unified-contextuality.md](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/paper/unified-contextuality.md)). Release `v1.2.0` and its frozen
artifacts are not changed by this file. The result was obtained on 10 November 2026 by the Claude
(Anthropic) line of work, under the direction of Alexander S. Donahue, 0thernes LLC.

* **Proof.** Written out below, in six short steps.
* **Lean 4.** The statement that the strict law fails in case C3 for every $N \ge 4$ is proved in
  [lean/HoggarBound/CarrierFamily.lean](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/lean/HoggarBound/CarrierFamily.lean) (theorem
  `c3_strict_law_fails_general`; standard axioms only), with the definitions of the library that
  carries the other Lean theorems of the combined paper. What the Lean statement says, and what it
  leaves to the reader, is listed under [Formal verification](#formal-verification).
* **Exact computation.** The carriers are checked in integer arithmetic on the complete configurations
  for three, four, five and six qubits by [scripts/cospectral_family.py](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/scripts/cospectral_family.py)
  (43 checks), and for three, four and five qubits by a second program that shares no method with it,
  [scripts/cospectral_family_tensor_check.py](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/scripts/cospectral_family_tensor_check.py) (18 checks).
  The consequence for case C11 is checked by
  [scripts/cospectral_family_cone_lift.py](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/scripts/cospectral_family_cone_lift.py) (21 checks).
* **Review.** Automated review passes, described under [Review record](#review-record). Not peer
  reviewed.

## What was open

B. W. Jonah's note on hyperplane completions
([doi:10.5281/zenodo.23524332](https://doi.org/10.5281/zenodo.23524332), version 0.5; cited as [J3] in the
combined paper) classifies sixteen cases. In case C3 the configuration is a hyperbolic quadric and the
hyperplane is the one whose polar point lies on the quadric. The *strict law* says that two carriers
with the same carrier spectrum have the same completion spectrum. Conjecture E of the note says that on
sign carriers, that is carriers with values $\pm 1$, the strict law fails "in every vertex case" for
every $N \ge 4$; C3 is one of the nine vertex cases. The note proves the conjecture for C1 and C6,
reports exact pairs for six further cases at $N = 4$, and reports C3 as open for all $N \ge 4$, after
random searches at $N = 4$ and $N = 5$ found no pair. For $N = 3$ it reports exact C3 pairs, without
their data.

Section 8 of the combined paper settles $N = 4$ by one explicit pair of carriers. Theorem 17 below
settles case C3 for every $N \ge 4$, and by a lemma of the note this also settles case C11 for every
$N \ge 4$ (Corollary 18).

## Setting

$N \ge 3$ qubits, $m = N - 1$, $n = 2^m$, $D = 2^N$. $\mathcal Q = Q^+(2N-1,2)$ is the set of real
non-identity $N$-qubit Pauli observables, $`p_\star = Z \otimes I_n`$ (the first factor is the qubit of
highest index), $H$ the section (the observables of $\mathcal Q$ that commute with $`p_\star`$) and
$O = \mathcal Q \setminus H$. Let $R$ be the set of real non-identity $m$-qubit Pauli observables,
$|R| = (n-1)(n+2)/2$. Then

```math
H = \{ p_\star \} \cup \{ I \otimes P,\; Z \otimes P : P \in R \}, \qquad |H| = 1 + (n-1)(n+2), \qquad |O| = n^2 .
```

A context is a set $`\ell`$ of three pairwise commuting observables of $\mathcal Q$ whose product is
$`s_\ell`$ times the identity, $`s_\ell = \pm 1`$, as in Section 2 of the combined paper. A sign carrier is
a map $`\sigma : H \to \{-1,+1\}`$. Its carrier operator is $`A_\sigma = \sum_{s \in H} \sigma(s) P_s`$, and its
completion matrix $`\Lambda_\sigma`$, indexed by $O$, has the entry $`s_\ell\, \sigma(s)`$ at $(p,q)$ for every
context $`\ell = \{s, p, q\}`$ with $s \in H$ and $p, q \in O$, and zero elsewhere. These are the objects
of [J3] and of Section 8 of the combined paper.

Vectors of $`\mathbb{F}_2^m`$ are written as integers, bit $k$ for qubit $k$. A real $m$-qubit Pauli
observable is $`P_{a,c} = i^{\,a\cdot c} X^a Z^c`$ with $a \cdot c$ even, where $a \cdot c$ is the number of
common bits, and $`X^a Z^c\, |b\rangle = (-1)^{c \cdot b}\, |b + a\rangle`$. In the data files an observable
$X^a Z^c$ on $N$ qubits has the label $a + 2^N c$, and bit 0 is the rightmost tensor factor, as in the
combined paper; for $N = 4$ the polar point $ZIII$ has the label 128.

## The theorem

**Theorem 17 (case C3, every number of qubits).** For every $N \ge 4$ there are sign carriers
$\sigma$ and $\tau$ on $H$ such that $`A_\sigma`$ and $`A_\tau`$ have the same characteristic polynomial and

```math
\operatorname{tr} \Lambda_\sigma^3 - \operatorname{tr} \Lambda_\tau^3 = -\tfrac32\, n^3 \neq 0 .
```

So the two completion matrices have different spectra, and the strict law fails for sign carriers in
case C3 for every $N \ge 4$. One may take $\tau$ equal to $\sigma$ except at the $n/2$ points
$Z \otimes W \otimes X$, $`W \in \{I, Z\}^{\otimes (N-2)}`$, where the two carriers have opposite signs.
For $N = 3$ a variant gives a pair with difference $-288$ (Remark 1). The number 17 continues the
numbering of the combined paper after Corollary 16 of the
[addendum on completion optima](ADDENDUM-completion-optima.md).

### The carriers

Choose a vertex $`t \in \mathbb{F}_2^m`$ and, for every non-zero $`a \in \mathbb{F}_2^m`$, a vertex $u_a$.
Let $G$ be the graph on the vertex set $`\mathbb{F}_2^m`$ whose $n - 1$ edges are the pairs
$`\{u_a, u_a + a\}`$: one edge for each non-zero difference. Define signs on $R$ by

```math
\varepsilon(P_{a,c}) = (-1)^{c \cdot u_a}\, (-1)^{(a \cdot c)/2} \quad (a \neq 0), \qquad
\varepsilon(P_{0,c}) = (-1)^{c \cdot t} .
```

The signs depend only on the edges, not on which end of an edge is called $u_a$, because
$c \cdot a$ is even. Let $F$ be a set of edges of $G$ that is a union of connected components of $G$
not containing $t$. Define

* $\sigma$: $`\sigma(p_\star) = +1`$ and $`\sigma(I \otimes P) = \sigma(Z \otimes P) = \varepsilon(P)`$ for all $P \in R$;
* $\tau$: the same, except that $`\tau(Z \otimes P_{a,c}) = -\varepsilon(P_{a,c})`$ whenever $a$ is the difference
  of an edge of $F$.

For the theorem take $m \ge 3$, $u_1 = 0$, $u_2 = u_3 = 4$, $u_a = 2$ for $a \ge 4$, $t = 2$, and
$`F = \{\{0, 1\}\}`$. The edge $`\{0,1\}`$ is a connected component, because every other edge
($`\{4, 6\}`$, $`\{4, 7\}`$ and $`\{2, 2 + a\}`$ with $a \ge 4$) avoids the vertices 0 and 1. For $a = 1$ the
condition $a \cdot c$ even means that bit 0 of $c$ vanishes, so $`P_{1,c} = W \otimes X`$ with $W$ a
product of $I$ and $Z$ factors, and $\varepsilon = +1$ on these observables.

### Proof

*Step 1: blocks.* Every $P_s$, $s \in H$, commutes with $`P_{p_\star}`$, so $`A_\sigma = C_\sigma \oplus D_\sigma`$ on the
two eigenspaces of $`P_{p_\star}`$, and

```math
C_\sigma = \sigma(p_\star)\, I + \sum_{P \in R} \big(\sigma(I \otimes P) + \sigma(Z \otimes P)\big) P, \qquad
D_\sigma = -\sigma(p_\star)\, I + \sum_{P \in R} \big(\sigma(I \otimes P) - \sigma(Z \otimes P)\big) P .
```

Each $P \in R$ appears in exactly one of the two blocks, with coefficient $\pm 2$. This is the block
decomposition of [J3, Theorem B3] and equation (C4) of the combined paper.

*Step 2: two character sums.* Since $`\varepsilon(P_{a,c})\, P_{a,c} = (-1)^{c \cdot u_a} X^a Z^c`$, and the
vectors $c$ with $a \cdot c$ even form the hyperplane orthogonal to $a$,

```math
\sum_{c \,:\, a \cdot c \text{ even}} (-1)^{c \cdot u_a}\, X^a Z^c
 = \tfrac{n}{2} \big( |u_a + a\rangle\langle u_a| + |u_a\rangle\langle u_a + a| \big) \quad (a \neq 0), \qquad
\sum_{c \neq 0} (-1)^{c \cdot t}\, Z^c = n\, |t\rangle\langle t| - I .
```

Indeed the first sum sends $|b\rangle$ to $`\sum_c (-1)^{c \cdot (u_a + b)} |b + a\rangle`$, and the sum of a
character over a hyperplane is $n/2$ if the character is trivial on it, that is if
$`b + u_a \in \{0, a\}`$, and $0$ otherwise. The second is the same computation over all $c$, minus the
term $c = 0$.

*Step 3: the blocks are graphs.* By Steps 1 and 2, with $\operatorname{Adj}$ the adjacency matrix,

```math
C_\sigma = -I + 2n\, |t\rangle\langle t| + n \operatorname{Adj}(G), \qquad D_\sigma = -I,
```
```math
C_\tau = -I + 2n\, |t\rangle\langle t| + n \operatorname{Adj}(G - F), \qquad D_\tau = -I + n \operatorname{Adj}(F) .
```

*Step 4: equal carrier spectra.* Let $V_2$ be the set of vertices of the components in $F$ and $V_1$
its complement, which contains $t$. Then $`2\,|t\rangle\langle t| + \operatorname{Adj}(G) = M_1 \oplus M_2`$ with
$M_1$ supported on $V_1$ and $M_2 = \operatorname{Adj}(F)$ supported on $V_2$. In units of $n$ and after
adding $I$, the pair of blocks is $`(M_1 \oplus M_2,\; 0)`$ for $\sigma$ and
$`(M_1 \oplus 0,\; 0 \oplus M_2)`$ for $\tau$. Both have the union of spectra
$`\operatorname{spec} M_1 \uplus \operatorname{spec} M_2 \uplus \{0^{\,n}\}`$. So $`A_\sigma`$ and $`A_\tau`$ have the
same eigenvalues with the same multiplicities.

*Step 5: the completion matrix.* This step is [J3, Theorem A and Theorem B3, case C3], which holds
for every $N \ge 3$, and Section 8.4 of the combined paper for $N = 4$; the short proof is repeated so
that the addendum can be read alone. An outside observable anticommutes with $`P_{p_\star}`$ and has the
form

```math
P_p = \begin{pmatrix} 0 & M_p \\ M_p^{\mathsf T} & 0 \end{pmatrix} .
```

The $n^2$ real matrices $M_p$ are pairwise orthogonal for the trace form, hence a basis of all real
$n \times n$ matrices. If $s \in H$ commutes with $p \in O$, then $`P_s P_p`$ is $\pm$ a real observable
$P_q$ that anticommutes with $`P_{p_\star}`$ and differs from $P_p$; so $`\ell = \{s, p, q\}`$ is a context,
$`P_s P_p = s_\ell P_q`$, and each $s$ commuting with $p$ gives exactly one outside context through $p$.
Every context with one point in $H$ and two in $O$ arises once in this way, and $`p_\star`$ commutes with
no outside point. Therefore $`\tfrac12 (A_\sigma P_p + P_p A_\sigma) = \sum_q (\Lambda_\sigma)_{qp} P_q`$: in the
basis of the $M_p$, $`\Lambda_\sigma`$ is the matrix of $`M \mapsto \tfrac12 (C_\sigma M + M D_\sigma)`$. Its
eigenvalues are $\tfrac12 (c_i + d_j)$, so

```math
\operatorname{tr} \Lambda_\sigma^3 = \tfrac18 \big( n \operatorname{tr} C_\sigma^3 + 3 \operatorname{tr} C_\sigma^2 \operatorname{tr} D_\sigma
 + 3 \operatorname{tr} C_\sigma \operatorname{tr} D_\sigma^2 + n \operatorname{tr} D_\sigma^3 \big) .
```

*Step 6: the difference.* For both carriers $\operatorname{tr} C = n$ and $\operatorname{tr} D = -n$, and
$`\operatorname{tr} C^3 + \operatorname{tr} D^3 = \operatorname{tr} A^3`$ is the same by Step 4. By orthogonality of
the Pauli observables, $`\operatorname{tr} C^2 = n + 4n\, r_C`$ and $`\operatorname{tr} D^2 = n + 4n\, r_D`$, where
$r_C$ and $r_D$ count the observables of $R$ carried by each block, and $r_C + r_D = |R|$. Inserting
this in the formula of Step 5 gives, for every sign carrier with $`\sigma(p_\star) = +1`$,

```math
\operatorname{tr} \Lambda_\sigma^3 = \tfrac{n}{8} \operatorname{tr} A_\sigma^3 - \tfrac32\, n^2\, |R| + 3 n^2\, r_D(\sigma),
```

and therefore, for any two such carriers with the same carrier spectrum,

```math
\operatorname{tr} \Lambda_\sigma^3 - \operatorname{tr} \Lambda_\tau^3 = 3 n^2 \big( r_D(\sigma) - r_D(\tau) \big) .
```

Here $r_D(\sigma) = 0$ and $r_D(\tau) = |F| \cdot n/2$, since each difference $a$ carries $n/2$
observables. With $|F| = 1$ this is $-\tfrac32 n^3$. $\qquad\blacksquare$

The identity of Step 6 is the form for general $N$ of equations (C8) and (C9) of the combined paper.
The use of a cubic trace to separate completion spectra is that of [J3, Lemma D (D1)], which treats
the cases C1 and C6.

### Case C11

**Corollary 18 (case C11).** The strict law fails for sign carriers in case C11 for every $N \ge 4$.

*Proof.* [J3, Lemma D (D2)], the cone lift, turns a pair of sign carriers that refutes the strict law
in case C3 on $N$ qubits into such a pair in case C11 on $N + 1$ qubits: add a qubit, let $e$ be $Z$
on it, keep the polar point, give the value $+1$ to $e$ and the value $\sigma(s)$ to $s$ and to $e + s$.
The carrier spectrum becomes $2 \operatorname{spec} A + 1$ together with $D$ copies of $-1$, and the
completion spectrum becomes $2 \operatorname{spec} \Lambda + 1$ together with $|O|$ copies of $-1$. Apply
this to the carriers of Theorem 17, and for four qubits to the three-qubit pair of Remark 1.
$\qquad\blacksquare$

For the lifted carriers
$`\operatorname{tr} \Lambda'^3 = 8 \operatorname{tr} \Lambda^3 + 12 \operatorname{tr} \Lambda^2 + 6 \operatorname{tr} \Lambda`$,
so the cubic traces of the lifted pair differ by $`-12\, n^3`$, with $n = 2^{N-1}$ for the base case on
$N$ qubits. The note [J3] reports exact C11 pairs for $N = 3, 4, 5$, and proves the conjecture only for
C1 and C6; so with Theorem 17 the conjecture is settled for C1, C6 (in [J3]), C3 and C11. The lemma is
[J3]'s; the program `scripts/cospectral_family_cone_lift.py` does not use it and checks the lifted
pairs on the complete lifted configurations with 4, 5 and 6 qubits, built from the definitions.

**Remarks.**

1. The construction gives many pairs: any graph with one edge per non-zero difference, and any set of
   its components away from $t$. For $N = 3$ a single edge cannot be a component, but the triangle
   $`\{0, 1, 3\}`$ with $t = 2$ is (for instance $u_1 = 0$, $u_2 = 1$, $u_3 = 0$), and the same proof
   gives a pair with difference $-\tfrac32 n^3 \cdot 3 = -288$. Three-qubit C3 pairs are already
   reported in [J3], without data; this one is the instance produced by the construction.
2. For two cospectral sign carriers with the value $+1$ at $`p_\star`$, Step 6 shows that the completion
   cubic traces differ exactly when the carriers have different numbers of observables $P$ with
   $`\sigma(I \otimes P) \neq \sigma(Z \otimes P)`$. If both have the value $-1$ at $`p_\star`$ the same holds, with
   the opposite sign of the difference. For the pair of Section 8 these numbers are 0 and 2, which
   gives $3 \cdot 64 \cdot (0 - 2) = 14976 - 15360$.
3. The largest completion eigenvalues of the two carriers of the theorem differ by exactly $n/2$:
   the largest eigenvalue of $C$ is the same for both, and the largest eigenvalue of $D$ is $-1$ for
   $\sigma$ and $n - 1$ for $\tau$.
4. The carriers of the theorem are not small changes of the carrier that is $+1$ everywhere: $\sigma$
   has the sign $-1$ on 13 of the 35 block observables for $N = 4$ and on 50 of the 135 for $N = 5$.
   A search shows that small changes cannot work at five qubits. Take all sign carriers with $+1$ at
   $`p_\star`$ that differ from the all-plus carrier in at most three block observables $P$, each changed in
   one of three ways: a sign flip of $P$ in $C$, or a move of $P$ to $D$ with either sign. At five
   qubits there are 10 908 676 such carriers, and no two of them are cospectral with different block
   spectra. At four qubits there are 182 176, and exactly four classes of cospectral carriers contain
   different block spectra; three of these classes contain different $r_D$, hence different completion
   cubic traces, and the program finds the pair of Section 8 in one of the three. The search is
   exhaustive and exact (`scripts/c3_sparse_search.py`, `results/c3_sparse_search.json`). It says
   nothing about pairs with only one member in this set.

## Explicit instances and numbers

Case C3, the carriers of Theorem 17 (the triangle variant for $N = 3$):

| $N$ | section, outside points, outside contexts | points where the carriers differ | $\operatorname{tr}\Lambda^3$ |
|---|---|---|---|
| 3 | 19, 16, 72 | 6 | 0 and 288 |
| 4 | 71, 64, 1120 | $ZIIX$, $ZIZX$, $ZZIX$, $ZZZX$ | 15744 and 16512 |
| 5 | 271, 256, 17280 | the 8 points $Z \otimes W \otimes X$ | 649728 and 655872 |
| 6 | 1055, 1024, 269824 | the 16 points $Z \otimes W \otimes X$ | 23021568 and 23070720 |

Case C11, the cone lifts of the first three rows:

| qubits | points of the cone, section, outside points, outside contexts | $\operatorname{tr}\Lambda'^3$ |
|---|---|---|
| 4 | 71, 39, 32, 304 | 1728 and 4032 |
| 5 | 271, 143, 128, 4544 | 152832 and 158976 |
| 6 | 1055, 543, 512, 69376 | 5612544 and 5661696 |

The complete sign tables, the graph and the characteristic polynomials are in
[results/cospectral_family.json](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/results/cospectral_family.json) and
[results/cospectral_family_cone_lift.json](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/results/cospectral_family_cone_lift.json).

## Formal verification

[lean/HoggarBound/CarrierFamily.lean](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/lean/HoggarBound/CarrierFamily.lean) is a new file for Lean
4.35.0 with Mathlib v4.35.0. It has no `sorry` and no `native_decide`, and each of its audited
statements depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. It changes no
existing Lean file. Its main theorem is

```lean
theorem c3_strict_law_fails_general (hm : 3 ≤ m) :
    ∃ σ τ : Pt (m + 1) → ℝ,
      (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (sectionPts m) σ).charpoly = (opA (sectionPts m) τ).charpoly ∧
      (completionMatrix m σ).charpoly ≠ (completionMatrix m τ).charpoly
```

for $N = m + 1$ qubits. The objects are those of the library that carries the other Lean theorems of
the combined paper (`HoggarBound/Pauli.lean`, `Bound.lean`, `Quadric.lean`): the points `Pt N`, the
Hermitian Pauli matrices `pauli u` with the product rule `pauli u * pauli v = tau u v • pauli (u + v)`,
the symplectic form `symp`, the real quadric `realPoints N`, the sign `lineSign u v` of the context
`{u, v, u + v}`, and the operator `opA S f`, the sum of `f u • pauli u` over `u ∈ S`. The new
definitions are

```lean
def polar (m : ℕ) : Pt (m + 1) := (0, Pi.single 0 1)                -- Z on qubit 0
def sectionPts (m : ℕ) : Finset (Pt (m + 1)) :=
  (realPoints (m + 1)).filter fun s => symp s (polar m) = 0
def outsidePts (m : ℕ) : Finset (Pt (m + 1)) :=
  (realPoints (m + 1)).filter fun s => symp s (polar m) = 1
noncomputable def completionMatrix (m : ℕ) (σ : Pt (m + 1) → ℝ) :
    Matrix {p // p ∈ outsidePts m} {p // p ∈ outsidePts m} ℝ :=
  fun p q => if p.1 ≠ q.1 ∧ symp p.1 q.1 = 0
    then lineSign (p.1 + q.1) q.1 * σ (p.1 + q.1) else 0
```

So the theorem says: on the real quadric of $N \ge 4$ qubits, with the polar point $Z$ on one qubit,
there are two carriers with values $\pm 1$ whose carrier operators have the same characteristic
polynomial and whose completion matrices have different characteristic polynomials. The file also
proves the facts that make these definitions the ones of the Setting:

| statement | Lean name |
|---|---|
| the polar point lies on the quadric and in the section | `polar_mem_sectionPts` |
| two different commuting outside points $p$, $q$ span a context whose third point $p + q$ is in the section, and $p + q$ is in the section only then | `add_mem_sectionPts`, `add_mem_sectionPts_iff` |
| a section point and an outside point that commute span a context with a second outside point | `add_mem_outsidePts` |
| the polar point commutes with no outside point | `symp_polar_outside` |
| $\lvert O \rvert = n^2$, $\lvert H \rvert = 1 + 2 \lvert R \rvert = n^2 + n - 1$, $2\lvert R \rvert + 2 = n^2 + n$ | `card_outsidePts`, `card_sectionPts`, `card_sectionPts_add_one`, `card_realLabels` |
| the sign of a context does not depend on the order of its points; the completion matrix is symmetric | `tau_add_comm`, `completionMatrix_transpose` |
| the carrier operator is Hermitian | `opA_isHermitian` (library) |

Two further statements give the numbers of Theorem 17, in coordinates (integer matrices, with the
first tensor factor split off):

```lean
theorem c3_all_qubits_completion (hm : 3 ≤ m) :
    ∃ (σI σZ τI τZ : V m × V m → ℤ),
      (∀ p, σI p = 1 ∨ σI p = -1) ∧ (∀ p, σZ p = 1 ∨ σZ p = -1) ∧
      (∀ p, τI p = 1 ∨ τI p = -1) ∧ (∀ p, τZ p = 1 ∨ τZ p = -1) ∧
      (carrierOp 1 σI σZ).charpoly = (carrierOp 1 τI τZ).charpoly ∧
      trace (completion 1 σI σZ ^ 3) - trace (completion 1 τI τZ ^ 3)
        = -(3 / 2 : ℚ) * ((2 : ℚ) ^ m) ^ 3
```

and `completionMatrix_liftCarrier`, which says that the coordinate matrix `completion` is the matrix
`completionMatrix` above, reindexed. The witnesses are the carriers of Theorem 17 with the graph of
"The carriers" (`defaultT`, `defaultU`, `defaultF`; `default_separated` is the statement that the edge
$`\{0,1\}`$ is a component away from $t$).

**Parts of the file and steps of the proof.**

| part | content | step |
|---|---|---|
| 1, 2 | for integer matrices of any size: the operator $M \mapsto CM + MD$ as a Kronecker sum, the trace of its cube, equal characteristic polynomials and the gap when a block, or a part $A_2$ with $A_1 A_2 = 0 = A_2 A_1$, moves from $C$ to $D$ | 4, 5 (trace formula), 6 |
| 3 | the two character sums over $`\mathbb{F}_2^m`$ | 2 |
| 4 | the two carriers as sign tables, their blocks as graph matrices, the two main statements for a set of edges that touches neither $t$ nor another edge, and the instance for every $m \ge 3$ | 3, 4, 6 |
| 5 | the carrier operator as a sum of Kronecker products over the section | 1 |
| 6 | the outside observables, the completion matrix as a sum over the section of normalised traces, its symmetry, the trace of its cube; different characteristic polynomials from different cubic traces | 5 |
| 7 | the same objects in the language of the library, and the transfer of the theorem to them | Setting |

**What the Lean statement leaves to the reader.**

1. That the definitions above are the objects of [J3] and of the Setting: `realPoints N` is the
   hyperbolic quadric $Q^+(2N-1,2)$ of the real observables; the polar point is a point of it; the
   lines of the configuration are the contexts, with the sign given by the product of the three
   operators (`context_product` in the library); the carrier operator and the completion matrix are
   defined as in [J3], the latter with the entry $`s_\ell\, \sigma(s)`$ for each context with one section
   point and two outside points, and zero elsewhere.
2. That for Hermitian and for real symmetric matrices equal characteristic polynomials mean equal
   spectra with multiplicities, so that the conclusion is the failure of the strict law.
3. The trust base: the Lean kernel, Mathlib at the pinned revision, the three standard axioms.

Not in Lean: Corollary 18 (it rests on [J3, Lemma D (D2)] and is checked by program on the complete
configurations with 4, 5 and 6 qubits), the pair for $N = 3$, Remarks 1 to 4 and the tables.

```bash
cd lean && lake build HoggarBound.Bound HoggarBound.Quadric && lake env lean HoggarBound/CarrierFamily.lean
```

prints one line for each audited statement, and no line may name another axiom. The workflow *Case C3
for every number of qubits* runs this on a clean machine and enforces the list.

## How to check

```bash
python scripts/cospectral_family.py --six
```

The last line must read `43 of 43 checks passed` (without `--six`: 35 checks, a few seconds, written
to `results/cospectral_family_n3-5.json` since 10 November 2026, so that the committed record is not
overwritten). For
$N = 3, 4, 5, 6$ the script builds every real Pauli matrix, the section, all outside contexts and their
signs (from a phase formula and, up to five qubits, again from products of three matrices), both
carriers as sign tables on the section, the carrier operators, and both completion matrices from the
contexts. It then checks, in integers: the block form and the graph formula of Step 3; equality of the
two characteristic polynomials; that the $n^2$ blocks $M_p$ are orthogonal and that the identity of
Step 5 holds on all of them; the trace formula against the direct value of $\operatorname{tr}\Lambda^3$;
the difference; and that the carriers differ exactly at the points $Z \otimes W \otimes X$. It repeats all
of this on the complete configurations for 12 random graphs with random sets of components at $N = 3$
and at $N = 4$, and it has two negative controls: moving an edge that is not a whole component, or the
component that contains $t$, must destroy the equality of the characteristic polynomials. Four more
checks test Steps 2 to 4 and the arithmetic of Step 6 on the blocks only, for 100 random graphs; there
the trace formula of Step 5 is used, not tested. NumPy is needed; no floating point enters a comparison.

```bash
python scripts/cospectral_family_tensor_check.py
```

This second program takes only the two sign tables from the output of the first. It builds every
Pauli observable as a Kronecker product of the literal $2 \times 2$ matrices, decides reality,
commutation and the sign of each context from matrix entries and matrix products, compares the two
carrier operators through the power sums $\operatorname{tr} A^k$ for all $k$ up to $2^N$, fills the
completion matrices from the contexts it found, and compares its counts and traces with the recorded
ones. It also checks that the two tables differ exactly at the words $Z \otimes W \otimes X$. The last
line must read `18 of 18 checks passed`.

```bash
python scripts/cospectral_family_cone_lift.py
```

Case C11: the last line must read `21 of 21 checks passed`. The three programs are stages of
`scripts/run_all.sh` and steps of the workflow *Case C3 for every number of qubits*
(`.github/workflows/c3-all-qubits.yml`; corrected on 10 November 2026, the first statement named the
workflow *Saturated configurations*).

```bash
python scripts/c3_sparse_search.py 3 3
```

The search of Remark 4 for four qubits, a few seconds; `3 4` is the five-qubit search, about fifteen
minutes.

## Scope

* Theorem 17 settles case C3 for every $N \ge 4$ and, with [J3, Lemma D (D2)], case C11 for every
  $N \ge 4$. The other vertex cases that [J3] leaves without a proof (C5, C8, C12, C14, C15) are not
  touched; C14 would follow from C5 by the same lemma.
* It shows that the completion spectra differ. It does not determine the least number of outside
  contexts violated by a completion, for either carrier.
* The framework of carriers and completions, the classification into cases, the block decomposition,
  the identification of the completion matrix with $`M \mapsto \tfrac12 (CM + MD)`$, the cone lift and the
  conjecture are Jonah's [J3]. New here are the graph construction of Steps 2 to 4 and the resulting
  families of pairs.
* Novelty is claimed only to the extent of a bounded search. On 10 November 2026 the source had the
  single version 0.5, which reports case C3 as open for $N \ge 4$; searches of Zenodo, arXiv, OpenAlex,
  DataCite, GitHub and the open web for the conjecture, the case, the construction and the numbers of
  the tables found no other treatment of case C3 for $N \ge 4$. Full texts were searched only for
  [J3] and its companion note; unpublished work, in particular by the author of [J3], cannot be
  excluded.

## Review record

On 10 November 2026, before publication, the addendum, its programs and the Lean file were examined by
separate automated passes: instances of the same AI system that wrote them (Claude), each started
without the others' work and with one task. This is an internal check. It is not peer review.

| pass | task | outcome |
|---|---|---|
| proof | re-derive Steps 1 to 6; rebuild the carriers for $N = 3, \dots, 6$ from the text alone, without the programs of the repository | no error found; every number of the tables reproduced |
| sources | read [J3] in full; compare definitions, attributions and scope | no error in the theorem; the result also settles case C11; credits were incomplete |
| programs, twice | read the programs line by line; mutation tests; independent recounts, among them the five-qubit search | no vacuous check; one description promised more than its test |
| prior art | 54 queries on Zenodo, arXiv, OpenAlex, DataCite, GitHub and the web | nothing found; limits as stated under Scope |
| Lean, Parts 1 to 6 | statements fixed in advance and tested numerically; proofs written by separate passes; separate audits of changed statements, axioms and fidelity to the mathematics | no statement changed; the definition of the completion matrix by traces was not tied to the contexts |
| Lean, Part 7 | statements fixed in advance and tested numerically for 3 and 4 qubits; proofs written by separate passes; the separate audit did not complete, so the check was a comparison of all 83 statement paragraphs with the final file and the axiom list of all 74 audited declarations | no statement changed; standard axioms only |

Every finding of the review of the addendum and its programs rated critical or major was tested
again by a further pass before it was accepted. What changed in response:

1. Case C11 follows by the cone lift of [J3]: Corollary 18 and the program
   `scripts/cospectral_family_cone_lift.py` were added, and the statements on the open cases corrected.
2. The four checks on random graphs "on the blocks" use the trace formula of Step 5 and do not test
   it. They are now described as such, and the same test on complete configurations for random graphs,
   and two negative controls, were added.
3. Parts 1 to 6 of the Lean file define the completion matrix by normalised traces. Part 7 was added:
   it states the theorem with the contexts and signs of the library and proves that the two
   definitions agree.
4. Smaller points: Remark 2 for carriers with $-1$ at the polar point; the definition of a context in
   the Setting; the credit for Step 5, the block decomposition and the three-qubit pairs to [J3]; the
   label convention of the data files; the wording of Remark 4, and the lookup of the pair of
   Section 8 by the search program; the description of the second program.

## Text proposed for the next revision of the combined paper

* Abstract, Section 1.1 and Section 8.1: the four-qubit certificate is one instance; the strict law
  fails on sign carriers in case C3 for every $N \ge 4$ (Theorem 17), by an explicit family, and in
  case C11 for every $N \ge 4$ (Corollary 18).
* Section 8: add Theorem 17 with its proof and Corollary 18 after the four-qubit statement, and
  Remark 2 next to equation (C8).
* Section 9.2 and the claim map (`docs/CLAIMS.md`): the Lean statement `c3_strict_law_fails_general`
  and its scope, as under "Formal verification" above.
* Section 12: replace "settles only the four-qubit instance" by the statement that cases C3 and C11
  are settled, while C5, C8, C12, C14 and C15 and all completion optima remain open.

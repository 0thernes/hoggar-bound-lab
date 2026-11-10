# Addendum: Conjecture E holds in all nine vertex cases

**Folded into the combined paper, version 1.3.0 (10 November 2026), Section 8.7 (Theorem 19).** This file keeps
the result as first stated.

**Status.** Originally proposed addition for the next revision of the combined paper
([paper/unified-contextuality.md](../paper/unified-contextuality.md)), after
[ADDENDUM-c3-all-qubits.md](ADDENDUM-c3-all-qubits.md) (Theorem 17, case C3). Release `v1.2.0` is not
changed by this file. Obtained on 10 November 2026 by the Claude (Anthropic) line of work, under the
direction of Alexander S. Donahue, 0thernes LLC.

* **Proof.** Below. It uses two results of the source: the restriction lemma and the graded law
  ([J3, Theorems A and B3]). For case C8 it also uses the identification of [J3, Remark 2].
* **Exact computation.** [scripts/conjecture_e.py](../scripts/conjecture_e.py) builds each case at
  $n = 4$ and $n = 5$ from the definitions of [J3]: the configuration, the hyperplane, the section,
  the outside lines and their signs. It checks the type of the case and both claims in exact
  arithmetic. It does the same at $n = 3$ for the four cases that already fail there (81 checks;
  [results/conjecture_e.json](../results/conjecture_e.json)).
* **Lean.** Only case C3 is a Lean theorem (`c3_strict_law_fails_general`,
  [lean/HoggarBound/CarrierFamily.lean](../lean/HoggarBound/CarrierFamily.lean)). The other eight
  cases are not formalized.
* Not peer reviewed.

## The statement

[J3] is B. W. Jonah, *The reach of the section-square law*, version 0.5,
[doi:10.5281/zenodo.23524332](https://doi.org/10.5281/zenodo.23524332). Its Theorem B4 lists sixteen
hyperplane cases. Nine of them have a section with a vertex: C1, C3, C5, C6, C8, C11, C12, C14, C15.
For real carriers the strict law fails in all nine [J3, Theorem B2]. For sign carriers, that is
carriers with values $\pm 1$, the note proves failure in C1 and C6 for every $n \ge 3$ by a
computer-assisted base case and a lifting lemma [J3, Corollary 3]. It reports exact pairs for some
of the other cases at $n = 4$ and $n = 5$, finds the strict law true for all sign carriers in C5,
C8, C12, C14 and C15 at $n = 3$, and conjectures:

> **Conjecture E** [J3, Section 6]. On sign carriers the strict law fails in every vertex case for every $n \ge 4$.

Case C3 was settled for every $n \ge 4$ by Theorem 17, and C11 by Corollary 18.

**Theorem 19.** Conjecture E is true. In each of the nine vertex cases and for every $n \ge 4$
there are two sign carriers $\sigma$, $\tau$ on the section whose carrier operators have the same
characteristic polynomial and whose completion matrices have different cubic traces, hence
different spectra. In C1, C3, C6 and C11 this also holds for $n = 3$.

The carriers are explicit and of three kinds:

| cases | construction | difference $`\operatorname{tr}\Lambda_\sigma^3 - \operatorname{tr}\Lambda_\tau^3`$ |
|---|---|---|
| C1, C3, C5 | graphs over $\mathbb{C}$, $\mathbb{R}$, $\mathbb{H}$; a component of the graph moves from the block $P_d = +1$ to the block $P_d = -1$ | $`-3\kappa\, 4^{n-1}\, r`$ |
| C12, C15 | the complex graph on $n - 2$ qubits; a component moves from the block $P_e = +1$ to the block $P_e = -1$ | $`6 \cdot 4^{n-2}\, r`$ |
| C6, C11, C14 | the pair swap: all base observables move from one coupled pair to the other | $`-24\kappa\, 4^{n-2}\, \lvert Y_0 \rvert`$ |
| C8 | C1 on $n - 1$ qubits, through the identification of [J3, Remark 2] | that of C1 on $n - 1$ qubits |

Here $\kappa = 2$ for the complex cases C1 and C6 and $\kappa = 1$ otherwise; $r$ is the number of
section points at which $\sigma$ and $\tau$ differ in the first two rows, a positive number; and
$\lvert Y_0 \rvert$ is the number of points of the base of the cone, which is positive for
$n \ge 4$.

## Conventions

As in [J3]: a point $v = (x \mid z)$ of $`\mathbb{F}_2^{2n}`$ is the Pauli word with factor $I$, $X$,
$Z$, $Y = iXZ$ on qubit $q$ for $(x_q, z_q) = (0,0), (1,0), (0,1), (1,1)$; $`q_0(v) = \lvert x \wedge z \rvert`$
mod 2; $B$ is the symplectic form; $`q_c = q_0 + B(c, \cdot)`$; $`Q_c = \{v \ne 0 : q_c(v) = 0\}`$ is
hyperbolic for $q_0(c) = 0$ and elliptic for $q_0(c) = 1$. For a line $`L = \{s, p, q\}`$,
$`P_s P_p P_q = s_L I`$. For a section $S = X \cap d^\perp$ and $O = X \setminus S$, the carrier operator is
$`A_\sigma = \sum_{s \in S} \sigma(s) P_s`$ and the completion matrix $`\Lambda_\sigma`$ has the entry
$`s_L\, \sigma(s)`$ at $(p, q)$ for each outside line $`\{s, p, q\}`$ with $s \in S$. On a block of
$m$ qubits the observable $`P_{a,c} = i^{\lvert a \wedge c \rvert} X^a Z^c`$ acts by
$`X^a Z^c \lvert b \rangle = (-1)^{c \cdot b} \lvert b + a \rangle`$, vectors of $`\mathbb{F}_2^m`$ written as
integers. In the data files a point $(x \mid z)$ has the label $x + 2^n z$.

Two facts from [J3, Theorem B3] are used. Let $\chi$ run over the joint eigenspaces of the central
Paulis of the case, $`A_\chi`$ the block of $`A_\sigma`$ on $`E_\chi`$, and let a coupled pair be two
eigenspaces that differ only in the eigenvalue of $P_d$.

1. **Preserved pairs.** A pair preserved by the antiunitary $\theta$, or a case with no $\theta$
   (C1, C3, C5, C6, C11, C14):
   $`\Lambda_\sigma`$ restricted to the pair is the operator $`M \mapsto \tfrac12 (A_\chi M + M A_{\chi'})`$ on
   a real space that is $\kappa$ copies of a real form of the complex matrices between the two
   eigenspaces. Hence, with $k$ the common dimension of the two eigenspaces,

   ```math
   \operatorname{tr} \Lambda^3 \big|_{\text{pair}} = \tfrac{\kappa}{8}\big(k\operatorname{tr} A_\chi^3 + 3\operatorname{tr} A_\chi^2 \operatorname{tr} A_{\chi'}
     + 3\operatorname{tr} A_\chi \operatorname{tr} A_{\chi'}^2 + k\operatorname{tr} A_{\chi'}^3\big) . \tag{T1}
   ```

2. **Swapped pairs.** A pair swapped by $\theta$ (C12, C15): the block on one $P_e$-eigenspace is
   $`A' \oplus \bar A'`$ for a Hermitian $A'$ of size $k$ with spectrum $\mu$ (the Jordan spectrum). The
   completion restricted to it has the eigenvalues $`\tfrac12(\mu_i + \mu_j)`$ for $i \le j$ (C12) or $i \lt j$
   (C15), each twice. Hence, with $`p_j = \operatorname{tr} A'^j`$,

   ```math
   \operatorname{tr} \Lambda^3 \big|_{\text{block}} = \tfrac14 \big( (k \pm 4)\, p_3 + 3\, p_1 p_2 \big),
   \qquad + \text{ for C12},\; - \text{ for C15}. \tag{T2}
   ```

For a sign carrier the blocks are signed sums of block observables, each block observable sits in
one block of a coupled pair with coefficient $\pm 2$ (or, in a cone, in one block with $\pm 4$), and
Pauli orthogonality gives $`\operatorname{tr} A_\chi^2 = k\,(\gamma^2 + 4 r_\chi)`$, where $\gamma$ is the
constant term and $`r_\chi`$ the number of block observables carried by $`A_\chi`$ (coefficient $\pm 2$).

## The base cases C1, C3, C5: graphs over R, C and H

Put $d = Z$ on qubit $n - 1$ and let qubits $0, \dots, n-2$ form the block; then
$`S = \{d\} \cup \{I \otimes P,\; Z \otimes P : P \in R\}`$ with $R$ the block observables in $X$, and
$`A_\sigma = C \oplus D`$ with

```math
C = \sigma(d) + \sum_{P \in R} \big(\sigma(I \otimes P) + \sigma(Z \otimes P)\big) P, \qquad
D = -\sigma(d) + \sum_{P \in R} \big(\sigma(I \otimes P) - \sigma(Z \otimes P)\big) P .
```

* **C3** ($X = Q^+$, $c = 0$): $R$ is the real observables, $a \cdot c$ even. This is Theorem 17.
* **C1** ($X = W$): $R$ is all observables. For $a \ne 0$ and $a \cdot c$ odd, put
  $`\varepsilon(P_{a,c}) = (-1)^{c \cdot u_a} (-1)^{(\lvert a \wedge c\rvert - 1)/2}`$, so that
  $`\varepsilon(P_{a,c}) P_{a,c} = (-1)^{c \cdot u_a}\, i X^a Z^c`$; on the observables with $a \cdot c$ even
  keep the signs of Theorem 17. The character sum over the affine hyperplane
  $`\{c : a \cdot c = 1\}`$ gives

  ```math
  \sum_{c \,:\, a \cdot c \text{ odd}} (-1)^{c \cdot u}\, X^a Z^c = \tfrac{N}{2} \big( \lvert u + a\rangle\langle u \rvert - \lvert u \rangle\langle u + a \rvert \big),
  \qquad N = 2^{n-1},
  ```

  an antisymmetric edge $J$. So with every observable in $C$ (all $\sigma(I\otimes P) = \sigma(Z \otimes P)$,
  $\sigma(d) = 1$),

  ```math
  C = -I + 2N \lvert t \rangle\langle t \rvert + N \sum_{a \ne 0} \big( E_a + i J_a \big), \qquad D = -I,
  ```

  a Hermitian weighted graph with a real edge $E_a$ and an imaginary edge $iJ_a$ for each direction
  $a$, both on the pair $`\{u_a, u_a + a\}`$.
* **C5** ($X = Q_c$ with $c = Y$ on qubit 0, which makes $Q_c$ elliptic and $q_c(d) = 0$): qubit 0 of
  the block carries the quaternionic structure and qubits $1, \dots, n-2$ carry the graph, on
  $N' = 2^{n-2}$ vertices. $R$ consists of $I \otimes P''$ with $P''$ real and of $\sigma_k \otimes P''$ with
  $`k \in \{X, Y, Z\}`$ and $P''$ imaginary. With the signs above,

  ```math
  C = -I + 2N'\, I \otimes \lvert t \rangle\langle t \rvert + N' \sum_{a \ne 0} \Big( I \otimes E_a + \sum_{k} \sigma_k \otimes i J_a \Big), \qquad D = -I,
  ```

  a quaternion-Hermitian graph with four edges for each direction (units $1$, $i$, $j$, $k$).

In each case the observables of one direction and one edge type form a *unit* of $N/2$ (or
$N'/2$) observables, and moving a unit to $D$ means $\tau(Z \otimes P) = -\sigma(Z \otimes P)$ on it. The
proof of Theorem 17 now applies word for word.

* **Step 4.** If the moved units are the edges of a union $F$ of connected components that does
  not contain $t$, then the blocks are $`(M_1 \oplus M_2,\, 0)`$ and $`(M_1 \oplus 0,\, 0 \oplus M_2)`$ in units
  of $N$ after adding $I$, on a splitting of the vertex set that every edge respects. So
  $`\operatorname{spec} A_\sigma = \operatorname{spec} A_\tau`$.
* **Step 6.** By (T1), with $\operatorname{tr} C = k$, $\operatorname{tr} D = -k$ and $k = 2^{n-1}$,
  $`\operatorname{tr}\Lambda^3 = \tfrac{\kappa k}{8}\operatorname{tr} A^3 + \text{const} + 3\kappa k^2\, r_D`$. So
  $`\operatorname{tr}\Lambda_\sigma^3 - \operatorname{tr}\Lambda_\tau^3 = -3\kappa k^2\, r_D(\tau)`$, which is negative.

For $n - 1 \ge 3$ graph qubits take the graph of Theorem 17 ($u_1 = 0$, $u_2 = u_3 = 4$, $u_a = 2$
otherwise, $t = 2$) for every edge type, and move the units of direction $1$. With two graph qubits
take the triangle $`\{0, 1, 3\}`$ ($u_1 = 0$, $u_2 = 1$, $u_3 = 0$, $t = 2$) and move everything. This
gives C1 and C3 for $n \ge 3$ and C5 for $n \ge 4$, since C5 has one graph qubit fewer. With a single
graph qubit every edge contains $t$, which agrees with the strict law holding in C5 at $n = 3$.

## C12 and C15: the complex graph between the two P_e-blocks

Put $e = Z$ on qubit $n-1$, $d = Y$ on qubit $n-2$, and let qubits $0, \dots, n-3$ form the base. For
C12, $X = Q^+ \cap e^\perp$; for C15, $X = Q_c \cap e^\perp$ with $c = Y$ on base qubit 0. In both,
$q(e) = 0$, $d \in e^\perp$ and $q(d) = 1$. The section is

```math
S = \{e\} \cup \{ Z_e^{\,a}\, Y_d^{\,b(w)} \otimes w : a \in \{0,1\},\; w \ne 0 \text{ a base observable} \},
```

with $b(w) = q_c(w)$ fixed by $w$. Every non-identity base Pauli occurs. On the eigenspace
$Z_e = s$, $Y_d = +1$ the carrier operator acts as the Jordan block

```math
A'_s = s\,\sigma(e) + \sum_{w} \big( \sigma(I \otimes w) + s\, \sigma(Z_e \otimes w) \big) P_w ,
```

and on $Y_d = -1$ as its conjugate by $\theta$ ([J3, equation (1)]), with the same spectrum. These
are the complex blocks of C1, on $n - 2$ qubits. Take the complex graph signs on the base and
$\sigma(e) = 1$, every observable in the block $s = +1$. Then $`A'_+ = -I + 2N_b \lvert t\rangle\langle t \rvert + N_b H`$
and $`A'_- = -I`$ with $N_b = 2^{n-2}$, because the observables with $a = 0$ contribute $-2I$ to
$`A'_+`$. Moving the units of a component $F$ away from $t$ to the block $s = -1$ gives
$`A'_+ = -I + 2N_b\lvert t\rangle\langle t\rvert + N_b H_{G - F}`$ and $`A'_- = -I + N_b H_F`$. The union of the two
Jordan spectra is unchanged, so $`\operatorname{spec} A_\sigma = \operatorname{spec} A_\tau`$. In (T2),
$`p_1(A'_\pm) = \pm N_b`$ for both carriers, and $`p_2(A'_+) + p_2(A'_-)`$ and $`p_3(A'_+) + p_3(A'_-)`$ are
fixed by the carrier spectrum. Only $`p_2(A'_-)`$ changes, from $N_b$ to $N_b + 2N_b^2\lvert F \rvert$, so

```math
\operatorname{tr}\Lambda_\sigma^3 - \operatorname{tr}\Lambda_\tau^3 = 3 N_b^3 \lvert F \rvert = 6 N_b^2\, r > 0
```

in both cases. The graph needs at least two base qubits, so $n \ge 4$; with one base qubit
every edge contains $t$, which agrees with the strict law holding in C12 and C15 at $n = 3$.

## C6, C11, C14: the pair swap

Let $X$ be the cone over $`Y \in \{W, Q^+, Q^-\}`$ on $n - 1$ qubits with vertex $e = Z$ on qubit
$n-1$, and $d = Z$ on qubit $n - 2$ (C6, C11, C14 respectively; for C14, $c = Y$ on qubit 0). Then

```math
S = \{e, d, e + d\} \cup \{ Z_e^{\,t} Z_d^{\,b} \otimes w : t, b \in \{0,1\},\; w \in Y_0 \},
```

where $Y_0$ is the base, a nondegenerate $W$, $Q^+$ or $Q^-$ on the remaining $n - 2$ qubits. Put
$\sigma = \tau = 1$ on $e$, $d$, $e + d$ and, at $Z_e^t Z_d^b \otimes w$,

```math
\sigma = (-1)^{t + b}, \qquad \tau = (-1)^{b} .
```

The blocks on $(Z_e, Z_d) = (\pm, \pm)$ have constant terms $3, -1, -1, -1$ for $(+,+), (+,-), (-,+), (-,-)$.
Under $\sigma$ every base observable sits in the block $(-,-)$ with coefficient $4$; under $\tau$ in
the block $(+,-)$. Both blocks have the constant $-1$. So $`A_\tau`$ is $`A_\sigma`$ with the two blocks
exchanged, that is, $`A_\tau = U A_\sigma U^{\dagger}`$ for the controlled-NOT $U$ that flips $Z_e$ when $Z_d = -1$.
The coupled pairs are $`\{(+,+), (+,-)\}`$ and $`\{(-,+), (-,-)\}`$, so the base moves from one pair to the
other. With $`G = \sum_{w \in Y_0} P_w`$, $k = 2^{n-2}$ and (T1),

```math
\operatorname{tr}\Lambda_\sigma^3 - \operatorname{tr}\Lambda_\tau^3
 = \kappa k \sum_{g \in \operatorname{spec} G} \big( (-1 + 2g)^3 - (1 + 2g)^3 \big) + 2\kappa k^2
 = -24\,\kappa\, k \operatorname{tr} G^2 = -24\,\kappa\, k^2 \lvert Y_0 \rvert .
```

This is negative as soon as the base is not empty: for every $n \ge 3$ in C6 and C11, and for every
$n \ge 4$ in C14. At $n = 3$ the base of C14 is the empty elliptic quadric $Q^-(1, 2)$, which
agrees with the strict law holding there. The construction does not use Theorem 17. As a second
check, the cone lifts [J3, Lemma D (D2)] of the pairs of C1, C3, C5 on $n - 1$ qubits are verified
too.

## C8: through C1

Let $X = Q^+ \cap e^\perp$ with the nucleus $e = Y$ on qubit $n-1$, and $d = r = Z$ on qubit $n-2$. Every
point of $X$ is $P' \otimes I$ with $P'$ real or $P' \otimes Y$ with $P'$ imaginary, for a unique non-identity
Pauli $P'$ on qubits $0, \dots, n-2$. Two points commute exactly when their $P'$ do. On every line the
factors $Y$ occur an even number of times, so the line signs are those of $W(2n-3, 2)$. On the
eigenspace $Y = +1$ the carrier operator is the carrier operator of $W(2n-3, 2)$ for the transported
carrier; on $Y = -1$ it is its complex conjugate. So $`\operatorname{spec} A_\sigma`$ is twice the C1 spectrum
on $n - 1$ qubits, and $`\Lambda_\sigma`$ is the C1 completion matrix on $n - 1$ qubits. This is
[J3, Remark 2] made explicit. The C1 pairs on $n - 1 \ge 3$ qubits therefore give C8 for every
$n \ge 4$.

$\blacksquare$ *(Theorem 19)*

## Remarks

1. The constructions need $n \ge 4$ exactly in the five cases C5, C8, C12, C14 and C15, in which
   [J3] finds the strict law true for all sign carriers at $n = 3$ by exhaustive computation.
2. For C1 and C6 the theorem gives an explicit proof, without computer search, of [J3, Corollary 3].
   The base pairs of that corollary are in a data set that is not public.
3. In the cone cases the two carriers differ by flipping the sign on $e$ times the base, and the
   carrier operators are conjugate by a controlled-NOT. That gate maps $d^\perp$ to a different
   hyperplane, so it does not preserve the completion problem.

## The numbers

Exact values from `scripts/conjecture_e.py` (the pair of the table in each case):

| case | $n$ | section, outside, outside lines | $`\operatorname{tr}\Lambda_\sigma^3`$, $`\operatorname{tr}\Lambda_\tau^3`$ | difference |
|---|---|---|---|---|
| C1 | 3 | 31, 32, 240 | $-192$, 960 | $-1152$ |
| C1 | 4 | 127, 128, 4032 | 57600, 60672 | $-3072$ |
| C1 | 5 | 511, 512, 65280 | 2491392, 2515968 | $-24576$ |
| C3 | 3 | 19, 16, 72 | 0, 288 | $-288$ |
| C3 | 4 | 71, 64, 1120 | 15744, 16512 | $-768$ |
| C3 | 5 | 271, 256, 17280 | 649728, 655872 | $-6144$ |
| C5 | 4 | 55, 64, 864 | $-1152$, 3456 | $-4608$ |
| C5 | 5 | 239, 256, 15232 | 219648, 231936 | $-12288$ |
| C6 | 3 | 15, 16, 56 | $-288$, 288 | $-576$ |
| C6 | 4 | 63, 64, 992 | 8064, 19584 | $-11520$ |
| C6 | 5 | 255, 256, 16256 | 732672, 926208 | $-193536$ |
| C8 | 4 | 31, 32, 240 | $-192$, 960 | $-1152$ |
| C8 | 5 | 127, 128, 4032 | 57600, 60672 | $-3072$ |
| C11 | 3 | 11, 8, 20 | $-96$, 96 | $-192$ |
| C11 | 4 | 39, 32, 304 | 1344, 4800 | $-3456$ |
| C11 | 5 | 143, 128, 4544 | 129792, 183552 | $-53760$ |
| C12 | 4 | 31, 40, 380 | 1776, 624 | 1152 |
| C12 | 5 | 127, 144, 5112 | 116640, 113568 | 3072 |
| C14 | 4 | 23, 32, 176 | $-960$, 960 | $-1920$ |
| C14 | 5 | 111, 128, 3520 | 37632, 79104 | $-41472$ |
| C15 | 4 | 31, 24, 132 | 720, $-432$ | 1152 |
| C15 | 5 | 127, 112, 3080 | 46944, 43872 | 3072 |

Every difference equals the formula of its row in the first table.

## How to check

```bash
python scripts/conjecture_e.py
```

The last line must read `81 of 81 checks passed` (about ten seconds). For each case and each
$`n \in \{4, 5\}`$, and for C1, C3, C6 and C11 also $n = 3$, the program checks three things.

1. The case. It checks the type of the quadric and of $e$ and $d$ as in [J3, Table 1], and that the
   vertex set of the section is the one in the table.
2. The carrier spectra. The power sums $\operatorname{tr} A^k$, $k = 1, \dots, 2^n$, are equal, with
   Python integers on Gaussian-integer matrices.
3. The completion. The completion matrices are built from all outside lines, with the signs
   $s_L$ checked against products of three matrices for $n = 4$. Their cubic traces must differ.

It does the cone cases twice, by the pair swap and by the cone lift. Arguments `4 5 6` add $n = 6$,
which is slower. NumPy is needed; no floating point enters a comparison of characteristic
polynomials, and the integer entries of the completion matrices are far below $2^{53}$.

## Scope

* Theorem 19 is a statement about sign carriers in the nine vertex cases of [J3]. The completion
  optima are not touched. Neither are the seven cases without a vertex, where the strict law holds
  [J3, Theorem B1].
* The proof uses [J3, Theorems A and B3] for the block structure of the carrier operator and the
  spectrum of the completion on a coupled pair, and [J3, Remark 2] for C8. Case C3 alone is proved
  in Lean, without these results (Theorem 17). For the other cases the general proof is on paper and
  the instances $n = 4, 5$ are checked by exact computation.
* The framework, the classification and the conjecture are Jonah's. New here: the graph
  constructions over $\mathbb{R}$, $\mathbb{C}$ and $\mathbb{H}$, their transfer to C12 and C15, the pair swap
  for the cones, and the resulting proof of the conjecture.
* Novelty is claimed only to the extent of the bounded search recorded in the C3 addendum. On
  10 November 2026 the source had the single version 0.5, and no other treatment of the conjecture
  was found. Unpublished work by the author of [J3] cannot be excluded.

# A machine-checked spectral floor for Pauli contextuality

**Lean 4 formalization for every number of qubits, an independent reproduction of the October 2026 results, and an end-to-end demonstration on the Tsotchke stack**

0thernes (Alexander S. Donahue), 0thernes LLC, with Claude (Anthropic) as AI research system<br>
Hoggar Bound Lab, version 1.0, 9 November 2026. Research preprint. Not peer reviewed.

> **Priority note.** The inequality formalized here was first posted by B. W. Jonah on 21 October 2026
> (Zenodo, [doi:10.5281/zenodo.23538829](https://doi.org/10.5281/zenodo.23538829)), where it is called the
> *spectral lower bound* or *spectral floor*. We derived it independently on 9 November 2026 and learned of the
> earlier notes the same day, during our own literature audit. Priority for the bound, for its saturation
> by Hoggar-type states, and for the exact four- and five-qubit values belongs to the works cited in
> Section 1.2. What is new here is stated in Section 1.1.

## Abstract

For $N$ qubits, a noncontextual hidden-variable model assigns a value $\pm 1$ to every Pauli observable.
Quantum mechanics fixes the sign of the product of any three mutually commuting Pauli observables whose
product is $\pm I$ (a *context*), and no assignment can reproduce all of these signs. The *contextuality
degree* is the least number of contexts an assignment must get wrong. We give a complete, kernel-checked
Lean 4 proof (Lean 4.35, Mathlib; no axioms beyond the standard three) of the spectral floor: for every
$N \ge 1$, every set $S$ of non-identity $N$-qubit Pauli observables with all of its induced contexts, and
every assignment, the number of satisfied minus violated contexts is at most
$`(D-2)\,|S|^{3/2} / (6\sqrt{D-1})`$, where $D = 2^N$. The formal development works with the explicit
$2^N \times 2^N$ complex Pauli matrices and derives the context signs from matrix multiplication. Checked
corollaries: every assignment violates at least the fraction $1/2 - \sqrt{D+1}/(D+2)$ of all contexts
of the full $N$-qubit Pauli configuration, for every $N$; at least 63 of 315 contexts for three qubits
(the known exact value); at least 1451 of 5355 for four qubits; at least 28786 of 86955 for five qubits;
at least 315 of 1575 on the four-qubit hyperbolic quadric (the known exact value); and at least 6426 of
23715 on the five-qubit hyperbolic quadric. The last statement is, to our knowledge, the first formally
verified proof that the degree of $Q^+(9,2)$ is not $4743$, a question raised by Li, Gupta and Ganesh
and first answered, with computer assistance, by Jonah. We also reproduce the best known assignments
for two to five qubits with an independent search, confirm the geometry of their violated contexts, and
run the corresponding state-independent contextuality test end to end on Tsotchke's Moonlab simulator,
with the quantum geometric tensor kernels of QGTL, the quantum_rng generator and the Eshkol language
as independent components. Every numerical claim is a test that can fail; the repository contains the
tests, a negative control and the Lean sources.

## 1. Scope

### 1.1 What is new in this work

1. **A formal proof.** The spectral floor is proved in Lean 4 for every number of qubits $N \ge 1$ and
   for *arbitrary* sets of observables with their induced contexts (theorem `hoggar_bound`). The proof
   is about the actual matrices: Pauli operators are defined as explicit complex matrices indexed by bit
   vectors, their product phases and commutation rule are theorems, and the bound is derived from the
   spectral theorem. Earlier accounts of the bound are explicitly not formally verified [J2], and the
   earlier Lean development of Li, Gupta and Ganesh [LGG] covers one four-qubit configuration by a
   different (combinatorial) argument.
2. **Formally verified numerical corollaries**, listed in the abstract and in Table 2, including formal
   answers to two questions asked in [LGG]: the degree of $Q^+(9,2)$ exceeds $4743$, and the violated
   fraction of the four-qubit full space and of the five-qubit hyperbolic quadric is strictly above $1/5$.
3. **A statement for arbitrary observable sets.** The published statements of the floor concern
   line-closed families (the full space and the quadrics). The trace argument needs no closure
   hypothesis, and the Lean theorem has none.
4. **Consequences spelled out for all $N$**: an exponentially growing quantum-to-classical ratio with
   a proof (the 2010 argument for such growth rests on a lemma that fails at three qubits), a noise
   threshold that tends to zero, a two-sided estimate of the optimal violated fraction (Proposition 4),
   and a reading of violated contexts in terms of the quantum geometric tensor (Proposition 3).
5. **An independent reproduction and a running demonstration**: a search engine, four independent
   implementations of the geometry (C, Python, JavaScript, Eshkol) and the Lean model agree on every
   count; the experiment runs on the Tsotchke stack with each component labelled for what it is.

### 1.2 What is not new, and whose it is

* The contextuality degree and its first values: de Boutray, Holweck, Giorgetti, Masson and Saniga
  [dB]; Muller, Saniga, Giorgetti, de Boutray and Holweck [M1] (three-qubit degree 63, the split Cayley
  hexagon of violated contexts); Muller, Saniga, Giorgetti, Holweck and Kelleher [M2] (upper bounds
  for four to seven qubits, lower bound $L/5$); Saniga et al. [S] (hexagons).
* The exact value $315$ for the four-qubit hyperbolic quadric, its 240 optimal sets and a Lean proof of
  that value: Li, Gupta and Ganesh [LGG].
* The exact values $d(Q^-(7,2)) = 315$, $d(W(7,2)) = 1575$, $d(Q^+(9,2)) = 6975$ (computer-assisted),
  the operator $A = \sum_v f(v) P_v$ and its Hoggar spectrum $`\{21, -3^7\}`$: Jonah [J1].
* The spectral floor itself, its Kramers (quaternionic) form for elliptic quadrics, the description of
  quadrics by the antiunitaries $P_c K$, and the theorem that the floor is attained exactly for
  $W(5,2)$, $Q^+(7,2)$, $Q^-(5,2)$ (and trivially $`Q^-(3,2)`$): Jonah [J2], with the trace formula also
  in [J3]. Stronger five-qubit lower bounds ($d(W(9,2)) \ge 28830$, $d(Q^-(9,2)) \ge 6510$) are
  announced, with proofs held privately, in [J4].
* The scalar inequality behind the floor is classical: it is Okumura's lemma [O] (equivalently the
  maximal sample skewness, Wilkins [W]).
* The Hoggar lines and the cubic purity condition for quantum states: Hoggar [H], Stacey [St],
  Jones and Linden [JL].

Our derivation in Sections 3 to 5 was made without knowledge of [J1]–[J4]; where it coincides with
them we say so. We did not re-run the exhaustive computations behind the exact values of [J1] and do
not vouch for them; we only observe that every assignment we found is consistent with them.

## 2. Setting

**Pauli operators.** Let $D = 2^N$. A *point* is a nonzero vector $v = (a \mid c) \in \mathbb{F}_2^{2N}$.
It labels the Hermitian operator

```math
P_v \;=\; i^{\,|a \wedge c|}\, X^{a} Z^{c},
```

a tensor product of $I, X, Y, Z$ (the exponent $|a \wedge c|$ counts the factors equal to $Y = iXZ$).
$P_0 = I$, $P_v^2 = I$, and $\operatorname{tr} P_v = 0$ for $v \ne 0$. Products close up to a phase,

```math
P_u P_v = \tau(u,v)\, P_{u+v}, \qquad
\tau(u,v) = i^{\,k_u + k_v + 3 k_{u+v}}\,(-1)^{c_u \cdot a_v}, \quad k_v = |a_v \wedge c_v| ,
```

and with the symplectic form $\langle u, v\rangle = c_u\cdot a_v + c_v \cdot a_u$ one has
$\tau(v,u) = (-1)^{\langle u,v\rangle}\tau(u,v)$ and $\tau(u,v)^2 = (-1)^{\langle u,v\rangle}$.
So $P_u$ and $P_v$ commute exactly when $\langle u,v\rangle = 0$, and then $`\tau(u,v) = s(u,v) \in \{+1,-1\}`$.

**Contexts.** A *context* (a line of the symplectic polar space $`W(2N-1,2)`$) is a set
$`\ell = \{u, v, u+v\}`$ of three distinct points with $\langle u, v\rangle = 0$. Its three operators commute and
$`P_u P_v P_{u+v} = s_\ell\, I`$ with $s_\ell = s(u,v)$, which does not depend on the order.

**Configurations and assignments.** Fix a set $S$ of points and let $\mathcal{L}(S)$ be the set of all
contexts contained in $S$, $L_S = |\mathcal{L}(S)|$. An assignment $`f : S \to \{+1,-1\}`$ *violates*
$\ell$ when $f(u) f(v) f(u+v) \neq s_\ell$. Put

```math
\beta_S(f) = \sum_{\ell \in \mathcal{L}(S)} s_\ell\, f(u) f(v) f(u+v) = L_S - 2\,\mathrm{viol}(f),
\qquad d(S) = \min_f \mathrm{viol}(f).
```

$d(S)$ is the contextuality degree [dB]. For the noncontextuality inequality
$\chi = \sum_\ell s_\ell \langle P_u P_v P_{u+v}\rangle \le L_S - 2 d(S)$ quantum mechanics gives
$\chi = L_S$ in every state [C, LGG].

**Three families.** The *full space* is $`S = \mathbb{F}_2^{2N}\setminus\{0\}`$, with $D^2-1$ points
and $L = (D^2-1)(D^2-4)/12$ contexts. For $c \in \mathbb{F}_2^{2N}$ let $q_0(v) = |a\wedge c| \bmod 2$ and
$`Q_c = \{ v \ne 0 : q_0(v) + \langle c, v\rangle = 0\}`$. $Q_c$ is a *hyperbolic* quadric $Q^+(2N-1,2)$ if
$q_0(c) = 0$ and an *elliptic* quadric $Q^-(2N-1,2)$ if $q_0(c) = 1$. With $K$ complex conjugation in the
computational basis, $\theta_c = P_c K$ is antiunitary, $\theta_c P_v \theta_c^{-1} = (-1)^{q_0(v) + \langle c,v\rangle} P_v$
and $\theta_c^2 = (-1)^{q_0(c)}$. So the quadrics are the sets of Pauli observables fixed by a Pauli
antiunitary: a real structure ($\theta^2 = 1$) for hyperbolic quadrics and a quaternionic structure
($\theta^2 = -1$) for elliptic ones [J2]. $Q_0$ is the set of real symmetric Pauli matrices (an even
number of $Y$ factors).

## 3. The spectral floor

**Theorem 1 (spectral floor; Jonah [J2] for the three families; formalized here for arbitrary $S$).**
Let $N \ge 1$, let $S$ be any set of points and $`f : S \to \{\pm 1\}`$. Then

```math
\beta_S(f) \;\le\; \frac{(D-2)\,|S|^{3/2}}{6\sqrt{D-1}},
\qquad\text{hence}\qquad
d(S) \;\ge\; \frac{L_S}{2} - \frac{(D-2)\,|S|^{3/2}}{12\sqrt{D-1}} .
```

*Proof.* Let $A = \sum_{v \in S} f(v) P_v$, a Hermitian $D \times D$ matrix.

*(i) Three traces.* $\operatorname{tr} A = 0$ because $0 \notin S$. Since
$`\operatorname{tr}(P_u P_v) = D\,\delta_{uv}`$ and $f(v)^2 = 1$, $`\operatorname{tr} A^2 = D\,|S|`$. Since
$`\operatorname{tr}(P_u P_v P_w) = D\,\tau(u,v)\,[w = u+v]`$,

```math
\operatorname{tr} A^3 = D \sum_{\substack{u, v \in S \\ u+v \in S}} f(u) f(v) f(u+v)\, \tau(u,v).
```

The pairs with $\langle u,v\rangle = 1$ cancel against their transposes, because $\tau(v,u) = -\tau(u,v)$.
The pairs with $\langle u,v \rangle = 0$ are the ordered pairs of distinct points of a context
($u = v$ would give $u + v = 0 \notin S$), six for each context, each contributing $s_\ell f(u)f(v)f(u+v)$.
Therefore $`\operatorname{tr} A^3 = 6 D\, \beta_S(f)`$.

*(ii) A scalar inequality* (Okumura [O]). Let $x_1, \dots, x_n$ be real with $\sum x_i = 0$ and
$\sum x_i^2 = n m$, $n \ge 2$, and let $a = \sqrt{(n-1)m}$. By the Cauchy–Schwarz inequality applied to
the other $n-1$ numbers, $x_i^2 \le (n-1)(nm - x_i^2)$, so $x_i \le a$ for every $i$. Hence
$(x_i - a)\big((n-1)x_i + a\big)^2 \le 0$. Summing over $i$ and using the two constraints,

```math
(n-1) \sum_i x_i^3 \;\le\; n\, m\, (n-2)\, a .
```

*(iii) Conclusion.* Apply (ii) to the eigenvalues of $A$ with $n = D$, $m = |S|$:
$`(D-1) \cdot 6 D \beta \le D\,|S|\,(D-2)\sqrt{(D-1)|S|}`$. $\qquad\blacksquare$

Three remarks. First, no closure property of $S$ is used: products that leave $S$ do not contribute to
the trace. Second, the hypothesis $f = \pm 1$ enters only through $\operatorname{tr} A^2 = D|S|$, so the
argument bounds the cubic form $T(x) = \sum_\ell s_\ell x_u x_v x_w$ on the sphere $\sum x_v^2 = |S|$.
Third, the bound applies to the induced configuration only, that is, with *all* contexts contained
in $S$.

**Theorem 2 (quaternionic form; Jonah [J2]).** If every $P_v$, $v \in S$, commutes with an
antiunitary $\theta$ with $\theta^2 = -1$ (for instance, $S$ lies in an elliptic quadric), then

```math
\beta_S(f) \;\le\; \frac{(D-4)\,|S|^{3/2}}{6\sqrt{2(D-2)}} .
```

*Proof.* $A$ is a real combination of operators commuting with $\theta$, so $\theta A = A \theta$. If
$A x = \lambda x$ then $A\theta x = \lambda \theta x$, and $\langle x, \theta x\rangle = 0$ because
$\langle \theta x, \theta y\rangle = \overline{\langle x, y \rangle}$ gives
$\langle x, \theta x\rangle = \overline{\langle \theta x, \theta^2 x\rangle} = -\langle x, \theta x\rangle$.
Every eigenspace is therefore an orthogonal sum of planes $`\{x, \theta x\}`$ and every eigenvalue has even
multiplicity (Kramers). Apply (ii) to the $D/2$ distinct pair values, with the same $m$.
$\qquad\blacksquare$

Theorem 2 is not part of the Lean development; it is checked numerically (Section 9).

**Closed forms.** With the standard counts, Theorems 1 and 2 give for the three families the same
expression in different arguments. Writing $\varphi(D) = \tfrac12 - \sqrt{D+1}/(D+2)$,

| family | points | contexts $L$ | violated fraction at least |
|---|---|---|---|
| full space $W(2N-1,2)$ | $D^2-1$ | $(D^2-1)(D^2-4)/12$ | $\varphi(D)$ |
| elliptic quadric $Q^-(2N-1,2)$ | $(D+1)(D-2)/2$ | $(D+1)(D-2)(D+2)(D-4)/48$ | $\varphi(D)$ |
| hyperbolic quadric $Q^+(2N-1,2)$ | $(D-1)(D+2)/2$ | $(D-1)(D+2)(D-2)(D+4)/48$ | $\varphi(D/2)$ |

The three cases are the complex, quaternionic and real members of Dyson's threefold way; the real
family at $N$ qubits has the same floor as the complex family at $N-1$ qubits.

## 4. Saturation

**Theorem 3 (equality; Jonah [J2, Theorem 6]).** Equality holds in Theorem 1 if and only if there is a
unit vector $\psi$ with

```math
\langle \psi | P_v | \psi \rangle = f(v)\,\sqrt{\frac{D-1}{|S|}} \quad (v \in S), \qquad
\langle \psi | P_v | \psi \rangle = 0 \quad (v \notin S,\ v \ne 0).
```

*Proof.* Equality in (ii) forces $`x_i \in \{a, -a/(n-1)\}`$ for every $i$, and the zero sum forces exactly
one value $a$. So $`A = (a-b)\,|\psi\rangle\langle\psi| + b\,I`$ with $b = -a/(D-1)$; reading off Pauli
coefficients gives the claim, and the converse is the same computation backwards. $\qquad\blacksquare$

For the full space the condition says that $\psi$ is a fiducial vector of a SIC covariant under the
$N$-qubit Pauli group. Such vectors exist only for $N = 1$ and $N = 3$ (Godsil and Roy [GR]; an
elementary proof through the integrality of the floor is in [J2]): for $N = 3$ they are the Hoggar lines.

**The three saturated cases.** The Hoggar fiducial $\psi_H \propto (-1+2i, 1, 1, 1, 1, 1, 1, 1)$ has
$\langle P_v \rangle = \pm 1/3$ for all 63 three-qubit Pauli observables. We verified the following by
exact counting in four independent implementations (Section 9); the values themselves are known
[M1, dB, LGG, J2].

| configuration | assignment | violated | floor | spectrum of $A$ |
|---|---|---|---|---|
| $W(5,2)$: 63 points, 315 contexts | signs of $\langle\psi_H\vert P_v\vert \psi_H\rangle$ | 63 | 63 | $`\{21, (-3)^7\}`$ |
| $Q^-(5,2)$: 27 points, 45 contexts | the same signs, restricted | 9 | 9 | $`\{9^2, (-3)^6\}`$ |
| $Q^+(7,2)$: 135 points, 1575 contexts | signs of the realified $\psi_H \in \mathbb{R}^{16}$ | 315 | 315 | $`\{45, (-3)^{15}\}`$ |

In the third row, $\mathbb{C}^8$ is read as $\mathbb{R}^{16}$; the resulting real four-qubit state has
expectation $\pm 1/3$ on all 135 real Pauli observables and $0$ on the 120 imaginary ones (this
description of the optimal assignments of $Q^+(7,2)$ as sign patterns of real Pauli-flat states is
announced in [J4]). The violated contexts form, respectively, a classically embedded split Cayley
hexagon (63 lines, three per point, incidence graph of diameter 6 and girth 12, the three lines through
each point in one totally isotropic plane), nine pairwise disjoint lines, and a copy of the dual polar
space $DW(5,2)$ (315 lines, seven per point, collinearity graph distance-regular with intersection
array $`\{14,12,8;1,3,7\}`$), in agreement with [M1, S, M2, LGG].

By Theorem 3, the optimal assignments of $W(5,2)$ are exactly the sign patterns of Pauli-covariant SIC
fiducials in dimension 8. Our enumeration finds 120 optimal violated sets in the orbit of the Hoggar
pattern under $Sp(6,2)$, and the context–point incidence matrix has rank 56 over $\mathbb{F}_2$, so each
set comes from $2^7 = 128$ assignments: $120 \cdot 128 = 15360 = 240 \cdot 64$ assignments, matching the
240 Hoggar-type SICs of 64 vectors each [St]. For $Q^+(7,2)$ the orbit of our violated set under the
reflections of $O^+(8,2)$ has 240 elements, the number proved in [LGG].

**Proposition 3 (violated contexts in the quantum metric).** Let $\psi$ be a state, $p_v = \langle P_v\rangle$,
and let $Q_{uv} = \tfrac14\big(\langle P_u P_v\rangle - p_u p_v\big)$ be its quantum geometric tensor along
the flows $e^{-itP_v/2}$. For a context $`\{u, v, w\}`$ with sign $s$, the Fubini–Study metric is
$`g_{uv} = \tfrac14 (s\,p_w - p_u p_v)`$. If $f = \operatorname{sign}(p)$, the context is violated exactly when
$4|g_{uv}| = |p_w| + |p_u p_v|$ and satisfied exactly when $4|g_{uv}| = \big||p_w| - |p_u p_v|\big|$.

*Proof.* $`\langle P_uP_v\rangle = s\,p_w`$; the context is violated when $`s\,p_w`$ and $p_u p_v$ have opposite
signs. $\qquad\blacksquare$

For $\psi_H$: $g_{vv} = 2/9$; $|g_{uv}| = 1/9$ on the 189 commuting pairs lying on the 63 violated contexts,
$1/18$ on the 756 pairs lying on satisfied contexts, $1/36$ on the 1008 anticommuting pairs; the Berry
curvature has modulus $1/6$ on anticommuting pairs and vanishes on commuting ones. The hexagon is the
set of pairs of largest off-diagonal metric (computed with the QGTL kernels, Section 8).

## 5. Consequences for all $N$

**Corollary A (full space).** For every $N \ge 1$ every assignment of the $D^2 - 1$ Pauli observables
violates at least $`\varphi(D)\,L`$ contexts (Lean: `full_space_fraction`). Since a uniformly random
assignment violates $L/2$ contexts on average, $d/L \to 1/2$.

**Exponential violation.** The ratio of the quantum value to the noncontextual bound of the full
inequality satisfies $L/(L-2d) \ge (D+2)/(2\sqrt{D+1}) \sim 2^{N/2-1}$. Cabello [C] proposed this
inequality in 2010 and argued for exponential growth; his Lemma 3 identifies the bound with the number
of positive contexts, which is correct for two qubits but not for three, where 252 of the 315
predictions can be satisfied rather than 225 [M1]. Corollary A proves the growth.

**Noise.** If imperfections scale every correlator by a visibility $\eta$, the inequality is violated
when $\eta \gt 1 - 2d/L$, hence whenever $\eta \gt 2\sqrt{D+1}/(D+2)$: above $0.6$ for three qubits, $0.458$
for four, $0.338$ for five, $0.062$ for ten. In the notation of [C, MS] the tolerated error per context
$\varepsilon = 2d/L$ is at least $1 - 2\sqrt{D+1}/(D+2)$, which exceeds $0.707$ (the largest value
confirmed in the search of [MS], for configurations of a different kind) from six qubits on and tends
to $1$.

**Proposition 4 (the floor is sharp up to a logarithmic factor).** For every pure $N$-qubit state with
$M = \max_{v \ne 0} |\langle P_v \rangle|$ there is an assignment of the full space with

```math
\beta \;\ge\; \frac{(D-1)(D-2)}{6\,M^3}, \qquad\text{so}\qquad
\frac{1}{(D+1)(D+2)\,M_N^3} \;\le\; \frac12 - \frac{d}{L} \;\le\; \frac{\sqrt{D+1}}{D+2},
```

where $M_N$ is the least value of $M$ over all states. $M_N \ge 1/\sqrt{D+1}$, with equality exactly when a
Pauli-covariant SIC exists, and $M_N \le C\sqrt{\log D / D}$ for an absolute constant $C$.

*Proof.* A pure state has $\operatorname{tr}\rho^3 = 1$; with $\rho = D^{-1}(I + \sum_v p_v P_v)$ and
$\sum_{v\ne 0} p_v^2 = D-1$, the trace computation of Theorem 1 gives
$`T(p) = \sum_\ell s_\ell\, p_u p_v p_w = (D-1)(D-2)/6`$ (the cubic purity condition [JL, St]). Choose the
signs $f(v)$ independently with mean $p_v/M$. Then $`\mathbb{E}\,\beta(f) = T(p)/M^3`$, and some $f$ does at
least as well. The upper bound on $M_N$ follows from Lévy's lemma for Haar-random states and a union
bound over the $D^2-1$ observables [HLW]. $\qquad\blacksquare$

So $\tfrac12 - d/L = \Theta(2^{-N/2})$ up to a factor $\log^{3/2} D$. In four sample runs the sign patterns
of Haar-random states reached between 50 and 64 per cent of the floor value of $\beta$ for four and five qubits.
We did not find Proposition 4 in the notes we could read; we do not claim it is new.

**Averaging between families.** Every context of $W(7,2)$ lies on exactly 24 of its 120 elliptic
quadrics, and every context of $Q^+(9,2)$ lies in exactly 112 of its 496 sections by an imaginary Pauli
observable, each a signed copy of $W(7,2)$ [LGG, J1]; we re-verified these incidences by enumeration.
With Theorem 2 and integer rounding this gives $d(Q^-(7,2)) \ge 291$, $d(W(7,2)) \ge 1455$,
$d(Q^+(9,2)) \ge 6444$, $d(W(9,2)) \ge 28791$, each below the values of [J1, J4] and stated here only to
show what the floor alone yields.

## 6. The data against the floor

Table 1 confronts every published or pre-printed value we know with the floor. "Floor" is the integer
bound of Theorem 1 (Theorem 2 for elliptic quadrics), computed in exact integer arithmetic.
"Best assignment" is the smallest number of violated contexts known; all entries up to five qubits were
reproduced by our own search (Section 9).

| configuration | $N$ | points | contexts | averaging bound $\lceil L/5\rceil$ [M2, LGG] | floor | best assignment | exact value |
|---|---|---|---|---|---|---|---|
| $W(3,2)$ | 2 | 15 | 15 | 3 | 2 | 3 | 3 [dB] |
| $Q^+(3,2)$ | 2 | 9 | 6 | – | 1 | 1 | 1 |
| $W(5,2)$ | 3 | 63 | 315 | 63 | **63** | 63 | 63 [M1] |
| $Q^+(5,2)$ | 3 | 35 | 105 | 21 | 14 | 21 | 21 [dB] |
| $Q^-(5,2)$ | 3 | 27 | 45 | 9 | **9** | 9 | 9 [dB] |
| $W(7,2)$ | 4 | 255 | 5355 | 1071 | 1451 | 1575 [M2] | 1575 [J1]* |
| $Q^+(7,2)$ | 4 | 135 | 1575 | 315 | **315** | 315 [M2] | 315 [LGG] |
| $Q^-(7,2)$ | 4 | 119 | 1071 | 215 | 291 | 315 [M2] | 315 [J1]* |
| $W(9,2)$ | 5 | 1023 | 86955 | 17391 | 28786 | 31479 [M2] | open ($\ge 28830$ [J4]*) |
| $Q^+(9,2)$ | 5 | 527 | 23715 | 4743 | 6426 | 6975 [M2] | 6975 [J1]* |
| $Q^-(9,2)$ | 5 | 495 | 19635 | 3927 | 6501 | 7087 [M2] | open ($\ge 6510$ [J4]*) |
| $W(11,2)$ | 6 | 4095 | 1396395 | 279279 | 527621 | 553140 [M2] | open |
| $Q^+(11,2)$ | 6 | 2079 | 365211 | 73043 | 120901 | 132391 [M2] | open |
| $Q^-(11,2)$ | 6 | 2015 | 332475 | 66495 | 125624 | 131700 [M2] | open |
| $W(13,2)$ | 7 | 16383 | 22362795 | 4472559 | 9227609 | 9406024 [M2] | open |
| $Q^+(13,2)$ | 7 | 8255 | 5720715 | 1144143 | 2161542 | 2331191 [M2] | open |
| $Q^-(13,2)$ | 7 | 8127 | 5458635 | 1091727 | 2252409 | 2294580 [M2] | open |

\* computer-assisted, not formally verified, not peer reviewed; we did not re-run these computations.

Reading of the table. (1) All 17 rows are consistent with the floor; it is attained in the three rows
in bold and, after rounding, in $Q^+(3,2)$, the Mermin–Peres square. (2) From four qubits on (five for
hyperbolic quadrics) the floor exceeds the averaging bound $L/5$, and the gap to the best assignment
shrinks: the floor closes 75, 81, 91 and 96 per cent of the interval between $L/5$ and the best
assignment for the full space at $N = 4, 5, 6, 7$. (3) For seven qubits the best known assignments of
the full space and of the elliptic quadric are within two per cent of the floor.

An empirical regularity, also recorded for four qubits in [J1]: in every best assignment we computed,
$A + 3I$ has low rank. The spectra of $A$ are $`\{21 \pm 16\sqrt6, (-3)^{14}\}`$ for $W(7,2)$,
$`\{(9 \pm 4\sqrt{23})^2, (-3)^{12}\}`$ for $Q^-(7,2)$, $`\{45 \pm 56\sqrt2, (-3)^{30}\}`$ for $Q^+(9,2)$, and three
(respectively three pairs of) eigenvalues different from $-3$ for $W(9,2)$ (respectively $`Q^-(9,2)`$).

## 7. The Lean 4 development

The sources are in `lean/HoggarBound/` (1273 lines in six modules; Lean 4.35.0, Mathlib v4.35.0).

| module | content |
|---|---|
| `Moment.lean` | `sum_cube_le` (the scalar inequality); `trace_pow_eq_sum_eigenvalues_pow` ($\operatorname{tr}A^k = \sum \lambda_i^k$ for Hermitian $A$); `trace_cube_le` |
| `Pauli.lean` | bit vectors `Fin N → ZMod 2`; Weyl operators and `pauli u` as explicit complex matrices; `pauli_mul`, `context_product` ($P_uP_vP_{u+v} = \tau(u,v) I$), `pauli_comm`; traces of one, two and three Pauli operators; $\tau = \pm 1$ on commuting pairs |
| `Bound.lean` | `flags` (ordered commuting pairs with product in $S$: six per context), `beta6`, the operator `opA`; `trace_opA_cube` ($`\operatorname{tr}A^3 = D\,\beta_6`$); **`hoggar_bound`** |
| `Counting.lean` | `violated`, `beta6_eq_card`; the flag count of the full space for every $N$ (`card_flags_all`); `violatedLines` and `card_violated_le`; `four_qubit_contexts` |
| `Corollaries.lean` | `full_space_bound`, `full_space_fraction` (all $N$); `three_qubit_contexts`, `five_qubit_contexts` |
| `Quadric.lean` | the real quadric; its point and flag counts for every $N$ by character sums; `four_qubit_hyperbolic_contexts`, `five_qubit_hyperbolic_contexts` |

The main theorem, as checked:

```lean
theorem hoggar_bound (hN : 1 ≤ N) (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S) (f : Pt N → ℝ)
    (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ N - 1) * beta6 S f
      ≤ ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card)
```

Here `beta6 S f` is six times $\beta_S(f)$, a sum over ordered pairs, and the sign of a context is by
definition the real part of the scalar $\tau(u,v)$ with `pauli u * pauli v * pauli (u + v) = tau u v • 1`.
Table 2 lists the corollaries.

| Lean theorem | statement |
|---|---|
| `full_space_fraction` | for all $N \ge 1$: $`\#\text{violated flags} \ge \big(\tfrac12 - \sqrt{2^N+1}/(2^N+2)\big)\,\#\text{flags}`$ |
| `three_qubit_contexts` | every assignment of the 63 observables violates at least 63 contexts |
| `four_qubit_contexts` | every assignment of the 255 observables violates at least 1451 contexts |
| `five_qubit_contexts` | every assignment of the 1023 observables violates at least 28786 contexts |
| `four_qubit_hyperbolic_contexts` | every assignment of the 135 real observables violates at least 315 contexts |
| `five_qubit_hyperbolic_contexts` | every assignment of the 527 real observables violates at least 6426 contexts |

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for each of them: no `sorry`, no
`native_decide`, no additional axiom.

**What is not formalized.** Theorem 2 (the quaternionic form) and all elliptic-quadric numbers;
Theorem 3 and every statement about equality or geometry; Proposition 4; the limit statement as a
theorem about limits (the inequality for each $N$ is formal); the exact values of [J1]. Upper bounds are
witnesses checked by the programs of Section 9.

**Independent audit.** A separate set of agent sessions, working concurrently in the same repository
and without editing our files, re-checked the six modules from source, confirmed the axiom report, and
added two modules of its own (`IndependentContexts.lean`, `IndependentWitness.lean`). They prove that a
violated context carries exactly six violated flags and, by kernel evaluation of an integer certificate
(no `native_decide`), that the explicit assignment
"$`f(a,c) = +1`$ if $a = 0$ or $c = 0$ or the number of $Y$ factors is at least 2, and $-1$ otherwise"
violates exactly 63 contexts; together with `three_qubit_contexts` this is a formal proof that the
three-qubit degree is exactly 63. Their reports are in `results/lean-audit.md`,
`results/literature-audit.md` and `results/stack-independent-audit.md`, and their companion note is
`paper/independent-research-note.md`. The literature audit is what first pointed us to [J1].

## 8. A running example on the Tsotchke stack

All four components are used for what they are.

* **Moonlab** (v1.2.1, prebuilt WebAssembly engine) is a classical state-vector simulator. It plays
  the quantum device.
* **quantum_rng** is a classical, "quantum-inspired" integer and trigonometric mixer, not a hardware
  quantum source. It supplies seeded pseudo-random numbers. Its stream depends on the C library it is
  built against, so no result depends on its exact values: every count is recomputed independently.
* **QGTL** (quantum_geometric_tensor): only the `diffgeo_*` kernels (Fubini–Study metric, Berry
  curvature), which we had verified earlier against closed forms, are used.
* **Eshkol** (v1.3.6) is a Scheme dialect with automatic differentiation. It carries an independent
  implementation of the geometry and the differentiation checks.

**Experiment on Moonlab** (`src/moonlab_experiment.mjs`, seed 20261109). A Pauli observable is
measured projectively by rotating its eigenbasis onto $Z$ of one qubit (gates $H$, $S^\dagger$, CNOT),
calling Moonlab's single-qubit measurement with a number from quantum_rng, and undoing the rotation.

| step | what is done | result |
|---|---|---|
| E0 | Moonlab's $\langle P\rangle$ against a direct evaluation; repeated measurement | agree to $8.6\times10^{-16}$; repeats agree |
| E1 | $\psi_H$ on 3 simulated qubits; 63 expectation values; signs as an assignment | all $\pm 1/3$ (to $6\times10^{-16}$); 63 of 315 contexts violated, three through each point |
| E2 | realified $\psi_H$ on 4 simulated qubits | $\pm 1/3$ on 135 real observables, $0$ on 120 imaginary ones; 315 of 1575 violated, seven through each point |
| E3 | every context measured sequentially on random states, $N = 2,3,4$, three runs each | $15/15$, $315/315$, $5355/5355$ products equal to the quantum sign (16065 projective measurements and 161406 gates per four-qubit run) |
| E4 | the same with a random Pauli error of probability $p$ on each qubit before each measurement; 3000 to 4000 sampled contexts | Figure 2 and the table below |

Fraction of sampled contexts whose three outcomes multiply to the quantum sign in the simulation, against the proved ceiling $1 - d_{\text{floor}}/L$ for noncontextual models:

| error $p$ | $N=2$ | $N=3$ | $N=4$ |
|---|---|---|---|
| 0 | 1.000 | 1.000 | 1.000 |
| 0.01 | 0.979 | 0.969 | 0.957 |
| 0.02 | 0.958 | 0.939 | 0.930 |
| 0.05 | 0.897 | 0.867 | 0.830 |
| 0.10 | 0.805 | 0.747 | 0.717 |
| 0.20 | 0.669 | 0.616 | 0.591 |
| ceiling, proved | 0.800 | 0.800 | 0.729 |
| best classical model known | 0.800 | 0.800 | 0.706 |

These are frequencies in a seeded software simulation. They illustrate the inequality and are not
measurements on hardware or a loophole analysis.

![Figure 1](figures/fig1_fraction.png)

*Figure 1. Lower bound on the fraction of violated contexts for the full N-qubit Pauli configuration, the earlier bound 1/5, and the best assignments known.*

![Figure 2](figures/fig2_noise.png)

*Figure 2. Simulated success fraction on Moonlab against the classical ceilings.*

![Figure 3](figures/fig3_spectra.png)

*Figure 3. Spectra of $`A = \sum f(v)P_v`$ for the best assignments at three and four qubits.*

**QGTL** (`src/qgt_hoggar.c`). The kernels `diffgeo_compute_fubini_study` and
`diffgeo_compute_berry_curvature`, applied to $\psi_H$ and the 63 tangent vectors $-\tfrac{i}{2}P_v\psi_H$,
return the values of Proposition 3 to $10^{-16}$, and the 189 pairs with $|g_{uv}| \gt 1/12$ are exactly
the pairs on the 63 violated contexts. For the realified state the 945 largest entries recover the 315
violated contexts and the Berry curvature vanishes identically, as it must for a real state.

**Eshkol** (`src/eshkol/hoggar.esk`). An exhaustive pass over all $2^{15}$ two-qubit assignments gives
minimum 3, attained 640 times. The Hoggar signs violate 63 contexts. Reverse-mode automatic
differentiation of the cubic form at the Hoggar Pauli vector $x^\ast$ gives $T(x^\ast) = 7 = (D-1)(D-2)/6$ and
$\nabla T(x^\ast) = 3x^\ast$ to $7\times10^{-16}$ (the Lagrange condition for a maximizer on the sphere); nested
forward-mode second derivatives along four tangent directions are negative ($-0.59$ to $-0.74$).

## 9. Falsifiability and replication

**Predictions that could fail.** (P1) No assignment violates fewer contexts than the floor. (P2) The
three saturated cases are reached exactly. (P3) For every $S$ and $f$, $\operatorname{tr}A = 0$,
$\operatorname{tr}A^2 = D|S|$, $\operatorname{tr}A^3 = 6D\beta$. (P4) On an elliptic quadric the spectrum of
$A$ is doubly degenerate. (P5) For every pure state $T(p) = (D-1)(D-2)/6$. (P6) Ideal sequential
measurements reproduce every context sign in every state. A single counterexample to P1 would be an
assignment whose violation count anyone can recompute in milliseconds.

**Tests** (`scripts/run_all.sh`).

* `hoggar exhaust2`: all 32768 two-qubit assignments; minimum 3 (640 assignments); for the square,
  minimum 1.
* `scripts/run_falsify.sh`: 20 runs over $N = 2, \dots, 5$ and the three families; 20000, 5000 and 500
  uniformly random assignments and 1500, 200 and 12 annealed ones per configuration for
  $N = 3, 4, 5$. No assignment below the floor. Minima reached by annealing: 63, 21, 9 ($N=3$);
  1575, 315, 315 ($N=4$); 31479, 6975, 7087 ($N=5$). These equal the best known values in every case.
* A negative control: the false claim $d(W(5,2)) \ge 64$ is refuted by the Hoggar witness with exit
  code 3, showing that the harness can fail.
* `scripts/analysis.py` (62 checks) and `scripts/ladder.py` (14 checks): P3 on random data to machine
  precision; P4 on all 120 four-qubit elliptic quadrics; P5; the geometry of the violated sets; closed-form
  counts against enumeration; agreement of the C and Python integer bounds.
* Witness files (`data/witness/`) are recounted by an independent routine that uses no tables.

**Independent implementations.** The geometry, the context signs and the counts are implemented five
times: C (`src/hoggar.c`), Python/NumPy with explicit matrices (`scripts/analysis.py`), JavaScript
(`src/moonlab_experiment.mjs`), Eshkol, and the Lean model, in which the signs are theorems about matrix
products. They agree on every number in this paper.

## 10. Limitations and open problems

* The floor is not attained beyond the three listed cases [J2]. Exact values for five or more qubits
  are open except $Q^+(9,2)$ [J1]; the floor alone leaves the intervals of Table 1.
* The exact four- and five-qubit values rest on computer-assisted work that is neither formally verified
  nor peer reviewed [J1]. A formal proof of $d(W(7,2)) = 1575$ would be a natural next target; our
  Lean development gives the lower bound 1451 only.
* The quaternionic form (Theorem 2) is proved on paper and tested numerically, not formalized.
* The literature search was bounded (arXiv and Zenodo queries on 9 November 2026). Statements of the
  form "to our knowledge" mean exactly that.
* Nothing here is an experiment on quantum hardware, and nothing shows a computational advantage.
  The simulation demonstrates what quantum mechanics predicts and what no noncontextual model can do.

## 11. Disclosure, availability, licence

The research direction, derivations, programs, Lean proofs and text were produced on 9 November 2026 by
an AI system (Claude, Anthropic) in a single working session at the request and under the direction of
the first author, who is responsible for the release. A second group of AI agent sessions audited the
work independently (Section 7). No human has refereed it.

Code, proofs, data and this paper: <https://github.com/0thernes/hoggar-bound-lab>. Third-party
components (Moonlab, quantum_rng, quantum_geometric_tensor) are MIT-licensed by their authors and are
vendored with their licences and provenance records.

## References

* [C] A. Cabello, *Proposed test of macroscopic quantum contextuality*, Phys. Rev. A 82, 032110 (2010), arXiv:1002.3135.
* [dB] H. de Boutray, F. Holweck, A. Giorgetti, P.-A. Masson, M. Saniga, *Contextuality degree of quadrics in multi-qubit symplectic polar spaces*, J. Phys. A 55, 475301 (2022), arXiv:2105.13798.
* [GR] C. Godsil, A. Roy, *Equiangular lines, mutually unbiased bases, and spin models*, European J. Combin. 30, 246 (2009), arXiv:quant-ph/0511004.
* [H] S. G. Hoggar, *64 lines from a quaternionic polytope*, Geom. Dedicata 69, 287 (1998).
* [HLW] P. Hayden, D. W. Leung, A. Winter, *Aspects of generic entanglement*, Commun. Math. Phys. 265, 95 (2006).
* [J1] B. W. Jonah, *A section–square law for Pauli quadrics, and an independently regenerated proof that the four-qubit elliptic quadric has contextuality degree 315*, preprint, Zenodo, 20 October 2026, doi:10.5281/zenodo.23510634.
* [J2] B. W. Jonah, *Structure theorems for hyperplane completions in Pauli contextuality*, preprint v0.3, Zenodo, 21 October 2026, doi:10.5281/zenodo.23538829.
* [J3] B. W. Jonah, *The reach of the section-square law: hyperplane completions of symplectic and quadric Pauli configurations*, preprint, Zenodo, 20 October 2026, doi:10.5281/zenodo.23524332.
* [J4] B. W. Jonah, *Results digest, 20 October 2026: multi-qubit contextuality degrees, Pauli-flat states and certification*, Zenodo, doi:10.5281/zenodo.23518569.
* [JL] N. S. Jones, N. Linden, *Parts of quantum states*, Phys. Rev. A 71, 012324 (2005).
* [LGG] Z. Li, A. Gupta, V. Ganesh, *The four-qubit hyperbolic quadric has contextuality degree 315*, arXiv:2610.26465 (19 October 2026).
* [M1] A. Muller, M. Saniga, A. Giorgetti, H. de Boutray, F. Holweck, *New and improved bounds on the contextuality degree of multi-qubit configurations*, Math. Struct. Comput. Sci. 34, 322 (2024), arXiv:2305.10225.
* [M2] A. Muller, M. Saniga, A. Giorgetti, F. Holweck, C. Kelleher, *A new heuristic approach for contextuality degree estimates and its four- to six-qubit portrayals*, J. Phys. A 58, 215302 (2025), arXiv:2407.02928.
* [MS] A. Muller, M. Saniga, *Automated search for highly contextual Kochen–Specker proofs*, arXiv:2609.19862 (2026).
* [O] M. Okumura, *Hypersurfaces and a pinching problem on the second fundamental tensor*, Amer. J. Math. 96, 207 (1974).
* [S] M. Saniga, F. Holweck, C. Kelleher, A. Muller, A. Giorgetti, H. de Boutray, *Hexagons govern three-qubit contextuality*, Quantum 9, 1601 (2025), arXiv:2312.07738.
* [St] B. C. Stacey, *Geometric and information-theoretic properties of the Hoggar lines*, arXiv:1609.03075 (2016).
* [W] J. E. Wilkins, *A note on skewness and kurtosis*, Ann. Math. Statist. 15, 333 (1944).

## Appendix A. Reproduction

```bash
# engine, random source, QGT program (gcc; no other dependency)
bash scripts/build.sh
# every test: exhaustive N=2, falsification suite, analysis, ladder, Moonlab, QGTL, Eshkol
bash scripts/run_all.sh
# Lean (needs elan; fetches Lean 4.35.0 and the Mathlib cache)
cd lean && lake exe cache get && lake build
```

## Appendix B. Witness assignments

`data/witness/nN_t.txt` holds, for $N$ qubits and family $t$ (`f` full, `h` hyperbolic, `e` elliptic), one
header line and a hexadecimal mask whose bit $v$ is set when $f(v) = -1$, with $v = a + 2^N c$. The
three-qubit Hoggar witness produced by the Moonlab run is

```text
3 f 63
163e5efe76fefe00
```

`build/hoggar verify N t file` recounts any witness from the definitions.

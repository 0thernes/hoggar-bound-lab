# Frontier prior-art check and feasible research targets

Date: 2026-11-09. This is a research-selection report, not an announcement of a new theorem. It records a bounded inspection of primary sources and distinguishes explicit open problems, our proposed extensions, and public claims whose evidence is private. The existing published artifact establishes formal verification, not historical novelty.

## Recommendation

The initial target was **case C3 of Jonah's Conjecture E at four qubits**. During this research task, a separate project agent found an explicit pair, and the direct signed-context audit below independently validated its finite claim. A dimension-lifting theorem remains a further target. The quickest useful analytic extension is a **quantitative stability theorem** converting contextuality-score deficit into distance from a pure-state Pauli vector. Exact five-qubit elliptic/full degrees remain larger, substantially harder targets; the present scalar spectral relaxation cannot settle them.

### Target 1: the C3 sign-carrier spectral question

Jonah, *The reach of the section-square law*, v0.5, Section 6, page 8, states:

> On sign carriers the strict law fails in every vertex case for every n ≥ 4.

The paper names this **Conjecture E**. Its C3 case concerns a hyperbolic quadric split by a hyperplane whose polar point lies on the quadric. This case is specifically reported open for every n ≥ 4. The source reports unsuccessful random searches at n=4 and n=5; their lack of a pair is not a nonexistence proof. Other cases have either proven lifts or finite examples. [Primary deposit and PDF](https://zenodo.org/records/23524332).

**Precise finite target.** Put X=Q+(7,2), choose d=Z on the first qubit, and let S be the points of X commuting with d and O its complement in X. A sign carrier is a function σ:S→{−1,+1}. Define

\[
A_\sigma=\sum_{s\in S}\sigma(s)P_s,\qquad
(\Lambda_\sigma)_{pq}=
\begin{cases}
s_{\{s,p,q\}}\sigma(s),&\{s,p,q\}\text{ is an outside line},\\
0,&\text{otherwise}.
\end{cases}
\]

The strict law would say that the spectrum of A determines that of Λ. To establish its failure, exhibit σ and τ with identical characteristic polynomials of A but different characteristic polynomials of Λ. A single differing exact trace moment of Λ suffices for the second condition.

The following block formulas are an independent translation of the source's C3 graded law into the project's tensor-Pauli convention. For n qubits put k=2^(n−1). Let R be the nonidentity real Paulis on the last n−1 qubits. Then

\[
S=\{Z\otimes I\}\cup\{I\otimes P,Z\otimes P:P\in R\}.
\]

With α=σ(Z⊗I), a_P=σ(I⊗P), b_P=σ(Z⊗P),

\[
B_+=\alpha I+\sum_{P\in R}(a_P+b_P)P,\qquad
B_-=-\alpha I+\sum_{P\in R}(a_P-b_P)P.
\]

Thus A=diag(B+,B−), and

\[
\operatorname{spec}\Lambda
=\{(\lambda_i(B_+)+\lambda_j(B_-))/2:1\le i,j\le k\},
\]

with multiplicity one for each ordered pair. At n=3 there are 19 carrier signs and 16 outside points; at n=4 there are 71 carrier signs and 64 outside points. Every coefficient pair assigns its Pauli to exactly one block with coefficient ±2.

For α=1, let r count the Paulis assigned to B+. Then

\[
\operatorname{tr}B_\pm=\pm k,\quad
\operatorname{tr}B_+^2=k(1+4r),\quad
\operatorname{tr}B_-^2=k(1+4(|R|-r)).
\]

Consequently

\[
\operatorname{tr}\Lambda^3
=\frac{k}{8}\left[
\operatorname{tr}A^3+
12k(|R|-2r)
\right].
\]

For cospectral carriers with the same α, differing r therefore certifies differing completion spectra. This identity is a proposed search simplification; it is not a result attributed to Jonah or a novelty claim.

**Witness availability.** The paper reports n=3 C3 counterexamples but supplies no signs or spectra. Its data-availability paragraph, page 10, says the computational data are held privately. The primary deposit lists only the PDF and a commitments text file. The held computation archive is GROW3_20261020_LANE_v2.zip, SHA-256 6d22260a6659b6b1943d9bd13ad1acefb02e13fa333f0d6ed90d1178935bfc9c. A hash is not an accessible witness. Regenerating a three-qubit pair is a realistic preliminary task: after fixing α=1, only 2^18 carriers remain.

**What would count as progress.** An exact n=4 pair would settle the previously open n=4 C3 instance in the inspected source. A lift that preserves both carrier cospectrality and a differing completion moment would extend it to all higher n. The source's existing tensor lift applies to C1/C6; its cone lift carries C3 to C11 rather than back to C3, so those lifts do not directly settle this target.

**Regenerated known-case control.** During this task a separate project agent regenerated an n=3 pair, recorded in results/frontier-c3-pair.json. Its common carrier polynomial is (x−5)(x−1)²(x+3)³(x²−2x−47), whereas the completion cubic traces are 0 and 96. The plus-block support sizes are r=8 and r=6: the formula above predicts the difference −3k²Δr=96 at k=4. The two negative blocks exchange eigenvalues {1,1} and {5,−3}, preserving their trace. The factorization and support counts were separately checked in this audit. This reproduces a previously reported existence and is not the open n=4 result.

**Feasibility.** Existing Pauli generation and matrix tools can build the required operators. Integer characteristic-polynomial or trace-moment certificates can be checked independently. A finite Lean certificate is plausible, although exact characteristic-polynomial equality for a 16×16 matrix may be more expensive than verifying an explicit conjugacy or low-degree annihilating polynomials. Approximate equal eigenvalues are discovery filters only. Mere gauge transformations or a symmetry preserving the split cannot establish the required mismatch.

**Four-qubit result found during this task.** The pair in results/frontier-c3-n4-pair.json has the common carrier polynomial

\[
(x-3)^2(x+1)^8(x+5)^2(x+13)
(x^3-25x^2-133x+1621),
\]

where the line break denotes multiplication of the displayed factors. Its two completion cubic traces are 14976 and 15360. The plus-block support sizes are 35 and 33; the exact difference −3·8²·(−2)=384 agrees with those traces.

The independent verifier scripts/frontier_c3_context_verify.py reconstructs all 135 real four-qubit Paulis from the literal 2×2 matrices, selects the 71-point section commuting with Z on the first factor, and constructs Λ directly from the 1120 signed outside contexts on 64 outside points. It does not use the discovery code's block-completion spectral formula. Both exact carrier characteristic polynomials and both integer cubic traces match the candidate. A deliberate sign flip of one context is detected for each carrier. The recorded output is results/frontier-c3-context-verification.json.

**Hypothesis and normalization audit.** This is exactly C3, not a transferred cone case: X is the full real hyperbolic quadric, d=Z⊗I is a point of X, S=X∩d-perp, and every carrier value is ±1. In the primary source, page 2 defines Λ with entry s_Lσ(s), and Theorem A identifies it with Jordan multiplication J_A(M)=(AM+MA)/2 on the outside Pauli span. The Pauli basis is orthonormal for tr(PQ)/D. Table 1, page 4, gives C3 pair sums divided by two with multiplicity one. Hence there is no missing factor of two or extra degeneracy. The outside violation count is 560−xᵀΛx/4.

The source's question is whether equal carrier spectra force equal completion spectra. The differing cubic traces disprove that implication in this instance and therefore **establish the n=4 C3 instance of Conjecture E**, which predicts failure. They do not refute Conjecture E or prove its remaining higher-dimensional instances. The verification recorded here is computational; any Lean theorem is the responsibility of the separate formalization task.

**Priority boundary.** The primary source explicitly labels C3 open for n≥4. On 2026-11-09 its latest-version API still returned record 23524332, v0.5. The PDF and publication metadata are dated 2026-10-20; the API creation timestamp is 2026-10-21T07:30:57.429829−07:00. Thus a precise citation distinguishes the manuscript date from the deposit date. Searches for the exact conjecture, the title with C3, sign-carrier spectra, and Pauli cospectral examples found no additional primary n≥4 example. A creator-filtered Zenodo search also returned no later relevant note. This supports comparison to the inspected source; it does not establish absolute first priority.

### Target 2: quantitative contextuality-to-state stability

The inspected Jonah sources give the exact spectral inequality and exact equality characterization. They do not state the quantitative estimate below. This is an elementary proposed extension of classical moment inequalities; the bounded searches do not establish that it is historically new.

Let A be traceless Hermitian of dimension n≥2 with tr(A²)=nm>0. Set c=n−1, a=√(cm), and

\[
\delta=\frac{nm(n-2)a}{c}-\operatorname{tr}A^3.
\]

A concrete theorem to prove is that some rank-one projector P satisfies

\[
\left\|A-\frac{na}{c}P+\frac{a}{c}I\right\|_F^2
\le\frac{2c\,\delta}{na}.
\tag{S}
\]

The residual identity

\[
\sum_i(a-\lambda_i)(c\lambda_i+a)^2=c^2\delta
\]

and Σ(cλ_i+a)²=n²a² imply a−λ_max≤c²δ/(n²a²). Choosing a top eigenvector gives (S). This derivation has been checked algebraically here; formal proof and numerical verification belong to the separate stability task.

For a signed Pauli sum on support S, let q_u=(c/a)f(u) on S and zero elsewhere, and let p_u=tr(PP_u) be the nonidentity Pauli vector of P. Orthogonality gives the associated target

\[
\sum_{u\ne0}(p_u-q_u)^2
\le \frac{2c^3\delta}{n^2a^3}.
\]

In the full three-qubit case, if f violates 63+e contexts, this specializes to a pure state with

\[
\sum_{u\ne0}\bigl(p_u-f(u)/3\bigr)^2\le e/9.
\]

Every coordinate whose expectation has the opposite sign to f contributes at least 1/9 to this error; hence their number is at most e. If zero expectations are counted as mismatches, the same lower contribution holds. This is closeness to the sign pattern of **some** pure state. It is not automatically closeness to an exact Hoggar state or its finite orbit. Such a conclusion needs another rigidity theorem.

**Feasibility and potential value.** The scalar proof closely follows the existing Lean cubic proof and should be tractable. The matrix/pure-state bridge needs a top-eigenvector projector and a Pauli Parseval identity. The existing QGTL/state-vector path can exercise the reconstruction and falsify a bad constant. A sharp constant, a useful error threshold, or a certified discrete-orbit recovery theorem would carry more content than merely restating equality.

**Related sources checked.** Jonah's structure preprint, Lemma 5 and Theorem 6, covers exact extremal spectra and equality [primary PDF](https://zenodo.org/records/23538829). Pauli-flat states, including states with some zero coefficients, are already studied by Cieśliński, arXiv:2610.07172v1, 5 October 2026 [primary paper](https://arxiv.org/html/2610.07172v1). Classical Okumura estimates and geometric rigidity are extensive subjects; searches containing “Okumura inequality” with “quantitative”, “deficit”, “remainder” and “stability” did not identify the displayed modulus, but that result is a search limitation, not a priority certificate. “Stability eigenvalue” papers about hypersurfaces should not be confused with stability of the algebraic inequality.

### Target 3: a public certified improvement for five-qubit elliptic degree

The exact five-qubit elliptic and full-space degrees are not established in the inspected deposits. The relevant reported bounds are:

| Configuration | Public analytic floor | Two-program announcement | One-program computed announcement | Published witness upper bound |
|---|---:|---:|---:|---:|
| Q−(9,2), 495 points, 19,635 lines | 6,501 | 6,510 | 6,513 | 7,087 |
| W(9,2), 1,023 points, 86,955 lines | 28,786 | 28,830 | 28,844 | 31,479 |

The announcements are in Jonah's digest, Section 2.1. Their proofs/code are private; the text assigns the two columns different verification status. The upper bounds come from Muller and collaborators' published assignments and are also reproduced by this project's independent witness checks. “Known best” here means strongest statements found in these primary sources, not a guarantee of an exhaustive literature census. [Digest PDF](https://zenodo.org/records/23518569), [Muller et al. primary manuscript](https://arxiv.org/html/2407.02928v1).

**Concrete research targets.** Prove d(Q−(9,2))≥6514 with a public, checkable certificate, or disprove the natural witness-optimality conjecture d(Q−(9,2))=7087 by finding a lower witness. Exact equality 7087 is the larger target. The full-space analogue is proving d(W(9,2))=31479 or finding a smaller witness. These equalities are proposed targets, not assertions that the inspected sources explicitly conjecture them.

**Why the existing bound will not finish the job.** Jonah's reach preprint, Theorem C, proves that the specified single-hyperplane product-of-spheres relaxation attains the same optimum as the global spectral relaxation. Reusing that relaxation, even with more numerical precision, cannot close the gap. Discrete sign information, exact rounding with additional restrictions, coupled sections, or stronger polynomial certificates are needed.

**Feasibility.** Heuristic witness search is immediately available but an unsuccessful search proves no lower bound. A complete exact 495-variable optimization is not a modest extension of the current Lean code. A smaller rational/integer certificate obtained from additional structure is more plausible, but no such certificate has been constructed in this report. This is the highest-impact target here and the least predictable.

## Targets that should not be presented as new resolutions

- Li, Gupta and Ganesh's 2026 Section 11 questions about the four-qubit elliptic/full values and the five-qubit hyperbolic value have prior claimed answers in Jonah's deposits. An additional primary companion, *Answers to two open problems*, v0.6, DOI 10.5281/zenodo.23518323, explicitly addresses them and discusses optimal-set classifications. [Primary deposit](https://zenodo.org/records/23518323).
- Their higher-rank L/5 question is already contradicted at five-qubit hyperbolic degree 6975 by that prior claim and by the weaker formal bound in this project. A new proof of the contradiction is not a new question resolution. [Original questions, Section 11](https://arxiv.org/html/2610.26465v1#S11).
- A conceptual classification of the four-qubit hyperbolic optima is already announced in Jonah's digest, Section 3.2, conditional on two external classification results. A fully public checked proof could strengthen the evidence, but the conceptual route is prior art.
- Arbitrary-support and nonnegative vertex-weight extensions of the cubic trace calculation are straightforward: coefficients t_u f(u) give context weights t_u t_v t_w and second moment DΣt_u². Arbitrary independent context weights generally do not factor this way. The factorized-weight lemma alone is insufficient grounds for a major novelty claim.
- Exact equality, Pauli-flat saturation, Kramers pairing, and the full-space asymptotic one-half limit all follow the previously identified spectral mechanism. They should not be recycled as a new breakthrough.

## Source and access record

Primary PDFs read locally: J1 section-square, J2 structure v0.3, J3 reach v0.5, J4 digest v1, and the additional answers v0.6 companion. Temporary copies are in %TEMP%/hoggar-literature-audit/. The original Li paper and the Pauli-flat paper were accessed at arXiv. J3's exact n=3 witness data were specifically sought and are not public in its deposit.

This report records research targets and the independently validated finite C3 example found while pursuing them. It does not certify absolute novelty, solve Conjecture E in all dimensions, establish a new exact contextuality degree, or import private evidence into the project's formal theorem set.

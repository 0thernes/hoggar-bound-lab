# Cospectral Pauli carriers with different completion spectra: an exact four-qubit C3 certificate

**Alexander S. Donahue — 0thernes LLC, Hoggar Bound Lab**  
**Correspondence: 0_0@0thernes.art**  
**2026-11-09**  
**Research preprint; not peer reviewed**

## Abstract

We give two explicit sign assignments on a 71-point hyperplane section of the real four-qubit Pauli configuration. Their $16\times16$ carrier operators have identical characteristic polynomials, while the associated $64\times64$ completion operators have different cubic traces, 14976 and 15360. Thus the carrier spectrum does not determine the completion spectrum in case C3 of Jonah's classification. This establishes the four-qubit C3 instance of the failure predicted by his Conjecture E; the inspected preprint explicitly leaves this instance open. Each assignment is specified by four negative Pauli words. The certificate reduces to factorizations of four $8\times8$ block polynomials and an exact trace identity. The largest completion eigenvalues also differ by exactly two, producing a difference of 32 in the corresponding continuous-relaxation lower bounds. Independent programs reconstruct the operators from literal Pauli matrices and from all 1120 signed outside contexts; deliberate sign mutations provide falsification controls. A Lean 4 development verifies carrier cospectrality and completion noncospectrality, including the connection to the Pauli model. We distinguish this finite result from the conjecture in arbitrary dimension, exact binary completion optima, historical priority, and physical experiments.

## 1. The spectral question

A Pauli contextuality configuration consists of observables and compatible triples whose products are signed identities [4]. Fixing values on part of the configuration leaves a completion problem on its remaining observables. Spectral relaxations can bound the number of constraints that any completion must violate. The question considered here is whether the spectrum of the fixed part contains enough information to recover the spectrum governing that completion.

Jonah's classification of hyperplane completions separates several cases according to the ambient configuration and the chosen hyperplane [1]. His *strict law* means that equal carrier spectra always imply equal completion spectra within a specified class of carriers. For real-valued carriers, the classification has a criterion involving vertices of the section. Restricting every carrier value to $\pm1$ is a different question: a counterexample using zero coefficients is not necessarily an admissible sign carrier.

Section 6 of [1] states Conjecture E, predicting failure of the strict law on sign carriers in every vertex case for every number of qubits $n\ge4$. The source reports several established cases and finite examples, but specifically states:

> Case C3 is open for $n\ge4$.

Here C3 is a hyperbolic quadric split by a hyperplane whose polar point belongs to that quadric. The present certificate addresses $n=4$. It proves failure of the strict law in that instance, thereby establishing the corresponding instance of Conjecture E. It is not a counterexample to Conjecture E, which predicts this failure.

The construction concerns the information retained by a spectral relaxation. It does not compute a new contextuality degree. In particular, the known degree 315 of the full real four-qubit configuration [2] is a different statement from the completion-spectrum comparison made here.

## 2. Conventions and complete specification

Use the Hermitian matrices $I,X,Z$ and $Y=iXZ$. For binary strings $x,z$ of length $n$, write

\[
P_{x,z}=i^{\sum_jx_jz_j}X^xZ^z.
\]

The exponent is an ordinary integer sum. A numeric label is $x+2^n z$, with the bit of index zero at the **rightmost** tensor factor. A Pauli word is printed in tensor-factor order from left to right. Thus the four-qubit label 128 denotes $d=ZIII$.

Let $q(x,z)=x\cdot z$ modulo two. The real nonidentity Paulis are those with $q=0$, equivalently an even number of $Y$ factors. They form the 135-point hyperbolic quadric

\[
X=Q^+(7,2).
\]

The symplectic form is $[u,v]=x_u\cdot z_v+z_u\cdot x_v$. Two labels commute precisely when this form vanishes. A line is an unordered triple $\{u,v,u+v\}$ of distinct nonzero commuting labels, with sign $s_L$ defined by $P_uP_vP_{u+v}=s_LI$.

Choose $d=ZIII$ and divide $X$ into its section and outside points:

\[
S=\{v\in X:[v,d]=0\},\qquad O=X\setminus S.
\]

There are 71 section points and 64 outside points. Indeed, if $R$ is the set of 35 real nonidentity three-qubit Paulis, then

\[
S=\{Z\otimes I_8\}\cup
\{I\otimes P,Z\otimes P:P\in R\}.
\]

Outside points have first factor $X$ with a real three-qubit factor, or first factor $Y$ with an imaginary three-qubit factor. These contribute 36 and 28 points respectively. Every line not wholly in $S$ contains exactly two points of $O$ and one point of $S$. There are 1120 such outside lines.

Define the two carriers $\sigma_0,\sigma_1:S\to\{-1,+1\}$ to be positive everywhere except at the following four words:

| Carrier | Negative Pauli words | Negative numeric labels |
|---|---|---|
| $\sigma_0$ | IIZZ, IYYI, ZIZZ, ZYYI | 48, 102, 176, 230 |
| $\sigma_1$ | IYXY, ZIIZ, ZIZZ, ZYXY | 87, 144, 176, 215 |

In particular, both assign $+1$ to $d$. This table completely specifies the witnesses without an external search seed or downloaded assignment.

For any carrier $\sigma$ define its Hermitian carrier operator

\[
A_\sigma=\sum_{s\in S}\sigma(s)P_s.
\]

Its completion matrix $\Lambda_\sigma$ is indexed by $O$. For an outside line $L=\{s,p,q\}$, put

\[
(\Lambda_\sigma)_{pq}=(\Lambda_\sigma)_{qp}
=s_L\sigma(s);
\]

all other entries, including the diagonal, are zero. If $y\in\{-1,+1\}^O$ is an outside assignment, its number of violated outside lines is

\[
F(\sigma,y)=560-\frac14y^{\mathsf T}\Lambda_\sigma y.
\tag{1}
\]

The factor one quarter arises because the symmetric quadratic form counts each outside line twice. These are the definitions and normalization of [1, Section 2].

## 3. Exact finite theorem

**Theorem 1.** The carriers specified above have the same characteristic polynomial,

\[
\begin{aligned}
\chi_{A_{\sigma_0}}(t)=\chi_{A_{\sigma_1}}(t)
={}&(t-3)^2(t+1)^8(t+5)^2(t+13)\\
&{}\cdot(t^3-25t^2-133t+1621).
\end{aligned}
\tag{2}
\]

Their completion matrices satisfy

\[
\operatorname{tr}\Lambda_{\sigma_0}^3=14976,\qquad
\operatorname{tr}\Lambda_{\sigma_1}^3=15360.
\tag{3}
\]

Consequently the completion spectra differ, despite identical carrier spectra. This is a failure of the strict law for sign carriers in the four-qubit C3 configuration.

Equality of characteristic polynomials establishes carrier cospectrality with multiplicities. Conversely, matrices with the same spectrum have equal cubic traces. The difference 384 in (3) is therefore a certificate of unequal completion spectra; computing 64 eigenvalues numerically is unnecessary.

## 4. Block certificate and proof

Because every section operator commutes with $d$, its carrier is block diagonal in the $\pm1$ eigenspaces of $d$:

\[
A_\sigma=\begin{pmatrix}C_\sigma&0\\0&D_\sigma\end{pmatrix}.
\]

Write $\alpha=\sigma(Z\otimes I)$, $a_P=\sigma(I\otimes P)$, and $b_P=\sigma(Z\otimes P)$. The two $8\times8$ real symmetric blocks are

\[
C_\sigma=\alpha I+\sum_{P\in R}(a_P+b_P)P,\qquad
D_\sigma=-\alpha I+\sum_{P\in R}(a_P-b_P)P.
\tag{4}
\]

Each nonidentity real Pauli appears in exactly one block, with coefficient $+2$ or $-2$. This exclusivity follows from $a_P,b_P\in\{-1,+1\}$.

For three-qubit numeric labels use $x+8z$ with the same rightmost-bit convention, and write $P_v$ for the associated matrix. Put $T=\sum_{P\in R}P$. The witness table gives

\[
\begin{array}{ll}
C_0=I+2(T-2P_{24}-2P_{54}),&
D_0=-I,\\
C_1=I+2(T-P_8-P_{24}-2P_{47}),&
D_1=-I+2P_8+2P_{24}.
\end{array}
\tag{5}
\]

Here $P_8=IIZ$, $P_{24}=IZZ$, $P_{47}=YXY$ and $P_{54}=YYI$. Thus (5) is also a short algebraic specification of all four blocks.

Let

\[
q(t)=t^3-25t^2-133t+1621,\qquad
h(t)=(t+13)q(t).
\]

Exact determinant evaluation of the matrices in (5) gives:

| Block | Characteristic polynomial |
|---|---|
| $C_0$ | $(t-3)^2(t+5)^2h(t)$ |
| $D_0$ | $(t+1)^8$ |
| $C_1$ | $(t+1)^4h(t)$ |
| $D_1$ | $(t-3)^2(t+1)^4(t+5)^2$ |

These are finite integer identities, checked by characteristic-polynomial computation. They can be reproduced directly from (5); no classification theorem or approximate root comparison enters the calculation. The polynomial of $D_1$ is also immediate from the joint eigenvalues of its two commuting Z-type Paulis. Multiplying the two block polynomials in each row-pair gives (2).

The spectral mechanism is a redistribution between blocks. Two copies each of eigenvalues $3$ and $-5$ move from the plus block to the minus block; four copies of $-1$ move in the opposite direction. The unlabelled union stays fixed, while the spectra associated with the two eigenspaces of $d$ change.

To calculate the completion traces, identify the outside Pauli span with the real off-diagonal symmetric matrices

\[
\begin{pmatrix}0&M\\M^{\mathsf T}&0\end{pmatrix},
\qquad M\in\mathbb R^{8\times8}.
\]

Taking one half of the anticommutator with $A$ induces

\[
M\longmapsto \frac12(C_\sigma M+M D_\sigma).
\tag{6}
\]

In the outside Pauli basis its matrix is exactly $\Lambda_\sigma$. This is [1, Theorem A and Table 1, C3]; it can also be checked directly by multiplying Pauli matrices. Therefore

\[
\operatorname{spec}\Lambda_\sigma
=\left\{\frac{c_i+d_j}{2}:1\le i,j\le8\right\},
\tag{7}
\]

where $c_i$ and $d_j$ are the respective block eigenvalues. Each ordered pair contributes once.

Expanding the cubes in (7) yields

\[
\begin{aligned}
\operatorname{tr}\Lambda_\sigma^3
={}&\operatorname{tr}A_\sigma^3\\
&+\frac38\left[
(\operatorname{tr}C_\sigma^2)(\operatorname{tr}D_\sigma)
+(\operatorname{tr}C_\sigma)(\operatorname{tr}D_\sigma^2)
\right].
\end{aligned}
\tag{8}
\]

Both carriers have $\operatorname{tr}C=8$, $\operatorname{tr}D=-8$ and $\operatorname{tr}A^3=18336$. If $r$ counts the real Paulis assigned to $C$, Pauli orthogonality gives

\[
\operatorname{tr}C^2=8(1+4r),\qquad
\operatorname{tr}D^2=8(1+4(35-r)).
\tag{9}
\]

For $\sigma_0$, $r=35$, giving square traces 1128 and 8. For $\sigma_1$, $r=33$, giving 1064 and 72. Thus (8) becomes respectively

\[
18336+3(8-1128)=14976,
\qquad
18336+3(72-1064)=15360.
\]

This proves (3) and completes the certificate.

## 5. An exact gap in the continuous relaxation

The example changes more than an interior moment of the completion spectrum.

**Corollary 2.** The largest completion eigenvalues differ by exactly two:

\[
\lambda_{\max}(\Lambda_{\sigma_1})
-\lambda_{\max}(\Lambda_{\sigma_0})=2.
\tag{10}
\]

To see this, let $r_*$ be the largest root of $q$. We have $q(25)=-1704$ and $q(30)=2131$. Also $q'(t)=3t^2-50t-133$ is positive for $t\ge25$, so $q$ has exactly one root above 25. Its roots are real because they occur in the polynomial of a real symmetric block. Thus $r_*\in(25,30)$, while the other roots lie below 25. Both plus blocks have largest eigenvalue $r_*$; their other explicit factors contribute only $-13,-5,-1$ or $3$. The minus-block maxima are $-1$ for $D_0$ and $3$ for $D_1$. Equation (7) therefore gives maxima $(r_*-1)/2$ and $(r_*+3)/2$, proving (10).

Relaxing the binary outside assignment in (1) to the sphere $y^{\mathsf T}y=64$ gives

\[
\min_{\|y\|^2=64}F(\sigma,y)
=560-16\lambda_{\max}(\Lambda_\sigma).
\tag{11}
\]

Consequently this relaxed minimum is 32 lower for $\sigma_1$ than for $\sigma_0$. The optimization in (11) is continuous. A binary vector need not be a top eigenvector, so neither (10) nor (11) proves that the exact binary completion minima differ by 32, or even that they differ.

![Carrier and completion spectra for the two assignments: Assignment A is $\sigma_0$ and Assignment B is $\sigma_1$. Numerical locations in this display illustrate the certificate; the equality of carrier polynomials, unequal integer completion cubic traces, and exact largest-eigenvalue gap are established algebraically. Multiplicities are part of the spectra.](c3-figures/spectra.png){width=100%}

## 6. Independent verification and falsification

The search output alone is not the verification boundary. The deposited workflow provides several distinct checks.

The literal-matrix verifier constructs each four-qubit Pauli from the $2\times2$ matrices. It independently selects the real configuration and the section, constructs $A$, computes its integer characteristic polynomial, and forms the Jordan operator. Exact Pauli coordinates reconstruct every image of that operator. A recorded change-of-basis matrix $T$ satisfies $T^{\mathsf T}T=TT^{\mathsf T}=8I$ and intertwines the completion matrix with the block Jordan representation. These identities check that no missing component is hidden by a projection.

A separate signed-context verifier constructs $\Lambda$ from outside lines themselves. It checks commutation, multiplies each triple to determine its sign, and visits all 1120 outside contexts. It then checks both carrier polynomials and both integer completion cubic traces. This route does not use the block spectral formula (7). Its tensor construction orders the last three factors oppositely to the printed convention; reversing those factors is a fixed orthogonal basis permutation, so the two descriptions represent the same assignments after that explicitly specified relabelling.

The computations use exact characteristic polynomials in SymPy and integer context matrices. Literal Pauli entries $0,\pm1$ and $\pm i$ are represented exactly during initial tensor construction; the real matrices are then converted to integers. The small matrix sizes and entry bounds keep the integer products within signed 64-bit range. No eigenvalue tolerance determines whether the certificate passes.

For a negative control, the context verifier flips one off-diagonal context coefficient and its symmetric partner. The cubic traces change to 14808 and 15144 respectively, and the required comparison fails. This tests detection of a specific sign inconsistency. The verifier rejects optimized Python execution because that execution mode would disable assertions.

The interactive model provides another executable implementation. It builds the integer Pauli matrices and context signs, computes characteristic polynomials using a BigInt Faddeev–LeVerrier recurrence, and evaluates cubic traces with BigInt arithmetic. Changing a sign assignment triggers a fresh computation. This makes the stated certificate directly falsifiable in the interface; a modified assignment is not required to retain cospectrality.

**Eshkol execution.** A serial compiled arithmetic run uses the Tsotchke Eshkol compiler, version 1.3.6-evolve, through the command eshkol-run -r. Given the two integer carriers $A,B$ and integer certificate matrices $M,R$, it checks $AM=MB$ and $MR=RM=46656I$. Thus $M$ is invertible over the rationals, providing another certificate of carrier similarity. The program separately evaluates the block moment formula and returns completion cubic traces 14976 and 15360. A Python arbitrary-precision replay bounds every input, product and ordered accumulation in this program by 408304 in absolute value, safely below $2^{63}-1$. The recorded run exited with code zero and empty standard error, using process-local paths to the existing LLVM 21 and CUDA 12.9 installations. Its command, environment settings, outputs and hashes are recorded in results/frontier-c3-eshkol.json. This establishes the tested serial arithmetic execution; compiler correctness, GPU operations and parallel-worker behavior are outside its qualification.

**Lean 4 verification.** The Lean 4.35.0 and Mathlib 4.35.0 development connects these explicit witnesses to the actual four-qubit Pauli configuration. It identifies the complete 71-point section and 64-point complement, verifies the sign assignments, and relates the integer certificate matrices to complex Pauli sums and real signed-context completion operators. It proves equality of the carrier characteristic polynomials and canonical eigenvalue lists, but inequality of the completion characteristic polynomials and real eigenvalue multisets, retaining multiplicities. The completion cubic traces are proved exactly as 14976 and 15360. The principal declarations in the HoggarBound.C3 namespace are `four_qubit_C3_counterexample`, `pauli_carrier_eigenvalues_eq`, `pauli_completion_eigenvalue_multisets_ne`, and `four_qubit_C3_spectral_counterexample`.

All source checks completed successfully, and the axiom audit of 42 declarations found only `propext`, `Classical.choice`, and `Quot.sound`. The finite arithmetic uses kernel reduction; no unproved project axiom, proof placeholder, or native-evaluation axiom is required. Source hashes, commands, successful build records and the axiom report are retained in results/frontier-c3-lean-audit.md and its linked evidence. The printed characteristic-polynomial factorization, the exact largest-eigenvalue gap 2, and the continuous-relaxation gap 32 are algebraic deductions in this paper and are not included in those Lean theorem statements.

## 7. Source comparison and scope

The literature comparison used the primary PDF of [1], including its definitions, case table, Conjecture E and data-availability statement. The manuscript is dated 20 October 2026; its Zenodo metadata records deposition on 21 October. On 9 November 2026 the latest-version endpoint still returned v0.5. The source reports C3 examples at three qubits, but its data are held privately. A separately regenerated three-qubit example was used only as an implementation control; reproducing that previously reported case is not the contribution here.

Focused searches checked the conjecture name, C3, hyperplane completion spectra and Pauli cospectral examples, together with related primary deposits. No additional primary $n\ge4$ C3 example was identified. This is a bounded evidence synthesis. It does not establish an exhaustive citation census or absolute historical priority. It is also not a statistical meta-analysis: there are no pooled experimental effect sizes.

The distinction from earlier spectral contextuality work is narrow. Jonah already gives the Jordan representation, the block-spectrum laws, the cubic spectral floor and its equality structure [1,3]. Those mechanisms are used here with attribution. The present result is the fully specified sign-carrier certificate for the four-qubit C3 instance and its exact spectral consequences.

Several limits are material. The result does not settle the remaining dimensions of C3, the other unproved instances of Conjecture E, or an exact contextuality degree. It does not classify all cospectral carriers. It says nothing about physical quantum hardware or quantum computational advantage. The software runs are mathematical experiments on finite matrices. Any broader claim needs a separate theorem or experiment.

## 8. Research provenance and AI assistance

Alexander S. Donahue initiated and directed the project and specified the Tsotchke tool stack. OpenAI Codex research and coding agents performed the literature search, selected the finite C3 problem, discovered the witness pair, developed the algebraic arguments and Lean formalization, implemented the independent checks and demonstration, and drafted the manuscript and figures. The figures display computed matrix data. The numerical and formal evidence is provided for reproduction and external scrutiny; computational verification should not be mistaken for human peer review. AI tools are disclosed as tools, not listed as authors. Venue-specific author validation and accountability requirements apply to any scholarly submission of this artifact.

**Funding and affiliation.** This research was self-funded by the author. The author is the sole operator of 0thernes LLC, with which this project is affiliated.

## 9. Reproducibility

The repository is [Hoggar Bound Lab](https://github.com/0thernes/hoggar-bound-lab). Run the following commands from its root with Python, NumPy, SymPy and Node.js installed:

~~~text
python scripts/frontier_c3_verify.py
python scripts/frontier_c3_context_verify.py
node tests/frontier_c3_browser_test.cjs
python scripts/frontier_c3_integer_bounds.py
python scripts/frontier_c3_demo.py
~~~

The last command requires Eshkol. Set the ESHKOL_RUN environment variable to the executable when it is not on the system path. The wrapper generates build/frontier_c3_demo.esk and invokes eshkol-run -r on that file. On the recorded Windows installation, it supplies existing matching LLVM and CUDA library paths to the child process while respecting explicit environment settings. The complete command and process-local overrides are retained in the result record. Its checks use the published integer similarity certificate rather than a random search.

For the formal proof, use the repository's pinned Lean toolchain and Mathlib dependency lock. From the lean directory, build the following targets sequentially to limit simultaneous memory use, then run the declaration audit:

~~~text
lake build HoggarBound.C3Data
lake build HoggarBound.C3Certificate
lake build HoggarBound.C3Geometry
lake build HoggarBound.C3Theorem
lake build HoggarBound.C3Spectra
lake env lean C3Verification.lean
~~~

The recorded Windows finite-certificate check took approximately 61 minutes; its timing and memory counters are retained with the proof log. This cost concerns exact proof checking, not the interactive demonstration, and does not measure a physical quantum process.

The principal records are results/frontier-c3-n4-pair.json, results/frontier-c3-n4-verification.json, results/frontier-c3-n4-completions.json, and results/frontier-c3-context-verification.json. The direct-context report records 135 configuration points, 71 section points, 64 outside points, 1120 contexts, both polynomials and traces, mutation results, dependency versions and SHA-256 hashes. Both raw-byte and LF-normalized input hashes distinguish local Windows line endings from Git-normalized text.

The independent context check was run with Python 3.9.13, NumPy 2.0.2 and SymPy 1.14.0. Reproduction requires a release containing the C3 artifacts; the theorem's complete assignments are also specified in Section 2, independently of repository state. The research preprint and code remain open to external mathematical and implementation review.

## References

1. B. W. Jonah. *The reach of the section-square law: hyperplane completions of symplectic and quadric Pauli configurations*. Preprint v0.5, dated 20 October 2026; deposited 21 October 2026. Section 2, Theorem A, Table 1, and Section 6, Conjecture E. [Primary deposit](https://zenodo.org/records/23524332). [DOI](https://doi.org/10.5281/zenodo.23524332).
2. Z. Li, A. Gupta and V. Ganesh. *The Four-Qubit Hyperbolic Quadric Has Contextuality Degree 315*. arXiv:2610.26465v1, 19 October 2026. [Primary text](https://arxiv.org/html/2610.26465v1).
3. B. W. Jonah. *Structure theorems for hyperplane completions in Pauli contextuality*. Preprint v0.3, 21 October 2026. [Primary deposit](https://zenodo.org/records/23538829). [DOI](https://doi.org/10.5281/zenodo.23538829).
4. H. de Boutray, F. Holweck, A. Giorgetti, P.-A. Masson and M. Saniga. *Contextuality degree of quadrics in multi-qubit symplectic polar spaces*. J. Phys. A 55 (2022), 475301. [Corrected arXiv record](https://arxiv.org/abs/2105.13798). [DOI](https://doi.org/10.1088/1751-8121/aca36f).

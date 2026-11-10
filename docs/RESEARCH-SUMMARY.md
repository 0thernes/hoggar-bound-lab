# What the four-qubit C3 certificate proves

Alexander S. Donahue — 0thernes LLC, Hoggar Bound Lab.

Two explicitly specified assignments of signs to four-qubit Pauli observables produce **the same carrier spectrum and different completion spectra**. The result shows that the carrier's eigenvalues, even when known exactly with all multiplicities, can discard information needed to determine a related contextuality optimization.

This is a finite mathematical result. Its Pauli-model connection and spectral distinction are checked in Lean 4. It is published as a research preprint with exact certificate data and an [interactive verifier](https://0thernes.github.io/hoggar-bound-lab/c3-lab/). It is not a physical quantum experiment or a peer-reviewed article.

## The question in plain terms

Begin with the 135 nonidentity real symmetric Pauli observables for four qubits. Choose the polar observable `ZIII`. The 71 observables commuting with it form a section; the other 64 lie outside it. Assign a sign, either `+1` or `−1`, to each section observable.

That one sign assignment produces two matrices. The **carrier** is the signed sum of the section observables, acting on the 16-dimensional four-qubit state space. The **completion** is a 64-by-64 matrix recording how the fixed section signs constrain the 1120 outside contexts. Each outside context contains one section observable and two outside observables.

The question is whether the carrier spectrum determines the completion spectrum. In this four-qubit C3 geometry, the answer is **no**. The complete eigenvalue list of the carrier loses information about how eigenvalues are distributed between the two eigenspaces of `ZIII`. The completion operator depends on that distribution.

## A small, explicit witness

Every section sign is positive except for the four words listed in each row. Words are tensor products in the displayed left-to-right order. Numeric labels use the paper's convention `v = a + 16c`, with bit zero corresponding to the rightmost tensor factor.

| Assignment | Negative Pauli words | Negative numeric labels |
| --- | --- | --- |
| A | `IIZZ`, `IYYI`, `ZIZZ`, `ZYYI` | 48, 102, 176, 230 |
| B | `IYXY`, `ZIIZ`, `ZIZZ`, `ZYXY` | 87, 144, 176, 215 |

Let the carrier matrices be `A₀,A₁` and the completion matrices be `Λ₀,Λ₁`. The checked result is

```math
\operatorname{spec}(A_0)=\operatorname{spec}(A_1),\qquad
\operatorname{tr}(\Lambda_0^3)=14976,\qquad
\operatorname{tr}(\Lambda_1^3)=15360.
```

The last two integers differ by 384. Since a cubic trace is the sum of cubed eigenvalues, the completion spectra cannot be equal. This conclusion is exact; no numerical tolerance or visual comparison of plotted eigenvalues is required.

The paper's short algebraic proof separates each carrier into two eight-dimensional blocks. Both carriers have the same combined eigenvalues, but some eigenvalues move between the positive and negative polar sectors. The completion eigenvalues are the half-sums of one eigenvalue from each sector. Consequently equal combined carrier spectra need not give equal completion spectra. The Jordan representation and block-spectrum framework are attributed to Jonah's prior work.

## What is formalized, and what is checked separately

The [formal audit](../results/frontier-c3-lean-audit.md) records successful Lean 4.35.0 and Mathlib 4.35.0 checks. Its 42 C3 declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. The finite arithmetic uses kernel reduction. The proof includes the bridge from its integer matrices to the original Pauli sums and signed-context operators.

| Claim | Evidence and scope |
| --- | --- |
| The actual real Pauli section has 71 points and its complement has 64 points; the two sign assignments are valid. | Checked in the C3 Lean geometry development. |
| The original complex Pauli carriers have equal characteristic polynomials and canonical eigenvalue lists. | Checked in Lean, including an exact integer similarity certificate. |
| The original real signed-context completions have cube traces 14976 and 15360, unequal characteristic polynomials, and unequal real eigenvalue multisets. | Checked in Lean, preserving multiplicities. |
| The displayed common carrier polynomial factors as stated in the paper. | Exact algebraic and executable checks; not an additional conclusion of the 42-declaration Lean audit. |
| The largest completion eigenvalues differ by exactly 2. | Algebraic deduction from the block polynomials and completion formula; outside those Lean theorem statements. |
| The two continuous-relaxation minima differ by exactly 32. | Algebraic consequence of the largest-eigenvalue gap and the paper's normalization; outside those Lean theorem statements. |
| All 1120 outside contexts give the reported completion matrices and traces. | A separate direct signed-context program checks the construction and includes deliberate sign-error controls. |

The continuous relaxation replaces the 64 binary outside signs by a real vector `y` with squared length 64. Its objective is

```math
F(\sigma,y)=560-\frac14 y^{\mathsf T}\Lambda_\sigma y,
\qquad
\min_{\|y\|^2=64}F(\sigma,y)=560-16\lambda_{\max}(\Lambda_\sigma).
```

Assignment B's relaxed minimum is 32 lower than Assignment A's. The restriction to binary signs is different: the paper does not determine the exact binary minima, or even establish that they differ.

## Prior work and the contribution

B. W. Jonah's *The reach of the section-square law*, v0.5, defines C3 and Conjecture E and reports the three-qubit C3 case while leaving C3 at four or more qubits open. The inspected manuscript is dated 20 October 2026 and was deposited on 21 October. This certificate establishes the **four-qubit C3 instance of the failure predicted by Conjecture E**. It is a counterexample to the strict spectral law, not to Conjecture E. [Primary source](https://doi.org/10.5281/zenodo.23524332).

Jonah's earlier *Structure theorems for hyperplane completions in Pauli contextuality*, v0.3, already supplies the spectral-floor formula and related structure results. The repository's earlier bound work is presented with that attribution. The C3 witness is a separate result, using the existing spectral framework. [Prior spectral-bound source](https://doi.org/10.5281/zenodo.23538829).

The [source comparison](../results/frontier-prior-art.md) is a bounded literature audit, not an exhaustive priority proof or a statistical meta-analysis. This project does not establish all remaining dimensions of C3, all cases of Conjecture E, a classification of every cospectral carrier, or historical first priority.

## How to inspect or challenge the result

The [paper](../paper/c3-spectral-counterexample.md), [PDF](../paper/c3-spectral-counterexample.pdf), [witness data](../results/frontier-c3-n4-pair.json), and [formal audit](../results/frontier-c3-lean-audit.md) describe the same finite pair. The interactive verifier recomputes characteristic polynomials and cubic traces with JavaScript BigInt arithmetic when signs change. A modified assignment is not expected to preserve the certificate.

From the repository root, the principal independent executable checks are:

```sh
python scripts/frontier_c3_verify.py
python scripts/frontier_c3_context_verify.py
node tests/frontier_c3_browser_test.cjs
python scripts/frontier_c3_integer_bounds.py
python scripts/frontier_c3_demo.py
```

The final command requires the installed Tsotchke Eshkol toolchain. Its recorded serial compiled run checks an integer carrier-similarity certificate and reproduces the completion cube traces. The integer-bound replay is separate evidence about that execution. It does not certify the compiler, GPU operations, parallel execution, or physical quantum hardware. Moonlab, QGTL, and quantum_rng have separately documented roles in the earlier stack experiments; the C3 theorem does not depend on a hardware or randomness claim from them.

For formal reproduction, use the pinned Lean toolchain and dependency lock. From `lean/`, execute these targets sequentially:

```sh
lake build HoggarBound.C3Data
lake build HoggarBound.C3Certificate
lake build HoggarBound.C3Geometry
lake build HoggarBound.C3Theorem
lake build HoggarBound.C3Spectra
lake env lean C3Verification.lean
```

The audit records the substantial finite-certificate runtime and memory use; the interactive demo does not rerun Lean. Separate successful Windows and Ubuntu checks are recorded in [publication status](../publication/STATUS.md).

## Authorship and release status

The author credit is Alexander S. Donahue, affiliated with 0thernes LLC. OpenAI Codex agents performed substantive research, discovery, derivation, implementation, formalization, verification, visualization, and manuscript drafting under human direction, as disclosed in the paper. AI tools are not named as authors. Separate implementations and formal proof checking do not constitute human critical review or journal peer review.

The fixed research artifact is [v0.2.0-c3-certificate](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v0.2.0-c3-certificate). The [v1.2.0 edition](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v1.2.0) updates presentation and metadata while preserving that paper and proof content. [Publication status](../publication/STATUS.md) distinguishes the observed GitHub release from any later archive deposit, arXiv announcement, indexing, journal submission, or acceptance. See the [glossary](../GLOSSARY.md), [changelog](../CHANGELOG.md), and [license explanation](../LEGAL.md) for the surrounding documentation.

# Literature and mathematical-claims audit

Audit date: 2026-11-09. Scope: the claims in `NOTES.md`, a bounded search for closely related work, and an independent algebraic check. This is a critical literature synthesis, not a statistical meta-analysis and not a certification of priority. The separate Lean audit owns the actual kernel-build evidence.

## Finding that changes the novelty claim

**Correction after direct inspection of additional primary sources:** Jonah's *Structure theorems for hyperplane completions in Pauli contextuality*, v0.3, **21 October 2026**, already states the identical cubic spectral bound. Its Theorem 1 gives the cubic-trace identity for line-closed configurations; Lemma 5 gives the sharp third-moment optimization; Theorem 6 gives

\[
\operatorname{Spec}_X=\frac{m^{3/2}(D-2)}{6\sqrt{D-1}},
\qquad d(X)\ge(L-\operatorname{Spec}_X)/2
\]

for the full and hyperbolic families, and the Kramers refinement for the elliptic family. It also gives equality conditions and saturation cases in Theorems 6–8. These are direct matches, not merely related mechanisms. The earlier *Reach of the section-square law*, v0.5, 20 October 2026, Section 7, also uses the trace identity and spectral relaxation. The PDFs were downloaded from the primary Zenodo API and read. The earlier statement in this audit that no identical formula had been found is superseded. [Structure preprint, pp. 2–7](https://zenodo.org/records/23538829), [reach preprint, pp. 8–9](https://zenodo.org/records/23524332).

Brent W. Jonah's **20 October 2026** preprint, *A section–square law for Pauli quadrics, and an independently regenerated proof that the four-qubit elliptic quadric has contextuality degree 315*, already claims the exact degrees

\[
d(Q^-(7,2))=315,\qquad d(W(7,2))=1575,\qquad d(Q^+(9,2))=6975.
\]

It provides spectral/Hoggar constructions, finite enumeration and exact certificates; it explicitly describes its status as computer-assisted, not formally verified, and not peer reviewed. The primary Zenodo metadata, PDF and source TeX were retrieved directly. The supplied standard-library verifier `python -I -B code/check_p1r_v2.py .` completed successfully here, checking geometry, supplied orbit representatives, all 42 certificates, and witnesses. **The exhaustive census was not rerun**, so this audit does not independently establish the whole result. This prior claim must nevertheless be cited; the weaker bounds in this lab must not be advertised as the first resolution or the current strongest bounds for these three instances. [Primary deposit and files](https://zenodo.org/records/23510634), [DOI](https://doi.org/10.5281/zenodo.23510634).

The supportable contribution is a Lean formalization of this prior spectral bound, explicit finite corollaries, a kernel-checked three-qubit witness, and reproducible independently checked experiments. Our theorem also makes an arbitrary induced-support statement explicit. Jonah's Theorem 1 assumes line-closure; its page 3 scope paragraph excludes non-line-closed sets from that operator identity. Its Theorem 6 covers the three complete families. For arbitrary S, the cubic trace still counts induced lines because components of A² outside the span of S are orthogonal to A. Thus the trace identity and bound need less than line-closure, although the stronger operator identity need not hold. This is a modest relaxation of stated hypotheses, not evidence of a new spectral principle or established priority.

Jonah's separate 20 October digest announces five-qubit full and elliptic lower bounds 28830 and 6510, respectively, with proofs and code held privately. Its primary deposit metadata was checked; these announcements are not independently certified by this audit. Our values 28786 and 6501 should not be called the strongest reported bounds. [Primary digest](https://zenodo.org/records/23518569).

## Verified primary-source context

| Source | Evidence relevant to this lab | Consequence for wording |
|---|---|---|
| Li, Gupta and Ganesh, arXiv:2610.26465v1, submitted 19 October 2026 | Proves the four-qubit hyperbolic degree 315 and classifies 240 optimal violated sets; includes a Lean proof. Section 11 asks whether the five-qubit hyperbolic degree is 4743 and whether the hyperbolic degree always equals L/5 when integral. | Recovering 315 is a verification/example, not a new solution. A bound 6426 independently rules out 4743, but Jonah's earlier preprint already claims the stronger answer 6975. [Full text, §11](https://arxiv.org/html/2610.26465v1#S11). |
| Muller et al., arXiv:2407.02928v1; J. Phys. A 58 (2025) 215302 | Table 1 gives full-space upper bounds 1575, 31479, 553140 and 9406024 for N=4–7. Section 4 derives an L/5 lower bound. The quadric search gives 315 for both four-qubit quadrics and 6975/7087 for the five-qubit hyperbolic/elliptic cases. | These are useful published baselines and witness targets. Label upper bounds as upper bounds, not optima. [Full paper](https://arxiv.org/html/2407.02928v1), [journal DOI](https://doi.org/10.1088/1751-8121/add22b). |
| Muller et al., arXiv:2305.10225v3; MSCS 34 (2024) 322–343 | Establishes the three-qubit full-space degree 63, correcting the earlier value 90; discusses the associated 63-line hexagon. | The value 63 and geometric hexagon are prior results. [Full paper](https://arxiv.org/html/2305.10225v3), [journal DOI](https://doi.org/10.1017/S0960129524000057). |
| de Boutray et al., arXiv:2105.13798v4; J. Phys. A 55 (2022) 475301 | Defines contextuality degree through unsatisfied signed constraints and studies quadrics. The record notes a correction to Table 2. | Cite the corrected version when comparing numbers. [Primary record](https://arxiv.org/abs/2105.13798), [journal DOI](https://doi.org/10.1088/1751-8121/aca36f). |
| Cabello, arXiv:1002.3135v2; PRA 82 (2010) 032110 | Lemma 3 identifies its classical bound from the all-positive assignment. The three-qubit 63-violation witness yields a larger score than the claimed bound based on 90 violations. | Explain the precise failed bound and cite the later correction; do not call the whole contextuality framework false. [Lemma 3](https://arxiv.org/html/1002.3135v2), [journal DOI](https://doi.org/10.1103/PhysRevA.82.032110). |
| Muller and Saniga, arXiv:2609.19862v1, submitted 17 September 2026 | Studies general observable-context hypergraphs, reports epsilon=2d/L up to 0.707, and asks about limits for repeated copies of its graph constructions. | A limit proved for the full Pauli-line family does **not** settle the specific repeated-graph question. Context sizes and families differ. [Discussion](https://arxiv.org/html/2609.19862v1#S6). |
| Zhao et al., arXiv:2512.16654v2, revised 2 October 2026 | Bounds classical values of stabilizer-testing nonlocal games, including asymptotic examples. | Related asymptotic separation already exists in a different, state-dependent/nonlocal-game setting. Do not claim the first asymptotically strong contextuality result of any kind. [Primary record](https://arxiv.org/abs/2512.16654). |
| Stacey, arXiv:1609.03075v1 | Develops Hoggar SIC geometry and cubic purity constraints. | The Hoggar states and the broad purity/triple-product connection are established constructions. [Full paper](https://arxiv.org/html/1609.03075v1). |
| Godsil and Roy, *Equiangular lines, mutually unbiased bases, and spin models*, Lemma 3.1 | Proves that a maximal equiangular orbit of the tensor Pauli group can occur only at N=1 or 3. | The tensor-Pauli qualification matters: this does not forbid SICs in other dimensions with other covariance groups. [Primary manuscript, §3](https://arxiv.org/pdf/quant-ph/0511004). |

The scalar cubic inequality is classical: it is commonly called **Okumura's inequality**, rather than a new inequality discovered in this lab. Its exact trace form and attribution to Okumura (1974), Lemma 2.1, appear in Baltazar and Ribeiro, equation (3-12). [Primary research paper, p. 40](https://msp.org/pjm/2018/297-1/pjm-v297-n1-p02-s.pdf), [Okumura DOI](https://doi.org/10.2307/2373587). The original 1974 full text was not accessible during this audit; the modern paper's statement was read.

## Independent derivation and necessary hypotheses

Let S contain distinct **nonidentity** Hermitian tensor-Pauli operators on D=2^N dimensions. Include **every** commuting line whose three vertices lie in S. For f:S→{−1,+1}, put A=Σ f(v)P_v and let β be the signed satisfied-minus-violated line count. Orthogonality gives tr A=0 and tr A²=D|S|. In tr A³, products with nonzero total Pauli label have zero trace. Each commuting zero-sum triple contributes six equal real terms; the anticommuting permutations cancel. Therefore tr A³=6Dβ. For an arbitrary subset of lines this identity generally fails.

For n real numbers λ_i with sum zero and Σλ_i²=nm, put a=√((n−1)m). Cauchy–Schwarz on all coordinates except i proves λ_i≤a. Summing

\[
(a-\lambda_i)(\lambda_i+a/(n-1))^2\ge0
\]

gives

\[
\sum_i\lambda_i^3\le \frac{nm(n-2)a}{n-1}.
\]

Taking n=D and m=|S| proves the notebook's general bound. This elementary derivation does not need an optimization heuristic or a random-number generator. Random search can test implementations and find upper-bound witnesses; it cannot establish the universal inequality.

For the full Pauli space (N≥2), m=D²−1 and L=(D²−1)(D²−4)/12, yielding

\[
d/L\ge\tfrac12-\frac{\sqrt{D+1}}{D+2}.
\]

Averaging independent unbiased signs shows some assignment violates at most L/2 contexts. Consequently this family has d/L→1/2. This conclusion is an analytic consequence, not an empirical fit. Formal status of the limit must be distinguished from the finite Lean theorem unless separately kernel checked.

## Corrections and exclusions for the manuscript

1. **Kramers hypothesis:** setwise invariance of S under an antiunitary is insufficient. One needs θAθ⁻¹=A with θ²=−I; pointwise fixation of every chosen P_v is a sufficient condition for every assignment. Only then may the paired spectrum be reduced to n=D/2.
2. **Equality case:** for nonempty S and n=D, equality forces a rank-one top eigenspace and a pure state with constant nonzero Pauli modulus √((D−1)/|S|). Under the Kramers refinement the corresponding equality object is a rank-two normalized projector, not a pure state supported only on the elliptic quadric. The coefficient is √((D/2−1)/|S|). Zero-size and low-dimension cases need separate treatment.
3. **Rounded values:** independent 50-digit Decimal evaluation gives full-space integer lower bounds 2, 63, 1451, 28786, 527621, **9227609**, 156705492 for N=2,…,8. The notebook's approximate N=7 entry 9227604 is inaccurate. Integer certification should use exact rational comparisons rather than floating-point rounding near equality.
4. **Terminology:** simulated quantum measurements are not physical quantum experiments; the quantum-inspired QRNG is not certified physical quantum randomness. A proof assistant verifies a mathematical statement in its declared model, not novelty, experimental validity, or Nobel-level importance.
5. **Scope:** 1451 and 6426 are valid lower bounds if the formal model/build checks pass, but they do not establish the exact optima 1575 and 6975. The external Jonah claim should be described separately from this lab's checked theorem.
6. **Suggested paper claim:** “We formalize and independently validate the spectral lower bound used in Jonah's October 2026 preprints, state it for arbitrary induced Pauli supports, and provide checked finite corollaries and reproducible saturation examples.” Avoid “unprecedented,” “first ever,” “definitive proof of quantum advantage,” or “solves all contextuality degrees.”

## Search and reproducibility record

The later J2/J3/J4 leads came from the concurrently written main manuscript and were treated as leads, not evidence. J2 was retrieved through https://zenodo.org/api/records/23538829 and its primary PDF, NOTE_STRUCT_v0_3.pdf (494933 bytes; MD5 768047b62152d5166c1376d72a7c4303, matching the API). The relevant inspected passages are Theorem 1 and its scope, pp. 2–3; Lemma 5/Theorem 6, p. 5; and the saturation classification, pp. 6–7. J3's NOTE_SQREACH_v0_5.pdf (411588 bytes; API MD5 a81bec21afb99c066a3a4b86a8119c18) was also downloaded and Section 7 read. The primary metadata for record 23518569 supplies the status of the J4 announcements. No private proof or data commitment was treated as an accessible proof.

Primary arXiv records and full texts were accessed directly. Searches included `Pauli contextuality third moment`, `contextuality Hoggar bound`, `Pauli skewness contextuality`, `Pauli Okumura`, and related spectral-bound phrases. The search identified Jonah's deposit through an index; all claims used above were then checked against the primary Zenodo API and downloaded source. This is a bounded review, not an exhaustive citation census.

Zenodo artifacts retrieved: `NOTE_P1R_v0_7.pdf` (343012 bytes; declared MD5 `2b63970649b6eaff5eb1ff2e5cc3e547`) and `P1R_EVIDENCE_20261020.zip` (692655 bytes; declared MD5 `7479545baedd953ebcea12413b6c08ad`). Temporary audit copy: `%TEMP%/hoggar-literature-audit/`. The verifier completed with exit code 0 and `VERDICT: ALL CHECKS PASS`; the census, transfer scripts, classification and proof-log checker were not run as part of this literature audit. No third-party proof result is silently imported as a Lean theorem.

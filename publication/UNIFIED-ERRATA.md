# Clarifications incorporated into the combined manuscript

The canonical combined manuscript is [unified-contextuality.md](../paper/unified-contextuality.md),
version 1.2.0. The original [spectral-floor manuscript](../paper/spectral-floor.md) and
[C3 manuscript](../paper/c3-spectral-counterexample.md) remain preserved as source studies. The
baseline used for integration is commit `8add759`; source hashes and the section/reference mapping
are recorded in [unified-source-map.json](../results/unified-source-map.json).

The items below supersede the corresponding prose in the preserved floor study. They make domain
hypotheses, degenerate cases and verification limits explicit. They do not change the Lean sources,
the universally quantified `hoggar_bound` theorem, the exact degree certificates, or the checked C3
operators and spectral conclusions. The universal floor still applies to arbitrary supports,
including the empty set, for every number of qubits covered by its original statement.

| Original location or wording | Combined-manuscript correction | Reason |
| --- | --- | --- |
| Section 2: closure under products of any two commuting observables | Require distinct commuting labels `u,v` in the support to have `u+v` in the support; operator products are understood up to sign | A label multiplied by itself gives the excluded identity. Commuting Pauli products may also have a minus sign. |
| Section 2: the coordinate `c` also names the full symplectic offset of a quadric | Use `w` for the quadric offset and retain `(a,c)` for the Pauli label | Prevents the same symbol from simultaneously denoting an N-bit coordinate and a 2N-bit offset. The formulas are equivalent. |
| Theorem 2: quaternionic formula without an explicit lower limit on N | State N at least 2; take one eigenvalue from each Kramers pair, with pair multiplicity | The displayed denominator contains `sqrt(D-2)`, and the scalar argument needs at least two pairs. Pair values need not be distinct. |
| Closed-form table and Section 6 ratios | Interpret violated fractions only when the context count is positive; full-space ratios and noise thresholds use N at least 2 | A configuration with no contexts has degree zero but no defined violated fraction. The count inequality retains N at least 1. |
| Theorems 3 and 4: saturation equivalence for an unspecified support | Require a nonempty support | The state modulus divides by the support size; the zero matrix does not have the claimed simple largest eigenvalue. The general lower bound itself needs no such restriction. |
| Proposition 3: metric equalities characterized satisfied and violated contexts without excluding zero expectations | Require the three expectations on the tested context to be nonzero | Otherwise the sign assignment is undefined or convention-dependent, and the two metric expressions can coincide. All tested flat-support contexts satisfy the added condition. |
| Theorem 4(d): outside sum for every point outside the support | Explicitly exclude the identity label | The outside sum was defined only for nonzero outside points. |
| Proposition 9: signed stabilizer groups meet only in the identity, therefore the states are mutually unbiased | Require complementary underlying Pauli label spaces | Signed groups of orthogonal states can intersect only at the identity: the groups for `|0>` and `|1>` are a counterexample to the original wording. Complementary label spaces supply the claimed overlap. |
| Proposition 10: graph has all three listed eigenvalues, including in the complete case | Specify its degree and say nonprincipal character eigenvalues lie among the two displayed candidates; absent character classes contribute no eigenvalue | For the full Hoggar support the graph is complete, and one candidate eigenvalue is absent. The character identity is unchanged. |
| Theorem 12: closing description excluded every four-qubit flat phase state | Retain the theorem's nonzero-form restriction throughout the conclusion | The zero form gives diagonal-Clifford stabilizer states, which are flat for every N. The enumerated nonzero forms and orbit counts are unchanged. |
| Seven-qubit discussion: the circuit is the only flat phase state | Describe the suggested unique class with nonzero associated form, up to CNOT circuits and diagonal Clifford gates | The evidence is a census within one family and random samples outside it; it does not exclude the zero-form stabilizer states or prove uniqueness beyond the tested family. |
| Nine-qubit discussion: a flat phase state would have 130816 support points and modulus 1/16 | Identify these values with the constant-rank-eight candidate family | Proposition 11 alone allows support size `(D-1) 2^r` for other constant even ranks; it does not force rank eight at nine qubits. |
| Limitations: only three-, five- and seven-qubit flat phase states are available | Name the nonzero-form odd-qubit family with constant rank N−1 | The text also gives a two-qubit example, and zero-form stabilizer states exist for every N. The nine-qubit question concerns the specified rank-eight family. |
| Limitations: all exact four- and five-qubit classical-family values are unformalized | Name the external values for the four-qubit full space, four-qubit elliptic quadric and five-qubit hyperbolic quadric | The four-qubit hyperbolic degree 315 has Lean proofs and must not be included in that blanket exclusion. |
| Following the flat-state table: first seven rows are proved in Lean | Specify exact-degree statements for the seven explicit masks and their finite counts; state identification is checked separately | A table row also contains state, modulus, excess and geometry information outside those Lean statements. |
| Section 10: every implementation agrees on every number in the paper | Describe agreement on overlapping checks and state the different implementation scopes | The seven-qubit counts are not kernel-evaluated, and C3 has its own independent verifiers. |
| Moonlab noise table: all ceilings described as spectral-floor ceilings | Identify the two-qubit value 0.800 as using the known exact degree 3 | The spectral floor alone rounds to 2 for the full two-qubit configuration. The displayed numeric value was correct; its attribution needed qualification. |
| Appendix A: saturation proof builds use under 5 GB each | Refer to measured CI evidence rather than that resource estimate | The successful saturation CI recorded peak RSS above 5 GiB. Its timings and memory values are observations, not portable guarantees. |

The combined text also records the precise C3 verification boundary: equality of the original Pauli
carrier spectra, inequality of completion spectra, and cube traces 14976/15360 are Lean-checked. The
printed polynomial factorizations, largest-eigenvalue gap two, and spherical-relaxation gap 32 are
exact algebraic and executable results outside that 42-declaration audit. A spherical gap is not a
claim about the binary optimum.

The combined manuscript adds a direct connection between its two parts: both C3 assignments violate
132 of the section's 455 contexts, despite the different completion spectra. This follows from the
existing trace identity and is also recounted by `scripts/unified_section_score.py`; the evidence is
`results/unified-section-score.json`. It is an ordinary derived/executable observation, not a new
specialized Lean theorem.

The corrected funding paragraph states only the information supplied by the author: the research
was self-funded, and the author is the sole operator of the affiliated 0thernes LLC. Additional
competing interests and completion of venue-specific human critical review remain undeclared. The
combined AI disclosure distinguishes the Claude-developed floor study from the Codex-developed C3,
independent checks and integration. No external peer review is claimed.

These corrections were identified during manuscript integration and independent mathematical review.
They are reported openly so readers can distinguish the combined manuscript from its preserved
precursors; no released artifact is silently rewritten.

## Version 1.3.0 (10 November 2026)

Three statements above describe the state of version 1.2.0 and are superseded by later work, not by a
correction of the record: the exact-degree statements now cover all eight masks of the flat-state
table; the seven-qubit counts are kernel-evaluated (`phase7_contexts`, `phase7_degree`; see
[ADDENDUM-seven-qubit-lean.md](ADDENDUM-seven-qubit-lean.md)); and the author has since declared no
competing interests (Section 13 of version 1.3.0; [AUTHOR-DECLARATIONS.md](AUTHOR-DECLARATIONS.md)).
The canonical manuscript named in the first paragraph is now version 1.3.0. Version 1.3.0 of the combined
manuscript also folds in the other addenda of this folder; see [PAPER-MAP.md](PAPER-MAP.md) and the
[changelog](../CHANGELOG.md).

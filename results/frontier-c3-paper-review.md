# Final C3 preprint layout review

Date: 2026-11-09. Result: **PASS for the identified nine-page PDF**. Every page was rendered with PyMuPDF at 1.2 times PDF resolution to `build/c3-final-paper-preview/page-1.png` through `page-9.png` and inspected individually with the image viewer. The PDF was not modified during this review.

## Identified artifact

- File: `paper/c3-spectral-counterexample.pdf`
- Size: 96,260 bytes; nine pages.
- SHA-256: `5be6ba1318ce5cfeebf3a89b79dcfd428f87e228234e2f5075b14807a7f34836`
- Markdown SHA-256, exact local bytes: `7b394af67904619b5d77bb3bca7f911396d8c90879e4b561875da0053c678453`
- Markdown SHA-256, LF normalized: `8f5f4827ce8c46a65cc3dd270a9386e094ca4f3379c14971ffe00985c0a8c018`
- TeX SHA-256, exact local bytes: `56107c5941a92c12f04f508c09031859b9957025b8606f5524bbbe3dcbcb7142`
- TeX SHA-256, LF normalized: `9e6ca0f4b51ce3ec5bf25b32bfe335e8bc42f105c752fbaf7b085a40c70159c8`
- Build provenance: `results/frontier-c3-paper-build.json`; Pandoc 3.13 and Tectonic 0.17.0.

The PDF hash was recomputed after visual inspection and still matched this record. Source hashes above are the matching build record's values; LF normalization distinguishes Git-normalized text from local Windows line endings.

## Result

The nine-page final technical manuscript is readable. No clipped equation, missing mathematical glyph, overlapping text, cropped table, broken figure, or text outside the page margins was observed. LaTeX subscripts, superscripts, Greek letters, transposes, block matrices and polynomial expressions render correctly. The former Unicode mathematical-glyph issue is resolved in these renders.

| Page | Observed result |
| --- | --- |
| 1 | Title, author, business correspondence address, date and preprint status are clear. The abstract's completed Lean-verification sentence, spectral question and short primary-source quotation are readable. |
| 2 | Pauli conventions and numeric labels are legible. The four-negative-sign specification table fits the margins and preserves all entries. |
| 3 | Completion normalization, exact theorem, common characteristic polynomial and block decomposition render correctly. Equation numbers remain separated from equations. |
| 4 | Four-block specification, polynomial-factorization table, real off-diagonal block representation and completion-spectrum formula are readable. The table is compact without clipping. |
| 5 | Cubic-trace identity and its two evaluations are clear. Largest-eigenvalue and continuous-relaxation corollaries fit the margins, with the binary-optimum limitation visible. |
| 6 | Both spectrum panels, axes and legends are visible. The caption maps Assignment A/B to the sign assignments and distinguishes numerical display from exact proof. The smallest figure annotation is readable at page zoom. Verification and negative-control prose is intact. |
| 7 | Eshkol execution details and final Lean section are legible, including long theorem names. Standard axiom dependencies and exclusions of the displayed factorization and gaps from Lean scope are visible. Source-comparison limitations follow cleanly. |
| 8 | AI provenance and self-funding/LLC disclosures are readable. Python/Node commands and sequential Lean commands each form intact code blocks. The recorded finite-proof runtime is distinguished from a physical process or interactive-demo runtime. |
| 9 | Remaining artifact/version notes and all four references are readable. Link text is distinct and long artifact names remain within margins. The shorter final page is acceptable. |

## Resolved draft concerns

The three minor concerns in the earlier eight-page draft have been addressed: the cube-expansion introduction stays with equation (8), reproduction commands are intact, and the figure caption maps both assignments explicitly.

## Scope and publication consistency

The final PDF identifies itself as a research preprint, not peer-reviewed publication. Its metadata names Alexander S. Donahue and 0thernes LLC. A scoped contact scan of 12 text files in the publication package/C3 sources and the PDF text/metadata found only the authorized address `0_0@0thernes.art`; LaTeX-escaped underscores were normalized for that comparison. No personal account address was found in that scope. The PDF contains nine link annotations; this layout review did not retest every remote destination.

The formal section agrees with `results/frontier-c3-lean-audit.md`: 42 declarations, actual original Pauli and signed-context operators, carrier cospectrality, completion noncospectrality, and cubic traces 14976/15360. The factored polynomial and exact gaps two and 32 have separate algebraic/executable evidence and are explicitly outside those Lean theorem statements.

This is automated-agent visual QA of the identified files. It is not human critical review, author approval, an external referee report, a priority determination, or a submission/acceptance event. Any change to the PDF after this hash requires a new identified review.

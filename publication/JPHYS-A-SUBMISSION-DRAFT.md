# Journal of Physics A submission preparation

Prepared 2026-11-09. Local draft only: not submitted, not signed, and not a declaration of completed human critical review. The author identity and publication correspondence address below were explicitly confirmed by the user. No ORCID was supplied.

## Form metadata

| Field | Prepared value |
| --- | --- |
| Journal | Journal of Physics A: Mathematical and Theoretical |
| Article type | Paper |
| Title | Cospectral Pauli carriers with different completion spectra: an exact four-qubit C3 certificate |
| Author | Alexander S. Donahue |
| Affiliation | 0thernes LLC |
| Corresponding author | Alexander S. Donahue |
| Publication correspondence | 0_0@0thernes.art |
| Suggested subject | Quantum mechanics and quantum information theory; foundations of quantum mechanics |
| Additional subject, if available | Mathematical physics; physical combinatorics; operator theory |
| Keywords | Quantum contextuality; Pauli operators; spectral invariants; finite geometry; formal verification; reproducible computation |
| Publication model recommendation | Standard subscription route; no optional gold-open-access purchase requested |
| Existing preprint location | [Public paper record](https://0thernes.github.io/hoggar-bound-lab/paper/c3-spectral-counterexample.html) and [versioned release](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v0.2.0-c3-certificate); no arXiv ID or Zenodo DOI has been assigned |
| Funding declaration | This research was self-funded by the author. |
| Competing interests disclosed so far | The author is the sole operator of 0thernes LLC, with which this project is affiliated. |
| Other competing interests | Not yet explicitly declared; do not infer that none exist. |
| Final author approval | Pending review of the concrete final manuscript |
| Simultaneous journal review | Must be absent at actual submission; do not mark a present-tense certification here |

The author should confirm the business affiliation's city/country only if the submission form requires them. Do not infer these from a computer timezone or IP address.

The funding and LLC relationship statements above were supplied by the author. They do not certify a legal nonprofit or tax status, and they do not establish that the author has completed the final manuscript's critical review or approval.

## Abstract draft

We specify two sign assignments on a 71-point hyperplane section of the real four-qubit Pauli configuration. Their 16-by-16 carrier operators have identical characteristic polynomials, while their 64-by-64 completion operators have cubic traces 14976 and 15360. The carrier spectrum therefore does not determine the completion spectrum in case C3 of Jonah's classification. This establishes the four-qubit C3 instance of the failure predicted by Conjecture E in the cited preprint. Each assignment is specified by four negative Pauli words. Four block-polynomial factorizations and an exact trace identity give an algebraic certificate. The mechanism redistributes eigenvalues between the two eigenspaces of the polar Pauli observable while preserving their combined multiset. A Lean 4 development verifies carrier cospectrality and completion noncospectrality, including the connection to the original Pauli model and the two exact cubic traces. Separately, algebraic arguments give a largest-completion-eigenvalue gap of two and a continuous-relaxation gap of 32. Independent literal-matrix and signed-context programs provide reproducible checks, including deliberate sign-mutation controls. The result does not settle higher-dimensional cases, exact binary completion optima, historical priority, or physical experiments.

The completed audit uses Lean 4.35.0 and Mathlib 4.35.0 and checks 42 declarations with only `propext`, `Classical.choice` and `Quot.sound`. It covers the actual 71-point section, 64 outside labels, original Pauli carriers, original signed-context completions, carrier characteristic-polynomial and eigenvalue equality, and completion characteristic-polynomial and eigenvalue-multiset inequality. The printed polynomial factorization, block/Jordan derivation, largest-eigenvalue gap two and continuous-relaxation gap 32 are separately checked algebraic results, not additional Lean theorem conclusions. See `results/frontier-c3-lean-audit.md`.

## Cover text draft

This manuscript presents an explicit finite result about the information retained by a spectral relaxation of Pauli contextuality. It constructs two sign carriers on the same real four-qubit polar section whose carrier characteristic polynomials coincide, while their completion spectra differ. This resolves the four-qubit C3 instance explicitly left open in the inspected version of B. W. Jonah's preprint, *The reach of the section-square law* (DOI 10.5281/zenodo.23524332). It confirms that instance of the failure predicted by Conjecture E; it does not refute the conjecture or claim its resolution in arbitrary dimension.

Each witness is fully specified by four negative Pauli words. A short block-polynomial and cubic-trace argument supplies an exact certificate. The completion operators' largest eigenvalues differ by exactly two, so the failure affects the associated continuous relaxation rather than only a non-extremal spectral statistic. Literal-matrix, signed-context and browser implementations provide separate executable checks and deliberate error controls. A completed Lean 4 development proves carrier cospectrality and completion noncospectrality for the original Pauli operators and signed contexts, including the exact cubic traces. Its 42 audited declarations use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; the source and successful audit are supplied. The printed factorization and exact spectral-gap corollaries have separate algebraic and executable checks and are explicitly outside the Lean theorem statements.

We consider the paper relevant to the journal's quantum foundations and mathematical physics readership. The manuscript attributes the underlying Jordan representation and spectral machinery to prior work and limits its new claim to this explicit finite certificate and its consequences. Its substantial generative-AI involvement is disclosed in the manuscript and supporting materials.

This is prepared descriptive cover text. Before submitting, replace prospective phrases with the actual final package state and add only true author-controlled declarations concerning approval, exclusivity, rights, funding and conflicts. No journal acceptance or willingness to review is implied.

## Detailed AI-role disclosure draft

**Factual process description:** OpenAI Codex AI agents were used on 9 November 2026 for research problem selection within a human-requested project, primary-source literature discovery and checking, candidate construction and computational search, algebraic derivations, program and test generation, Lean proof authoring, execution and inspection of verification tools, figure and interactive-demo production, and manuscript drafting and revision. The AI role extended well beyond language editing. The algorithms, explicit witnesses, exact arithmetic certificates, code and successful verification logs are the evidence for the reported finite calculations; agent prose is not treated as the mathematical certificate.

The comparison with prior work was performed by AI agents against retrieved primary documents. The mathematical example was found and checked by AI-assisted computational workflows. Several checks used separately implemented algorithms, but this does not constitute independent human review. The plotted spectra are numerical displays of explicitly defined finite matrices; they are not physical measurements. SymPy, NumPy, JavaScript BigInt, Lean/mathlib and Eshkol are computational tools used in the disclosed workflow. Their roles and versions should be taken from the final release records.

**Model provenance:** Record the actual model names/versions where the execution record exposes them. Where only the Codex product/agent identity and date are retained, state that limitation rather than invent a model identifier. Add any other AI provider only if it contributed to this particular manuscript or its research, and describe that contribution separately from the project's earlier spectral-bound work.

**Human contribution and accountability, to be completed by the author:** The user initiated and directed the broad project. The record available to this preparation task does not establish that Alexander S. Donahue has personally reconstructed the proof, checked all references, reviewed the generated code or critically revised and approved the final manuscript. The author must accurately describe the intellectual contribution, critical review, validation and final approval actually performed, and accept responsibility as required by the journal. Do not turn this unfinished paragraph into an assertion that those actions have already occurred.

For IOP submission, put the substantive research-tool use in Methods and a concise tool/purpose/verification statement in a separate AI disclosure within Acknowledgments. The actual extent of human review belongs in the final statement. IOP's current policy permits disclosed AI research assistance but requires author validation and critical engagement. [Official AI policy](https://publishingsupport.iopscience.iop.org/questions/generative-ai-tools/).

## Data and code availability draft

The explicitly defined Pauli sign assignments, finite matrices, exact certificates, verification programs and formalization source are available in the Hoggar Bound Lab [release v0.2.0-c3-certificate](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v0.2.0-c3-certificate), at fixed commit `d3811e3b53048fa8f3206f08494f0a9834eed287`. The release includes the final paper and checksummed verification evidence. A DOI archive may be added if a compliant deposit is completed. The project currently uses a custom verification license permitting download, build, execution, study and attributed quotation for checking and reproducing the results; it does not grant unrestricted modified redistribution or commercial use. Third-party components retain their own licenses. See the release's `LICENSE` and `NOTICE` files.

Use that fixed release for submission and reproducibility. No DOI has been assigned to this paper. If a paper-specific license is later authorized, identify it separately from the code license.

## Attachments to prepare

1. Final complete manuscript PDF with all figures and tables, an accurate AI disclosure and the final formal-verification boundary.
2. A compact supplement/readme linking the frozen code release, exact witness, independent checks and the Lean reproduction command and audit.
3. Figure source/data and editable TeX/bibliography retained for revision and production.
4. Final checksums and concise dependency information; exclude credentials, private correspondence and unrelated local files.

IOP allows an initial complete PDF and relevant supplementary data; the workflow and applicable author responsibilities are linked in `ROUTES.md`. No editorial message, reviewer invitation, submission, rights grant or payment has been made by this preparation task.

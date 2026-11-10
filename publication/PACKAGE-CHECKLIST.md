# C3 submission package checklist

Prepared 2026-11-09. This is a checklist, not a completed submission or an attestation by a human author. The mathematical and administrative gates are separate.

## Claim and manuscript

- [x] Freeze release commit `d3811e3b53048fa8f3206f08494f0a9834eed287`, published as `v0.2.0-c3-certificate`. See `STATUS.md` for observed public records.
- [x] Produce the final technical manuscript `paper/c3-spectral-counterexample.md`, its LaTeX source and nine-page PDF. Human critical review and approval remain separate below.
- [x] Replace the formal-verification placeholder with checked theorem names, exact statement boundaries, Lean/Mathlib 4.35.0 and the successful 42-declaration axiom report. The factored polynomial and exact gaps 2 and 32 are explicitly outside the Lean theorem conclusions.
- [x] Preserve the exact claim: 71-point section, 64 outside labels, 1120 outside contexts; equal carrier characteristic polynomials; completion cubic traces 14976/15360; largest-eigenvalue gap 2 and continuous-relaxation gap 32.
- [x] Clearly distinguish a counterexample to the strict spectral law from confirmation of the four-qubit C3 instance of Jonah's Conjecture E. No claim that Conjecture E was disproved or all dimensions were settled.
- [x] Keep physical experiments, exact binary completion optima, historical priority and general novelty outside the established claim.
- [x] Include the primary J3 citation and relevant J2 attribution, supported by the recorded primary-source audit.
- [x] Classify the work as an original mathematical/computational research preprint, not a statistical meta-analysis.
- [x] Visually inspect all nine final pages and record PDF/source checksums in `results/frontier-c3-paper-review.md` and `results/frontier-c3-paper-build.json`. This is automated-agent layout QA, not human author approval or journal peer review.

## Human authorship and disclosure

- [x] Record the user-confirmed author identity: Alexander S. Donahue, 0thernes LLC. The root agent added C3-specific `paper/c3-citation.cff`. Identity confirmation does not by itself certify intellectual contribution or completed critical review.
- [ ] Confirm that the human author meets this manuscript's actual contribution and accountability requirements.
- [ ] Record the author's actual intellectual contribution, critical revisions, verification performed, final approval and responsibility. Do not substitute automated agent review for a statement that the human personally performed it.
- [ ] Resolve Zenodo's human-conducted research eligibility before deposit. The certificate's mathematical validity does not answer that separate policy question.
- [x] Use the user-confirmed affiliation, 0thernes LLC. No honorary university affiliations or invented credentials.
- [x] Use the user-designated business correspondence address `0_0@0thernes.art` in the publication package. No ORCID was supplied; omit it. No personal account email belongs in the package.
- [ ] Obtain or recover the author's own ORCID for Journal of Physics A: IOP requires it for the submitting author. The current absence of an identifier is a pending account requirement, not a reason to invent one.
- [x] Record the author-supplied funding statement: “This research was self-funded by the author.”
- [x] Record the author-supplied relationship disclosure: “The author is the sole operator of 0thernes LLC, with which this project is affiliated.”
- [ ] Complete any additional competing-interest declaration required by the venue. No statement that other interests are absent has been supplied; do not infer “none.”
- [ ] Disclose OpenAI Codex AI agents, use date(s), and actual model/version identifiers when available. Include search, candidate generation, mathematical derivation, code, formal proof authoring, validation, figures and manuscript drafting/revision as applicable. Add other AI systems only where their contributions to this artifact are evidenced.
- [x] Distinguish independent implementations from independent human peer review. Neither the code review nor a Lean proof is journal peer review.

Draft factual disclosure core, to be completed with the actual human review rather than a pre-signed attestation:

> OpenAI Codex AI agents were used on 9 November 2026 for literature discovery and checking, finite-example search, mathematical derivation, implementation, formalization, validation, visualization and manuscript drafting. The computational methods, certificate files, versioned code and verification records are provided for inspection. [Human author: add the actual intellectual contributions and the extent of critical review and validation completed.]

The bracketed instruction is an unfinished field, not a completed attestation. Replace it with an accurate statement before submission; do not assert that the human performed checks which were performed only by AI agents or automated tools.

## Reproducibility payload

- [x] Final paper PDF, editable TeX/Markdown, figure files, references and concise build instructions.
- [x] Exact witness and matrix/certificate JSON, including `results/frontier-c3-n4-pair.json`, the literal-matrix verification report, completion data and integer similarity certificate.
- [x] Independent signed-context verifier and `results/frontier-c3-context-verification.json`, including the negative-control results.
- [x] Browser model and `tests/frontier_c3_browser_test.cjs`; the public demo was checked against release commit `d3811e3b53048fa8f3206f08494f0a9834eed287`.
- [x] Lean sources, `lean-toolchain`, dependency lock information, exact reproduction command, complete successful log and axiom audit for the final C3 theorem.
- [x] Eshkol program generation, integer-bound replay, successful execution report and process-local toolchain requirements in `results/frontier-c3-eshkol.json`. Its qualification is explicitly serial.
- [x] Dependency versions and environment information in the context verifier, Lean audit, paper/source build and Eshkol reports; SHA-256 checksums in the release. The Lean manifest distinguishes raw-byte and LF-normalized source hashes.
- [x] Package only relevant research artifacts: the release asset and portable-source allowlists exclude private correspondence, caches, dependency trees and unrelated chat transcripts. Published source and evidence received a scoped contact/privacy check.
- [x] Retain original third-party copyright and license notices. The manuscript summarizes AI provenance; no independent human provenance review is asserted.

## Licenses and identifiers

- [x] Read the current repository `LICENSE` and `NOTICE`. It is a custom verification license, not MIT/Apache/CC BY and not unrestricted open source.
- [ ] Make an explicit paper license decision. CC BY 4.0 is compatible with the checked Quantum/SciPost final-publication requirements, but selecting it grants rights beyond the existing project license; do not apply it automatically to all code and third-party files.
- [ ] Put any separately authorized paper license in a clear paper-level notice. Ensure Zenodo license metadata accurately describes each included class of file; it supports mixed/custom licenses.
- [ ] Use a version DOI for the fixed paper/artifact and record its relationship to repository releases and any separate supplement. Do not invent DOI strings or assign competing DOIs to the same deposited object.
- [x] C3-specific citation metadata was added by the root agent at `paper/c3-citation.cff`. Keep it synchronized with final publication metadata; do not re-use the earlier paper's title or preferred citation.
- [ ] Record arXiv ID, journal submission ID and eventual publication DOI only after observing real platform acknowledgments.

## Route-specific files and gates

**Zenodo:** account authentication; human-author eligibility; correct resource type (preprint for paper, software/dataset for distinct supplements); files, creators, description, publication date, version, license and related identifiers. Reserve the DOI before final PDF build if appropriate; publish only the finalized files.

**arXiv:** an authenticated author account was observed on 2026-11-09; account access is resolved. The author deferred submission. Any required quant-ph endorsement, informed license choice and author-controlled submission attestations remain pending. The author explicitly retained Alexander S. Donahue, 0thernes LLC as the manuscript credit after comparison with the account profile. The minimal XeLaTeX archive with its figure and ancillary notices is prepared, locally compiled and included in the public release as `c3-source-xelatex.zip`; arXiv's own server compilation remains to be tested. The current polished PDF alone is insufficient because it derives from LaTeX. Keep large artifacts in the versioned GitHub release, or a DOI archive if subsequently deposited, and include only useful ancillary files.

**Journal of Physics A:** complete PDF and supplements; truthful author/contact/contribution/funding/interest statements; research-data availability; separate AI acknowledgment and research-method description; concise cover text explaining the C3 result and its boundary; original research Paper classification. Standard subscription publication avoids an optional APC.

**Quantum Information Processing:** editable source plus PDF, 150–250 word abstract, 4–6 keywords, title-page contact fields, required submission-interface declarations and Methods AI disclosure. Consider only after the previous journal process is closed or withdrawn.

**Quantum:** quant-ph arXiv identifier, Scholastica access, 1–3 topical groups, author contribution/AI statement and a candid significance case. No simultaneous journal submission. Do not select a paid option without a deliberate funding decision.

**SciPost:** the current broad AI involvement conflicts with the inspected authoring policy. Do not treat it as ready to submit or conceal AI scope. Live database-driven acceptance criteria were not retrievable in this review.

## Evidence and reporting

After each action, retain the platform's actual identifier/status, date, file hashes and public URL. Say “archived,” “preprint announced,” “submitted,” “under review” or “accepted” only when the corresponding event is observed. A DOI deposit or search listing must never be reported as peer-reviewed acceptance. Policy citations and the basis for route choices are in `ROUTES.md`.

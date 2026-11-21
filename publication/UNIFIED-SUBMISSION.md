# One combined manuscript: submission package

**Spectral bounds and their limits in Pauli contextuality: exact configurations and a proof of Jonah's Conjecture E**

Version **1.8.0** (21 November 2026; built cleanly on versions 1.4.0–1.7.0; version 1.2.0 was titled *Spectral bounds and their limits in Pauli contextuality: exact configurations and a four-qubit C3 certificate*). Author: **Alexander S. Donahue — 0thernes LLC**. Correspondence:
**0_0@0thernes.art**. ORCID: [0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648).

This is the single current manuscript requested by the author. The earlier spectral-floor and C3
submission drafts describe preserved source studies; they must not trigger separate submissions of
the combined material. The [paper map](PAPER-MAP.md) records their relationship. Prepared files and
saved account details are not submission receipts or evidence of acceptance.

## Files and destinations

| File | Use |
| --- | --- |
| [Canonical manuscript](../paper/unified-contextuality.md) | One editable source, common notation, bibliography and proof boundaries |
| [Full PDF](../paper/unified-contextuality.pdf) | Public research preprint; identical to the full typeset PDF |
| [Full HTML](../paper/unified-contextuality.html) | Public abstract/full text and Scholar citation metadata |
| [Journal manuscript](unified-contextuality/jphysa/manuscript.pdf) | Main PDF for Journal of Physics A: Mathematical and Theoretical |
| [Journal supplement](unified-contextuality/jphysa/supplementary.pdf) | Tools, executable checks, reproduction and witness material |
| [Section map](unified-contextuality/journal-section-map.json) | Explicit main/supplement allocation; section numbers remain those of the full paper |
| [arXiv source archive](unified-contextuality/arxiv-source.zip) | Portable XeLaTeX source and required figures |
| [Submission metadata](unified-metadata.json) | Title, author, abstract, public URLs and actual declaration status |
| [Plain-text abstract](unified-abstract.txt), [BibTeX](unified-citation.bib) | Form-ready abstract and preprint citation without invented journal or DOI fields |
| [Build record](../results/unified-paper-build.json) | Compiler versions, file hashes, counts and artifact consistency |
| [Proof and source continuity](../results/publication-v1.8.0-audit.json) | Retained C3 artifacts, unchanged Lean sources, 100-declaration Lean audit and all exact integer verifiers |

The [eight-destination distribution plan](DISTRIBUTION-PLAN.md) distinguishes journal review, preprint
hosting, discovery, author identity and preservation. Google Scholar and OpenAIRE require observed
indexing results; they do not accept a paper through the same process as a journal.

## Journal fields and cover text

Use **Journal of Physics A: Mathematical and Theoretical**, article type **Paper**, with the relevant
quantum-mechanics/quantum-information or mathematical-physics section offered by the live form.
Use the full title and abstract from the current metadata file. Suggested keywords are quantum
contextuality; Pauli observables; spectral bounds; finite geometry; cospectrality; formal verification.

Prepared descriptive cover text:

> This manuscript studies what spectral information establishes about Pauli contextuality and what
> it fails to retain in a related completion problem. It integrates a Lean 4 formalization of the
> previously known spectral floor with configurations attaining that floor---including an infinite
> family of non-closed contextual pure-CCZ determinant states |Psi_{3m}> (m >= 1) and finite degrees
> 75, 480, 2016 and 729344---and explicit sign carriers whose spectra agree while their completion
> spectra differ. On the classical four- and five-qubit geometries, Lean 4 proves exact CSS witnesses,
> double-counting ladders, and unconditional Kramers-lifted bounds d(W(7,2)) >= 1455 and
> d(Q^+(9,2)) >= 6444, alongside an independent 42-orbit C census and pure-integer dual check
> reproducing Jonah's exact triple (315, 1575, 6975). A four-qubit C3 pair has completion cubic
> traces 14976 and 15360 and exact global binary completion minima 368 and 344 (exact gap 24,
> kernel-certified via pure-integer MET-SDP triangle-cut duals); a graph family settles case C3 for
> every N >= 4, and variants together with a cone pair swap and a universal cubic-trace identity
> settle all nine vertex cases at the eigenvalue-multiset level for every N >= 4, proving Jonah's
> Conjecture E. All main theorems (100 newly audited declarations in VerifyNewFormalizations.lean plus
> retained baseline, saturation and C3 audits) are formalized in Lean 4.35.0 using only standard
> axioms, and are checked by exact computation through six qubits. The manuscript claims no priority
> for the spectral floor or for Jonah's exact classical degrees.
>
> The paper connects these components through shared notation and exact reconstruction. It separates
> kernel-checked theorems and finite counts from additional algebraic arguments and executable
> computations (including the 42-orbit W(5,2) census and the 540.3M-form nine-qubit rank-8 cyclic
> census). The public source release supplies proof sources, audit records, reproducible programs and
> deliberate error controls. Substantive Claude/Anthropic, OpenAI Codex, and Google Gemini /
> Antigravity involvement is disclosed with its actual scope.
>
> The manuscript is relevant to quantum foundations and mathematical physics because it treats both
> quantitative noncontextual constraints and an explicit limit on the information carried by a
> spectral invariant. Earlier source preprints and their archived versions are disclosed in the
> publication map; the submitted work is the combined manuscript (version 1.8.0).

The descriptive cover text above makes no certification of journal exclusivity, acceptance, or
completed human critical review. The later [author declarations](AUTHOR-DECLARATIONS.md) record
conditional approval/accountability, the no-competing-interest statement and accepted arXiv rights
and license. They were recorded for version 1.2.0; use their precise scope, and record any approval
of version 1.8.0 before submitting it. An AI tool must not write responses
to future referee reports where the publisher requires the author's own evaluation.

## Author-controlled declarations

Confirmed: the research was self-funded; the author is the sole operator of affiliated 0thernes LLC
and declares no competing interests. The author approved version 1.2.0 and accepted accountability
conditional on the assistant's readiness assessment, which supports offering it as a disclosed research
preprint. For version 1.3.0 the author directed the assistant to fold in the addenda and publish, for
version 1.4.0 to continue, and on 21 November 2026 gave explicit autonomous-approval instructions for
versions 1.5.0–1.8.0; no separate human line-by-line review of the 1.3.0–1.8.0 text or Lean code is
recorded (AUTHOR-DECLARATIONS.md, Versions 1.3.0–1.8.0). His recorded direction, goals, resources and funding are described in
[AUTHOR-DECLARATIONS.md](AUTHOR-DECLARATIONS.md); no personal mathematical/reference review or
critical intellectual revision was identified. Those activities cannot be inferred from permission.
The listed distribution destinations are repositories/indexes/archives, with no other journal named.
No nonprofit/tax status, academic appointment or external endorsement is inferred.

The existing verification license and third-party notices remain authoritative. A repository release
does not silently grant an additional Creative Commons license. An arXiv or repository distribution
license must be selected deliberately if required by the destination. The author has now explicitly
authorized the perpetual non-exclusive arXiv license and accepted the arXiv agreement and rights
declarations. This does not grant an additional license to Zenodo or change the repository license.

IOP requires disclosed AI research use and the author's validation and critical engagement.
[Official IOP AI policy](https://publishingsupport.iopscience.iop.org/questions/generative-ai-tools/).
Its authorship criteria also require substantial intellectual contribution, drafting or critical
intellectual revision, final approval, and accountability. Funding or general supervision alone is
insufficient. The author's factual account of these activities, including reference validation,
remains required; a permission to submit does not establish that the activities occurred.
[Official authorship criteria](https://publishingsupport.iopscience.iop.org/questions/ethics-of-authorship/).
Zenodo requires a verifiable basis in research conducted by human authors; the disclosed AI-originated
workflow remains an eligibility question that a proof check alone does not resolve.
[Official Zenodo depositor policy](https://support.zenodo.org/help/en-gb/13/227).

## arXiv and archival records

The suggested primary category is `quant-ph`, with `math.CO` as a possible cross-list. The account's
default `math.QA` does not determine the paper's classification; arXiv moderation controls the final
categories. The archive specifies XeLaTeX. The accepted agreement and non-exclusive license were
selected in the live form; continuing in `quant-ph` returned an endorsement requirement. The
author completed sign-in to the endorsement flow, which confirmed an endorsement email was sent.
The author deferred obtaining an endorser. No files have been uploaded or finally submitted.
See [the endorsement checkpoint](ARXIV-ENDORSEMENT.md); after the author resumes and resolves it, review arXiv's actual
compiled output before final submission.

Use the combined title, version and canonical public URL for ORCID and preservation records. Do not
enter Journal of Physics A as the publication venue before an actual journal publication. A public
ORCID preprint entry and a preserved repository snapshot do not establish peer review or indexing.

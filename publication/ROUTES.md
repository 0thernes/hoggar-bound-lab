# Publication routes for the exact four-qubit C3 certificate

Policy review: 2026-11-09. Official publisher/repository documentation only. This is a route assessment and preparation record; no account, deposit, submission, message, or payment was made by this review.

## Recommended sequence

1. The finite C3 proof and verification package is complete: 42 Lean declarations passed the stated axiom audit, and all nine final PDF pages were visually reviewed. Complete a real human author review and an accurate contribution/AI-use statement; those are separate from automated verification.
2. Preserve the finalized release on GitHub and, **if the human-research eligibility requirements are met**, deposit the paper and reproducibility artifacts on Zenodo with a DOI. Choose archive license metadata consistent with the existing project license and any separately authorized paper license.
3. Submit the same preprint to arXiv, primary category `quant-ph`, with a justified `math.CO` cross-list if accepted by moderation. This gives the relevant community a discoverable, versioned preprint.
4. Submit to **one peer-reviewed journal at a time**. Our first recommendation is *Journal of Physics A: Mathematical and Theoretical*, as an original research Paper. *Quantum Information Processing* is a possible subsequent alternative. *Quantum* is a demanding option if a specialist assesses the finite result as a sufficiently substantial advance. SciPost currently presents a material AI-policy conflict.
5. Update the archive, arXiv record and project landing page with any eventual journal reference/DOI. Let discovery services index those canonical records; do not represent indexing as a separate scientific validation.

These rankings are judgments about this particular manuscript, not predictions of acceptance. The mathematical result is narrow: two explicitly specified sign carriers on a 71-point four-qubit real Pauli section have equal carrier characteristic polynomials and unequal completion spectra. Their completion cubic traces are 14976 and 15360; the largest completion eigenvalues differ by 2 and the associated continuous-relaxation minima differ by 32. This establishes the four-qubit C3 instance of the failure predicted by Jonah's Conjecture E. It does not settle all dimensions, compute a new exact contextuality degree, establish historical priority, or report a physical experiment.

## Archives and discovery

### Zenodo: DOI-bearing preservation, conditional on eligibility

Zenodo supports papers, software and data, assigns a DOI at publication, and permits reserving a DOI while a record is still a draft. Uploaded files become fixed at publication; plan versioned corrections. Avoid duplicate DOIs for identical content already deposited elsewhere. A distinct software/data supplement can have its own DOI with a clear relation to the paper. [Quick start](https://help.zenodo.org/docs/get-started/quickstart/), [DOI guidance](https://help.zenodo.org/docs/deposit/describe-records/reserve-doi/).

**Material AI gate:** Zenodo requires a verifiable basis in research conducted by its human authors. It disallows AI tools as authors, creators or contributors and expects disclosure of substantive AI use. It specifically treats AI-originated core findings without the uploader's own research engagement as an eligibility concern. Exact software certificates do not establish that a named person has performed the required human research or review. Do not upload under an invented human-validation attestation; retain the accurate contribution history and resolve this requirement first. [Official depositor AI policy, published 27 April 2026](https://support.zenodo.org/help/en-gb/13/227).

Zenodo is not a peer-review service and does not assess scientific correctness. A DOI makes the artifact identifiable; it is not an acceptance decision by a physics journal. [Content policy](https://support.zenodo.org/help/en-gb/2-content/141-what-content-is-not-suitable-for-zenodo).

Account access is required. The license field is mandatory and defaults to CC BY 4.0, but custom and mixed licenses are supported. **Do not accept that default for this repository:** its current `LICENSE` is a restrictive verification license. Use an accurate custom license or an explicitly authorized paper-specific license, while preserving third-party notices. [License documentation](https://help.zenodo.org/docs/deposit/describe-records/licenses/).

### arXiv: the field-facing preprint

`quant-ph` is the recommended primary classification because the question concerns Pauli contextuality and quantum spectral relaxations. `math.CO` is a plausible secondary classification for the finite polar geometry; that is our subject assessment, subject to arXiv moderation. Use one submission with cross-listing, not duplicate category submissions. [Cross-listing policy](https://info.arxiv.org/help/cross.html).

The submitting human needs an account and the necessary endorsement. Institutional email is not a fabricated prerequisite to be manufactured: the official policy provides a personal-endorsement route as well. Endorsement is not peer review. Do not send bulk requests or contact moderators privately. [Endorsement requirements](https://info.arxiv.org/help/endorsement.html).

Session observation, 2026-11-09: an authenticated author account was observed, with no submissions listed. At the author's explicit request the account affiliation was changed to 0thernes LLC, and the saved account page confirmed success. The account display name remains Alexander Donahue; the author explicitly confirmed Alexander S. Donahue, 0thernes LLC as the manuscript credit. Paper submission remains deferred at the author's request; no draft or submission was started. The profile's default category is `math.QA`; the prepared paper's recommended primary classification remains `quant-ph`. A default category does not establish that endorsement for another category has been granted. Current status for all requested services is recorded in [AFFILIATIONS.md](AFFILIATIONS.md).

Substantial generative-AI use must be reported in the work; AI tools cannot be authors, and human authors remain responsible. Submissions must be substantial, topical, self-contained scholarly research. Moderation may decline or reclassify them. [Moderation and AI policy](https://info.arxiv.org/help/moderation/index.html#AI-language-tools).

Because this PDF is generated from LaTeX, submit a clean LaTeX source package, figures and bibliography, not just its PDF. Include every required local dependency and inspect arXiv's own compiled output. [Submission formats](https://info.arxiv.org/help/submit/index.html). The distribution license is irrevocable for the submitted version; choose it deliberately and check future journal compatibility. [License policy](https://info.arxiv.org/help/license/index.html).

Identity and current affiliation must be truthful. ORCID is recommended, not a credential to invent. The submission agreement requires an original author or an arXiv-approved proxy; ordinary tool access does not independently establish proxy approval. The human author must own the relevant attestations. [Identity policy](https://info.arxiv.org/help/policies/identity_and_affiliation.html), [submission agreement](https://info.arxiv.org/help/policies/submission_agreement.html).

### Google Scholar and other discovery systems

Google Scholar is an index, not a journal or an archive deposit. Its official guidance recommends a crawlable paper PDF linked from a publications page, with title, authors and references clearly present. Indexing may take time and is not guaranteed by creating a profile or DOI. Configure the project landing page and canonical metadata after author information is finalized. [Official inclusion guidance](https://scholar.google.com/intl/en/scholar/inclusion.html).

### Secondary archives: OSF transition and conditional Figshare data deposit

**OSF Projects is unsuitable for a new ongoing project workflow.** Its official transition announcement, updated 2 November 2026, says new Projects/Components stop after 16 November 2026 and existing Projects become read-only on 19 February 2027. Existing public files, URLs and DOIs are intended to remain accessible. OSF Registrations and Preprints continue; this is not an announcement that all OSF services are closing. Our recommendation is to preserve the working repository elsewhere rather than build this project's update process around OSF Projects. [Official OSF transition](https://help.osf.io/article/759-details-of-osf-projects-transition).

**Figshare is a conditional option for a distinct certificate dataset, not another copy of the paper.** The free platform's stated scope is reusable nontraditional research outputs; its policy excludes journal articles and already-published objects with existing DOIs. A separately documented set of exact matrices, sign assignments, integer certificates and validation data could be considered on that basis, with links to the paper and source release. Do not redeposit an identical DOI-bearing Zenodo object merely to obtain another DOI. [Figshare policies](https://info.figshare.com/user-guide/figshare-policies/).

The free platform lists CC0 and CC BY 4.0 license options, which do not match this project's restrictive verification license. No relicensing is authorized by this note; a dataset-only rights decision would have to be explicit. [Official platform/license comparison](https://info.figshare.com/figshare-plus/). No explicit depositor generative-AI policy was located in this focused official-source check, and the linked general terms returned HTTP 403. Absence of an identified rule is not permission: suitability, accurate AI-method disclosure, human accountability and the actual terms/license must be resolved before a deposit. No Figshare account, paid service or submission has been initiated.

## Peer-review targets

### First recommendation: Journal of Physics A: Mathematical and Theoretical

**Fit assessment:** its mathematical physics, quantum foundations and eigenvalue-problem scope matches this result. It requires significant, original, correct work with a physical motivation; a finite example still needs a convincing explanation of the information lost by the carrier spectrum. Submit a research **Paper**, not an invited review or a claim to a major general breakthrough. Its subscription route is free of publication charges. Optional gold open access is currently GBP 2655 / EUR 3050 / USD 3665, excluding applicable tax; no payment is necessary for the standard route. [Official scope, article types and charges](https://publishingsupport.iopscience.iop.org/journals/journal-of-physics-a-mathematical-and-theoretical/about-journal-physics-mathematical-theoretical/).

IOP explicitly permits disclosed AI-assisted ideation, methodology, code, analysis and text, with appropriate author validation and critical revision. Describe research use in Methods and provide a separate acknowledgment disclosure naming tools, purposes and actual verification. It does not permit AI-generated reviewer responses; a human must critically engage with reviews. [Current AI policy](https://publishingsupport.iopscience.iop.org/questions/generative-ai-tools/).

Authors must meet contribution, intellectual revision, final approval and accountability criteria. Submission must be exclusive to this journal while under consideration; enter genuine corresponding-author contact information. IOP requires the submitting author's ORCID. The author supplied [0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648); connecting/authenticating it in the journal account remains a separate step. [Author responsibilities and ORCID requirement](https://publishingsupport.iopscience.iop.org/publishing-support/authors/authoring-for-journals/submit-journal-article/). Initial submission can use one complete PDF plus supplements, with source retained for production. [Submission workflow](https://publishingsupport.iopscience.iop.org/questions/how-to-submit-your-journal-article/).

### Alternative: Quantum Information Processing

The journal covers quantum information theory, although its emphasis on protocols makes this purely structural result a less direct fit than Journal of Physics A. [Official scope](https://link.springer.com/journal/11128/aims-and-scope).

Its guidelines require accurate author/contact information, contribution and competing-interest declarations, a 150–250 word abstract and 4–6 keywords. LaTeX source and compiled PDF should accompany submission. Significant LLM use belongs in Methods or an equivalent section; human accountability remains mandatory. No simultaneous submission to another journal is allowed. [Author guidelines](https://link.springer.com/journal/11128/submission-guidelines).

The subscription route has no APC. Optional open access is currently GBP 2190 / USD 3090 / EUR 2490, before applicable taxes, and the amount is set by the acceptance date. Check the actual license agreement before committing rights. [Publishing models and charges](https://link.springer.com/journal/11128/how-to-publish-with-us).

### Ambitious option: Quantum

Quantum requires an arXiv paper posted in or cross-listed to `quant-ph`, and submission through Scholastica. It has no mandatory initial formatting template. Author contributions and the scope of substantive AI use—including code and calculations—must be declared. Acceptance requires a very significant technical or conceptual contribution; merely correct incremental work is explicitly below threshold. For this finite example, that is a real desk-rejection risk. Submission is exclusive, and accepted articles and their final arXiv versions use CC BY 4.0. [Official author instructions and criteria](https://quantum-journal.org/instructions/authors/).

There is no submission fee. The current regular publication contribution is EUR 600, with a EUR 100 option and full waiver available; the payment page says a waiver needs no justification. Do not make a payment or claim a waiver request has been filed. [Official payment policy](https://quantum-journal.org/payment/).

### SciPost Physics Core: topic candidate with an AI-policy conflict

SciPost's official live policy pages returned an Anubis access-denied screen during this review. Its own public source mirror was therefore inspected at commit `80506bb722d0d74b8045e09714c218417c954129` (6 November 2026). This is a primary source snapshot, **not a claim that every database-driven criterion or deployed page was retrieved**. The generic authoring template allows direct submission or the preferred preprint route and states that submission/publication are free. [Official source: authoring guidelines](https://github.com/SciPost/SciPost/blob/80506bb722d0d74b8045e09714c218417c954129/scipost_django/submissions/templates/submissions/_author_guidelines.html).

The journal terms require exclusive peer-review submission, CC BY 4.0 on acceptance and responsible human authorship. More consequentially, their GenAI section states: “Any use in authoring beyond text polishing or light editing likely constitutes impermissible use.” It also rejects blanket delegation and requires detailed disclosure. The current AI-led research/drafting therefore is **not a straightforward compliant submission**. Do not disguise it as light editing. Any future consideration would require transparent editorial policy clarification; none has been requested. [Official source: journal terms, GenAI section](https://github.com/SciPost/SciPost/blob/80506bb722d0d74b8045e09714c218417c954129/scipost_django/journals/templates/journals/journals_terms_and_conditions.html).

## Meaning of broad dissemination

Professional dissemination means a coherent, linked record: reproducible release, eligible DOI archive, disciplinary preprint, and one journal review process. Simultaneously submitting this manuscript to several exclusive journals would conflict with the checked policies. Creating many nominally different copies or splitting this one finite result into multiple near-identical papers would obscure the evidence. Repository availability, moderation, DOI registration, search indexing and journal peer review are distinct milestones and must be reported separately.

See `PACKAGE-CHECKLIST.md` and `c3-metadata-draft.json` for the prepared inputs and the remaining factual fields. No acceptance, deposit identifier, author review, conflict declaration, ORCID, email, institutional credential or payment has been invented.

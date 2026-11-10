# Author declarations and supported contributions

Recorded **9 November 2026, America/Los_Angeles** for the combined **v1.2.0** paper,
*Spectral bounds and their limits in Pauli contextuality: exact configurations and a four-qubit C3 certificate*.
Author: **Alexander S. Donahue — 0thernes LLC**. This record updates submission preparation after
the public release; it does not change the frozen release manuscript, license or scientific results.

## Declarations supplied by the author

- **arXiv:** the author explicitly accepted the Submission Agreement, confirmed authority and
  necessary submission rights, and authorized the perpetual, non-exclusive arXiv distribution license.
  The corresponding agreement and license controls were selected in the live form. Continuing in
  `quant-ph` produced an endorsement requirement, before any file upload or final submission.
- **Approval and responsibility:** the author approved this version and accepted accountability
  conditional on the assistant's assessment that the work is complete, thorough and ready to publish.
  The assessment below supports offering v1.2.0 as a disclosed research preprint. It does not certify
  satisfaction of every journal authorship criterion or completed human critical review.
- **Funding:** the research was personally self-funded. The author is the sole operator of the
  affiliated 0thernes LLC.
- **Competing interests:** the author declares no competing interests. The sole-operator relationship
  with 0thernes LLC remains disclosed. Public-benefit intent is the author's stated motivation; no
  independent legal, tax-exempt or charitable status has been verified or is asserted.
- **Other dissemination:** the author identified Zenodo, Google Scholar, arXiv and the other
  repositories, author records, indexes and archives in the distribution plan. Those are not other
  journal submissions. No other journal under review was identified in the author's response; this
  is not an independently verified universal statement about submissions outside this project.
- **Human review:** the author asked the assistant to infer contributions from the recorded process.
  No specific proof, argument, reference or intellectual revision personally checked or performed by
  the author was identified. That missing history cannot be reconstructed from automated checks.

## Contribution statement supported by the project record

> Alexander S. Donahue initiated and directed the project, specified the Tsotchke software stack,
> supplied its funding and resources, set the requirements for reproducible computation and formal
> verification, and directed the integration and public distribution of the two studies. He approved
> version 1.2.0 for dissemination and accepted accountability conditional on the documented readiness
> assessment. Claude and OpenAI Codex agents performed the substantive research, formalization,
> computational verification and manuscript preparation described in Section 13. The record does not
> establish that the human author personally derived the results or completed critical mathematical
> and reference review.

This is a description of demonstrated activities, not a certification that all IOP authorship
criteria are met. General project direction, resources and funding do not by themselves establish
substantial intellectual contribution or critical intellectual revision under the journal's policy.
An AI assistant's review cannot be attributed to the human author.

Prepared funding/interests text for a later manuscript revision or submission form:

> This research was self-funded by Alexander S. Donahue, the sole operator of the affiliated
> 0thernes LLC. The author declares no competing interests.

## Readiness assessment and its limits

The published v1.2.0 package is suitable to offer as a **research preprint with disclosed AI
provenance and explicit verification boundaries**. The supporting evidence includes the successful
formal-proof and executable CI records, unchanged proof-source audit, exact finite certificates,
negative controls, corrected prior-work attribution, compiled artifacts, bibliography/source audits,
and release/download/deployment integrity checks linked in [STATUS.md](STATUS.md). No new proof run
or external human peer review is implied by this assessment.

The general spectral floor is credited to prior work. Seven-qubit finite counts and the printed C3
factorizations/relaxation gaps retain their stated boundaries outside the respective Lean conclusions.
Claims of historical priority, universal completeness or journal acceptance are not established.
The later [binary-completion addendum](ADDENDUM-completion-optima.md) is a proposed future-revision
result, outside the approved and frozen v1.2.0 submission artifacts.

For **Journal of Physics A**, preparation is complete but the record does not yet establish all
four IOP authorship criteria: substantial intellectual contribution, drafting or critical intellectual
revision, final approval, and accountability. Approval and responsibility do not retrospectively
establish that intellectual review occurred. Scholarly qualifications or a formal academic appointment
are not the issue; the requirement is the actual contribution and review performed. ScholarOne also
requires sign-in before the live submission declarations can be assessed.

For **Zenodo**, the disclosed AI-originated research workflow still requires an eligibility resolution
under its depositor policy. A no-conflict declaration, proof verification or approval does not resolve
the distinct requirement for a verifiable basis in human-conducted research. The arXiv license
authorization applies to arXiv; it does not authorize a new Creative Commons or other repository license.

Policy sources: [IOP authorship](https://publishingsupport.iopscience.iop.org/questions/ethics-of-authorship/),
[IOP AI use](https://publishingsupport.iopscience.iop.org/questions/generative-ai-tools/),
[Zenodo AI-research policy](https://support.zenodo.org/help/en-gb/13/227),
[arXiv submission agreement](https://info.arxiv.org/help/policies/submission_agreement.html).

## A concrete route to completing human critical review

The following is a review aid, not a completed checklist. Record the reviewer's actual conclusions,
questions, corrections and sources as the work is performed.

1. Read Sections 1, 9, 12 and 13, and explain which claims are prior work, newly formalized, finitely
   certified, externally computed or still open. In particular, distinguish the two 135-point supports.
2. Check the hypotheses and trace/count normalization behind the spectral floor and its application
   to the four-, five- and seven-qubit examples. Compare each claimed Lean result with its theorem
   statement and the corresponding audit record.
3. Follow the C3 assignments through their actual Pauli interpretation, equal carrier spectra and
   unequal completion cubic traces. Explain why a spherical-relaxation gap alone is not an exact
   binary-optimum gap in the frozen version.
4. Consult the primary sources used for attribution, especially Jonah's floor/completion work and
   the cited contextuality-degree papers. Record which propositions were actually checked and
   whether the manuscript describes their scope accurately.
5. Examine the independent reconstruction and deliberate error controls. Identify what passing
   software checks establish and what they leave outside their scope.
6. Record substantive revisions or a reasoned critical assessment, then assess the journal's
   authorship requirements truthfully. Obtaining a qualified human review can help; it must not be
   represented as work the named author performed or automatically confer authorship on anyone.

## Version 1.3.0 (10 November 2026)

The author directed the assistant to continue, to fold the new results recorded in the addenda into
the combined paper, and to publish it. The declarations above were recorded for v1.2.0; the funding and
competing-interest text prepared above is used in Section 13 of v1.3.0. Two statements of the
assessment above describe v1.2.0 and are superseded: the seven-qubit finite counts are now Lean
theorems (`phase7_contexts`, `phase7_degree`), and besides the binary-completion addendum, v1.3.0
contains three further results (case C3 for every number of qubits, case C11, Conjecture E). No
separate author review or approval of the v1.3.0 text, and no new arXiv, journal or Zenodo
declaration, is recorded. The
assessment limits stated above apply unchanged: the new results are AI-originated, Theorem 19 relies
on two structure theorems of an unreviewed preprint, and only case C3 of it is proved in Lean.

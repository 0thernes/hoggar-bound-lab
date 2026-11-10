# C3 publication-readiness consistency check

Checked 2026-11-09; updated after completion of the finite Lean certificate and final nine-page PDF review. This report concerns publication metadata and policy readiness, not human author approval or a platform submission.

## Checks completed

- Inspected the current route document, checklist, structured metadata, Journal of Physics A draft and C3-specific citation file, plus relevant public manuscript/landing-page/demo statements.
- Scanned 17 applicable text/PDF files in `publication/`, the `paper/c3-*` files, `c3-lab/`, and the repository README/license. Extracted PDF text and metadata as part of the contact check. The sole email found was the authorized business address `0_0@0thernes.art`. No unknown or personal account email was found in that checked scope.
- Author identity is consistent: Alexander S. Donahue, 0thernes LLC. The PDF author/title metadata agrees with the manuscript and C3 citation. No ORCID or university affiliation has been fabricated.
- C3 manuscript and metadata describe a research preprint, not peer-reviewed publication. The cited Jonah DOIs are clearly prior-work identifiers, not claimed identifiers for this manuscript.
- The manuscript's current AI contribution statement accurately attributes direction to the human user and substantive research/drafting to AI agents. It does not claim completed human critical review or personal reconstruction of the proof.
- The custom verification license is consistently preserved. No current C3 publication file claims the entire project is MIT, CC BY or unrestricted open source. Quantum/SciPost's future CC BY requirement is identified as a separate licensing decision, not an already granted license.
- The formal-verification placeholder has now been replaced from the successful 42-declaration audit. The submission abstract and cover draft state the original Pauli-model cospectrality/noncospectrality result and exact cubic traces, while excluding the printed factorization and gaps two and 32 from Lean theorem scope. The updated draft abstract has 174 whitespace-delimited words.
- All nine pages of the final PDF were visually inspected; its SHA-256 is `5be6ba1318ce5cfeebf3a89b79dcfd428f87e228234e2f5075b14807a7f34836`. The corresponding report is `frontier-c3-paper-review.md`. A fresh contact scan of 12 applicable text files plus the PDF found only the authorized business address after normalizing LaTeX underscore escapes. The earlier 17-file scan above remains a historical observation of the broader previous snapshot.

## Preparation issues corrected

1. `ROUTES.md` referred to a current license “mismatch”, although the present files already preserve the license. Replaced that with the actual remaining task: choose compatible archive metadata and any separately authorized paper license. Also changed “accepted release” to “finalized release” to avoid ambiguity with journal acceptance.
2. The structured draft abstract had 149 whitespace-delimited words, just below the Quantum Information Processing alternative's 150-word minimum. Added a mathematically substantive sentence explaining redistribution between polar-observable eigenspaces. The matching journal draft now includes that explanation too; this is preparation text, not a change to the canonical paper.
3. A checklist disclosure example ended with a conditional but copyable assertion that the human review was documented elsewhere. Replaced it with an unmistakable unfinished field for the human's actual contributions/review. The separate Journal of Physics A draft already correctly leaves that attestation incomplete.

## Remaining concrete items

- The technical manuscript, final source/build hashes, precise formal boundary and PDF visual QA are complete. The root agent is freezing the immutable release and regenerated source bundle; retain their actual observed identifiers rather than inventing an archive or journal status.
- An immutable C3 release identifier and observed public URLs. `paper/c3-citation.cff` already carries the intended version `0.2.0-c3-certificate`; the preparation JSON deliberately retains a null release version/hash until the actual release is frozen. Synchronize these at release.
- Funding has now been supplied: “This research was self-funded by the author.” The relationship disclosure is: “The author is the sole operator of 0thernes LLC, with which this project is affiliated.” Other competing interests have not been explicitly declared; do not infer that none exist. These statements do not certify any legal nonprofit or tax status.
- Venue-specific human authorship, critical revision, final approval and accountability. Existing identity confirmation and broad permission to publish do not establish that the required intellectual review has occurred.
- For Zenodo, determine whether the actual human research contribution satisfies its depositor policy; do not promise that a later checkbox approval alone resolves the policy's research-basis requirement.
- For arXiv, genuine author account/access, any required endorsement, final distribution-license choice and author-controlled submission attestations. The author is unsure whether an existing account exists; check before creating another. The proposed non-exclusive perpetual distribution route does not silently change the repository license.
- No actual arXiv ID, Zenodo record DOI, journal submission ID or acceptance has been observed by this preparation task. Continue to report those milestones separately.

## Concise final human action to request

Only after the concrete final manuscript and verification summary are available, the root agent can ask:

> Please review the final paper and verification summary. Send any corrections or critical comments and describe which claims or checks you reviewed; then confirm whether you approve this exact version and accept responsibility as its author. The package already records your self-funding and sole-operator LLC relationship; please identify any additional competing interests required for the journal declaration.

Explain the reason in the same message: Journal of Physics A's author policy requires a substantial intellectual contribution, critical drafting/revision, final approval and accountability; its AI policy permits the disclosed computational assistance but requires real author validation. [IOP author responsibilities](https://publishingsupport.iopscience.iop.org/publishing-support/authors/authoring-for-journals/submit-journal-article/), [IOP AI policy](https://publishingsupport.iopscience.iop.org/questions/generative-ai-tools/).

This requests actual critical engagement and an accurate statement of its extent. It does not require or invite an unsupported claim that the human personally reran every program or reconstructed every Lean proof. Do not prefill or sign that statement for the author. No external messages or submissions were sent in this check.

# Publication status: combined paper v1.2.0

The author requested one combined research paper for eight destinations. The current manuscript is
**Spectral bounds and their limits in Pauli contextuality: exact configurations and a four-qubit C3 certificate**,
by **Alexander S. Donahue — 0thernes LLC**, ORCID
[0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648), correspondence **0_0@0thernes.art**.

The [submission package](UNIFIED-SUBMISSION.md), [machine-readable metadata](unified-metadata.json),
[source-paper map](PAPER-MAP.md), and [distribution plan](DISTRIBUTION-PLAN.md) identify the same work.
The [unified errata](UNIFIED-ERRATA.md) records corrected hypotheses and scope statements inherited from
the spectral-floor source study. The general Lean bound and existing proof sources are unchanged.

## Current combined-paper status

| Destination | Observed status |
| --- | --- |
| GitHub / project website | Combined release, public PDF and HTML are being prepared; older source-study releases remain public. |
| Google Scholar | Correct combined HTML/PDF metadata is being prepared. Profile setup was incomplete at article selection; no combined-paper indexing observed. |
| arXiv | Account access, saved affiliation 0thernes LLC and linked ORCID verified. A combined-paper draft was opened at the agreement/license step; no files uploaded, agreement accepted, or paper submitted. Combined source archive prepared; no public identifier. The latest eight-destination instruction supersedes the earlier source-paper deferral. |
| Journal of Physics A: Mathematical and Theoretical | Combined main manuscript and supplement prepared. ScholarOne still showed its login screen. No journal submission, review or acceptance. |
| Zenodo | Saved profile affiliation 0thernes LLC verified. No combined-paper deposit or DOI. AI-origin/human-research eligibility and distribution-license decisions remain unresolved. |
| ORCID | Matching public record and authenticated editor verified. Works (0) was observed; no combined-work entry saved yet. |
| OpenAIRE | Authenticated account observed with “No ORCID links found.” No combined research-product record or indexing observed. |
| Software Heritage | Earlier source releases are archived; no snapshot of the completed combined release verified yet. |
| Internet Archive | Earlier source-study captures are recorded separately; no combined landing-page/PDF capture verified yet. |

These are different outcomes: a saved account is not a submission; a preprint or archive is not peer
review; an ORCID entry does not establish Scholar or OpenAIRE indexing. Each final action needs its
own observed receipt or public record.

## Verification evidence

- [Full Ubuntu run 42741638647](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42741638647)
  passed both the executable and Lean jobs at `87f08a0fb5007c8529abc13eabeec093027c0eba`.
  [Downloaded evidence audit](../results/full-ci-87-audit.json): 42 C3 declarations, six scalar-stability
  declarations and 22 baseline declarations use only `propext`, `Classical.choice` and `Quot.sound`.
- [Saturation run 42741638912](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42741638912)
  passed its executable and Lean jobs at the same source revision. Its separate
  [14-declaration audit](../results/saturation-ci-audit.json) has the same standard-axiom boundary.
  Circuit/state identification and seven-qubit counts are outside those 14 formal statements.
- [Publication continuity](../results/publication-v1.2.0-audit.json) compares 83 retained C3 artifacts
  and all 28 Lean/configuration files to their verified source revisions. This is continuity evidence,
  not a claim that writing the combined paper reran or extended the Lean proof.
- [Unified build](../results/unified-paper-build.json), [artifact audit](../results/unified-publication-audit.json)
  and [section-score check](../results/unified-section-score.json) record the new paper's packaging and
  executable connection between the two components. The section-score program recounts 455 contexts
  and 132 violations for each C3 witness; its single-sign negative control changes the count to 147.

The C3 factorization, largest-eigenvalue gap two and spherical-relaxation gap 32 remain separately
checked algebraic results outside its 42 Lean conclusions. No new global Lean theorem, historical
priority, external human review or quantum-hardware experiment is claimed by combining the papers.

## Preserved source studies

The spectral-floor study was published as [v1.1.1](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v1.1.1)
at `c656f52aef29b21f97e0daa241915aa7fbc0de2b`. The local v1.1.2 disclosure/documentation preparation
was not published as a release; its work is incorporated into v1.2.0.

The separate C3 source remains [v0.2.0-c3-certificate](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v0.2.0-c3-certificate),
commit `d3811e3b53048fa8f3206f08494f0a9834eed287`, published at 2026-11-10 01:33:37 UTC. Its nine-page PDF
is 96,260 bytes and retains SHA-256 `5be6ba1318ce5cfeebf3a89b79dcfd428f87e228234e2f5075b14807a7f34836`.
The original 23 release assets were downloaded and checksum-checked. Their publication does not
establish that the new combined manuscript has been distributed.

The earlier successful [C3 Linux run 42728421086](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42728421086)
remains part of the historical evidence. [Run 42732149645](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42732149645)
had a passing executable job but a cancelled redundant formal job; its overall conclusion is cancelled,
not a full proof pass. The newer successful full run above is an independent completed record.

## Remaining author-controlled declarations

Confirmed funding: self-funded by the author, who is the sole operator of affiliated 0thernes LLC.
Additional competing interests have not been declared. Actual human critical review and final approval
of the combined manuscript remain to be recorded. Automated checks do not establish that the human
performed those activities. Journal rights/exclusivity declarations and required distribution licenses
must be truthful and selected by the author. The manuscript discloses substantive Claude and Codex use.

The current custom verification license and third-party notices are preserved. No additional Creative
Commons grant, nonprofit/tax status, academic appointment or endorsement is inferred. See the
[IOP AI policy](https://publishingsupport.iopscience.iop.org/questions/generative-ai-tools/) and
[Zenodo depositor policy](https://support.zenodo.org/help/en-gb/13/227) for the venue requirements.

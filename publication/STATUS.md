# C3 publication status

Recorded 9 November 2026, America/Los_Angeles. The GitHub release timestamp is 10 November 2026 at 01:33:37 UTC. This is an original mathematical/computational research preprint, not a statistical meta-analysis or a peer-reviewed article.

| Destination | Observed status | Record |
| --- | --- | --- |
| GitHub | Published `v0.2.0-c3-certificate`, with 23 checksummed assets | [Versioned release](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v0.2.0-c3-certificate) |
| Project publication page | Public, with abstract, citation metadata and final PDF | [Paper record](https://0thernes.github.io/hoggar-bound-lab/paper/c3-spectral-counterexample.html) |
| Interactive demonstration | Public; its served assets match the tested source | [Exact C3 verifier](https://0thernes.github.io/hoggar-bound-lab/c3-lab/) |
| arXiv | Authenticated account affiliation saved as 0thernes LLC; source archive prepared; paper submission deferred at the author's request | No submission or arXiv identifier claimed |
| Zenodo | Account affiliation saved as 0thernes LLC; deposit eligibility and license steps remain unresolved | No deposit or DOI claimed |
| Journal of Physics A | Submission package prepared; actual author critical review, final approval and account access pending | No journal submission, review or acceptance claimed |
| Google Scholar | Publication page metadata is correct; author setup retains 0thernes LLC, but profile setup is incomplete at article selection | No completed public profile or indexing claimed |

## Fixed research artifact

The release tag resolves to commit `d3811e3b53048fa8f3206f08494f0a9834eed287`. Its nine-page PDF is 96,260 bytes, with SHA-256 `5be6ba1318ce5cfeebf3a89b79dcfd428f87e228234e2f5075b14807a7f34836`. Anonymous downloading of that published PDF returned the same bytes. All 23 release assets were downloaded and checked against the local release checksums before publication. All 66 hosted research files matched the frozen site manifest after deployment.

The exact claim is the explicit four-qubit C3 case: equal carrier spectra and unequal completion spectra, with completion cubic traces 14976 and 15360. The Lean development includes the Pauli-model connection and eigenvalue multiplicities. The printed polynomial factorization, largest-eigenvalue gap of 2 and continuous-relaxation gap of 32 have separate algebraic proofs in the paper; they are outside the stated Lean theorem boundary.

## Verification provenance

- Local Windows source checks and the 42-declaration C3 axiom audit passed. The six auxiliary scalar-stability declarations also passed.
- [Independent Ubuntu run 42728421086](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42728421086) completed successfully at `85520dc263c83de55d1a3d107cd80e7068be8616`. The downloaded logs independently confirm all 42 C3 and six stability declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- All 21 proof/configuration files match the successful Linux sources at the publication commit. The later presentation change affected only the landing-page HTML, its builder and its HTML hash record.
- [Run 42732149645](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42732149645), at research commit `026961ef81f70aa7cc464b527d4ca30e647e6b17`, had a successful executable job. Its redundant formal job was cancelled after the identical proof sources passed independently. The whole workflow is not described as successful. Its executable checks and the cancellation record are preserved in the release.
- [Pages deployment 42736147632](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42736147632) succeeded at the exact publication commit. The raw Linux job logs, original GitHub artifact ZIPs, source-equivalence audits and public-site verification record are retained as release assets.

## Author-controlled submission steps

The confirmed author is Alexander S. Donahue, 0thernes LLC, with correspondence at `0_0@0thernes.art`. The author reports that the research was self-funded and that he is the sole operator of 0thernes LLC. No ORCID was supplied; IOP requires the submitting author's ORCID, so obtaining or recovering the author's own identifier is a remaining journal account step. Additional competing interests have not yet been explicitly declared. The [IOP submission guide](https://publishingsupport.iopscience.iop.org/publishing-support/authors/authoring-for-journals/submit-journal-article/) documents the requirement.

Actual human critical review, final approval and accountability remain to be recorded; automated verification is not evidence that the human personally performed those activities. The manuscript discloses substantive AI involvement. The arXiv account's affiliation was changed to 0thernes LLC and the saved result verified on 9 November 2026. The account name remains Alexander Donahue; the explicitly confirmed manuscript credit is Alexander S. Donahue, 0thernes LLC. The author deferred arXiv paper submission. Account access is resolved; endorsement, author declarations, license choice and submission remain separate. Preserve the current custom verification license unless a separate license grant is explicitly chosen. [Affiliation records](AFFILIATIONS.md) distinguish completed profile changes from account-dependent updates still pending at other services.

Journal of Physics A is the first recommended peer-review route. Other journals are alternatives after any prior journal submission is closed or withdrawn, not simultaneous exclusive submissions. Policy sources and the conditional archive options are documented in [ROUTES.md](ROUTES.md). The prepared [journal package](JPHYS-A-SUBMISSION-DRAFT.md), [portable source instructions](ARXIV-SOURCE.md), and [short social drafts](SOCIAL-DRAFTS.md) are available; neither social post has been sent.

# Publication record: the spectral-floor paper

Version 1.1.2, 9 November 2026. Author: Alexander S. Donahue, 0thernes LLC, Washington, USA
(0_0@0thernes.art, ORCID [0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648)). This directory
holds the typeset paper and submission materials. See [venue guidance](../ROUTES.md) and
[the account-affiliation record](../AFFILIATIONS.md).

## Files

| File | Contents |
| --- | --- |
| `spectral-floor.tex`, `figures/` | XeLaTeX source generated from `paper/spectral-floor.md` by `scripts/build_latex.py` |
| `spectral-floor.pdf` | Typeset paper, 24 pages; the separate browser-rendered `paper/spectral-floor.pdf` has 26 pages |
| `arxiv-source.zip` | TeX, three figures and the arXiv compiler configuration |
| `ARXIV-SUBMISSION.md` | Prepared metadata, compilation steps and an unsent endorsement-request draft |
| `ZENODO-METADATA.json`, `ZENODO-NOTE.md` | Prepared creator metadata and the unresolved deposit-eligibility question |
| `jphysa/manuscript.pdf`, `jphysa/supplementary.pdf` | Journal form: a 20-page main manuscript and 5-page supplement; generated TeX and figures accompany them |
| `JPHYSA-SUBMISSION.md`, `JOURNAL-COVER-LETTER.md` | Submission sheet and unsent cover-letter draft for Journal of Physics A: Mathematical and Theoretical |
| `abstract.md` | The concise abstract shared by the manuscript forms |
| `build-record.json`, `jphysa/build-record.json`, compiler logs | Source/output hashes, page counts and compilation evidence |

## Status by venue

Release and deployment records are available at [release v1.1.2](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v1.1.2)
and [the repository workflow runs](https://github.com/0thernes/hoggar-bound-lab/actions). Existing releases
`v1.1.0` and `v1.1.1` remain historical snapshots. Local preparation of a submission package is not a
submission, DOI deposit or peer-review decision.

The archive timestamps below are 10 November 2026 UTC; the corresponding local work date is
9 November in America/Los_Angeles.

| Venue | Recorded status | Next step |
| --- | --- | --- |
| GitHub / project web page | Public releases and paper page exist; the release and workflow records above identify this revision | Use the tagged artifact and successful deployment record when citing a version |
| Software Heritage | Prior `v1.1.0` archive: visit 10 November 2026, 02:35 UTC; snapshot `swh:1:snp:e668d136e57bf7971a488db2706bd58ffbabede5` ([browse](https://archive.softwareheritage.org/browse/origin/directory/?origin_url=https://github.com/0thernes/hoggar-bound-lab)) | This identifies the earlier snapshot, not an archive of the current revision |
| Internet Archive | Prior `v1.1.0` captures: [paper page](https://web.archive.org/web/20261110023747/https://0thernes.github.io/hoggar-bound-lab/?v=1.1.0), [PDF](https://web.archive.org/web/20261110023819/https://0thernes.github.io/hoggar-bound-lab/paper/spectral-floor.pdf?v=1.1.0). The reported github.com-page capture failed | Preserve the historical URLs without claiming they contain the new revision |
| arXiv (`quant-ph`, proposed cross-list `math.CO`) | Account access and saved affiliation 0thernes LLC verified; submission deferred by the author; no paper submitted | Resume when ready, resolve any required endorsement, review the server-compiled paper and author attestations |
| Zenodo | Account affiliation saved as 0thernes LLC; metadata prepared; no deposit or DOI | Resolve human-research eligibility and the distribution license; see [ZENODO-NOTE.md](ZENODO-NOTE.md) |
| Journal of Physics A: Mathematical and Theoretical | Main manuscript, supplement and drafts prepared; observed ScholarOne pages remain at login; no authenticated journal profile or submission verified | Author sign-in, critical review, final approval, declarations and account/ORCID linking; one journal at a time |
| Google Scholar | Page metadata prepared; profile setup and indexing are not established as complete | Complete profile setup when the paper is available for selection; do not imply indexing from the presence of metadata |
| OpenAIRE | Authenticated My ORCID links page observed with no ORCID links found | Claim a record only after an eligible source is indexed; no paper linkage is established |
| Paperpal | Account access reported by the author | Optional pre-check of `jphysa/manuscript.pdf`; no upload or completed check is recorded |

The author supplied the ORCID printed above and in the paper. Its live ownership and journal linkage
have not been independently verified here. Saved account profiles are not paper submissions. No arXiv
identifier, DOI or journal submission identifier exists for this paper in this record.

## Revision and declarations

Relative to research commit `c656f52`, version 1.1.2 changes only the canonical paper's byline version
and funding/interest paragraph. It retains that commit's concise abstract, ORCID and expanded AI
disclosure. Mathematical text, formulas, references and proof sources receive no further edits in this
disclosure revision. The journal layout moves demonstration and replication material to a supplement
using the existing mechanical builder.

The confirmed declaration is: "This research was self-funded by the author. The author is the sole
operator of 0thernes LLC, with which this project is affiliated." Additional competing interests have
not yet been declared. The rebuilt TeX, PDFs, HTML and source archive contain this correction. Hashes
and the exact source comparison are in the build records and
[the disclosure revision record](../../results/spectral-floor-disclosure-revision.json).

## Author responsibilities

arXiv requires disclosure of significant generative-AI use and makes each author responsible for the
contents, including errors and incorrect references. AI tools cannot be authors. Computational checks
do not replace the author's critical review; moderation is separate from peer review.
[Official arXiv policy](https://info.arxiv.org/help/moderation/index.html#AI-language-tools).

Zenodo requires a human-conducted research basis and disclosure of substantive AI assistance. Formal
correctness alone does not settle eligibility; its policy directs uncertain depositors to support.
[Official Zenodo policy](https://support.zenodo.org/help/en-gb/13/227).

Journal of Physics A: Mathematical and Theoretical permits disclosed AI research assistance while
requiring actual author contribution, critical revision, final approval and accountability. Use the
prepared submission materials only after author-controlled statements are completed accurately. See
[the journal sheet](JPHYSA-SUBMISSION.md). None of these records establishes external peer review.

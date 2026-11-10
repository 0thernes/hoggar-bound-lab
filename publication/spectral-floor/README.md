# Publication record: the spectral-floor paper

Prepared version 1.1.1, 9 November 2026. Author: Alexander S. Donahue, 0thernes LLC, Washington, USA
(0_0@0thernes.art). This directory holds the typeset paper and what is needed to submit it. The policy
notes for each venue (AI-use rules, fees, licences) are in [../ROUTES.md](../ROUTES.md), written for the
companion note; they apply to this paper as well.

## Files

| file | what |
|---|---|
| `spectral-floor.tex`, `figures/` | LaTeX source generated from `paper/spectral-floor.md` by `scripts/build_latex.py` (XeLaTeX) |
| `spectral-floor.pdf` | the XeLaTeX typeset paper, 24 pages; the browser-rendered `paper/spectral-floor.pdf` has 27 pages |
| `arxiv-source.zip` | the archive to upload to arXiv |
| `ARXIV-SUBMISSION.md` | metadata, steps and the endorsement request for arXiv |
| `ZENODO-METADATA.json` | metadata for a Zenodo record |
| `JOURNAL-COVER-LETTER.md` | a cover letter draft for a journal submission |
| `build-record.json`, `tectonic-output.log` | hashes and the compile log |

## Status by venue

| venue | status | who acts next |
|---|---|---|
| GitHub repository | release `v1.1.0` is published; `v1.1.1` is this prepared disclosure/presentation revision | publish and verify the updated release |
| Project web page (GitHub Pages), with indexing metadata for Google Scholar | published; this revision still needs deployment; Scholar indexing has not been observed or guaranteed | verify the updated deployed files |
| Software Heritage | archival of the public repository requested | — |
| Internet Archive | snapshots of the paper page and PDF requested | — |
| arXiv (quant-ph, cross-list math.CO) | account access and saved affiliation 0thernes LLC verified; paper submission deferred; package prepared, not submitted | the author: resume when ready, resolve any required endorsement, review the compiled paper and submission terms |
| Zenodo (DOI) | account affiliation saved as 0thernes LLC; metadata prepared; no deposit or DOI | resolve human-research eligibility, final author review and the distribution license before deposit |
| Journal (first choice: Journal of Physics A) | cover letter drafted; account setup deferred; not submitted | author critical review, final approval, actual declarations and journal account/ORCID linking; one journal at a time |

The arXiv and Zenodo profile changes are recorded in [../AFFILIATIONS.md](../AFFILIATIONS.md). They are
not submissions or deposits. No arXiv identifier, DOI or journal submission identifier exists for this
paper. Actual author review, submission declarations and distribution-license choices remain separate.

The author supplied ORCID [0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648), now included in the prepared creator and submission metadata. It has not been independently live-verified or connected to a journal account by this metadata update.

## Revision and declarations

Version 1.1.1 changes the byline version and funding/interest disclosure only; the mathematical text,
formulas, references and proof sources are unchanged from the merged v1.1.0 source. The confirmed
declaration is: "This research was self-funded by the author. The author is the sole operator of
0thernes LLC, with which this project is affiliated." Additional competing interests have not yet
been declared. The rebuilt TeX, PDF, HTML and source archive contain this correction. Build hashes
and the source comparison are recorded in `build-record.json` and
[../../results/spectral-floor-disclosure-revision.json](../../results/spectral-floor-disclosure-revision.json).

## Recommended order

1. arXiv first: it is where the people who can judge this work will see it, and journals accept
   submissions that are on arXiv.
2. Zenodo for a DOI of the exact release (paper and repository snapshot), if the author is satisfied
   that its AI-use conditions are met.
3. One journal. The paper is long and has two parts (the formalization; the new configurations); an
   editor or referee may ask to split it.

A referee or an endorser will ask the author questions about the mathematics. The Lean theorems can be
defended by re-running the proof checker; the rest of the paper needs a reader who knows the field, and
finding one before a journal submission is worth more than any further automated check.

# Publication record: the spectral-floor paper

Version 1.1.0, 9 November 2026. Author: Alexander S. Donahue, 0thernes LLC, Washington, USA
(0_0@0thernes.art). This directory holds the typeset paper and what is needed to submit it. The policy
notes for each venue (AI-use rules, fees, licences) are in [../ROUTES.md](../ROUTES.md), written for the
companion note; they apply to this paper as well.

## Files

| file | what |
|---|---|
| `spectral-floor.tex`, `figures/` | LaTeX source generated from `paper/spectral-floor.md` by `scripts/build_latex.py` (XeLaTeX) |
| `spectral-floor.pdf` | the typeset paper, 24 pages |
| `arxiv-source.zip` | the archive to upload to arXiv |
| `ARXIV-SUBMISSION.md` | metadata, steps and the endorsement request for arXiv |
| `ZENODO-METADATA.json` | metadata for a Zenodo record |
| `JOURNAL-COVER-LETTER.md` | a cover letter draft for a journal submission |
| `build-record.json`, `tectonic-output.log` | hashes and the compile log |

## Status by venue

| venue | status | who acts next |
|---|---|---|
| GitHub repository and release `v1.1.0` | published | — |
| Project web page (GitHub Pages), with indexing metadata for Google Scholar | published; indexing by Google Scholar is automatic, takes days to weeks and is not guaranteed | — |
| Software Heritage | archival of the public repository requested | — |
| Internet Archive | snapshots of the paper page and PDF requested | — |
| arXiv (quant-ph, cross-list math.CO) | package ready; not submitted | the author: sign in, set the affiliation to 0thernes LLC, obtain an endorsement, accept the submission terms, submit |
| Zenodo (DOI) | metadata ready; not deposited | the author: Zenodo's rules for AI-assisted work require the depositor's own engagement with the research; licence to be chosen |
| Journal (first choice: Journal of Physics A) | cover letter drafted; not submitted | the author, after the arXiv posting; one journal at a time |

Nothing in the last three rows has been done on the author's behalf, because each needs a personal
login, a personal statement of responsibility for the content, and a licence decision.

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

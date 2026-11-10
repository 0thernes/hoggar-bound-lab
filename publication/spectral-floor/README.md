# Publication record: the spectral-floor paper

Version 1.1.0, 9 November 2026. Author: Alexander S. Donahue, 0thernes LLC, Washington, USA
(0_0@0thernes.art). This directory holds the typeset paper and what is needed to submit it. Policy notes
for further venues (fees, licences) are in [../ROUTES.md](../ROUTES.md), written for the companion note.

## Files

| file | what |
|---|---|
| `spectral-floor.tex`, `figures/` | LaTeX source generated from `paper/spectral-floor.md` by `scripts/build_latex.py` (XeLaTeX) |
| `spectral-floor.pdf` | the typeset paper, 24 pages |
| `arxiv-source.zip` | the archive to upload to arXiv |
| `ARXIV-SUBMISSION.md` | metadata, steps and the endorsement request for arXiv |
| `ZENODO-METADATA.json`, `ZENODO-NOTE.md` | metadata for a Zenodo record, and why no deposit has been made |
| `JOURNAL-COVER-LETTER.md` | a cover letter draft for a journal submission |
| `build-record.json`, `tectonic-output.log` | hashes and the compile log |

## Status by venue

| venue | status on 10 November 2026 (UTC) | who acts next |
|---|---|---|
| GitHub repository, release `v1.1.0` | published | — |
| Project web page (GitHub Pages), with indexing metadata for Google Scholar | published. Google Scholar indexes such pages by itself; that takes days to weeks and is not guaranteed | — |
| Software Heritage | archival of the public repository requested and accepted (save request 2635043) | — |
| Internet Archive | snapshots of the paper page and of the PDF taken (20261110022023, 20261110022123) | — |
| arXiv (quant-ph, cross-list math.CO) | package ready; **not submitted** | the author: set the account affiliation to 0thernes LLC, obtain an endorsement, accept the submission terms, submit |
| Zenodo (DOI) | metadata ready; **not deposited**, see `ZENODO-NOTE.md` | the author, after asking Zenodo whether the work is in scope |
| Journal (first choice: Journal of Physics A) | cover letter drafted; **not submitted** | the author, after the arXiv posting; one journal at a time |

Nothing in the last three rows has been done on the author's behalf. Each needs a personal login, a
personal statement of responsibility for the content, and a licence decision; and each venue has rules
about work produced with AI that the author has to meet in person.

## What the venues require of the author

* **arXiv** requires that significant use of generative AI be reported in the paper (it is, on the
  first page and in Section 12), that AI is not listed as an author, and that each author takes full
  responsibility for all contents. Since May 2026 a submission that shows the authors did not check
  AI output (for example an invented reference) leads to a one-year ban and a peer-review requirement
  afterwards. Every reference in the paper was checked against Crossref, arXiv or Zenodo on
  9 November 2026; the author should still read the paper before signing for it.
* **Zenodo** accepts only content grounded in research conducted by its human authors; see
  `ZENODO-NOTE.md`.
* **Journals** (IOP for Journal of Physics A) allow disclosed AI use but require that the listed
  author meets the authorship criteria: contribution, critical revision, final approval and
  accountability.

## Recommended order

1. arXiv first: it is where the people who can judge this work will see it, and journals accept
   submissions that are on arXiv. It needs an endorser, who will look at the paper.
2. One journal. The paper is long and has two parts (the formalization; the new configurations); an
   editor or referee may ask to split it.
3. Zenodo only if Zenodo confirms that the deposit is within its scope.

An endorser or a referee will ask the author questions about the mathematics. The Lean theorems can be
defended by re-running the proof checker; the rest of the paper needs a reader who knows the field, and
finding one is worth more than any further automated check.

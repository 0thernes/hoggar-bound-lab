# Publication record: the spectral-floor paper

Version 1.1.1, 9 November 2026. Author: Alexander S. Donahue, 0thernes LLC, Washington, USA
(0_0@0thernes.art, ORCID [0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648)). This directory holds the typeset paper and what is needed to submit it. Policy notes
for further venues (fees, licences) are in [../ROUTES.md](../ROUTES.md), written for the companion note.

## Files

| file | what |
|---|---|
| `spectral-floor.tex`, `figures/` | LaTeX source generated from `paper/spectral-floor.md` by `scripts/build_latex.py` (XeLaTeX) |
| `spectral-floor.pdf` | the typeset paper, 24 pages |
| `arxiv-source.zip` | the archive to upload to arXiv |
| `ARXIV-SUBMISSION.md` | metadata, steps and the endorsement request for arXiv |
| `ZENODO-METADATA.json`, `ZENODO-NOTE.md` | metadata for a Zenodo record, and why no deposit has been made |
| `jphysa/manuscript.pdf`, `jphysa/supplementary.pdf` (with `.tex` sources) | the journal form: a 20-page article of about 8 100 words and a 5-page supplement, built by `scripts/build_journal.py` |
| `JPHYSA-SUBMISSION.md`, `JOURNAL-COVER-LETTER.md` | form fields, required statements and steps for Journal of Physics A; the cover letter draft |
| `abstract.md` | the abstract (305 words), shared by all forms of the paper |
| `build-record.json`, `tectonic-output.log` | hashes and the compile log |

## Status by venue

| venue | status on 10 November 2026 (UTC) | who acts next |
|---|---|---|
| GitHub repository, releases `v1.1.0` and `v1.1.1` (adds the ORCID iD) | published | — |
| Project web page (GitHub Pages), with indexing metadata for Google Scholar | published. Google Scholar indexes such pages by itself; that takes days to weeks and is not guaranteed | — |
| Software Heritage | archived. The visit of 10 November 2026, 02:35 UTC, includes the tag `v1.1.0`: snapshot `swh:1:snp:e668d136e57bf7971a488db2706bd58ffbabede5` ([browse](https://archive.softwareheritage.org/browse/origin/directory/?origin_url=https://github.com/0thernes/hoggar-bound-lab)) | — |
| Internet Archive | snapshots of the final paper page and PDF: [page](https://web.archive.org/web/20261110023747/https://0thernes.github.io/hoggar-bound-lab/?v=1.1.0), [PDF](https://web.archive.org/web/20261110023819/https://0thernes.github.io/hoggar-bound-lab/paper/spectral-floor.pdf?v=1.1.0). Its capture of the github.com pages failed (the repository itself is in Software Heritage) | — |
| arXiv (quant-ph, cross-list math.CO) | package ready; **not submitted** | the author: set the account affiliation to 0thernes LLC, obtain an endorsement, accept the submission terms, submit |
| Zenodo (DOI) | metadata ready; **not deposited**, see `ZENODO-NOTE.md` | the author, after asking Zenodo whether the work is in scope |
| Journal of Physics A: Mathematical and Theoretical | manuscript, supplement, cover letter and form sheet ready (`JPHYSA-SUBMISSION.md`); **not submitted** | the author: write the statement of his own verification, then upload and confirm the declarations. One journal at a time |

Nothing in the last three rows has been done on the author's behalf. Each needs a personal login, a
personal statement of responsibility for the content, and a licence decision; and each venue has rules
about work produced with AI that the author has to meet in person.

## The author's accounts, and what each is for

All of them carry the same identity: Alexander S. Donahue, 0thernes LLC, 0_0@0thernes.art.

| account | use for this paper |
|---|---|
| ORCID [0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648) | the author identifier printed in the paper and required by IOP for the submitting author. Link it in the arXiv account, and add the paper under *Works* once it has an arXiv number. The record lists a second, personal email address: its visibility setting decides whether the public sees it |
| arXiv | the preprint; see `ARXIV-SUBMISSION.md`. The profile affiliation should read 0thernes LLC |
| Google Scholar profile | lists the author's papers. Scholar finds the paper's page by itself (the page carries the tags it reads); until then use *Add article manually* with the values below |
| OpenAIRE | no upload: OpenAIRE harvests arXiv and Zenodo records and lets the author claim them with the ORCID iD |
| Zenodo | a DOI for the release, if Zenodo confirms the work is in scope; see `ZENODO-NOTE.md` |
| IOP (Journal of Physics A), Paperpal Preflight | the journal submission and its optional pre-check; upload `spectral-floor.pdf` from this directory |

Values for *Add article manually* in Google Scholar: title "A machine-checked spectral floor for Pauli
contextuality, and new configurations that attain it"; author "Donahue, Alexander S."; publication date
2026/11/9; type *Other* (or the arXiv entry once it exists); institution 0thernes LLC; report number
"Hoggar Bound Lab, version 1.1"; URL https://0thernes.github.io/hoggar-bound-lab/.

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

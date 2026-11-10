# Journal of Physics A: Mathematical and Theoretical — submission sheet (version 1.1.2)

Prepared 9 November 2026 from IOP Publishing's own pages
([scope and article types](https://publishingsupport.iopscience.iop.org/journals/journal-of-physics-a-mathematical-and-theoretical/about-journal-physics-mathematical-theoretical/),
[how to submit](https://publishingsupport.iopscience.iop.org/questions/how-to-submit-your-journal-article/),
[generative AI policy](https://publishingsupport.iopscience.iop.org/questions/generative-ai-tools/)).
**Nothing has been submitted.** The submission and every declaration in it are the author's to make. Paperpal access was reported by the author; no pre-check upload, journal submission or independent account verification is implied.

## Files to upload

| file | role |
|---|---|
| `jphysa/manuscript.pdf` | the article: 20 pages, about 8 100 words of main text (IOP: a Paper is "usually approximately 10000 words") |
| `jphysa/supplementary.pdf` | supplementary material, 5 pages: the demonstration on the Tsotchke stack, the tests, how to reproduce, the witness format |
| `jphysa/manuscript.tex`, `jphysa/supplementary.tex`, `jphysa/figures/` | LaTeX source (XeLaTeX), kept for revision and production; IOP asks only for the PDF at first submission |

Both PDFs are built from `paper/spectral-floor.md` by `scripts/build_journal.py`; the journal form has
the same text as the public paper, with the demonstration and replication sections moved to the
supplement.

## Form fields

| field | value |
|---|---|
| Journal | Journal of Physics A: Mathematical and Theoretical |
| Article type | Paper |
| Section | Quantum mechanics and quantum information theory (foundations of quantum mechanics; quantum correlations). Second choice: Mathematical physics (physical combinatorics) |
| Title | A machine-checked spectral floor for Pauli contextuality, and new configurations that attain it |
| Abstract | the text of `abstract.md` (302 words by the build-record tokenizer), without the dollar signs |
| Keywords | quantum contextuality; Kochen–Specker theorem; multi-qubit Pauli group; symplectic polar spaces; Clifford hierarchy; bent functions; formal verification (Lean 4) |
| Author | Alexander S. Donahue |
| Affiliation | 0thernes LLC, Washington, USA |
| Email | 0_0@0thernes.art |
| ORCID (required for the submitting author) | 0009-0006-8168-9648 |
| Funders | This research was self-funded by the author; confirm the form selection accurately |
| Open access | the subscription route has no publication charge; gold open access is optional and costs a fee. The author's choice |
| Previously published material reproduced | none |
| Preprint | https://0thernes.github.io/hoggar-bound-lab/ and release `v1.1.2` of https://github.com/0thernes/hoggar-bound-lab; add the arXiv number when there is one |
| Cover letter | `JOURNAL-COVER-LETTER.md` |
| Suggested reviewers | optional. Do not name anyone the author has a connection with; areas are given in the cover letter |

## Statements the journal asks for, and where they are

| statement | where |
|---|---|
| AI disclosure statement, in the Acknowledgments | manuscript, *Acknowledgments*. It names the tool and model (Claude Fable 5, Anthropic) and what it was used for |
| Description of AI use in the research method | manuscript, Section 10, *How the work was produced* |
| Extent of the author's own verification | **to be written by the author.** IOP asks the disclosure to explain how far the authors verified, validated and critically reviewed the AI-assisted output, and its template sentence says the authors did so and take full responsibility. The manuscript currently says what is true today: the checks were made by the Lean kernel, by independent programs and by a second set of AI sessions, and no human has refereed the mathematics. Before submitting, the author should do the review he is prepared to sign for, and then replace that sentence with his own account of it |
| Data availability statement | manuscript, *Data availability statement* |
| Funding and competing interests | manuscript, *Acknowledgments*: self-funded by the author, the sole operator of affiliated 0thernes LLC. Additional competing interests remain undeclared |
| Ethics | no human participants, animals or personal data |
| Originality and exclusivity | author confirmation still required on the form; disclose the public preprint and all prior publication. Exclusive journal submission has not yet been attested. Submit to one journal at a time |
| Reference check | IOP requires every cited source to be verified against the original. All 27 references were checked on 9 November 2026 against Crossref, arXiv, Zenodo or the publisher's site |

## What to expect

* The journal's criteria are significance, originality and correctness, with a physical motivation.
  Editors may decline without review; referees may ask for the two parts of the paper (the
  formalization, the new configurations) to be separated.
* Referee reports must be answered by the author. IOP allows AI tools only to improve the language of
  a response, not to write it.
* An optional pre-check (Paperpal Preflight) can be run on `jphysa/manuscript.pdf` before submitting; it
  looks at language and technical formatting, not at the mathematics.

## Steps

1. Sign in to the journal's submission site and link the author-supplied ORCID if required. The observed ScholarOne pages remain at login; authenticated profile access and ORCID linkage are not yet verified.
2. Choose *Paper*, enter title, abstract and keywords from this sheet.
3. Enter the author details above.
4. Paste the cover letter; answer the funding, open-access and reproduced-material questions.
5. Upload `manuscript.pdf` as the main document and `supplementary.pdf` as supplementary data.
6. Read the IOP ethical policy, confirm the declarations in person, and submit.

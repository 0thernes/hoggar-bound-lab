# Changelog

Versions of the spectral-floor paper and of the code that supports it. The independent companion review
and the companion C3 note in this repository are released separately by their own tags
(`v0.1.0-independent-verification`, `v0.2.0-c3-certificate`).

## 1.1.1 — 9 November 2026

No change to any result, proof or program.

* The author's ORCID iD (0009-0006-8168-9648) is given in the paper, the web page's indexing metadata,
  `CITATION.cff`, the LaTeX source and the submission sheets.
* The random census of seven-qubit forms now covers the last type (B of rank 7); the full title and DOI
  of one reference were added; every reference was checked against Crossref, arXiv, Zenodo or the
  journal's site.
* `publication/spectral-floor/` records the state of each venue and what each requires of the author.

## 1.1.0 — 9 November 2026

New results (paper, Section 5)

* A saturation criterion for arbitrary sets of observables, closed or not (Theorem 4).
* The pivot configuration: 135 four-qubit observables, 1095 contexts, contextuality degree exactly 75,
  and the state that defines it (Theorem 5); the classification of the fourth-root-of-unity states on a
  bent support (Proposition 6).
* The five-qubit configuration of 496 observables and 10880 contexts: degree exactly 480 (Theorem 7).
* The support of a flat state is a two-character set (Proposition 10).
* Flat phase states of the third level of the Clifford hierarchy: criterion (Proposition 11), complete
  enumeration on up to five qubits (Theorem 12), and a seven-qubit state with 8128 observables,
  2 824 192 contexts and degree exactly 729 344 (Theorem 13).

Lean

* `MaskConfig.lean`: configurations and assignments given by bit masks; their counts as sums the kernel
  evaluates; `degree_of_certificate`.
* `Saturated.lean`, `SaturatedFive.lean`, `SaturatedPhaseFive.lean`: `pivot_degree`,
  `cieslinski5_degree`, `phase5_degree`, `quadric_degree`, `hoggar_degree`, `ccz_degree`, `lly_degree`
  and the context counts. Fourteen audited declarations, standard axioms only.
* `SaturatedVerification.lean`: the axiom audit for these modules.

Programs and tests

* `scripts/flat_states.py` (68 exact checks), `scripts/phase_states.py` (81 exact checks),
  `src/third_level.c` (census for N ≤ 5), `src/family7.c`, `src/orbits7.c`, `src/sample7.c` and
  `scripts/run_family7.sh` (the seven-qubit enumeration).
* `src/moonlab_saturated.mjs`: eight flat states on Moonlab, two of them prepared as circuits; every
  context measured, including all 2 824 192 of the seven-qubit configuration.
* `src/qgt_flat.c`, `src/eshkol/saturated.esk`: the QGTL kernels and the Eshkol replication on the new
  states.
* `scripts/run_all.sh` runs the new stages; a second workflow, *Saturated configurations*, runs them
  and the Lean build in continuous integration.

Paper and repository

* Title extended; Sections 5 and 8 to 11 rewritten; references added.
* Affiliation given as 0thernes LLC throughout; indexing metadata added to the web page.
* `scripts/build_latex.py`: LaTeX source, typeset PDF and arXiv archive in `publication/spectral-floor/`.
* `scripts/fix_github_math.py` and `scripts/check_github_math.py` keep every formula readable in GitHub's
  Markdown view.
* New documents: `SUMMARY.md`, `GLOSSARY.md`, `INDEX.md`, `LEGAL.md`, `lean/README.md`, this file.

## 1.0.0 — 9 November 2026

* Lean 4 proof of the spectral floor for every number of qubits and arbitrary sets of observables
  (`hoggar_bound`), with corollaries for three, four and five qubits and for the hyperbolic quadrics.
* Independent reproduction of the best known assignments for two to five qubits; falsification suite
  with a negative control.
* The state-independent contextuality experiment on Moonlab; the QGTL kernels on the Hoggar state; the
  Eshkol replication.
* Paper, web page and citation metadata.

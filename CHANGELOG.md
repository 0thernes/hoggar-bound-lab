# Changelog

Hoggar Bound Lab - Alexander S. Donahue, 0thernes LLC.

Project releases cover the spectral-floor study and the surrounding repository. The independent review and the C3 study also have fixed companion tags: `v0.1.0-independent-verification` and `v0.2.0-c3-certificate`. Their version numbers identify those artifacts, not earlier editions of the spectral-floor paper. [Publication status](publication/STATUS.md) records archive and journal milestones separately.

## 1.1.2 - documentation and metadata release

This release brings the repository documentation together after `v1.1.1`. It preserves the spectral-floor study's mathematical content and the fixed C3 paper and proof content; it does not announce a new theorem or repeat another study's verification as if it were the C3 audit.

- Present both studies through shared navigation, glossary, license explanation and version history, with a separate [C3 research summary](docs/RESEARCH-SUMMARY.md).
- Add a C3 claim-to-theorem register, Lean reproduction guide and release-continuity check.
- Use Alexander S. Donahue and 0thernes LLC consistently in active publication credits. Record account-affiliation changes and remaining submission steps in the publication status, separately from paper publication.
- Add the author-supplied ORCID 0009-0006-8168-9648 to current citation and submission metadata. Incorporate the later v1.1.0 reference completion, seven-qubit experiment update and archive identifiers from the shared main branch.
- Preserve the existing custom verification license and third-party notices. Explain the disclosed Claude/Anthropic and OpenAI Codex research workflows separately.
- Distinguish the spectral-floor and saturation modules from the 42-declaration C3 audit. For C3, the printed factorization, block/Jordan argument, largest-eigenvalue gap 2 and continuous-relaxation gap 32 retain separate algebraic/executable evidence.
- Distinguish public preprints, automated checks, human critical review and journal peer review.
- Replace the unsupported blanket competing-interest statement in the spectral-floor publication package with the author-confirmed self-funding and sole-operator disclosures; regenerate the affected document formats.
- Prevent an older completed verification workflow from replacing a newer Pages deployment.

The C3 reference PDF remains the nine-page artifact with SHA-256 `5be6ba1318ce5cfeebf3a89b79dcfd428f87e228234e2f5075b14807a7f34836`, first released at commit `d3811e3b53048fa8f3206f08494f0a9834eed287`. Project `VERSION` is `1.1.2`; the [release record](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v1.1.2) identifies its fixed commit and publication timestamp.

## 1.1.1 — 9 November 2026

No change to any result, proof or program.

* The author's ORCID iD (0009-0006-8168-9648) is given in the paper, the web page's indexing metadata,
  `CITATION.cff`, the LaTeX source and the submission sheets.
* The random census of seven-qubit forms now covers the last type (B of rank 7); the full title and DOI
  of one reference were added; every reference was checked against Crossref, arXiv, Zenodo or the
  journal's site.
* `publication/spectral-floor/` records the state of each venue and what each requires of the author.

## 1.1.0 — 9 November 2026

Spectral-floor study, [paper Section 5](paper/spectral-floor.md). The results and checks below are the `v1.1.0` release's reported scope, documented in [INDEX.md](INDEX.md) and its own proof records. They are separate from the C3 audit.

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

## Companion v0.2.0-c3-certificate — 9 November 2026

[Published research release](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v0.2.0-c3-certificate), commit `d3811e3b53048fa8f3206f08494f0a9834eed287`. The GitHub publication timestamp is 10 November 2026 at 01:33:37 UTC, corresponding to 9 November in the author's recorded America/Los_Angeles timezone.

- Publish the explicit four-qubit C3 sign assignments on a 71-point real Pauli section, with 64 outside points and 1120 outside contexts.
- Supply equal carrier characteristic polynomials and unequal completion cubic traces, 14976 and 15360. This establishes the four-qubit C3 instance of the strict-law failure predicted by Jonah's Conjecture E; it does not refute that conjecture or settle all dimensions.
- Include the complete C3 Lean development and 42-declaration axiom audit, with the Pauli and signed-context model connection and eigenvalue multiplicities.
- Include separate exact integer checks, a direct signed-context verifier with negative controls, a browser BigInt verifier, and a recorded serial compiled Eshkol arithmetic run.
- Publish the research paper, citation metadata, source archive, proof and execution records, and checksums. The release contains 23 checked assets; its detailed publication and CI provenance is recorded in [publication/STATUS.md](publication/STATUS.md).
- Attribute the Jordan representation, block-spectrum framework, earlier spectral floor, and original C3 question to the inspected primary sources. No historical-first or physical-hardware claim is made.

The paper is a research preprint. This release did not establish journal acceptance, an arXiv identifier, a DOI for this paper, or completed human critical review.

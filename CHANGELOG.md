# Changelog

Hoggar Bound Lab - Alexander S. Donahue, 0thernes LLC.

Project releases cover the spectral-floor study and the surrounding repository. The independent review and the C3 study also have fixed companion tags: `v0.1.0-independent-verification` and `v0.2.0-c3-certificate`. Their version numbers identify those artifacts, not earlier editions of the spectral-floor paper. [Publication status](publication/STATUS.md) records archive and journal milestones separately.

## 1.4.0 - 10 November 2026: a self-contained proof of Conjecture E

The combined paper is revised to version 1.4.0; its title and its theorem statements are unchanged.
In version 1.3.0 the proof of Theorem 19 (Conjecture E in all nine vertex cases) cited two structure
theorems of Jonah's preprint, which is not peer reviewed: Theorem A (the completion matrix is Jordan
multiplication by the carrier) and Theorem B3 (its decomposition into blocks). The paper now writes
out the arguments it needs, with credit, and uses the preprint only through its definitions and its
case list:

- Section 8.7, Lemma 20 (restriction), which is Jonah's Theorem A with essentially his proof: for a
  configuration that contains the sum of any two distinct commuting points, the completion matrix is
  the matrix of T -> (A T + T A)/2 on the real span of the outside Paulis. The nine configurations
  have this property.
- Section 8.7, Lemma 21 (Jordan multiplication between two blocks), the linear algebra of Steps 3 and
  4 of his proof of Theorem B3: the eigenvalues of M -> (C M + M D)/2 on all complex matrices, on a
  real form of them (case C5 uses a real form instead of his quaternionic description), and, when D is
  the complex conjugate of C, on the symmetric or antisymmetric matrices.
- The case paragraphs verify the hypotheses of Lemma 21 explicitly: the form and number of the outside
  Paulis, the antiunitary map Theta_c(T) = P_c conj(T) P_c and the real form it fixes (cases C3, C5 and
  the bases of C11 and C14), the splitting by P_e (cones, C12, C15), and in C12 and C15 the symmetry
  M^T = eta M of every outside block with eta = theta_c^2. The trace formulas (E8) and (E9) follow.
- Section 8.7, before the lemmas: each construction fixes one hyperplane class of its case; a Clifford
  unitary carries a pair to every class of the case (by Jonah's case list, Theorem B4, these form one
  orbit), conjugating the carrier operators and the completion matrices by signed permutations.
- Section 8.6, Corollary 18: the proof of Jonah's cone lift is repeated (the four lifts of each
  outside line, lifted carrier I + 2A and -I, lifted completion matrix with blocks Lambda and
  Lambda + I).
- Abstract, scope box, Sections 1.1, 9.3 (Table 9), 11.3, 12 and 13, and Appendix A state the new
  dependence. Section 8.6 step (v) points to Lemma 20.

New program `scripts/conjecture_e_lemmas.py`: for both carriers of every pair of Table 6 it checks the
identity of Lemma 20 at every outside point, each hypothesis that the proof verifies, the reduction of
C8 to C1, and the conclusion of Lemma 21 through tr Lambda^j, j <= 6, against the power sums of the
predicted eigenvalues, in Gaussian-integer arithmetic; four negative controls must fail. It passes 115
checks for three to five qubits (`results/conjecture_e_lemmas.json`, about ten seconds) and 46 at six
qubits (`results/conjecture_e_lemmas_n6.json`). Both runs are steps of the workflow *Case C3 for every
number of qubits*, whose regenerated records must equal the committed ones, and stages of
`scripts/run_all.sh`. The release audit (`scripts/publication_release_audit.py`, version 1.4.0) also
requires both records to be complete and the program to be a CI step.

Review before release: seven separate passes of the same AI system, each started without the others'
work (Lemma 20 and the closure property; Lemma 21 with (E8) and (E9); the C1, C3, C5 hypotheses; C12
and C15; the cones, C8 and Corollary 18; the program, with deliberate faults; the dependence on and
credit to Jonah's preprint), each finding examined by one or two adversarial verifiers. No
mathematical error was found. The 13 confirmed findings are corrected: the lemmas are credited as
Jonah's arguments written out rather than as special cases proved independently; a transport
paragraph carries each construction from its hyperplane class to every class of the case; one symbol
for the line sign; eta instead of epsilon for the sign of theta_c^2; the carrier tau of C12 and C15
written out; real dimension; the four lifts in Corollary 18; and in the program a guard that every
outside block of C12 and C15 is twice a unitary in bases lying in the right eigenspaces, with a fourth
negative control. The record is in `results/review-lemmas-20-21/`.

Verification of the release: at commit `7d746a3`, whose programs and Lean files are those of the
release, the workflow *Case C3 for every number of qubits* passed every step, both lemma steps included
([run 42834831157](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42834831157); logs kept in
`results/ci-run-42834831157/`), and so did the publication documentation checks
([run 42834873547](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42834873547)). The result of
Independent verification at the same commit ([run 42834831332](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42834831332))
is recorded in `publication/STATUS.md`. A complete `scripts/run_all.sh` in a fresh clone of `7d746a3`
passed all 24 stages (`results/run_all.log`).

Version strings, the metadata (with the 1.3.0 release kept as `previous_release`), `CITATION.cff`, the
BibTeX entry, the plain abstract (1903 characters), README, summary, index, glossary, claim register,
landing page, submission notes, errata, author declarations and the headers of two addenda are updated.
No Lean file changes; every Lean file of the earlier audits remains byte-identical.

## 1.3.0 - 10 November 2026: combined paper with Conjecture E

The combined paper ([paper/unified-contextuality.md](paper/unified-contextuality.md)) is revised to
version 1.3.0 and retitled *Spectral bounds and their limits in Pauli contextuality: exact
configurations and a proof of Jonah's Conjecture E*. It folds in the four addenda listed below:

- Section 8.5: Corollary 16, the binary completion minima of the four-qubit pair differ.
- Section 8.6: Theorem 17, case C3 for every N >= 4 by graph carriers, with the Lean theorem
  `c3_strict_law_fails_general`; Corollary 18, case C11; Remarks (a) to (d); Table 5.
- Section 8.7: Theorem 19, Conjecture E in all nine vertex cases; Tables 6 and 7. Outside case C3 the
  proof is on paper and uses [J3, Theorems A and B3]; it is checked by exact computation.
- Section 8.8; Section 9.3 (the Lean statement and what it leaves to the reader); Table 9 and the
  module tables; Section 11.3 (the programs); Sections 12 and 13; Appendices A and B.
- Section 5.3, 9.1 and abstract: the seven-qubit degree 729344 is a Lean theorem with kernel-evaluated
  counts.
- Funding and competing-interest statement from the author's recorded declarations.

Further checks: `scripts/conjecture_e.py 6` checks all nine vertex cases at six qubits (36 checks,
`results/conjecture_e_n6.json`); the program now writes runs at other than the default sizes to their own
record, so they no longer overwrite `results/conjecture_e.json`. The six-qubit run is a step of the
workflow *Case C3 for every number of qubits* and a stage of `scripts/run_all.sh`, which also gains the
seven-qubit check `scripts/phase_seven_lean.py`. Corrections from an independent review of Theorem 19
(no error found; wording and notation in Sections 8.6 and 8.7) and from the review of the seven-qubit
work (Sections 5.1, 5.3, 9.1, 9.3 and Appendix A) are included.

A final review of the whole change set in four independent lenses (mathematics and numbers, Lean
fidelity and reproducibility, consistency between documents, scholarly integrity), each with an
adversarial verifier, confirmed no critical finding; its 39 confirmed minor and major findings are
corrected. Among them: the Lean result for case C3 is stated for N >= 4 throughout; the proof of
Theorem 13 names which program computes what; the CI runs of the C3 workflow are described with the
checks each one ran; notation in Section 8.7; the tables are numbered in order of appearance (the new
tables of Section 8 are 5 to 7, the formal tables of Section 9 are 8 and 9); stale v1.2.0 statements
in the README, glossary, research summary, submission notes and errata; the metadata and plain-text
abstracts, which the unified audit now compares with the paper; addenda links on the site.
`scripts/cospectral_family.py` without `--six` now writes its own record instead of overwriting the
committed one.

Verification of the release: at commit `6189b62`, whose programs and Lean files are those of the
release, the workflow *Case C3 for every number of qubits* passed every step, the six-qubit Conjecture E
step included ([run 42817286684](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42817286684);
logs kept in `results/ci-run-42817286684/`), and the publication documentation checks passed
([run 42817314224](https://github.com/0thernes/hoggar-bound-lab/actions/runs/42817314224)). A complete
`scripts/run_all.sh` in a fresh clone passed all 22 stages and reproduced every committed record apart from
elapsed seconds (`results/run_all.log`).

Publication machinery: `scripts/build_unified_paper.py` takes the version from one constant and the
archive date from the byline; both publication audits move to 1.3.0 and gain checks (sources of the
seven-qubit and C3 Lean files unchanged since their CI runs, their axiom reports, the arXiv abstract
length); `publication/unified-metadata.json`, `CITATION.cff`, `VERSION`, the BibTeX entry, the plain
abstract, the README and the site list are updated. Every Lean file of the earlier audits is unchanged;
the C3 paper, its proof artifacts and release `v0.2.0-c3-certificate` are untouched.

### Results first recorded as addenda (now in 1.3.0)

- [Addendum](publication/ADDENDUM-conjecture-e.md), proposed for the next revision of the combined
  paper: **Jonah's Conjecture E holds** (Theorem 19). On sign carriers the strict law fails in all nine
  vertex cases C1, C3, C5, C6, C8, C11, C12, C14, C15 for every n >= 4 (C1, C3, C6, C11 already for
  n = 3). Explicit carriers: graphs over R, C and H for C1, C3, C5; the complex graph between the two
  P_e-blocks for C12 and C15; a pair swap for the cones C6, C11, C14; C1 on n - 1 qubits for C8. The
  proof uses the source's restriction lemma and graded law. `scripts/conjecture_e.py` builds every case
  from the definitions for n = 3, 4, 5 and checks equal carrier characteristic polynomials and
  different completion cubic traces in exact arithmetic (81 checks, `results/conjecture_e.json`). Only
  case C3 is a Lean theorem; the other eight cases are not formalized.
- [Addendum](publication/ADDENDUM-seven-qubit-lean.md), proposed for the next revision of the combined
  paper: **the seven-qubit contextuality degree 729344 is proved in Lean, with its counts.** The new
  theorems `phase7_degree` and `phase7_contexts` (`lean/HoggarBound/SaturatedPhaseSeven.lean`) have the
  form of the five-qubit ones: 8128 observables, 2824192 contexts, every assignment violates at least
  729344 of them and one violates exactly 729344. The two counts are double sums with 2^28 terms each.
  `lean/HoggarBound/MaskRows.lean` evaluates one row of such a sum on packed sets of codes and proves,
  for every number of qubits, that the result is the row of `MaskConfig.lean`; the kernel then evaluates
  the 16384 rows in 16 blocks (`decide +kernel`, no `native_decide`, no axiom beyond the standard three; audit in
  `lean/SaturatedSevenVerification.lean`, log in `results/lean-saturated-seven-axioms.log`). That the
  mask is the Pauli support of the state of Theorem 13 is checked by programs, as before. No existing
  Lean file is changed, and release 1.2.0, its manuscript and its artifacts are unchanged.
- `scripts/phase_seven_lean.py` (14 checks, two negative controls): the same evaluation in Python,
  compared with the direct double sums; it generates `SaturatedPhaseSeven.lean`. The workflow *Saturated
  configurations* runs it, builds the two new modules and enforces the axiom allowlist.
- [Addendum](publication/ADDENDUM-c3-all-qubits.md), proposed for the next revision of the combined
  paper: **the strict law fails in case C3 for every number of qubits N >= 4**, not only for N = 4,
  and therefore, by the cone lift of the source, **in case C11 for every N >= 4**. An explicit family
  of sign carriers, described by graphs on the block's basis states, gives for every N two carriers
  with the same carrier spectrum whose completion cubic traces differ by (3/2) n^3, n = 2^(N-1); the
  two carriers differ at the n/2 points Z (x) W (x) X. The proof is written out in the addendum.
  - Lean: `lean/HoggarBound/CarrierFamily.lean`, theorem `c3_strict_law_fails_general`, for every
    N >= 4, with the definitions of the existing library (real quadric, polar point, section, contexts
    and their signs). No `sorry`, no `native_decide`, no axiom beyond the standard three. A new file; no existing
    Lean file is changed. The addendum lists what the statement leaves to the reader.
  - Exact integer arithmetic on the complete configurations: `scripts/cospectral_family.py` (N = 3 to 6,
    random graphs, two negative controls; 43 checks), `scripts/cospectral_family_tensor_check.py` (a
    second route; 18 checks), `scripts/cospectral_family_cone_lift.py` (case C11 with 4, 5 and 6
    qubits; 21 checks).
  - The new workflow *Case C3 for every number of qubits* runs the programs and the Lean check.
  - The addendum records the automated review of the result and what it changed. Release 1.2.0 is
    unchanged.
- `scripts/c3_sparse_search.py`: exhaustive and exact search of the sign carriers with +1 at the polar
  point that differ from the all-plus carrier in at most three block observables (a sign flip, or a
  move to the other block with either sign). Five qubits: 10 908 676 carriers, no two cospectral with
  different block spectra. Four qubits: 182 176 carriers, exactly four classes of cospectral carriers
  with different block spectra, three of them with different completion cubic traces; the program
  finds the pair of the combined paper in one of the three (`results/c3_sparse_search.json`).
- [Addendum](publication/ADDENDUM-completion-optima.md), proposed for the next revision of the combined
  paper: the exact binary completion minima of the two C3 carriers differ. Every completion of the
  first carrier violates at least 347 of the 1120 outside lines, and an explicit completion of the
  second violates 344. This is exact rational arithmetic with explicit witnesses, not a Lean statement.
  Release 1.2.0, its manuscript and its artifacts are unchanged.
- `scripts/cospectral_pair.py`: a reconstruction of Section 8 from the definition of the Pauli matrices
  that shares no code with the C3 programs (30 checks, two negative controls). It is a stage of
  `scripts/run_all.sh` and a step of the workflow *Saturated configurations*.

## 1.2.0 - combined research manuscript

The author requested one paper combining the spectral-floor/saturation study and the four-qubit C3
certificate. The unified manuscript has a shared abstract, notation, bibliography, formal-proof map,
and Journal of Physics A package. It preserves the original source papers and their historical
releases. Integration is not a claim of a new theorem or a new priority for the spectral floor. Review also corrects missing nonempty/nonzero hypotheses and several overgeneralized prose statements, recorded in [UNIFIED-ERRATA.md](publication/UNIFIED-ERRATA.md).

Both C3 section assignments are independently recounted as violating 132 of 455 section contexts,
although their completion spectra differ. A single-sign mutation changes the violation count to 147.
This is derived/executable evidence, not a new Lean specialization or a binary completion optimum.

The repository documentation, citation, front page and submission metadata identify the combined
work. Eight requested channels are tracked separately by their actual publication, indexing,
identity and preservation roles. The LICENSE and NOTICE remain unchanged.

## Unreleased 1.1.2 integration preparation

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

The C3 reference PDF remains the nine-page artifact with SHA-256 `5be6ba1318ce5cfeebf3a89b79dcfd428f87e228234e2f5075b14807a7f34836`, first released at commit `d3811e3b53048fa8f3206f08494f0a9834eed287`. This integration preparation was not published as a release. Its documentation and disclosure corrections are incorporated in version 1.2.0.

## 1.1.1 — 9 November 2026

No change to the formal theorem statements or proof sources.

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

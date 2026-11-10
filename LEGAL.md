# License, authorship, and publication notices

Hoggar Bound Lab - Alexander S. Donahue, 0thernes LLC.

This page summarizes the repository's notices. **[LICENSE](LICENSE) governs project-authored files; [NOTICE](NOTICE) identifies third-party terms.** This summary does not change either.

## Copyright and license

The repository's copyright notice identifies **0thernes LLC (Alexander S. Donahue)**. Its custom **Verification licence** permits downloading, building, running, and studying the repository to check, reproduce, or referee its reported results, and quotation with attribution. Redistribution of modified versions and commercial use require the copyright holder's written permission.

The repository is publicly available under those terms; it is not offered under an unrestricted open-source license. A separately chosen paper or archive distribution license must be identified explicitly. It does not silently change the licenses of project code or third-party material. This page grants no additional rights. The work is provided as is, under the warranty and liability provisions of [LICENSE](LICENSE).

## Third-party components

[NOTICE](NOTICE) identifies the vendored components and their separate licenses:

| Component | Repository location | Governing notice |
| --- | --- | --- |
| Moonlab WebAssembly engine and loader | `third_party/moonlab/` | [MIT license](third_party/moonlab/LICENSE) and the directory's provenance record |
| Legacy seeded quantum_rng sources | `third_party/quantum_rng/` | [MIT license](third_party/quantum_rng/LICENSE) and the directory's provenance record |
| Selected QGTL differential-geometry sources | `third_party/qgtl/` | [MIT license](third_party/qgtl/LICENSE) and the directory's provenance record |
| Mathlib dependency | Fetched through Lake, not vendored | Apache 2.0, as recorded in `NOTICE`; consult the dependency's own license |

The project-written QGTL `stub/cblas.h` is identified separately in `NOTICE`. Preserve the original third-party copyright, license, and attribution notices. Use of these components does not imply endorsement by their authors.

Eshkol is used through an installed compiler for the recorded replication runs. Those executions do not relicense Eshkol or make it part of the project's own copyright claim. Tsotchke project names, Lean, Mathlib, Claude, and OpenAI Codex identify the tools and sources used; they do not imply institutional sponsorship or endorsement.

## Authorship and AI disclosure

Both research studies credit **Alexander S. Donahue**, affiliated with **0thernes LLC**. Public correspondence is `0_0@0thernes.art`.

- The [spectral-floor and flat-state paper](paper/spectral-floor.md) discloses Claude/Anthropic as the AI research system used under the author's direction. Its paper, programs, formalization, and result records have their own scope; see [SUMMARY.md](SUMMARY.md), [INDEX.md](INDEX.md), and [CITATION.cff](CITATION.cff).
- The independent companion review and [C3 paper](paper/c3-spectral-counterexample.md) disclose substantive OpenAI Codex agent work on literature research, discovery, derivation, code, formalization, verification, figures, and writing. Use the [C3 citation file](paper/c3-citation.cff) for that study and its fixed research release.

AI tools are disclosed as tools, not listed as authors. Automated checks and separately implemented programs do not establish that a human has critically reviewed and approved a manuscript. Venue-specific contribution, approval, and accountability statements must describe the human author's actual actions; they cannot be inferred from a successful program or Lean build.

The author supplied these declarations: **This research was self-funded by the author. The author is the sole operator of 0thernes LLC, with which this project is affiliated.** These statements do not certify the absence of other competing interests. No legal nonprofit, charitable, tax-exempt, university, or accredited-laboratory status is asserted here.

## Attribution and verification boundaries

The spectral floor and earlier classical-family results are attributed to the sources cited in the spectral-floor paper. The `v1.1.0` study reports further saturation and flat-state results; its novelty assessment and exact proof/computation boundaries are documented in that paper and its own index. The C3 development does not independently audit all of those results.

The C3 paper credits B. W. Jonah's [section-square-law preprint](https://doi.org/10.5281/zenodo.23524332) for the question, case classification, and completion framework, and his [structure preprint](https://doi.org/10.5281/zenodo.23538829) for the earlier spectral-bound machinery. It establishes the four-qubit C3 instance, not every dimension of Conjecture E or historical first priority.

The [C3 formal audit](results/frontier-c3-lean-audit.md) covers 42 declarations connecting the original Pauli geometry to equal carrier spectra and unequal completion spectra, including the exact cubic traces. Its printed polynomial factorization, block/Jordan argument, and gaps of 2 and 32 have separate algebraic/executable evidence and are outside those Lean theorem statements. Other studies' audits are not absorbed into that count.

## Publication and documentation versions

These works are research preprints, not peer-reviewed journal articles. A public GitHub release, a DOI deposit, an arXiv announcement, indexing, journal submission, and acceptance are distinct events. [Publication status](publication/STATUS.md) records the C3 dissemination history; the spectral-floor submission materials are under [publication/spectral-floor/](publication/spectral-floor/).

The `v1.2.0` project release updates presentation and metadata after `v1.1.0`, preserving both studies' mathematical content and the fixed `v0.2.0-c3-certificate` paper and proof. It grants no additional rights. Consult [CHANGELOG.md](CHANGELOG.md) and the release record for version history.

Author-supplied ORCID: [0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648).

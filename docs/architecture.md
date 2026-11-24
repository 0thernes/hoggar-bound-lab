# Repository Architecture (`hoggar-bound-lab`)

`hoggar-bound-lab` is organized as a **layered, append-only formal verification and reproducible research monorepo** built around one canonical manuscript (`paper/unified-contextuality.md`) and a strictly preserved history of frozen Lean 4 proofs.

```text
hoggar-bound-lab/
├── lean/                          # Lean 4.35.0 + Mathlib v4.35.0 formal proof library
│   ├── lean-toolchain             # Pinned: leanprover/lean4:v4.35.0 (FROZEN)
│   ├── lakefile.toml              # Package config (FROZEN)
│   ├── lake-manifest.json         # Pinned Mathlib/Batteries revisions (FROZEN)
│   ├── HoggarBound/
│   │   ├── [Frozen v0.1-v1.4]     # Moment, Pauli, Bound, Counting, Quadric, Stability,
│   │   │                          # C3Data..C3Spectra, MaskConfig, Saturated*, CarrierFamily
│   │   ├── [v1.5-v1.7]            # Kramers, SaturationTheory, ConjectureECore, ConjectureECones,
│   │   │                          # ConjectureE, ConjectureEExtras, AuditUpgrades
│   │   ├── [v1.8]                 # C3ExactOptimaData, C3ExactOptima, SaturatedPhaseSix,
│   │   │                          # NormPhaseFamily, ExactDegreesN4N5
│   │   └── [v1.9]                 # NonVacuity, Challenge (target stubs), Solution
│   ├── comparator.json            # 6-kernel lake comparator --paranoid configuration
│   └── VerifyNewFormalizations.lean  # 110-declaration #print axioms audit
├── scripts/                       # Exact integer/SymPy verifiers, builders & continuity audits
├── src/                           # C11 exhaustive censuses (w52_census_verify.c, n9_rank8_search.c) & Tsotchke demos
├── tests/                         # Property (Hypothesis), mutation/fuzz, browser (Node) & validation tests
├── blueprint/                     # Lean Blueprint LaTeX source & declaration-checked dependency DAG
├── data/                          # Certificates, orbit tables, flat state vectors & MANIFEST.sha256
├── paper/                         # Canonical unified manuscript (MD/PDF/HTML) & historical component PDFs
├── publication/                   # Submission packets (arXiv source zip, J. Phys. A PDFs, metadata, STATUS.md)
├── results/                       # Checked logs, JSON receipts, distribution & continuity audit records
├── c3-lab/, independent-review/   # Static interactive browser explorers (deployed via GitHub Pages)
└── docs/                          # Architecture, ADRs, statement fidelity, threat model, run-log, reviews, FAQ, glossary
```

## Six-Layer Verification Architecture

1. **Multi-Kernel Formal Proof (`lean/`):** Lean 4.35.0 official C++ kernel + `leanchecker-paranoid` + `lean4lean` + `nanoda` (0.4.19) + `con-leche` + `con-ron` via `lake comparator --config comparator.json --paranoid`, plus Batteries `lake exe runLinter`.
2. **Statement Fidelity & Non-Vacuity (`Challenge.lean`, `NonVacuity.lean`, `docs/statement-fidelity.md`):** Isolated target signatures paired with explicit inhabited witnesses for every headline theorem bundle.
3. **Exact Integer/Symbolic Computation (`scripts/`, `src/`):** Zero-floating-point Python/SymPy verifiers (`202` exact checks in CI) and C11 exhaustive censuses compiled with `-Wall -Wextra` and verified under ASan/UBSan (`-fsanitize=address,undefined`).
4. **Property, Mutation, Fuzz & Continuity Testing (`tests/`, `scripts/publication_release_audit.py`):** Hypothesis property tests, deliberate mutation-kill tests, parser fuzzing, browser tests, and byte-level frozen-file continuity checks.
5. **Blueprint & Documentation Integrity (`blueprint/`, `scripts/build_blueprint.py`, `scripts/check_readme_axioms.py`, `scripts/check_citations.py`):** Machine-checked Lean declaration cross-links, verbatim `#print axioms` sync in `README.md`, arithmetic tier audit, and citation resolution audit.
6. **Cryptographic Provenance & Archival (`.github/workflows/release.yml`, `data/MANIFEST.sha256`, `0thernes-research-archive`):** `SHA256SUMS`, GitHub Actions Sigstore SLSA attestations (`actions/attest-build-provenance`), GitHub Pages byte-identical deployment, Software Heritage SWHIDs, and pinned submodule archival.

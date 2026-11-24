# AGENTS.md

Canonical instructions for every coding agent working in `hoggar-bound-lab` (Codex, OpenCode, Claude Code, Gemini CLI, Antigravity, Cursor, Grok Build, Grok Bot and others).
`CLAUDE.md`, `GEMINI.md`, `.cursor/rules/build-standard.mdc` and `llms.txt` only point here. Edit this file, never the pointers.
Full standard: `docs/build-standard.md` (Build Standard for LLMs v1.1.0, 90 items). Read the relevant items before building.

## Project

- Name: Hoggar Bound Lab (`hoggar-bound-lab`)
- Purpose: Machine-checked Lean 4.35.0 proofs and exact integer/symbolic verifiers for spectral bounds on Pauli contextuality, floor-saturating configurations (including the infinite pure-CCZ determinant family `|Psi_{3m}>`), classical N=4..5 ladders, exact four-qubit C3 binary completion optima (368 vs 344, gap 24), and a full proof of Jonah's Conjecture E across all nine vertex cases for every N >= 4.
- Owner: Alexander S. Donahue (`0thernes`, ORCID `0009-0006-8168-9648`)
- Manifest: `repo.yaml` (project type, stack, flags and per-item status; schema in `repo-standard.schema.json`)
- Stack: Lean 4.35.0 + Mathlib v4.35.0 (`lean/`), Python 3.12 (`scripts/`, `tests/`), C11 (`src/*.c`), Node.js 24 (`c3-lab/`, `independent-review/`, `tests/*.cjs`), XeLaTeX (`paper/`, `publication/`)
- Layout: `lean/` (Lean 4 proofs, `VerifyNewFormalizations.lean`, `Challenge.lean`, `Solution.lean`, `comparator.json`), `scripts/` (exact verifiers, paper builder, site builder, audits), `src/` (C11 search/census programs & Tsotchke demos), `tests/` (property, mutation, fuzz, browser & validation tests), `paper/` (unified manuscript MD/PDF/HTML), `publication/` (submission packets, arXiv bundle, J. Phys. A PDFs), `blueprint/` (Lean Blueprint LaTeX & dependency DAG), `data/` (certificates, flat states, `MANIFEST.sha256`), `results/` (checked logs & JSON receipts), `docs/` (architecture, ADRs, threat model, run log, reviews, FAQ, glossary).
- Status: active (research preprint, not externally peer reviewed; AI-assisted under human direction)

## Commands

Use the task runner (A31). The `justfile` delegates to `scripts/dev.sh` and repository verifiers. Every command works from a clean clone.

- `just setup`: install pinned Python dependencies (`requirements.txt`) and fetch pinned Lean/Mathlib cache
- `just build`: build Lean 4.35.0 modules and compile C11 verifiers with `-Wall -Wextra`
- `just test`: run Python exact verifiers, property/negative/regression/mutation tests, and Node tests
- `just lint`: run `ruff`, `mypy`, C compiler warnings, and Batteries `lake exe runLinter` (report-only)
- `just sanitizers`: compile and run C11 verifiers under `-fsanitize=address,undefined`
- `just verify-lean`: build Lean modules, run 110-declaration axiom audit, and run `lake comparator --paranoid`
- `just blueprint`: check Lean declarations in `blueprint/` and rebuild the interactive dependency graph
- `just reproduce`: clean clone to headline results (exact verifiers + audits + site assembly)
- `just audit`: score this repo against Build Standard v1.1.0 (`scripts/audit-repo.sh` / `scripts/Audit-Repo.ps1`)
- `just release X.Y.Z`: bump `VERSION`, tag `vX.Y.Z`, and push straight to `main` (release workflow emits `SHA256SUMS` and SLSA attestations)

## Hard rules

- R1. Nothing may gate, block or slow a commit or push. No branch protection, no required status checks, no commit or tag signing requirements, no git hooks (pre-commit, pre-push, commit-msg), no push protection, no merge queues.
- R2. Commit and push straight to main. No pull requests and no feature branches. Fixes for failing checks are follow-up commits to main.
- R3. CI is informational. CI reports results on every push. A red CI run is a finding to fix, never a barrier.
- R4. Banned tools and files. No Dependabot or Renovate auto-PRs, no PR templates, no CodeRabbit, no Copilot review or `.github/copilot-instructions.md`, no FUNDING file unless the owner asks.
- R5. One-person lean, not corporate. Prefer one file over a framework, one command over a checklist, plain text over portals. Add process only if it directly helps the owner build or prove the work.
- R6. Never fabricate. Every claim, number, badge, screenshot and test result must come from a real run of the current code. Unverified means labeled unverified.
- R7. Classify every finding. Each finding is exactly one of: `bug`, `error`, `issue`, `problem`, `dilemma`, `conflict` (definitions below).
- R8. Precedence when rules collide. Owner's explicit instruction, then these hard rules, then this standard's items, then ecosystem conventions.

## Finding classes

Classify every finding as exactly one:

- `bug`: A defect in program logic: the code runs but does something different from its specification or intent.
- `error`: A wrong artifact or failed execution outside program logic: an incorrect number, claim, doc, config, version, build or command.
- `issue`: A gap: something this standard or the task requires is missing or incomplete, but nothing present is wrong.
- `problem`: An external obstacle that blocks progress and is not caused by the project's own code or artifacts.
- `dilemma`: A trade-off between two or more valid options where the right choice depends on the owner's priorities.
- `conflict`: Two requirements, sources or rules contradict each other, so satisfying one violates the other.

## Order of operations

1. Read this `AGENTS.md` first, then `docs/build-standard.md` and `repo.yaml`.
2. Respect all frozen-file invariants (see Known traps below) before modifying any file.
3. Keep the minimum core set passing at all times.
4. For each change, run its verification check and save or update its evidence artifact in `results/` or `docs/`.
5. Commit small, meaningful commits straight to `main` and push after each working step. Never open a PR or feature branch.
6. Report results: items done, items not applicable (with reason), items not done, and every finding classified as exactly one of the six classes.

## Minimum core set

- A01 README with a one-line purpose
- A03 Quickstart that works from a clean clone
- A06 LICENSE
- A07 CHANGELOG
- A08 Semantic version, tags and a single version source
- A09 Automated tests that pass
- A10 Informational CI
- A12 .gitignore
- A24 No secrets, build output or huge files committed
- A31 Task runner with one-word commands
- A32 Agent entry points: AGENTS.md canonical, plus CLAUDE.md, GEMINI.md, Cursor rules, llms.txt
- B01 Reproducible build from a clean clone
- B02 Pinned toolchains and lockfiles
- B04 CLAIMS.md ledger
- B05 Falsifiable tests per claim
- B06 Negative tests
- B07 Regression test per fixed bug
- B41 Limitations and real-vs-metaphor
- B43 Replication protocol

## Checklist (tier in brackets; exact status tracked in repo.yaml; details in docs/build-standard.md)

Part A: Repo Fundamentals

- [x] A01 README with a one-line purpose [core]
- [x] A02 Badge ribbon [recommended]
- [x] A03 Quickstart that works from a clean clone [core]
- [x] A04 Usage examples [core]
- [x] A05 Demo media [recommended]
- [x] A06 LICENSE [core]
- [x] A07 CHANGELOG [core]
- [x] A08 Semantic version, tags and a single version source [core]
- [x] A09 Automated tests that pass [core]
- [x] A10 Informational CI [core]
- [x] A11 Releases [recommended]
- [x] A12 .gitignore [core]
- [x] A13 .gitattributes and .editorconfig [recommended]
- [x] A14 CONTRIBUTING guide [recommended]
- [x] A15 CODE_OF_CONDUCT [recommended]
- [x] A16 SECURITY.md [core]
- [x] A17 SUPPORT.md [recommended]
- [x] A18 Issue templates [recommended]
- [x] A19 About description and topics [core]
- [x] A20 docs/ folder [recommended]
- [x] A21 Architecture Decision Records [recommended]
- [x] A22 CITATION.cff [advanced]
- [x] A23 Clean history and correct identity [core]
- [x] A24 No secrets, build output or huge files committed [core]
- [x] A25 Cross-platform CI [recommended]
- [x] A26 Social preview image [recommended]
- [x] A27 Pages demo or docs site [advanced]
- [ ] A28 Package manifest [recommended] (n/a: research repo, not an installable package)
- [x] A29 ROADMAP.md [recommended]
- [x] A30 Labels including the six finding classes [recommended]
- [x] A31 Task runner with one-word commands [core]
- [x] A32 Agent entry points: AGENTS.md canonical, plus CLAUDE.md, GEMINI.md, Cursor rules, llms.txt [core]
- [x] A33 Environment and configuration documented [core]
- [ ] A34 Observability basics: logs, errors, health [recommended] (n/a: not a long-running service)
- [x] A35 Data, migrations, backups and an offsite repo mirror [recommended]
- [ ] A36 One-command deploy and rollback [recommended] (n/a: static GitHub Pages only)
- [ ] A37 Performance budgets [advanced] (n/a: no speed/efficiency claims)
- [x] A38 Accessibility and internationalization [core]
- [x] A39 Third-party licensing and attribution [recommended]
- [ ] A40 AI components pinned, evaluated and budgeted [core] (n/a: code calls/ships no AI model)
- [ ] A41 Deprecation and upgrade path [advanced] (n/a: not a distributed package/API)
- [x] A42 Maintenance status [recommended]
- [ ] A43 examples/ directory [recommended] (n/a: not a library package)
- [x] A44 FAQ and glossary [recommended]
- [ ] A45 Privacy and personal-data handling [core] (n/a: collects no personal data)

Part B: Verification Ladder: prove it isn't BS

- [x] B01 Reproducible build from a clean clone [core]
- [x] B02 Pinned toolchains and lockfiles [core]
- [x] B03 Determinism checks [core]
- [x] B04 CLAIMS.md ledger [core]
- [x] B05 Falsifiable tests per claim [core]
- [x] B06 Negative tests [core]
- [x] B07 Regression test per fixed bug [core]
- [x] B08 Golden and snapshot tests [recommended]
- [ ] B09 Contract and API tests [recommended] (n/a: no API/protocol exposed)
- [x] B10 Property-based tests [core]
- [x] B11 Differential testing [recommended]
- [x] B12 Reference implementation as test oracle [recommended]
- [x] B13 Mutation testing [recommended]
- [x] B14 Metamorphic testing [advanced]
- [x] B15 Fuzzing [recommended]
- [x] B16 Sanitizers and runtime checkers [core]
- [x] B17 Static analysis and linters, report-only [recommended]
- [x] B18 Strict type checking [recommended]
- [ ] B19 Concurrency and race testing [advanced] (n/a: single-threaded deterministic verifiers)
- [x] B20 Numeric and floating-point stability [advanced]
- [ ] B21 Failure injection [advanced] (n/a: not a networked service)
- [x] B22 Formal specification and proof [advanced]
- [ ] B23 Design model checking [advanced] (n/a: mathematical theorem proving, not distributed state machine)
- [x] B24 Verified implementation language [advanced]
- [ ] B25 Bounded model checking of real code [advanced] (n/a: C census programs checked by ASan/UBSan + exact Python dual verification)
- [ ] B26 Honest benchmarks [core] (n/a: no performance claims)
- [ ] B27 Performance tracking over time, report-only [advanced] (n/a: no performance claims)
- [ ] B28 Controls and multiple seeds [core] (n/a: mathematical proofs & deterministic enumerations, not stochastic trials)
- [ ] B29 Significance testing [core] (n/a: exact algebraic theorems, not statistical hypothesis tests)
- [ ] B30 Effect sizes and confidence intervals [core] (n/a: exact integers/theorems, not statistical estimates)
- [ ] B31 Multiple-comparison correction [recommended] (n/a: not multi-arm statistical testing)
- [ ] B32 Pre-registration of hypotheses [advanced] (n/a: deductive formal mathematics, not empirical trials)
- [ ] B33 ML evaluation on held-out data [core] (n/a: no ML models)
- [ ] B34 AI hallucination and regression evals [core] (n/a: code calls/ships no AI model)
- [x] B35 Security scanning, report-only, with optional SBOM [recommended]
- [x] B36 Threat model [recommended]
- [x] B37 Release hashes and checksums [core]
- [x] B38 Build provenance and attestations [recommended]
- [x] B39 Data checksums and dataset versioning [recommended]
- [x] B40 Audit trail [recommended]
- [x] B41 Limitations and real-vs-metaphor [core]
- [x] B42 What would prove us wrong [core]
- [x] B43 Replication protocol [core]
- [x] B44 Independent replication [advanced]
- [x] B45 Peer and red-team review [recommended]

## Known traps

- **Frozen research files (DO NOT MODIFY):** `scripts/publication_release_audit.py` enforces byte-identical continuity against frozen commits `d3811e3` (21 C3 proof/config files + `LICENSE` + `NOTICE` + `paper/c3-*`), `87f08a0` (28 Lean/config files including `lean/lakefile.toml`, `lean/HoggarBound.lean`, `lean/lean-toolchain`, `lean/lake-manifest.json`), and `5dcea35` (`lean/HoggarBound/CarrierFamily.lean`). Add new Lean modules alongside them; never edit frozen files.
- **Challenge.lean sorry stubs:** `lean/HoggarBound/Challenge.lean` intentionally contains `sorry` stubs as the isolated statement-only specification checked against sorry-free `lean/HoggarBound/Solution.lean` by `lake comparator --config comparator.json --paranoid`. Never add `sorry` to any proof module or `Solution.lean`.
- **Unified abstract byte-sync:** `scripts/unified_publication_audit.py` asserts that `publication/unified-metadata.json` (`abstract`) matches the `## Abstract` section of `paper/unified-contextuality.md` byte-for-byte, including GitHub math delimiters like ``$`|\Psi_{3m}\rangle`$``.
- **Single GitHub Pages site:** `.github/workflows/independent-pages.yml` deploys `build/independent-site/` assembled by `scripts/independent_site.py`. Always mount the Lean Blueprint under `build/independent-site/blueprint/` inside that workflow; never add a competing Pages workflow.
- **PowerShell bracket-safety on Windows:** On the author's local ReFS Dev Drive (`Z:\[Vibe Coded (AI)]\...`), always use `-LiteralPath` in PowerShell file cmdlets and relative paths for `gh release create`.
- **Owner-only legal & external actions:** Never unilaterally alter `LICENSE`, copyright-holder text (`0thernes LLC` legal-entity status finding logged in `LIMITATIONS.md`), or fabricate ORCID/arXiv/Zenodo/Palomar/journal submissions.

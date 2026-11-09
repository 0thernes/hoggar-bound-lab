# Independent CI workflow audit

Date: 2026-11-09. Workflow: `.github/workflows/independent-verification.yml`.

The workflow has two required jobs on `ubuntu-24.04`, triggered by pushes, pull requests, and manual dispatch. It only requests `contents: read`; it does not publish or modify the repository. All external actions are pinned to the commit IDs resolved from their official release tags during this audit.

## Executable job

The job builds the C engine against the vendored classical `quantum_rng` implementation, installs Python 3.12 with NumPy 2.0.2, runs the independent tensor-matrix validator, regenerates the explorer data and checks its Git diff, and runs the Node explorer-model tests with Node 24. It archives the resulting logs and numerical report.

The numerical report is platform-dependent and is deliberately archived rather than compared byte-for-byte with a Windows-generated report. The explorer data is compared through Git, which respects the repository's `* text=auto eol=lf` normalization.

Local validation on Ubuntu 24.04 under WSL used GCC 13.3.0, Python 3.12.3, NumPy 2.0.2, and Node 22.22.2. It passed:

- 12 geometry families and 138,792 contexts compared against independent matrix multiplication;
- all 8 available witness files;
- 120 random sparse supports and deliberate sign-error controls;
- regeneration of all 5 explorer profiles, matching the existing data after line-ending normalization;
- 750 incremental-flip comparisons, greedy search, and witness export.

The only GCC warning was the existing unused `aux` variable in vendored QRNG code. Node 24 remains the configured CI runtime; the local Linux Node validation used the installed Node 22 runtime.

## Lean job

The job installs the pinned Lean environment through the official Lean action, retrieves only the required Mathlib import cache, builds `HoggarBound`, explicitly builds `HoggarBound.IndependentContexts` and `HoggarBound.IndependentWitness`, and runs `lake env lean IndependentVerification.lean`.

A final allowlist check consumes the printed axiom dependencies and fails on any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. It also fails if an expected report is missing or the audited list unexpectedly shrinks below 22 declarations. This check passed against the current verification output and rejected a deliberate mutation introducing `sorryAx`.

The finite kernel computation previously approached 10 GB on Windows. The Lean job has a 60-minute timeout, runs with `LEAN_NUM_THREADS=1`, builds the expensive witness after its dependencies, logs resources and peak memory, and conditionally adds swap until RAM plus swap reaches 14 GiB. It fails explicitly if there is insufficient disk for this headroom and the toolchain. No required check is skipped or marked `continue-on-error`.

GitHub currently documents 16 GB RAM for standard public Ubuntu runners and 8 GB for private runners; this explains the explicit resource handling. See the [official runner specifications](https://docs.github.com/en/actions/reference/runners/github-hosted-runners). Lean setup inputs and selective build behavior were checked against the [official Lean action](https://github.com/leanprover/lean-action) and the locally installed cache CLI. The independent proof's successful local build is documented separately in `results/lean-audit.md`.

## Workflow validation and limits

The workflow parsed successfully with a YAML parser and passed **actionlint 1.7.12** with exit code zero. Its axiom-checking Python block was exercised with both valid output and an intentionally invalid axiom report. The local command log is `results/independent-ci-local.log`; that log retains the temporary-environment setup attempts as well as successful validation.

This audit did not dispatch GitHub Actions or change remote state. A hosted run remains necessary to confirm GitHub runner installation, networking, cache availability, and peak Linux memory for the finite certificate. Missing witness files, a changed generated explorer dataset, a Lean failure, or an unexpected axiom will fail the workflow rather than silently weaken the checks.

# ADR 0001: Append-Only Frozen Proof Continuity

- **Date:** 2026-11-10 (formalized in ADR format 2026-11-24)
- **Status:** Accepted

## Context

`hoggar-bound-lab` evolved across multiple independently audited milestones (`v0.2.0-c3-certificate` at `d3811e3`, `v1.1.0` saturation at `87f08a0`, `v1.3.0` all-qubit C3 at `5dcea35`). Modifying earlier audited Lean files or `lakefile.toml` would invalidate the cryptographic hashes linking those historical Linux CI evidence bundles to the current tree.

## Decision

Treat all 21 proof/configuration files from `d3811e3` (including `LICENSE` and `NOTICE`), all 28 Lean/config files from `87f08a0` (including `lean/lakefile.toml`, `lean/HoggarBound.lean`, `lean/lean-toolchain`, `lean/lake-manifest.json`), and `CarrierFamily.lean` from `5dcea35` as **immutable frozen artifacts**, continuously verified by `scripts/publication_release_audit.py`. All subsequent formalizations (`v1.5.0`–`v1.9.0`) are added strictly as new self-contained modules under `lean/HoggarBound/`.

## Consequences

- **Positive:** Any reviewer can verify historical continuity byte-for-byte in seconds; new theorems never silently weaken previously checked statements.
- **Trade-off:** Frozen files cannot receive Lean 4.35.0 `module` headers or license rewrites without explicitly opening a breaking v2.0 continuity epoch approved by the owner.

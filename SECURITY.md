# Security Policy

## Scope

`hoggar-bound-lab` is a static mathematical-verification repository (Lean 4 proofs, Python/C11 verifiers, and static client-side HTML/JS demos). It operates no backend server, collects no personal data, and stores no credentials.

Security concerns in scope include:
- Supply-chain issues in pinned GitHub Actions workflows or Python/Lean dependencies.
- Memory-safety bugs or undefined behavior in `src/*.c` (audited with `-fsanitize=address,undefined` in CI).
- Accidental secret leakage in git history (audited with `gitleaks` in CI).
- Soundness / environment-injection vectors in Lean build or verification scripts (mitigated by sandboxed `lake comparator --paranoid` and [docs/threat-model.md](docs/threat-model.md)).

## Reporting a Vulnerability

Email `0_0@0thernes.art` with subject `[SECURITY] hoggar-bound-lab` and a minimal reproduction. Expected initial acknowledgement: within 7 days.

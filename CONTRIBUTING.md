# Contributing to Hoggar Bound Lab

This is a lean, one-person research repository operated under the [Build Standard for LLMs v1.1.0](docs/build-standard.md) and [AGENTS.md](AGENTS.md).

## How You Can Help

- **Independent replication (highest value):** Clone the repo, run the [REPLICATION.md](REPLICATION.md) commands on your own machine or container, and open an issue labeled `replication` with your OS, Lean/Python versions, commit SHA, and pass/fail log.
- **Adversarial statement-fidelity review:** Check whether any Lean declaration in [lean/HoggarBound/Challenge.lean](lean/HoggarBound/Challenge.lean) or [docs/statement-fidelity.md](docs/statement-fidelity.md) differs subtly from the paper or cited literature.
- **Finding reports:** Open an issue using `.github/ISSUE_TEMPLATE/` and tag it with one of the six finding classes (`bug`, `error`, `issue`, `problem`, `dilemma`, `conflict`).

## Maintainer Workflow

- Commits go straight to `main` (no branch protection or merge gates; CI is informational).
- Frozen research modules (`d3811e3`, `87f08a0`, `5dcea35`) must remain byte-identical so `scripts/publication_release_audit.py` continuity stays intact. Add new proofs or verifiers in new modules.
- **Licensing note:** The repository currently uses a verification-only [LICENSE](LICENSE). Before contributing code intended for redistribution or Mathlib upstreaming, note that re-licensing to Apache-2.0 / CC-BY-4.0 is an open item in [ROADMAP.md](ROADMAP.md).

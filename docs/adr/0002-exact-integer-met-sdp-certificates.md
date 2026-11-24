# ADR 0002: Pure-Integer MET-SDP & Dual Certificates Over Floating-Point Solvers

- **Date:** 2026-11-21 (formalized in ADR format 2026-11-24)
- **Status:** Accepted

## Context

Floating-point SDP/MILP solvers (CVXPY/SCS/CLARABEL/HiGHS) cannot serve as mathematical proofs because IEEE-754 rounding near integer thresholds can yield spurious bounds (the "floating-point illusion"). Both Proposition 16' (lower bound `330` on four-qubit C3) and Theorem 16'' (exact optima `368` and `344`) plus the 42-orbit $Q^-(7,2) \ge 315$ duals require airtight integer lower bounds.

## Decision

Use floating-point optimization strictly as an *untrusted heuristic oracle* to discover dual multipliers and triangle inequalities, then round/scale every dual certificate into exact integer arithmetic (`ℤ`) verified via fraction-free lower-triangular Cholesky / $L D L^\top$ + Gershgorin diagonal dominance (`C3ExactOptima.lean`, `AuditUpgrades.lean`, `scripts/c3_exact_optima_check.py`, `scripts/exact_degrees_n4_n5.py`). Explicitly audit and label any remaining float64 exploration scripts as `numerical_approximation` via `scripts/arithmetic_audit.py`.

## Consequences

- **Positive:** Zero floating-point trust base for every theorem and exact certificate; Lean 4's logical kernel verifies `368` and `344` directly using `decide +kernel` without `native_decide`.
- **Trade-off:** Integer certificate files (`C3ExactOptimaData.lean`, `data/c3_exact_optima_certs.json`, `data/q7minus_42_certs.json`) are larger than float arrays, requiring careful factoring to keep Lean compilation times under 3 minutes.

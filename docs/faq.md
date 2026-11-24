# Frequently Asked Questions (`hoggar-bound-lab`)

## What does this repository prove in Lean 4?

Lean 4.35.0 (`VerifyNewFormalizations.lean`: **110** newly audited declarations across 13 modules, plus retained baseline, saturation, 7-qubit, 4-qubit C3, and all-qubit C3 audits — strictly within `[propext, Classical.choice, Quot.sound]`) proves:

- **Theorem 1 & Corollary A:** The Pauli spectral floor and its asymptotic `1/2` `Filter.Tendsto` limit.
- **Theorem 2:** The quaternionic / Kramers spectral floor and elliptic quadrics $Q^-(2N-1,2)$ (`9`, `291`, `6501`).
- **Theorems 3–4 & Propositions 3, 8, 10:** Five-way saturation TFAE equivalence, $(2^N-1)|S| = \square$, QGT/Berry criteria, and two-character hyperplane sums.
- **Theorem 13b & finite degrees:** Exact degrees `75` ($N=4$), `480` ($N=5$), `2,016` ($N=6$), and `729,344` ($N=7$), plus the infinite non-closed contextual pure-CCZ determinant family `|Ψ_{3m}⟩` for every $m \ge 1$ directly from the state vector.
- **Theorem 16'':** Exact global binary completion minima `368` and `344` (**exact gap `24`**) for the four-qubit C3 cospectral pair via pure-integer MET-SDP triangle-cut duals.
- **Theorems 17, 19, 22 & Corollary 18:** Universal cubic-trace identity, cone lift, Clifford orbit transport, and Jonah's Conjecture E across all nine vertex cases for every $N \ge 4$ at the canonical Hermitian eigenvalue-multiset level.
- **Classical $N=4, 5$ ladders:** Symplectic transvection invariance, exact CSS witnesses (`315`, `1575`, `6975`), unconditional bounds $d(W(7,2)) \ge 1455$ and $d(Q^+(9,2)) \ge 6444$, Lemmas L1 & L4, and master reduction.
- **Non-Vacuity (`NonVacuity.lean`):** 10 explicit existential witness theorems proving no headline hypothesis bundle is vacuous.

## Is this peer reviewed?

**No.** This is a public, AI-assisted independent research preprint under human direction. Formal verification guarantees logical validity of the Lean statements under the three standard axioms; it is not journal peer review.

## Why are some Lean files frozen and untouched?

`scripts/publication_release_audit.py` enforces byte-identical continuity against the historical Linux CI commits `d3811e3` (21 C3 files + `LICENSE`/`NOTICE`), `87f08a0` (28 Lean/config files), and `5dcea35` (`CarrierFamily.lean`). See [ADR 0001](adr/0001-frozen-proof-continuity.md).

## Why does `lean/HoggarBound/Challenge.lean` contain `sorry`?

`Challenge.lean` is the isolated statement-only specification consumed by `lake comparator --config comparator.json --paranoid`. `lake comparator` checks that the sorry-free `Solution.lean` proves the definitionally identical types using only `[propext, Classical.choice, Quot.sound]` across all six bundled Lean 4.35.0 kernels. No proof module or `Solution.lean` ever uses `sorry`.

## Does this run on a real quantum computer?

**No.** All simulations and browser explorers run on classical CPUs/browsers. No quantum hardware experiment or quantum advantage is claimed.

## How do I independently verify everything in 5 minutes?

Follow [REPLICATION.md](../REPLICATION.md) or run `just reproduce` and `just verify-lean`.

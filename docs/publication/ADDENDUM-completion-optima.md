# Addendum: the binary completion minima of the two C3 carriers differ

**Folded into the combined paper, version 1.3.0 (10 November 2026), Section 8.5 (Corollary 16).** This file keeps
the result as first stated.

**Status.** Originally proposed addition for the next revision of the combined paper
([paper/unified-contextuality.md](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/paper/unified-contextuality.md)). Release `v1.2.0` and its frozen
artifacts are not changed by this file. The result was obtained on 9 November 2026 by the Claude
(Anthropic) line of work, under the direction of Alexander S. Donahue, 0thernes LLC, while Section 8 of
the combined paper was being re-derived independently. It is checked in exact integer and rational
arithmetic by [scripts/cospectral_pair.py](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/scripts/cospectral_pair.py) (30 checks). It is not
formalized in Lean and not peer reviewed.

## What the paper leaves open

Section 8.5 of the combined paper shows that the largest eigenvalues of the two completion matrices
differ by exactly 2, so that the continuous (spherical) relaxations of the two completion problems
differ by 32. It then says that this proves no difference between the exact binary completion minima,
and Section 12 lists those minima as not calculated.

## The statement

Notation as in Section 8 of the combined paper: $\mathcal Q = Q^+(7,2)$, section $H$ (71 points),
outside points $O$ (64 points), carriers $\sigma_0$ and $\sigma_1$, and for a completion
$`y \in \{-1,+1\}^O`$ the number $`F(\sigma, y) = 560 - \tfrac14\, y^{\mathsf T} \Lambda_\sigma\, y`$ of violated
outside lines (equation C1).

**Corollary 16 (the binary completion minima differ).**

1. Every completion of $\sigma_0$ violates at least 347 of the 1120 outside lines.
2. Every completion of $\sigma_1$ violates at least 315 of them.
3. Some completion of $\sigma_1$ violates exactly 344.

Hence

```math
\min_y F(\sigma_1, y) \;\le\; 344 \;<\; 347 \;\le\; \min_y F(\sigma_0, y) .
```

The two carriers have the same carrier spectrum and the same section score (132 of 455 section
contexts violated), and their completion problems have different exact optima.

*Proof.* By equation (C11), $`F(\sigma, y) \ge 560 - 16\, \lambda_{\max}(\Lambda_\sigma)`$ for every completion,
because $y^{\mathsf T} y = 64$. By Corollary 15 the two largest eigenvalues are $(\rho - 1)/2$ and
$(\rho + 3)/2$, with $\rho$ the largest root of $g(t) = t^3 - 25t^2 - 133t + 1621$, so the two bounds are
$568 - 8\rho$ and $536 - 8\rho$. The polynomial $g$ is increasing from 25 on and $\rho$ is its only
root there. Since

```math
g\!\left(\tfrac{221}{8}\right) = -\tfrac{25539}{512} \;<\; 0 \;<\; \tfrac{3067}{64} = g\!\left(\tfrac{111}{4}\right),
```

one has $221/8 \lt \rho \lt 111/4$, hence $346 \lt 568 - 8\rho \lt 347$ and $314 \lt 536 - 8\rho \lt 315$. The
number of violated lines is an integer, which gives items 1 and 2. For item 3, let $y$ be $-1$ at the
30 outside labels listed below and $+1$ at the other 34. Counting the 1120 outside lines one by one gives
344 violated lines; equivalently $`y^{\mathsf T} \Lambda_{\sigma_1} y = 864`$. $\qquad\blacksquare$

## Witnesses

Numeric labels $a + 16c$, as in Table 3 of the combined paper.

Completion of $\sigma_1$ with 344 violated outside lines (476 violated contexts of $\mathcal Q$ in all),
value $-1$ at 30 labels:

```text
26 41 59 63 72 88 90 104 105 120 123 153 155 159 170 171 175 204 205 206 217 219 220 222 234 235 236 237 252 255
```

Best completion found for $\sigma_0$, with 368 violated outside lines (500 in all), value $-1$ at 38
labels:

```text
8 12 13 14 24 26 28 30 40 41 44 45 56 59 60 63 90 93 105 110 123 125 126 153 155 157 159 170 171 174 175 189 190 217 219 234 235 255
```

Both were found by simulated annealing (6000 restarts each). They are upper bounds, not proved optimal:

| carrier | least number of violated outside lines |
|---|---|
| $\sigma_0$ | between 347 and 368 |
| $\sigma_1$ | between 315 and 344 |

## How to check

```bash
python scripts/cospectral_pair.py
```

The last line must read `30 of 30 checks passed`. The script rebuilds the 135 points, the 1575
contexts and their signs from the definition of the Pauli matrices (two routes for the signs), the two
carrier polynomials, the block polynomials, the identity between each completion matrix and the map
$`M \mapsto \tfrac12 (CM + MD)`$, the degree-64 characteristic polynomials of both completion matrices, the
enclosure of $\rho$, and both witnesses above by direct count. It shares no code with the programs of
the C3 study. The record is [results/cospectral_pair.json](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/results/cospectral_pair.json)
(`completion_witnesses`, `completion_minimum_intervals`); the log is
[results/cospectral_pair.log](https://github.com/0thernes/hoggar-bound-lab/blob/v1.4.0/results/cospectral_pair.log). The check is a stage of
`scripts/run_all.sh` and a step of the workflow *Saturated configurations*.

## Scope

* One finite instance, four qubits. Nothing is said about Conjecture E in other dimensions.
* The two minima are separated, not determined: only the intervals in the table are known.
* Exact arithmetic and explicit witnesses; no Lean statement. The Lean-checked part of Section 8 is
  unchanged: equal carrier spectra, different completion spectra, cubic traces 14976 and 15360.
* Novelty is claimed only to the extent of a bounded search: on 9 and 10 November 2026 the source of the
  conjecture ([doi:10.5281/zenodo.23524332](https://doi.org/10.5281/zenodo.23524332)) had the single
  version 0.5, which reports case C3 as open for four or more qubits, and searches of Zenodo for the
  conjecture and for the numbers 14976 and 15360 returned no other record.

## Text proposed for the next revision of the combined paper

* Abstract and Section 1.1: replace the statement that the gaps "are not statements about exact binary
  completion optima" by: the exact binary completion minima also differ, since every completion of one
  carrier violates at least 347 outside lines while the other carrier has a completion violating 344.
* Section 8.5: after equation (C11), add Corollary 16 with the proof above, and keep the sentence that
  Corollary 15 alone proves no difference.
* Section 9.2 and the claim map: list Corollary 16 as exact and executable evidence outside the Lean
  audit.
* Section 11.2: cite `scripts/cospectral_pair.py` as a further independent reconstruction.
* Section 12: replace "The exact binary completion minima of the two witnesses are not calculated here"
  by the two intervals.
* Appendix B: add the two label lists.

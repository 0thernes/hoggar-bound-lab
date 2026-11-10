# Hoggar Bound Lab

A machine-checked lower bound on how badly any noncontextual hidden-variable model must fail for
$N$-qubit Pauli observables, with an independent reproduction of the known values and a running
demonstration on the Tsotchke stack (Moonlab, quantum_geometric_tensor, quantum_rng, Eshkol).

**Paper:** [paper/spectral-floor.md](paper/spectral-floor.md) ([PDF](paper/spectral-floor.pdf), [HTML](https://0thernes.github.io/hoggar-bound-lab/))
&nbsp;·&nbsp; **Proofs:** [lean/HoggarBound](lean/HoggarBound)
&nbsp;·&nbsp; **Independent review:** [INDEPENDENT-REVIEW.md](INDEPENDENT-REVIEW.md)

Status: research preprint, 9 November 2026. Not peer reviewed. AI-generated under human direction.

**New finite result:** [Cospectral Pauli carriers with different completion spectra](paper/c3-spectral-counterexample.md)
([PDF](paper/c3-spectral-counterexample.pdf), [working exact-certificate demo](https://0thernes.github.io/hoggar-bound-lab/c3-lab/)).
Two explicit four-qubit sign carriers have the same characteristic polynomial, while their completion
cubic traces are 14976 and 15360. This establishes the four-qubit C3 instance left open in
[Jonah's Conjecture E, v0.5](https://zenodo.org/records/23524332).
The [Lean spectral theorem](lean/HoggarBound/C3Spectra.lean) and [42-declaration axiom audit](results/frontier-c3-lean-audit.md)
verify the Pauli-model connection, carrier cospectrality and completion noncospectrality. Independent integer
checks and an Eshkol execution record accompany the paper. This finite result is separate from the previously known spectral floor below;
it does not settle the conjecture in every dimension or establish historical priority.

## The statement

Take $N$ qubits, $D = 2^N$. Give every Pauli observable in a set $S$ a value $+1$ or $-1$. A *context*
is three mutually commuting observables of $S$ whose product is $\pm I$; quantum mechanics fixes the
sign of the product of their values. Then, for every $S$ and every assignment,

```math
\#\text{satisfied} - \#\text{violated} \;\le\; \frac{(D-2)\,|S|^{3/2}}{6\sqrt{D-1}} .
```

For all $4^N - 1$ observables this means at least the fraction $\tfrac12 - \sqrt{D+1}/(D+2)$ of the
contexts is violated: 63 of 315 for three qubits (exact), at least 1451 of 5355 for four, at least
28786 of 86955 for five, and the fraction tends to one half.

## Whose result this is

The inequality was first posted by **B. W. Jonah** on 21 October 2026 as the *spectral floor*
([doi:10.5281/zenodo.23538829](https://doi.org/10.5281/zenodo.23538829)); the exact four- and
five-qubit values 315, 1575 and 6975 are his computer-assisted results
([doi:10.5281/zenodo.23510634](https://doi.org/10.5281/zenodo.23510634)); the value 315 for the
four-qubit hyperbolic quadric is due to Li, Gupta and Ganesh (arXiv:2610.26465); the scalar inequality
is Okumura's lemma (1974). We found the bound independently on 9 November 2026 and learned of the
earlier notes during our own literature audit the same day.

What this repository adds:

* a complete **Lean 4 proof** for every $N \ge 1$ and arbitrary sets of observables, about the explicit
  complex Pauli matrices, with no axioms beyond `propext`, `Classical.choice`, `Quot.sound`;
* **formally verified corollaries**, including the first kernel-checked proof we know of that the
  five-qubit hyperbolic quadric has degree greater than 4743 (at least 6426);
* an **independent reproduction** of the best known assignments for two to five qubits, of the
  geometry of their violated contexts, and of the three cases where the bound is attained;
* the **state-independent contextuality experiment** run end to end on a simulator.

## Layout

| path | what |
|---|---|
| `lean/HoggarBound/` | the Lean 4 development (`Moment`, `Pauli`, `Bound`, `Counting`, `Corollaries`, `Quadric`; plus the independently written `IndependentContexts`, `IndependentWitness`) |
| `src/hoggar.c` | engine: geometry, exact integer bounds, verification, annealing search, falsification harness |
| `src/moonlab_experiment.mjs` | the experiment on Moonlab (WebAssembly) |
| `src/qgt_hoggar.c` | quantum geometric tensor of the Hoggar state with the QGTL kernels |
| `src/eshkol/hoggar.esk` | independent re-implementation and automatic-differentiation checks in Eshkol |
| `scripts/` | `build.sh`, `run_all.sh`, `analysis.py`, `ladder.py`, `run_falsify.sh`, `build_paper.py` |
| `data/witness/` | assignments (hex masks) for every configuration up to five qubits |
| `results/` | logs and JSON written by the runs |
| `third_party/` | vendored Moonlab engine, quantum_rng and one QGTL source file, with licences and provenance |
| `independent-review/`, `tests/`, `results/*audit*` | the independent companion review |

## Reproduce

```bash
bash scripts/build.sh
```

```bash
bash scripts/run_all.sh
```

```bash
cd lean && lake exe cache get && lake build
```

`run_all.sh` needs gcc, Python 3 with NumPy and Matplotlib, and Node; Eshkol is optional. It prints one
line per stage and ends with `ALL STAGES PASSED`; the last complete run is kept in
[results/run_all.log](results/run_all.log) and [results/falsify.log](results/falsify.log). The Lean
build needs [elan](https://github.com/leanprover/elan); it downloads Lean 4.35.0 and the Mathlib cache.

## What is and is not claimed

* The Lean theorems are exactly what their statements say; comments are not theorems.
* Lower bounds are proved. Upper bounds are explicit assignments that anyone can recount.
  Optimality of the four- and five-qubit assignments is not proved here.
* The quaternionic refinement for elliptic quadrics is proved on paper and tested numerically only.
* Moonlab is a classical simulator; quantum_rng is a classical "quantum-inspired" generator; only the
  `diffgeo_*` kernels of QGTL are used. Nothing here is a measurement on quantum hardware.
* No priority is claimed for the bound, for its saturation by Hoggar states, or for the exact values.

## Licence

Copyright © 2026 0thernes LLC. See [LICENSE](LICENSE). Third-party components keep their MIT licences
([NOTICE](NOTICE)).

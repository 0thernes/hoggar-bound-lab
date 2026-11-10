# The Lean 4 development

Lean 4.35.0 with Mathlib v4.35.0 (pinned in `lean-toolchain` and `lake-manifest.json`). Every theorem
listed here depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. There is no
`sorry`, no `native_decide` and no added axiom anywhere in these modules.

## What is proved

All statements are about explicit complex matrices: `pauli u` is the `2^N × 2^N` matrix
`i^{|a∧c|} X^a Z^c` for `u = (a, c)`, defined entry by entry; its product rule, its commutation rule and
the sign of a context are theorems, not definitions.

### The bound, for every number of qubits

```lean
theorem hoggar_bound (hN : 1 ≤ N) (S : Finset (Pt N)) (h0 : (0 : Pt N) ∉ S) (f : Pt N → ℝ)
    (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ N - 1) * beta6 S f
      ≤ ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card)
```

`beta6 S f` is six times (satisfied − violated contexts): a sum over ordered commuting pairs of `S` whose
product lies in `S`. `S` is an arbitrary finite set of non-identity Pauli observables.

### Corollaries for the classical families

| theorem | statement |
|---|---|
| `full_space_fraction` | for every N ≥ 1, the violated fraction of the full N-qubit configuration is at least 1/2 − √(2^N+1)/(2^N+2) |
| `three_qubit_contexts` | every assignment of the 63 three-qubit observables violates at least 63 contexts |
| `four_qubit_contexts` | every assignment of the 255 four-qubit observables violates at least 1451 contexts |
| `five_qubit_contexts` | every assignment of the 1023 five-qubit observables violates at least 28786 contexts |
| `four_qubit_hyperbolic_contexts` | at least 315 contexts for the 135 real four-qubit observables |
| `five_qubit_hyperbolic_contexts` | at least 6426 contexts for the 527 real five-qubit observables |

### Exact contextuality degrees

Each of these is a two-sided statement: every assignment violates at least `d` contexts, **and** some
assignment violates exactly `d`.

| theorem | configuration (given by a bit mask) | observables | contexts | degree |
|---|---|---|---|---|
| `pivot_degree`, `pivot_contexts` | four qubits, the pivot configuration | 135 | 1095 | 75 |
| `cieslinski5_degree`, `cieslinski5_contexts` | five qubits, support of the state of arXiv:2610.07172 | 496 | 10880 | 480 |
| `phase5_degree`, `phase5_contexts` | five qubits, support of `CCZ(0,1,4) CCZ(0,2,3) CS(0,1) CS(1,3) CS(2,4) \|+++++⟩` | 496 | 10880 | 480 |
| `quadric_degree` | four qubits, the hyperbolic quadric | 135 | 1575 | 315 |
| `hoggar_degree` | three qubits, all observables | 63 | 315 | 63 |
| `ccz_degree`, `lly_degree` | three and two qubits | 28, 12 | 56, 8 | 0 |

The seven-qubit degree 729 344 of the paper is **not** one of these theorems: its lower bound is
`hoggar_bound` with `S.card = 8128`, and its counts are made by programs.

## Modules

| module | content |
|---|---|
| `HoggarBound/Moment.lean` | the scalar inequality `sum_cube_le`; traces of powers of a Hermitian matrix as power sums of eigenvalues |
| `HoggarBound/Pauli.lean` | points, Pauli matrices, their products, traces and commutation |
| `HoggarBound/Bound.lean` | contexts as flags, the operator `A = Σ f(v) P_v`, `tr A³`, **`hoggar_bound`** |
| `HoggarBound/Counting.lean` | violated flags and contexts; the flag count of the full space for every N |
| `HoggarBound/Corollaries.lean` | the full-space corollaries |
| `HoggarBound/Quadric.lean` | the real quadric and its counts for every N, by character sums |
| `HoggarBound/MaskConfig.lean` | configurations and assignments as bit masks; `card_flags_cfg`, `card_violated_cfg`; `degree_of_certificate` |
| `HoggarBound/FlatData.lean`, `PhaseData.lean` | generated: the masks |
| `HoggarBound/SaturatedFive.lean`, `SaturatedPhaseFive.lean` | generated: the five-qubit counts, 16 kernel-evaluated blocks per sum |
| `HoggarBound/Saturated.lean` | the two-, three- and four-qubit counts and the exact-degree theorems |
| `HoggarBound/IndependentContexts.lean`, `IndependentWitness.lean` | written by the independent companion review |
| `HoggarBound/C3*.lean`, `Stability.lean` | the companion C3 note (separate work) |

The root module `HoggarBound.lean` imports the first six. The other modules are separate build targets,
so that the default build stays short.

## Build and audit

```bash
lake exe cache get
```

```bash
lake build
```

```bash
lake build HoggarBound.Saturated HoggarBound.SaturatedPhaseFive
```

```bash
lake env lean SaturatedVerification.lean
```

The last command prints the axioms of the fourteen declarations of the exact-degree modules; the
expected output is in `../results/lean-saturated-axioms.log`. `IndependentVerification.lean` does the
same for the core modules (expected output: `../results/lean-axioms.log`).

Resources: the default build takes a few minutes after the Mathlib cache is fetched. Each of the two
five-qubit modules takes ten to twenty minutes and under 5 GB of memory; `Saturated.lean` takes one to
two minutes.

## How the finite counts are checked

A configuration on N qubits is a number `mask < 2^(4^N)`: bit `a + 2^N c` says whether the observable
`(a, c)` belongs to it. `MaskConfig.lean` proves, for every N and every mask, that the number of flags of
the configuration, and the number of flags violated by an assignment that is itself given by a mask,
equal double sums over codes of Boolean expressions made of bit tests, exclusive or and addition. Those
sums are closed terms of type `ℕ`, and `decide +kernel` has the Lean kernel evaluate them. For five
qubits each sum has 2^20 terms; it is split into 16 blocks of 64 rows, one theorem per block, and the
blocks are added by `loop_blocks`. `degree_of_certificate` turns three evaluated numbers (observables,
flags, flags violated by the witness) and `hoggar_bound` into the two-sided statement.

The masks are generated by `scripts/flat_states.py --lean` and `scripts/phase_states.py --lean`, which
also verify in exact arithmetic that they are the supports and sign patterns of the states named in the
paper. That link is not part of the Lean statements, and the statements do not need it.

## Continuous integration

`.github/workflows/saturated-configurations.yml` builds the exact-degree modules, prints the axioms and
fails if any declaration uses an axiom outside the allowlist or if a source file contains `sorry`,
`native_decide` or an `axiom` declaration. `.github/workflows/independent-verification.yml` does the same
for the core proof and the companion modules.

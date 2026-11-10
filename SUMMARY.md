# Summary in plain language

Repository version 1.4.0, 10 November 2026. Research preprint, not peer reviewed. The combined study brings
together the Claude/Anthropic spectral-floor work and the OpenAI Codex C3/independent-verification work
under the direction of Alexander S. Donahue, 0thernes LLC. Version 1.3.0 adds Claude/Anthropic results that
answer Jonah's Conjecture E: in all nine vertex cases of his classification, a section's spectrum does
not determine the completion spectrum, for every number of qubits from four on. Version 1.4.0 makes
that proof self-contained: two lemmas write out, with credit, the arguments of Jonah's preprint that
it had only cited, and a new program checks them exactly.

The [unified paper](paper/unified-contextuality.md) asks two connected questions: what lower bounds can
spectral information certify, and which completion information can a section's spectrum fail to retain?
The exact C3 example answers the second question without invalidating the bound. The
[source-paper map](publication/PAPER-MAP.md) records the earlier artifacts and how they relate.

## The question

Quantum mechanics predicts the results of measurements, but it does not say that the measured quantities
had those values beforehand. A *noncontextual hidden-variable model* is the opposite idea: every
observable secretly has a definite value, +1 or −1, that does not depend on what else is measured with
it. For a handful of qubits this idea can be tested against simple arithmetic. Take three observables
that can be measured together and whose product is fixed by quantum mechanics (a *context*). The three
hidden values would have to multiply to that fixed sign. Since the theorem of Kochen and Specker (1967),
and for qubits since the examples of Mermin and Peres (1990), it is known that no assignment of hidden
values can do this for all contexts at once.

The *contextuality degree* asks how badly the idea fails: what is the smallest number of contexts that
any assignment of hidden values gets wrong? It is a number, it is hard to compute, and until recently it
was known only for small cases.

## What is in this repository

1. **A proof, checked by a computer, of a general lower bound** on that number, for any number of qubits
   and any set of observables. The inequality itself was first posted by B. W. Jonah in October 2026; we
   found it independently and then learned of his notes. What is new here is the formal proof in Lean 4:
   the proof checker verifies every step, and the statement is about the actual matrices.

2. **New cases where the bound is exactly right.** For a nonempty support, the bound is attained precisely when a quantum state
   exists whose measurement averages are "flat": the same size on a set of observables and zero on all
   others. We establish exact degrees for configurations and give circuit descriptions, including a
   five-qubit configuration Clifford-equivalent to the support of Cieśliński's previously reported state:


   | qubits | observables | contexts | fewest contexts any hidden-variable model gets wrong |
   |---|---|---|---|
   | 4 | 135 | 1 095 | 75 |
   | 5 | 496 | 10 880 | 480 |
   | 7 | 8 128 | 2 824 192 | 729 344 |

   For four, five and seven qubits the degrees of the specified supports are proved in Lean, including
   the counting (for seven qubits since version 1.3.0, with sums of 2^28 terms evaluated by the Lean
   kernel); the state and circuit identifications have separate evidence.

3. **A classification.** For one natural family of states (those made from a standard set of gates
   called T, controlled-S and CCZ) we checked every possibility on up to five qubits, more than 33 million
   of them. Within the subfamily with nonzero associated trilinear form, there is no flat state on four
   qubits and essentially one on five. The five-qubit
   one turns out to explain a state that another author had found numerically a month earlier. On seven
   qubits we checked about fifteen billion possibilities in the family we could cover, and found
   essentially one.

4. **A running demonstration.** The states are prepared as circuits on Moonlab, a simulator from the
   Tsotchke project, and every context is measured: all 2 824 192 of them for seven qubits. The simulated
   quantum results agree with the quantum prediction every time, which no hidden-variable model can do.
   This is a simulation on an ordinary computer, not an experiment on quantum hardware.

## What "proved" means here

* *Proved in Lean* means the Lean 4 proof checker accepted the statement, using only its three standard
  axioms. Anyone can re-run it; the continuous-integration runs on GitHub do so.
* *Checked in exact arithmetic* means a program counted with whole numbers, without rounding.
  Independent second and third implementations corroborate the checks identified in the evidence records;
  not every enumeration has three implementations.
* *Proved on paper* means the argument is written in the paper and has not been formalized.
* *Evidence, not proof* is said where it applies, for example for uniqueness beyond the families that
  were enumerated completely.

## What this is not

* Not peer reviewed. No specialist has refereed it.
* Not a claim of priority for the bound, for the three classical cases where it was known to be exact,
  or for the exact values of the classical families; those belong to the authors cited in the paper.
* Not an experiment, and not a claim of any quantum computational advantage.
* The novelty of the new cases rests on a bounded literature search made on 9 November 2026.

## Check it yourself

```bash
bash scripts/build.sh
```

```bash
bash scripts/run_all.sh
```

```bash
cd lean && lake exe cache get && lake build && lake build HoggarBound.Saturated HoggarBound.SaturatedPhaseFive HoggarBound.MaskRows HoggarBound.SaturatedPhaseSeven && lake env lean HoggarBound/CarrierFamily.lean
```

See [INDEX.md](INDEX.md) for where each claim is proved and tested, and [GLOSSARY.md](GLOSSARY.md) for
the terms.

## A separate four-qubit spectral result

The C3 companion gives two explicit sign assignments with identical carrier spectra but different
completion spectra. Their exact completion cubic traces are 14976 and 15360. This establishes the
four-qubit C3 instance left open in the cited prior work. The 42-declaration Lean audit includes the
connection to the original Pauli model and eigenvalue multiplicities. The paper's largest-eigenvalue
gap of 2 and continuous-relaxation gap of 32 have separate algebraic proofs and are outside that Lean audit.

Read the [C3 summary](docs/RESEARCH-SUMMARY.md), try the [working verifier](https://0thernes.github.io/hoggar-bound-lab/c3-lab/),
or follow the [claim-to-proof register](docs/CLAIMS.md). This study is distinct from the spectral floor
and saturation configurations described above; its original research artifact is fixed at
[v0.2.0-c3-certificate](https://github.com/0thernes/hoggar-bound-lab/releases/tag/v0.2.0-c3-certificate).

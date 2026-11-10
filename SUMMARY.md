# Summary in plain language

Version 1.1, 9 November 2026. Research preprint, not peer reviewed. Produced with an AI research system
(Claude, Anthropic) under the direction of Alexander S. Donahue, 0thernes LLC.

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

2. **New cases where the bound is exactly right.** The bound is attained precisely when a quantum state
   exists whose measurement averages are "flat": the same size on a set of observables and zero on all
   others. We found such states and sets that nobody had described (to our knowledge, after a limited
   search), and for them the contextuality degree is now known exactly:

   | qubits | observables | contexts | fewest contexts any hidden-variable model gets wrong |
   |---|---|---|---|
   | 4 | 135 | 1 095 | 75 |
   | 5 | 496 | 10 880 | 480 |
   | 7 | 8 128 | 2 824 192 | 729 344 |

   For four and five qubits the whole statement is proved in Lean, including the counting. For seven
   qubits the inequality is the Lean theorem and the counts are made by three separate programs.

3. **A classification.** For one natural family of states (those made from a standard set of gates
   called T, controlled-S and CCZ) we checked every possibility on up to five qubits, more than 33 million
   of them: there is no flat state of this kind on four qubits and essentially one on five. The five-qubit
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
* *Checked in exact arithmetic* means a program counted with whole numbers, no rounding, and a second
  and third program written separately got the same counts.
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
cd lean && lake exe cache get && lake build && lake build HoggarBound.Saturated HoggarBound.SaturatedPhaseFive
```

See [INDEX.md](INDEX.md) for where each claim is proved and tested, and [GLOSSARY.md](GLOSSARY.md) for
the terms.

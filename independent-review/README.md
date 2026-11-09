# Independent verification companion

This directory contains a working, dependency-free browser explorer of the lab's
checked Pauli-contextuality configurations. It was developed alongside the main
experiment by a separate review effort. The scalar inequality, spectral-floor
formula, and several finite optima have verified prior art; priority for the
general Lean formalization has not been established. Read the
[critical literature audit](../results/literature-audit.md).

Open `index.html` directly, or serve the repository with:

```sh
python -m http.server 8769 --bind 127.0.0.1
```

Then visit `http://127.0.0.1:8769/independent-review/`. The five profiles provide
stored witnesses for the full three-, four-, and five-qubit spaces and the real
four- and five-qubit quadrics. Flip observable signs, generate a random assignment,
apply strictly improving single flips, restore the witness, or export a text
assignment for the C verifier. A local search minimum is not a global proof.
Counters use every context; the graph draws at most 350 violated contexts.

## Mathematical and implementation evidence

- [Research note](../paper/independent-research-note.md): definitions, derivation,
  finite consequences, scientific context, and limitations.
- [Formal audit](../results/lean-audit.md): exact theorem statements and axioms.
- [Independent matrix checks](../results/independent_validation.json): 138,792
  contexts across 12 geometries, eight witness recounts, and 120 sparse supports.
- [Stack audit](../results/stack-independent-audit.md): separately replayed
  Moonlab simulation, QGTL tensor kernels, seeded software RNG, and Eshkol arithmetic.

The exact three-qubit theorem in `lean/IndependentVerification.lean` proves an
explicit assignment attains 63 violations, every assignment violates at least
63, and the full configuration contains 315 unordered contexts. The certificate
uses kernel reduction and the usual Lean axioms; no `sorry` or native-code
decision axiom is used. The five-qubit real theorem proves at least 6426, and the
stored witness gives at most 6975. This artifact does not prove that latter
upper bound optimal; an earlier preprint makes a separate stronger claim.

## Reproduce the independent checks

Use ordinary Python (not `python -O`), NumPy, Node.js, and GCC. From the repository
root on Windows:

```powershell
gcc -O2 -std=gnu11 -o build/hoggar.exe src/hoggar.c third_party/quantum_rng/src/quantum_rng/quantum_rng.c -Ithird_party/quantum_rng/src/quantum_rng -lm
python tests/independent_validation.py build/hoggar.exe
python scripts/independent_demo_data.py
node tests/independent_demo_test.cjs
python scripts/stack_audit.py
```

Create `build` if necessary. On Linux use `build/hoggar` and pass that path to the
Python checker. The stack script additionally needs the documented local Eshkol
installation; its report records the exact executable hash. See the CI workflow
for the portable core checks. To check all formal additions, from `lean`:

```sh
lake build
lake build HoggarBound.IndependentContexts HoggarBound.IndependentWitness
lake env lean IndependentVerification.lean
```

The root Lean library does not import the isolated independent modules, so all
three commands matter. The source hash manifest binds the audit to the inspected
files. Browser model tests compare 750 incremental flips with full recounts and
check descent and witness export across all five profiles. The explorer was also
operated in the browser: randomization, local improvement, profile switching, and
witness restoration produced the expected visible state.

## Interpretation

Moonlab is a classical state-vector simulator. The RNG is a classical
quantum-inspired mixer. The QGTL validation covers two specified differential
geometry kernels, and Eshkol supplies independent arithmetic checks. This is a
theoretical and computational research artifact, not a physical quantum
experiment, a demonstrated speedup, a statistical meta-analysis, or evidence of
worldwide scientific recognition.

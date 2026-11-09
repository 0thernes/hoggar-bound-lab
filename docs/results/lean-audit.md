# Independent Lean audit and exact three-qubit certificate

Audit date: 2026-11-09. Scope: the six original `HoggarBound` modules and the three isolated additions described below. This audit did not edit the original theorem files, root imports, or package manifest.

## Result

The original general lower-bound proof and all five advertised numerical corollaries checked successfully from source. The main statements are substantive theorems about explicit complex Pauli matrices and finite sets of observables; they do not assume the desired contextuality inequality as a hypothesis.

The independent additions also establish an exact optimum for the three-qubit model: **there are 315 unordered contexts, every sign assignment violates at least 63, and an explicit sign assignment violates exactly 63**. The upper-bound witness is checked by Lean's kernel using exact integer arithmetic. The proof uses neither floating-point arithmetic nor a native-code decision axiom.

All 22 declarations printed by `lean/IndependentVerification.lean`, including the finite certificate and exact optimum, report precisely:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean/Mathlib foundations, not assumptions specific to contextuality. The axiom output contains no `sorryAx`, no native decision axiom, and no new project axiom. A source scan of the audited files found no `sorry`, `axiom`, `unsafe`, `implemented_by`, or `opaque` declarations.

The three-qubit optimum is an already known mathematical result. Its successful independent formal reproduction is a verification result, not a claim of historical discovery.

## Exact checked scope

All names in this table are in namespace `HoggarBound`.

| Declaration | Checked content |
|---|---|
| `sum_cube_le` | General finite real third-moment inequality under zero-sum and prescribed-square-sum hypotheses. |
| `trace_cube_le` | Corresponding inequality for arbitrary finite traceless Hermitian complex matrices. |
| `context_product`, `pauli_comm` | Product phases and commutation for explicitly defined binary-labelled Pauli matrices, for arbitrary qubit count. |
| `trace_opA_cube` | Exact bridge from the cubic matrix trace to the signed sum over commuting ordered flags. |
| `hoggar_bound` | General bound for every `N >= 1`, every finite observable set excluding identity, and every assignment taking values `+1` or `-1` on that set. |
| `card_flags_all` | Exact full-space flag count for arbitrary `N`. |
| `full_space_fraction` | Every assignment violates at least the fraction `1/2 - sqrt(2^N + 1)/(2^N + 2)` of full-space flags. |
| `three_qubit_contexts` | At least 63 violated unordered full-space contexts. |
| `four_qubit_contexts` | At least 1451 violated unordered full-space contexts. |
| `five_qubit_contexts` | At least 28786 violated unordered full-space contexts. |
| `card_flags_real` | Exact flag-count identity for the even-Y (hyperbolic/real) observable set. |
| `four_qubit_hyperbolic_contexts` | At least 315 violated unordered real four-qubit contexts. |
| `five_qubit_hyperbolic_contexts` | At least 6426 violated unordered real five-qubit contexts. |
| `five_qubit_hyperbolic_not_one_fifth` | No valid real five-qubit assignment has exactly 4743 violated contexts. |
| `five_qubit_hyperbolic_no_assignment_below_6426` | There is no valid real five-qubit assignment with fewer than 6426 violations. |
| `hoggar_flags_certificate` | Exact integer enumeration: the explicit three-qubit Hoggar sign pattern violates 378 ordered flags. |
| `card_violated_eq_six` | Exactly six violated ordered flags per violated unordered context, for any observable set excluding identity. |
| `hoggar_contexts_exact` | The explicit sign pattern violates exactly 63 unordered contexts in the same complex Pauli model. |
| `three_qubit_total_contexts` | Exactly 315 unordered contexts in the three-qubit full space. |
| `three_qubit_exact_minimum` | A single theorem combining an explicit assignment attaining 63 with the universal lower bound of 63. |

## Model and argument audit

A point is a pair of binary vectors `(a,c)`. The matrix `pauli (a,c)` is `i^(#Y) X^a Z^c`, with matrix indices themselves binary vectors. The identity is the zero point. The symplectic form determines which pairs commute, and the product phase is proved from matrix multiplication. This fixes the sign convention explicitly rather than importing a table of context signs.

An ordered flag is a commuting pair `(u,v)` for which `u`, `v`, and `u+v` lie in the selected set. Excluding the identity guarantees that the three points are distinct. `lineOf` turns a flag into the unordered three-element set. A violation compares the assignment product against the real part of the explicitly proved Pauli product phase.

The analytic proof first bounds every eigenvalue using the zero-sum and square-sum constraints. It then sums the nonpositive polynomial `(x-a)((n-1)x+a)^2`. The spectral theorem converts this real inequality to the matrix inequality. Orthogonality of the Pauli matrices supplies the quadratic trace, and cancellation of anticommuting terms supplies the cubic trace. The resulting argument applies to all finite observable sets in the stated model, not just the numerically enumerated examples.

The original counting proof used the inequality `#violated flags <= 6 * #violated contexts`, which is sufficient for all published finite lower bounds. The independent `IndependentContexts.lean` strengthens this to equality. It proves invariance under cyclic rotation and swapping of a commuting triple, identifies each fiber of `lineOf` with all ordered distinct pairs in that three-element set, and counts the fiber as six.

The independent finite assignment is specified without an external witness file:

```text
f(a,c) = +1 if a=0 or c=0 or ycount(a,c)>=2;
         -1 otherwise.
```

`IndependentWitness.lean` defines a computable integer context sign using powers of `i` modulo four, proves that its real cast equals the original complex-matrix context sign, and checks the 378-flag count with `decide +kernel`. Thus the finite checker and the general lower bound are connected to the same formal model. The file comments identify the familiar Hoggar fiducial interpretation; the checked counting theorem does not depend on that interpretation or on a floating-point state-vector calculation.

## Reproduction

Toolchain actually used:

- Lean 4.35.0, Windows x86_64 GNU release, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Mathlib v4.35.0, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, matching `lake-manifest.json`.
- The Mathlib checkout was clean at audit time.

On this machine `H:` already maps to the repository directory, avoiding shell/build problems with the brackets in the physical path. No drive mapping was changed by this audit. From `H:\lean`, with Elan's `bin` directory on `PATH`:

```powershell
lake build
lake build HoggarBound.IndependentContexts HoggarBound.IndependentWitness
lake env lean IndependentVerification.lean
```

On another machine, run the same commands from the repository's `lean` directory after installing the pinned Lean toolchain and retrieving the Mathlib cache as usual. The isolated additions are deliberately not imported by the original root module, because another task was developing the same repository concurrently; the explicit second build command is necessary.

The original six sources were also freshly checked one by one, rather than relying only on Lake's cached replay:

```powershell
foreach ($name in @('Moment','Pauli','Bound','Counting','Corollaries','Quadric')) {
  lake env lean "HoggarBound\$name.lean"
  if ($LASTEXITCODE -ne 0) { throw "Source check failed: $name" }
}
```

Every original source check exited zero. The finite certificate is intentionally pure kernel computation and can require a few minutes and substantial memory; one observed run approached 10 GB. This resource cost affects reproduction convenience, not the statement or axiom dependencies.

Evidence files:

- `results/lean-source-recheck.log`: six fresh original source checks, each exit code zero.
- `results/lean-axioms.log`: original proof and initial explicit-corollary axiom check.
- `results/lean-witness-axioms.log`: integer bridge and finite certificate axiom check.
- `results/lean-independent-verification.log`: all 22 final declaration axiom checks.
- `results/lean-independent-build.log`: targeted Lake build of the isolated modules.
- `results/lean-source-sha256.json`: SHA-256 hashes of all audited sources, root imports, toolchain pin, and dependency manifest. These hashes tie this report to the exact source snapshot.

## Limits and claim boundaries

This audit did not find a mathematical loophole in the checked general lower bound. Nevertheless, the checked theorem statements are the authority: explanatory comments are not extra theorems.

The following claims are **not** established by this formal artifact:

- Historical novelty, priority, or improvement over every available preprint.
- Exact minima for four or five qubits, except where an additional formally checked witness and matching bound are supplied. In particular the five-qubit real theorem is the lower bound 6426, not an exact value 6975.
- The quaternionic/Kramers refinement or elliptic-quadric numerical lower bounds.
- A general classification of equality in the spectral bound, SIC existence/nonexistence, or the geometry of the violated lines.
- A formal limit theorem showing convergence of the full-space fraction to one half. The finite-`N` inequality is checked; the asymptotic statement is an ordinary mathematical consequence that would require its own Lean theorem to be described as formalized.
- Correctness of the C engine, Moonlab, QRNG, QGTL, or Eshkol implementations, physical hardware behavior, quantum advantage, or any experimental claim. Those require their own checks.

The user-requested scientific paper may cite this as a reproducible formal verification artifact. It should distinguish the general proved lower bounds, the exact known three-qubit optimum reproduced here, numerical witnesses elsewhere, and any unverified or historical claims.

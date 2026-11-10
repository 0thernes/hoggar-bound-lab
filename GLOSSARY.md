# Glossary

Terms as they are used in the paper and in this repository.

**Assignment.** A choice of a value +1 or −1 for every observable of a configuration: what a
noncontextual hidden-variable model would have to supply.

**Axioms (Lean).** Every Lean proof here depends only on `propext`, `Classical.choice` and `Quot.sound`,
the three axioms that almost all of Mathlib uses. `#print axioms` lists them for each theorem; no
`sorry`, no `native_decide`, no added axiom.

**Bent function.** A Boolean function on an even number of variables whose Walsh transform has constant
absolute value. Its support is a Hadamard difference set. The Pauli supports of the three-, five- and
seven-qubit flat phase states are supports of bent functions (Proposition 10).

**CCZ, CS, T gates.** Diagonal quantum gates: `T` multiplies the basis state 1 of one qubit by
exp(iπ/4); `CS` (controlled-S) multiplies the state 11 of two qubits by i; `CCZ` multiplies the state 111
of three qubits by −1. They generate the diagonal gates of the third level of the Clifford hierarchy.

**Classical families.** The full set of N-qubit Pauli observables and its two kinds of quadrics
(hyperbolic and elliptic). These are the configurations studied in the earlier literature.

**Clifford operation.** A unitary that maps Pauli observables to Pauli observables (up to sign). It
relabels a configuration without changing its contexts or its contextuality degree.

**Closed (configuration).** Containing the product of any two of its commuting observables. The
classical families are closed; the new configurations of Section 5 are not.

**Configuration.** A set S of Pauli observables together with all the contexts it contains.

**Context.** Three mutually commuting Pauli observables whose product is +I or −I. Quantum mechanics
fixes that sign.

**Contextuality degree d(S).** The least number of contexts of S that an assignment must violate.

**Flat state (on S).** A pure state whose Pauli expectation values are ±μ on S, with one modulus μ, and
zero on every other non-identity Pauli observable. The spectral floor is attained on S exactly when such a
state exists (Theorems 3 and 4).

**Kernel evaluation.** A finite count carried out inside Lean's proof checker (`decide +kernel`), as
opposed to by compiled code outside it. The five-qubit counts are sums of 2^20 terms evaluated this way
in 16 blocks.

**Lean 4, Mathlib.** The proof assistant and its mathematical library. Versions: Lean 4.35.0, Mathlib
v4.35.0.

**Mask.** A configuration or an assignment written as one large integer: bit `a + 2^N c` stands for the
observable with X-part `a` and Z-part `c`. The files in `data/flat/` and `lean/HoggarBound/FlatData.lean`
hold the same masks.

**Moonlab, QGTL, quantum_rng, Eshkol.** Components of the Tsotchke stack used for the demonstration:
a classical state-vector simulator; a library of which only the Fubini–Study and Berry-curvature kernels
are used; a classical seeded generator; a Scheme dialect with automatic differentiation.

**Pauli observable.** A tensor product of the matrices I, X, Y, Z on N qubits, not all I. It is labelled
by a non-zero vector (a | c) of 2N bits.

**Phase state.** A state with amplitudes of equal modulus on all basis states. Here: the states obtained
from the all-plus state by T, CS and CCZ gates (Section 5.3).

**Quadric.** The set of Pauli observables fixed by a Pauli antiunitary; for example the real ones (an
even number of Y factors).

**Saturated.** Said of a configuration on which the spectral floor is attained, so that the floor is the
exact contextuality degree.

**Spectral floor.** The inequality (satisfied − violated contexts) ≤ (D−2)|S|^{3/2} / (6√(D−1)) with
D = 2^N, first posted by B. W. Jonah (October 2026). The name is his.

**Two-character set.** A set of points of a finite projective space that meets every hyperplane in one
of two numbers of points. Such sets correspond to two-weight codes and strongly regular graphs.

**Violated context.** A context whose three assigned values do not multiply to the sign fixed by quantum
mechanics.

**Witness.** An explicit assignment, stored as a mask, that violates a stated number of contexts. Anyone
can recount it.

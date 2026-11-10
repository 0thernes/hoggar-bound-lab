A noncontextual hidden-variable model assigns a value $\pm 1$ to every $N$-qubit Pauli observable. The
*contextuality degree* of a set of observables is the least number of its contexts (commuting triples
with product $\pm I$) that such an assignment must get wrong. We give a kernel-checked Lean 4 proof, for
every $N$ and for arbitrary sets $S$, of the spectral floor first posted by B. W. Jonah:
the number of satisfied minus violated contexts is at most $(D-2)\,|S|^{3/2} / (6\sqrt{D-1})$, where
$D = 2^N$. The floor is attained exactly when a pure state has Pauli expectation values of one modulus
on $S$ and zero elsewhere. We exhibit such configurations outside the classical families and determine
their degrees exactly: 135 four-qubit observables with 1095 contexts (degree 75) and 496 five-qubit
observables with 10880 contexts (degree 480), both proved in Lean with kernel-evaluated counts, and 8128
seven-qubit observables with 2 824 192 contexts (degree 729 344). The Pauli support of any such state is
a two-character set, hence gives a strongly regular graph, and a bent function in the three-, five- and
seven-qubit cases. By exhaustive enumeration we classify the states $U|{+}\cdots{+}\rangle$, with $U$ a
diagonal gate of the third level of the Clifford hierarchy, that have this property on up to five
qubits: there is none on four qubits and one class on five, a circuit of three controlled-S and two
$CCZ$ gates whose configuration is Clifford-equivalent to the support of a state found numerically by
Cieśliński. On seven qubits a circuit of three controlled-S and eight $CCZ$ gates gives the configuration
above. For the classical families the checked corollaries include a violated fraction of at least
$1/2 - \sqrt{D+1}/(D+2)$ for the full $N$-qubit configuration, for every $N$. The work was produced with
an AI research system under the author's direction, as disclosed in the paper.

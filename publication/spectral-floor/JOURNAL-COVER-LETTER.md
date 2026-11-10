# Cover letter draft: Journal of Physics A

Draft for the author to review, correct and send personally with the submission described in
`JPHYSA-SUBMISSION.md`. Not sent.

---

Alexander S. Donahue
0thernes LLC, Washington, USA
ORCID 0009-0006-8168-9648
0_0@0thernes.art

To the Editors of Journal of Physics A: Mathematical and Theoretical,

I submit the manuscript "A machine-checked spectral floor for Pauli contextuality, and new
configurations that attain it" for consideration as a Paper in the section Quantum mechanics and quantum
information theory.

The contextuality degree of a set of multi-qubit Pauli observables measures how badly every
noncontextual hidden-variable model must fail on it; it is the classical bound of the corresponding
state-independent noncontextuality inequality. The manuscript has two parts.

First, it gives a complete Lean 4 proof, for every number of qubits and for arbitrary sets of
observables, of the spectral lower bound on this degree that B. W. Jonah posted in October 2026. The
manuscript states this priority on its first page. Earlier accounts of the bound are not formally
verified.

Second, it shows that the bound is exact on configurations outside the families studied so far, and
determines three contextuality degrees exactly: 75 for a set of 135 four-qubit observables, 480 for a
set of 496 five-qubit observables, and 729 344 for a set of 8128 seven-qubit observables. The first two
are proved in Lean, lower bound and witness. It also classifies, by exhaustive enumeration, the states
built from T, controlled-S and CCZ gates that give rise to such configurations on up to five qubits, and
shows that the Pauli support of any such state is a two-character set. The five-qubit configuration is
the Pauli support, up to a Clifford operation, of a state reported numerically by Cieśliński
(arXiv:2610.07172).

Disclosure of AI use. The research, the programs, the formal proofs and the text were produced with an
AI system (Claude Fable 5, Anthropic) working under my direction. This is stated in the Acknowledgments
and in Section 10 of the manuscript, in line with the journal's policy on generative AI. The formal
statements are checked by the Lean kernel, every number in the manuscript is produced by a program in
the public repository, https://github.com/0thernes/hoggar-bound-lab, and every reference was checked
against its source. [The author adds here, in his own words, what he reviewed and verified himself.]

The manuscript has not been published and is not under consideration by another journal. A preprint is
public at https://0thernes.github.io/hoggar-bound-lab/ [and arXiv identifier, once assigned]. The work
was funded by me through my own company, 0thernes LLC; I have no other competing interests. A
five-page supplement describes the simulated demonstration and the tests.

Areas of expertise suited to refereeing: quantum contextuality and Kochen–Specker sets of multi-qubit
Pauli observables; finite geometry of symplectic polar spaces and two-character sets; formalization of
mathematics in Lean.

Yours sincerely,
Alexander S. Donahue

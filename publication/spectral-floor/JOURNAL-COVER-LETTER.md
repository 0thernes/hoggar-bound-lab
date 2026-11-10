# Cover letter draft (journal submission)

Draft for the author to review, correct and send personally. Not sent. First choice of journal:
*Journal of Physics A: Mathematical and Theoretical* (see [../ROUTES.md](../ROUTES.md) for its AI-use
and authorship rules). Submit to one journal at a time, after the arXiv posting.

---

Alexander S. Donahue
0thernes LLC, Washington, USA
0_0@0thernes.art

To the Editors,

I submit the manuscript "A machine-checked spectral floor for Pauli contextuality, and new
configurations that attain it" for consideration as a Paper.

The contextuality degree of a set of multi-qubit Pauli observables measures how badly every
noncontextual hidden-variable model must fail on it. The manuscript has two parts.

First, it gives a complete Lean 4 proof, for every number of qubits and for arbitrary sets of
observables, of the spectral lower bound on this degree that B. W. Jonah posted in October 2026. The
manuscript states this priority on its first page. Earlier accounts of the bound are not formally
verified.

Second, it shows that the bound is exact on configurations outside the families studied so far, and
determines three contextuality degrees exactly: 75 for a set of 135 four-qubit observables, 480 for a
set of 496 five-qubit observables, and 729 344 for a set of 8128 seven-qubit observables. The first two
are proved in Lean, lower bound and witness. It also classifies, by exhaustive enumeration, the states
built from T, controlled-S and CCZ gates that give rise to such configurations on up to five qubits, and
shows that the Pauli support of any such state is a two-character set.

Disclosure of AI use. The research, the programs, the formal proofs and the text were produced with an
AI system (Claude, Anthropic) working under my direction. This is stated on the first page and in the
disclosure section of the manuscript. The formal statements are checked by the Lean kernel, and every
computation can be re-run from the public repository,
https://github.com/0thernes/hoggar-bound-lab. I take responsibility for the content of the submission.

The manuscript has not been published and is not under consideration elsewhere. A preprint is available
at [arXiv identifier, once assigned]. The work was funded by me through 0thernes LLC; there are no
competing interests. Data and code are public at the address above.

Suggested areas of expertise for referees: quantum contextuality and Kochen–Specker sets of multi-qubit
Pauli observables; finite geometry of symplectic polar spaces; formalization of mathematics in Lean.

Yours sincerely,
Alexander S. Donahue

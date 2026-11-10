# Research glossary for both studies

Hoggar Bound Lab — Alexander S. Donahue, 0thernes LLC.

Shared terms apply across the repository. For the spectral-floor and flat-state study, see [SUMMARY.md](SUMMARY.md), [INDEX.md](INDEX.md), and [the paper](paper/spectral-floor.md). For the C3 study, see the [research summary](docs/RESEARCH-SUMMARY.md), [paper](paper/c3-spectral-counterexample.md), and [formal audit](results/frontier-c3-lean-audit.md). Proof and computation claims remain specific to each study.

## Spectral-floor and flat-state terms

The section and theorem numbers mentioned here belong to the spectral-floor paper, not the C3 paper.

| Term | Meaning in this project |
| --- | --- |
| Assignment | A choice of `+1` or `-1` for each observable in a configuration. It is the collection of values tested against all of that configuration's contexts. |
| Configuration | A set of nonidentity Pauli observables together with all contexts it contains. |
| Contextuality degree | The smallest number of contexts violated by any sign assignment on a configuration. A particular assignment supplies an upper bound; proving a matching lower bound establishes the exact degree. |
| Violated context | A context whose three assigned values multiply to the opposite of its required Pauli product sign. |
| Closed configuration | A configuration containing the product, up to Pauli sign, of any two distinct commuting observables in it. The new Section 5 configurations are studied without assuming closure. |
| Classical families | The full nonidentity Pauli space and the hyperbolic and elliptic quadrics considered in the earlier literature. |
| Spectral floor | Jonah's lower-bound method, expressed as `(satisfied - violated) <= (D-2)|S|^(3/2)/(6 sqrt(D-1))`, with `D = 2^N`. The repository formalizes the inequality and studies configurations that attain it. |
| Flat state on a support | A pure state whose nonzero, nonidentity Pauli expectation values all have the same absolute value; they vanish outside its support. The spectral-floor paper's saturation criterion relates such states to equality in the bound. |
| Saturated configuration | A configuration attaining the spectral floor, so that the lower bound equals its contextuality degree. The claimed criterion and individual exact-degree certificates have their own proof scopes in [INDEX.md](INDEX.md). |
| Phase state | A state with equal absolute amplitudes in the computational basis. The spectral-floor study examines the family obtained from the all-plus state using `T`, controlled-`S`, and `CCZ` gates. |
| T, CS and CCZ gates | Diagonal gates multiplying the selected basis amplitude by `exp(i*pi/4)`, `i`, and `-1`, respectively. Here the selected bit patterns are `1`, `11`, and `111`. They generate the diagonal third-level Clifford-hierarchy gates up to global phase. |
| Clifford operation | A unitary mapping Pauli observables to Pauli observables up to sign. It relabels a configuration while preserving its contextuality degree. |
| Bent function | A Boolean function on an even number of variables whose Walsh transform has constant absolute value. Its support is a Hadamard difference set. The spectral-floor study relates bent supports to its flat phase states. |
| Two-character set | A set of projective points meeting every hyperplane in one of two possible numbers of points. The spectral-floor paper discusses the relation to flat-state supports. |
| Quadric | A family of Pauli labels selected by a binary quadratic form. The nonidentity real Paulis, with an even number of `Y` factors, form a hyperbolic example. |
| Mask | A finite set or sign assignment encoded by bits of an integer. Bit `a + 2^N c` corresponds to the Pauli label with X-part `a` and Z-part `c`. |
| Witness | Explicit data that can be recounted or checked. In degree calculations it is usually a sign assignment attaining a stated violation count; the C3 witness is a pair of section assignments with specified spectral properties. |
| Tsotchke stack | Moonlab is a classical state-vector simulator; selected QGTL kernels compute geometry quantities; the vendored quantum_rng is a classical seeded generator; Eshkol is the language/compiler used for the recorded replication. A run of these tools is not itself a quantum-hardware experiment. |

## C3 operators and geometry

| Term | Meaning in this project |
| --- | --- |
| Qubit | A quantum system whose pure-state vectors lie in a two-dimensional complex space. Four qubits have a 16-dimensional state space. The reported calculations manipulate finite matrices; they are not measurements on a physical quantum device. |
| Pauli observable | A tensor product of the one-qubit matrices `I`, `X`, `Y`, and `Z`, with the paper's fixed phase convention. The observables used here are Hermitian and have eigenvalues in `{−1,+1}`. |
| Real Pauli configuration | The 135 nonidentity four-qubit Pauli matrices that are real and symmetric. Their binary labels form the hyperbolic quadric denoted `Q+(7,2)` in finite geometry. |
| Context | Three distinct, pairwise commuting nonidentity Pauli observables whose product is either `+I` or `−I`. That product determines the context's required sign. |
| Sign assignment | A choice of `+1` or `−1` for each observable under consideration. This is the discrete input to the certificate. |
| Polar observable | The distinguished observable `d = Z ⊗ I ⊗ I ⊗ I`. In the paper's binary encoding its label is 128. It defines the section and the two symmetry sectors used in the proof. |
| Section | The 71 observables in the real configuration that commute with the polar observable. Both published assignments specify a sign at every section point. |
| Outside points | The other 64 observables in the real configuration. They anticommute with the polar observable. |
| Outside context | A context containing one section point and two outside points. There are 1120 such contexts in this example. |
| Carrier operator | The 16-by-16 matrix obtained by summing the section Pauli matrices, each multiplied by its assigned sign. A *sign carrier* refers to the assignment producing this operator. |
| Completion operator | The 64-by-64 real symmetric matrix encoding the signed outside contexts after the section assignment is fixed. Each nonzero entry is the corresponding context sign multiplied by the sign at its section point. |
| Jordan multiplication | The linear map `M ↦ (AM + MA)/2` associated with a carrier matrix `A`. Restricted to the outside Pauli span, it represents the completion operator. The paper attributes this framework to Jonah's prior work. |
| Symmetry sector | One of the two eight-dimensional eigenspaces of the polar observable, with eigenvalue `+1` or `−1`. The carrier is block diagonal across these spaces. Which eigenvalues belong to which sector matters for completion. |

## C3 spectra and the finite result

| Term | Meaning in this project |
| --- | --- |
| Spectrum | The eigenvalues of a matrix, including how often each occurs. For the Hermitian and real symmetric matrices here, all eigenvalues are real. |
| Multiplicity | The number of occurrences of an eigenvalue. Matching only the distinct eigenvalues is weaker than the equality proved here. |
| Characteristic polynomial | `det(tI − A)`. For the Hermitian carriers in this example, equality of this polynomial establishes equality of their spectra with multiplicities. |
| Cospectral | Having the same eigenvalues with multiplicities. The two carrier operators are cospectral; their completion operators are not. |
| Cubic trace | `tr(A³)`, the sum of the cubes of a matrix's eigenvalues. Different cubic traces certify different spectra. Equal cubic traces alone would not establish equal spectra. |
| C3 | A case label in B. W. Jonah's classification of hyperplane completions: a hyperbolic quadric cut by a hyperplane whose polar point lies on the quadric. It is not a physical device label or a claim about all contextuality scenarios. |
| Strict spectral law | The proposed implication that equal carrier spectra force equal completion spectra. The published pair is a counterexample to this implication in the four-qubit C3 case. |
| Conjecture E | Jonah's prediction that the strict law fails in the specified vertex cases for every number of qubits at least four. The project establishes the four-qubit C3 instance; it does not refute the conjecture or settle all its dimensions. |
| Continuous relaxation | Replacing the 64 outside signs by a real vector of squared length 64. This easier optimization is controlled by the largest completion eigenvalue. Its two minima differ by 32 in this example. |
| Binary optimum | The minimum when every outside variable must remain `−1` or `+1`. The paper does not determine the exact binary completion optima or prove that they differ. |

## Evidence and publication

| Term | Meaning in this project |
| --- | --- |
| Exact certificate | Explicit finite data and identities sufficient to check the claimed result, such as an invertible intertwining matrix and integer cube traces. The certificate can be checked without repeating its discovery search. |
| Lean 4 and Mathlib | The proof assistant and its mathematical library. The recorded studies use Lean 4.35.0 and Mathlib 4.35.0; each theorem must be read with its own statement and audit. |
| Lean kernel check | Verification of a formal proof by Lean's trusted proof-checking kernel. Finite certificates use kernel reduction (`decide +kernel`). The C3 geometry bridge connects its integer certificates to the original Pauli definitions. |
| Axiom audit | A report of the foundational assumptions on which named Lean declarations depend. The C3 audit covers 42 declarations; the saturation study has its own audit. These records list `propext`, `Classical.choice`, and `Quot.sound` for their checked declarations. A reported audit does not automatically cover every file or later theorem in the repository. |
| Formal boundary | The exact scope of the machine-checked theorem statements. The printed polynomial factorization, block/Jordan derivation, largest-eigenvalue gap 2, and relaxation gap 32 are outside the C3 Lean theorem statements and have separate algebraic/executable evidence. |
| Negative control | An intentional error introduced to check whether a verifier rejects a corrupted certificate. The signed-context verifier changes a symmetric pair of entries and detects the resulting incorrect cubic trace. |
| Independent implementation | A separately implemented calculation of the same mathematical quantities. This does not mean independent human review or journal peer review. |
| Research preprint | A publicly available research manuscript before journal peer review. GitHub publication, a future archive DOI, indexing, journal submission, and acceptance are distinct events. |
| AI assistance | The spectral-floor study discloses Claude/Anthropic assistance; the independent review and C3 study disclose OpenAI Codex assistance. The roles include substantive research, code, formalization and writing. AI tools are not credited as authors, and automated checks do not establish completed human critical review. |

The source for C3 and Conjecture E is B. W. Jonah, *The reach of the section-square law*, v0.5, [DOI 10.5281/zenodo.23524332](https://doi.org/10.5281/zenodo.23524332). See [publication status](publication/STATUS.md) for current publication status and [LEGAL.md](LEGAL.md) for the repository's license explanation.

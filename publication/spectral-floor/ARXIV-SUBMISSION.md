# arXiv submission sheet: the spectral-floor paper

Prepared for version 1.1.2 on 9 November 2026. Nothing has been submitted. The steps marked **author** need the author's own
arXiv login and personal confirmation; they cannot be done for the author.

## Files

| file | what |
|---|---|
| `arxiv-source.zip` | the upload: `spectral-floor.tex`, three PNG figures, `00README.json` (compiler: XeLaTeX, TeX Live 2025) |
| `spectral-floor.pdf` | the same source compiled locally with Tectonic 0.17 (24 pages), for comparison with arXiv's own PDF |
| `build-record.json` | hashes of the Markdown source, the TeX file, the PDF and the archive |

The archive is rebuilt with `python scripts/build_latex.py --pandoc … --tectonic …`.

## Metadata to enter

**Title**

A machine-checked spectral floor for Pauli contextuality, and new configurations that attain it

**Authors**

Alexander S. Donahue (0thernes LLC)

**ORCID:** [0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648) (author-supplied; account linking not independently verified).

**Affiliation, everywhere:** 0thernes LLC, Washington, USA. The arXiv account affiliation was saved
as `0thernes LLC` and the success state verified on 9 November 2026. The account display name remains
Alexander Donahue; the confirmed manuscript credit is Alexander S. Donahue. The Zenodo account
affiliation was also saved. These profile changes are not paper submissions or deposits. See
[the affiliation record](../AFFILIATIONS.md). The same publication affiliation is used in the paper,
citation metadata, indexing tags and venue templates.

**Abstract** (plain text, 1 845 characters; arXiv's limit is 1 920)

A noncontextual hidden-variable model assigns a value +1 or -1 to every N-qubit Pauli observable. The
contextuality degree of a set of observables is the least number of its contexts (commuting triples with
product +-I) that such an assignment must get wrong. We give a kernel-checked Lean 4 proof, for every N
and for arbitrary sets S, of the spectral floor first posted by B. W. Jonah: satisfied minus violated
contexts is at most (D-2)|S|^{3/2}/(6 sqrt(D-1)), with D = 2^N. The floor is attained exactly when a pure
state has Pauli expectation values of one modulus on S and zero elsewhere. We exhibit such configurations
outside the classical families and determine their degrees exactly: 135 four-qubit observables with 1095
contexts (degree 75) and 496 five-qubit observables with 10880 contexts (degree 480), both proved in Lean
with kernel-evaluated counts, and 8128 seven-qubit observables with 2824192 contexts (degree 729344). The
Pauli support of any such state is a two-character set, hence gives a strongly regular graph, and a bent
function in the three-, five- and seven-qubit cases. By exhaustive enumeration we classify the states
U|+...+>, U a diagonal gate of the third level of the Clifford hierarchy, with this property on up to
five qubits: none on four qubits and one class on five, a circuit of three controlled-S and two CCZ gates
whose configuration is Clifford-equivalent to the support of a state found numerically by Cieslinski. On
seven qubits a circuit of three controlled-S and eight CCZ gates gives the configuration above. Formally
verified corollaries for the classical families, a reproduction of the known values for two to five
qubits and simulated state-independent contextuality tests are included. The work was produced with an AI
research system under the author's direction, as disclosed in the paper.

**Comments**

24 pages, 3 figures. Lean 4 sources, programs and data: https://github.com/0thernes/hoggar-bound-lab

**Primary category:** quant-ph (Quantum Physics)

**Cross-list:** math.CO (Combinatorics)

**MSC classes:** 81P13, 05B10, 94D10, 68V20

The account's default category is math.QA. That is not the right home for this paper: its subject is
contextuality of multi-qubit Pauli observables (quant-ph), with finite geometry and difference sets as
the mathematical side (math.CO).

## Steps

1. **Author:** resume the authenticated arXiv account when ready. Submission remains deferred at the
   author's request; no paper draft or submission has been started.
2. **Author:** read and accept arXiv's submission terms. They include statements only the author can
   make: that the submitter is an author of the work, that the author takes responsibility for all of
   its content, and the choice of a licence. The repository's own licence is a restrictive
   verification licence; arXiv needs at least its non-exclusive distribution licence for the paper.
   This is the author's decision.
3. Select the primary category quant-ph. **If arXiv says an endorsement is needed** (usual for a first
   submission without an institutional email), it sends an endorsement request email with a
   six-character code and a link. See the next section.
4. Upload `arxiv-source.zip`. When asked for the processor, choose XeLaTeX (the archive's
   `00README.json` already says so). Check arXiv's compiled PDF against `spectral-floor.pdf`.
5. Paste the metadata above. Check the abstract preview: it contains no TeX.
6. **Author:** review the final preview and press *Submit*. Until the next announcement the submission
   can still be withdrawn or replaced; after announcement it is permanent, and corrections are new
   versions.

## Endorsement

arXiv requires a personal endorsement from an established arXiv author for a first submission to
quant-ph when the account's email is not one arXiv recognises as institutional. arXiv's own guidance (info.arxiv.org/help/endorsement):
choose someone knowledgeable in the subject, ideally someone who knows you; do not email many people at
once; you may attach the paper.

Where to look: the abstract pages of the arXiv papers this work builds on each have a link
*Which authors of this paper are endorsers?* at the bottom.

* arXiv:2610.26465 (Li, Gupta, Ganesh; four-qubit hyperbolic quadric, with a Lean proof)
* arXiv:2305.10225 and arXiv:2407.02928 (Muller, Saniga, Giorgetti, de Boutray, Holweck, Kelleher; contextuality degrees)
* arXiv:2105.13798 (de Boutray, Holweck, Giorgetti, Masson, Saniga)
* arXiv:2610.07172 (Cieśliński; the five-qubit state whose configuration is treated here)
* arXiv:1002.3135 (Cabello)

A request the author can adapt and send personally, to one person at a time:

> Subject: arXiv endorsement request (quant-ph): exact contextuality degrees with a Lean 4 proof
>
> Dear Dr …,
>
> I am the founder of 0thernes LLC, a small company in Washington State, and am preparing a first arXiv
> submission to quant-ph, for which I need an endorsement. The paper builds directly on your work
> [reference]. It gives a Lean 4 proof of the spectral lower bound
> on the contextuality degree of multi-qubit Pauli configurations and determines the degree exactly for
> three configurations outside the classical families (four, five and seven qubits). The paper, the Lean
> sources and all programs are public: https://github.com/0thernes/hoggar-bound-lab
>
> In fairness to you: the research and the text were produced with an AI system (Claude) under my
> direction, which the paper states on its first page and in its disclosure section. The formal
> statements are checked by the Lean kernel and the computations can be re-run from the repository.
>
> If you are willing to look at it, my endorsement code is ……. I would also be grateful for any
> criticism of the paper itself.
>
> With thanks,
> Alexander S. Donahue, 0thernes LLC, 0_0@0thernes.art

## What arXiv expects about AI use

arXiv does not allow AI tools as authors, requires significant use of generative AI to be reported in
the work, and holds each author fully responsible for all contents, however they were produced
(info.arxiv.org/help/moderation). The paper reports the use on its first page and in Section 12.

The official moderation policy requires careful scholarly preparation and permits rejection of work
containing serious errors, misrepresentations or inadequate research. The research-release record
reports reference checking and executable calculations; those automated checks do not establish that
the human author has critically reviewed the paper. Before submitting, check the references, the exact
claims and the disclosed limits, and complete the author's actual responsibility statement.
[Official moderation and AI policy](https://info.arxiv.org/help/moderation/index.html#AI-language-tools).

Whether to submit under these terms is the author's decision; moderators may also decline or reclassify
a submission.

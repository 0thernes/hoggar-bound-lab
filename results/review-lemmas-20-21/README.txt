Review of version 1.4.0 (Lemmas 20 and 21, their use in Theorem 19, the checker), 10 November 2026

Seven separate automated review passes (instances of Claude, each started without the others' work and
with one task) examined the changes of version 1.4.0 of the combined paper before release:

  lemma20   Lemma 20, its proof, the closure property of the nine configurations, the pointer in 8.6 (v)
  lemma21   Lemma 21 (a) and (b), and the trace formulas (E8) and (E9) that follow from it
  base      the hypotheses verified in the paragraph on C1, C3 and C5 (outside Paulis, the real form)
  swap      C12 and C15 (theta_c, the two bases, M^T = eta M, the real dimension, (E9))
  cones     the pair swap of C6, C11 and C14, the reduction of C8 to C1, and Corollary 18
  program   scripts/conjecture_e_lemmas.py against Section 11.3, with 29 deliberate faults
  deps      every citation of Jonah's preprint [J3], the dependency statements, and the credit to [J3]

Every finding was then examined by one adversarial verifier (minor findings) or two (the one finding
rated major), each asked to refute it. No mathematical error was found. The finding rated major (deps-1:
each construction fixes one hyperplane class, and passing to every class of a case needs a transport
and the case list of [J3]) was downgraded to minor by both verifiers. All 13 findings were confirmed or
partly confirmed and are corrected in version 1.4.0: see the CHANGELOG entry for 1.4.0.

  findings-and-verdicts.json   every finding, with location, evidence and proposed fix, and every verdict
  mutation-tests.log           the program pass: which checks each deliberate fault made fail
  mutation-summary.txt         one line per fault
  programs/                    the small programs the passes wrote for their own exact or numerical checks

The program pass found five surviving faults that are equivalent to the original (for example the order
of two commuting points), and two that were real: building the second basis of C12 and C15 wrongly made
every block zero, so the symmetry test passed vacuously. The checker now also requires each basis vector
to lie in the right eigenspace and every block to be twice a unitary, with a fourth negative control
(the second basis equal to the first). The mutation log refers to the checker as it was before that
change (where the symmetry sign was still called eps).

The programs were written against the draft of the paper at that time; line numbers in the JSON refer
to that draft. They are kept as records of the review, not as maintained tests. This is internal
checking by the same AI system, not peer review.

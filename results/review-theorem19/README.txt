Independent check of Theorem 19 (Conjecture E), 10 November 2026

These programs and outputs were written by a separate automated review pass (an instance of Claude,
started without the repository's programs) that was asked to refute Theorem 19 of the combined paper.
Its verdict was "no error found"; the review record is in publication/ADDENDUM-conjecture-e.md.

The pass worked on the draft of commit 042789c. Table numbers in its comments refer to that draft:
its "Table 7", "Table 8" and "Table 9" are Tables 5, 6 and 7 of version 1.3.0.

  python verify19.py 4         reproduces out_N4.txt (also 3, 5; out_N6_C3.txt is case C3 at six qubits)
  python cnot_check.py         the controlled-NOT conjugation of the pair swap (out_cnot.txt)
  python extra_check.py        the C11 cone-lift rows built on the C11 configuration (out_extra.txt)

The programs build every Pauli matrix from the 2 x 2 matrices with Gaussian-integer entries and use no
code of this repository. They are kept as records of the review, not as maintained tests.

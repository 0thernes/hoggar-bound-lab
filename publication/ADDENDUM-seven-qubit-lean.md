# Addendum: the seven-qubit contextuality degree, with its counts, is proved in Lean

**Status.** Proposed change for the next revision of the combined paper
([paper/unified-contextuality.md](../paper/unified-contextuality.md)). Release `v1.2.0` and its frozen
artifacts are not changed by this file. The result was obtained on 10 November 2026 by the Claude
(Anthropic) line of work, under the direction of Alexander S. Donahue, 0thernes LLC. It is a Lean 4
statement. The lower bound is the theorem `hoggar_bound` of the paper, and the three finite counts are
evaluated by the Lean kernel (`decide +kernel`; no `native_decide`, no added axiom). It is not peer
reviewed.

## What the paper says

Theorem 13 of the combined paper concerns the Pauli support $S_7$ of the seven-qubit phase state
$\Phi_7$: 8128 observables, 2 824 192 contexts, contextuality degree 729 344. In release 1.2.0 this degree
combines the Lean inequality, which needs only the number 8128, with counts of contexts and of violated
contexts made by three programs. Section 9.1 gives the reason: the two counts are double sums with
$2^{28}$ terms each, and they were not evaluated in the kernel. Evaluated term by term, as the five-qubit
sums are ($2^{21}$ terms in about seven minutes), they would need an estimated 40 core-hours.

## The statement

```lean
theorem phase7_degree :
    (∀ f : Pt 7 → ℝ, (∀ u ∈ cfg 7 phase7Mask, f u = 1 ∨ f u = -1) →
        729344 ≤ (violatedLines (cfg 7 phase7Mask) f).card) ∧
      ∃ f : Pt 7 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
        (violatedLines (cfg 7 phase7Mask) f).card = 729344

theorem phase7_contexts : (contexts (cfg 7 phase7Mask)).card = 2824192

theorem phase7_card : (cfg 7 phase7Mask).card = 8128
```

`cfg 7 phase7Mask` is the set of seven-qubit Pauli observables whose codes are the set bits of the
16384-bit number `phase7Mask` of `PhaseData.lean`, a file that release 1.2.0 already contains. The
statements have the form of `phase5_degree` and `phase5_contexts`: every assignment of values $\pm 1$
violates at least 729 344 contexts, some assignment violates exactly 729 344, and there are 2 824 192
contexts. As for the four- and five-qubit theorems, they are about the explicit complex Pauli matrices
of `Pauli.lean`, whose products, commutation and context signs are theorems.

`degree_of_certificate` (`MaskConfig.lean`, unchanged) derives the two-sided statement from three
numbers and two identities:

| quantity | value | Lean theorem |
|---|---|---|
| observables | 8128 | `phase7_card` |
| flags (ordered commuting pairs with product in the set, six for each context) | 16 945 152 = 6 × 2 824 192 | `phase7_flags` |
| flags violated by the assignment `phase7Neg` | 4 376 064 = 6 × 729 344 | `phase7_witness` |

```math
127 \cdot 8128 = 1016^2, \qquad 127\,(16\,945\,152 - 12 \cdot 729\,344) = 126 \cdot 8128 \cdot 1016 .
```

## How the kernel evaluates the two sums

`MaskConfig.lean` writes each count as a sum, over the $4^N$ codes $z$, of a row, and each row as a sum
over the $4^N$ codes $w$. The new module `MaskRows.lean` evaluates one row with a bounded number of
operations on large natural numbers and proves that the result is the row.

A set $S$ of codes is *packed* into the number $`\sum_{w \in S} 2^{bw}`$: one digit of $b$ bits for each
code, the digit being 0 or 1. On packed sets:

* intersection is the bitwise *and*, symmetric difference the bitwise *exclusive or*;
* the translate $`\{w : w \oplus z \in S\}`$ is obtained by exchanging blocks of digits, once for each set
  bit of $z$, so at most $2N$ times;
* the set of codes that commute with $z$ is an exclusive or of at most $2N$ fixed stripes (the sets of
  codes with a given bit);
* the number of elements is the remainder modulo $2^b - 1$, because $2^b \equiv 1$; it is the number
  itself as soon as $4^N \lt 2^b - 1$.

For commuting codes $z$ and $w$, the context $`\{z, w, z \oplus w\}`$ is violated by the assignment exactly
when

```math
g(z) \oplus g(w) \oplus g(z \oplus w) \oplus y(z)\,y(w) \oplus d(z, w) = 1 ,
```

where $y(u)$ is the parity of the number of $Y$ factors of $u$, $g(u)$ is the assigned value of $u$ (as a
bit) exclusive or the second binary digit of that number, and $d(z,w)$ is the parity of the number of
qubits on which $z$ has a $Z$ or $Y$ factor and $w$ an $X$ or $Y$ factor (`viol_bit`). The row of
violated flags is therefore the number of elements of the intersection of the packed flag set of $z$
with an exclusive or of at most five packed sets.

`flagRow_eq_fast` and `violRow_eq_fast` state that this evaluation is the row of `MaskConfig.lean`, for
every number of qubits, every mask, every assignment mask and every code $z$. They are general lemmas,
not checks of the seven-qubit instance; `card_flags_cfg_fast` and `card_violated_cfg_fast` follow.

For seven qubits $b = 16$, since $16384 \lt 65535$, and a packed set is a number of 262 144 bits. The
kernel evaluates the 16384 rows in 16 blocks of 1024 rows; one theorem for each block gives its two
partial sums (`p7_rows_0` to `p7_rows_15` in `SaturatedPhaseSeven.lean`):

| block | flags | violated flags | block | flags | violated flags |
|---|---|---|---|---|---|
| 0 | 1 133 440 | 292 544 | 8 | 1 101 184 | 284 480 |
| 1 | 1 033 088 | 266 560 | 9 | 1 067 904 | 275 904 |
| 2 | 1 100 928 | 284 352 | 10 | 1 002 112 | 259 136 |
| 3 | 1 067 648 | 275 776 | 11 | 1 033 856 | 266 944 |
| 4 | 1 066 368 | 275 136 | 12 | 1 034 112 | 267 072 |
| 5 | 1 034 112 | 267 072 | 13 | 1 067 904 | 275 904 |
| 6 | 1 033 856 | 266 944 | 14 | 1 067 136 | 275 520 |
| 7 | 1 067 648 | 275 776 | 15 | 1 033 856 | 266 944 |

The sums of the two columns are 16 945 152 and 4 376 064.

## How to check

```bash
cd lean && lake exe cache get && lake build HoggarBound.MaskRows HoggarBound.SaturatedPhaseSeven
```

```bash
lake env lean SaturatedSevenVerification.lean
```

The second command prints the axioms of thirteen declarations, among them `phase7_degree`,
`phase7_contexts` and the general lemmas. No line may name an axiom other than `propext`,
`Classical.choice` and `Quot.sound`. Eleven lines, those of `phase7_degree` and `phase7_contexts` among
them, list exactly these three; `viol_bit` lists two of them and `sign_table`, a finite case check,
none. The expected output is
[results/lean-saturated-seven-axioms.log](../results/lean-saturated-seven-axioms.log).

On a desktop computer (Windows 11, 10 November 2026) `MaskRows.lean` was checked in half a minute and
`SaturatedPhaseSeven.lean` in 5 to 14 minutes, depending on the load of the machine, with a peak
working set of 4.3 GB. The second file has its declarations checked one after the other
(`set_option Elab.async false`), because the kernel needs about 3 GB for one block of rows. These are
measurements, not guarantees.

From the repository root:

```bash
python scripts/phase_seven_lean.py
```

The last line must read `14 of 14 checks passed`. The script carries out the same evaluation in Python
and compares it with the direct double loop over the definitions of `MaskConfig.lean`: on random small
configurations, on the five-qubit phase state (the 32 block totals that the kernel has checked by the
direct double sum), and on sixteen sampled rows of the seven-qubit configuration. It recomputes the 16
blocks above, shows by two negative controls that the totals change when one bit of the data is
changed, and checks that `SaturatedPhaseSeven.lean` is the file it generates. The record is
[results/phase_seven_lean.json](../results/phase_seven_lean.json). The Lean file does not depend on the
script: every number in it is evaluated by the kernel.

The workflow *Saturated configurations* runs the three commands in its job `lean-degrees` and fails if
a declaration uses an axiom outside the allowlist or if a source file contains `sorry`, `native_decide`
or an `axiom` declaration.

## Scope

* One configuration. What is now a Lean theorem is the content of the first sentence of item 2 of
  Theorem 13 for the set given by the mask: 8128 observables, 2 824 192 contexts, degree exactly
  729 344.
* That the mask is the Pauli support of $\Phi_7$, and that the assignment is the sign pattern of its
  expectation values, is checked by programs in exact arithmetic (`scripts/phase_states.py`, and the C
  and JavaScript programs of Section 11), as for the four- and five-qubit configurations. This link is
  not part of the Lean statements, and the statements do not need it.
* The other parts of Theorem 13 are unchanged: item 1 (the expectation values of $\Phi_7$), the local
  numbers of item 2 (504, and the six numbers of contexts through an observable), the classification
  inside the family $\mathcal F$ (item 3) and the random census (item 4) remain computations outside
  Lean.
* The evaluation uses the arithmetic of the Lean kernel on natural-number literals (bitwise operations,
  shifts and remainder), on numbers of 262 144 bits. The four- and five-qubit theorems use the same
  kernel arithmetic on smaller numbers.
* No new mathematical claim is made: the number 729 344 is that of release 1.1.0. What changes is the
  level of verification of its two counts.

## Text proposed for the next revision of the combined paper

* Abstract. Replace "The first two degrees have kernel-checked counts; the seven-qubit counts are
  executable exact computations." by: "All three degrees are proved in Lean, with kernel-checked counts."
* Section 1.1. Replace "The seven-qubit circuit support has 8128 points, 2824192 contexts and degree
  729344; its finite counts are not kernel-checked." by: "The seven-qubit circuit support has 8128
  points, 2824192 contexts and degree 729344; this degree statement, with its finite counts and its
  witness, is also proved in Lean." In the sentence before it, "These degree statements, including their
  finite counts and witnesses, are proved in Lean" then covers the three configurations.
* Section 5.3, proof of Theorem 13. Replace "Item 1 and the counts of item 2 are finite computations in
  $\mathbb{Z}[i]$, made by three programs that share no code (Section 11). The lower bound is Theorem 1
  with $|S| = 8128$, $D = 128$" by: "Item 1 is a finite computation in $\mathbb{Z}[i]$, made by three
  programs that share no code (Section 11). The number of contexts and the degree of item 2 are the Lean
  theorems `phase7_contexts` and `phase7_degree` (Section 9.1); the other numbers of item 2 are computed
  by the same three programs. The lower bound is Theorem 1 with $|S| = 8128$, $D = 128$".
* Section 9.1, table of modules. Add the row "`MaskRows.lean` | packed sets of codes; `flagRow_eq_fast`,
  `violRow_eq_fast` (a row of either count, evaluated with a bounded number of operations on large
  numbers, for every $N$)", and replace the last row by "`PhaseData.lean`, `SaturatedPhaseFive.lean`,
  `SaturatedPhaseSeven.lean` | generated: the masks of $\Phi_5$ and $\Phi_7$; **`phase5_degree`**,
  **`phase7_degree`**".
* Section 9.1, table of theorems. Add the row "`phase7_degree` | for the 8128 observables in the support
  of the circuit state $\Phi_7$: at least 729344, and exactly 729344 for some assignment".
* Section 9.1, *How the exact degrees are checked*. Replace "For seven qubits the two sums have $2^{28}$
  terms each and were not evaluated in the kernel: the degree $`729\,344`$ of $S_7$ rests on
  `hoggar_bound`, which needs only the number 8128, and on a count of contexts and violated contexts
  made by programs." by: "For seven qubits the two sums have $2^{28}$ terms each. `MaskRows.lean`
  evaluates a row of either sum on packed sets of codes, with at most $2N$ exchanges of blocks, bitwise
  operations and one remainder, and proves for every $N$ that the result is the row; the kernel then
  evaluates the $2^{14}$ rows in 16 blocks. The degree $`729\,344`$ of $S_7$ is the theorem
  `phase7_degree`."
* Section 9.1, *Floor and saturation results outside the formalization*. Replace "the enumerations of
  Theorems 12 and 13 and the seven-qubit counts" by: "the enumerations of Theorems 12 and 13, and item 1
  and the local numbers of item 2 of Theorem 13".
* Section 9.2, table of claims. Replace "Degrees 75 and 480 for the explicit masks" by "Degrees 75, 480
  and 729344 for the explicit masks", and "Saturation equivalences, phase-state classification and
  seven-qubit counts" by "Saturation equivalences and phase-state classification".
* Section 11.1. In the item "The seven-qubit numbers 8128, 2 824 192 and 729 344 are computed three times
  without shared code", add: "and a fourth time by `scripts/phase_seven_lean.py`, with the evaluation
  that the kernel carries out". Replace "in particular, the seven-qubit context counts are outside the
  kernel evaluation, and the C3 checks use the separate programs described next" by: "in particular, the
  C3 checks use the separate programs described next".
* Section 12. Delete "The seven-qubit counts of contexts are checked by three programs but not by the
  Lean kernel."
* Appendix A. After `lake env lean SaturatedVerification.lean`, add the two commands of *How to check*.

The same earlier status is stated in `README.md`, `INDEX.md`, `docs/CLAIMS.md`, `lean/README.md`,
`CITATION.cff` and `publication/unified-abstract.txt`. They belong to release 1.2.0 and are left as they
are until the next revision.

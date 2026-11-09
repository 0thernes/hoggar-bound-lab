# Working notes (internal lab notebook)

Started 2026-11-09. Everything here is a working record; the paper in `paper/` is the polished statement.

## The result in one paragraph

For N qubits (D = 2^N) take any set S of non-identity Pauli observables and all "lines" inside it
(triples {u, v, u+v} of mutually commuting Paulis; product = +I or -I). A noncontextual assignment
f : S -> {+1,-1} satisfies a line when f(u) f(v) f(u+v) equals the sign of the operator product.
Let beta(f) = #satisfied - #violated. With A = sum_{v in S} f(v) P_v (Hermitian, traceless):

    tr A = 0,   tr A^2 = D |S|,   tr A^3 = 6 D beta(f).

Maximum skewness of n real numbers (one outlier) gives the **third-moment ("Hoggar") bound**

    beta(f) <= (n-2) |S|^{3/2} / (6 sqrt(n-1)),

with n = D in general, and n = D/2 when S is invariant under an antiunitary theta with theta^2 = -1
(Kramers pairs: elliptic quadrics). Equality iff there is a state whose Pauli expectation values are
supported on S with constant modulus sqrt((D-1)/|S|) ("S-flat state"); for S = everything that is a
Pauli-covariant SIC fiducial (exists only N = 1, 3: Hoggar lines).

Violated fraction lower bound for the three families (R / C / H = Dyson threefold way):

    complex  W(2N-1,2):  phi_C(D) = 1/2 - sqrt(D+1)/(D+2)
    quatern. Q^-(2N-1,2): phi_H(D) = phi_C(D)
    real     Q^+(2N-1,2): phi_R(D) = phi_C(D/2)

## Numbers (verified numerically in scratch prototypes, 2026-11-09)

| config | pts | lines | known d | old LB | our LB | UB (lit.) |
|---|---|---|---|---|---|---|
| W(3,2) doily | 15 | 15 | 3 | 3 | 2 | 3 |
| Q+(3,2) Mermin-Peres grid | 9 | 6 | 1 | 1 | 1 | 1 |
| W(5,2) | 63 | 315 | 63 | 63 | **63 tight** | 63 |
| Q+(5,2) | 35 | 105 | 21 | 21 | 14 | 21 |
| Q-(5,2) | 27 | 45 | 9 | 9 | **9 tight** | 9 |
| W(7,2) | 255 | 5355 | open | 1071 | **1451** (1455 via Q- averaging) | 1575 |
| Q+(7,2) | 135 | 1575 | 315 | 315 | **315 tight** | 315 |
| Q-(7,2) | 119 | 1071 | open | 215 | **291** | 315 |
| W(9,2) | 1023 | 86955 | open | 17391 | **28786** | 31479 |
| Q+(9,2) | 527 | 23715 | open ("=4743?") | 4743 | **6426** | 6975 |
| Q-(9,2) | 495 | 19635 | open | 3927 | (compute) | 7087 |
| W(11,2) | 4095 | 1396395 | open | 279279 | ~527621 | 553140 |
| W(13,2) | 16383 | 22362795 | open | 4472559 | ~9227604 | 9406024 |

* Hoggar fiducial psi = (-1+2i,1,1,1,1,1,1,1)/sqrt(12): all 63 Pauli expectations are +-1/3; sign pattern
  violates exactly 63 lines; violated lines form a generalized hexagon of order (2,2) (63 pts, 3 per point,
  incidence graph diameter 6, girth 12). F = I + A has spectrum {22, -2 x7}.
* Same sign pattern restricted to Q-(5,2): 9 violated; A has spectrum {9,9,-3 x6}. Restricted to Q+(5,2): 21.
* Realified Hoggar (C^8 -> R^16) is flat (1/3) on all 135 real 4-qubit Paulis, zero elsewhere; its sign
  pattern violates exactly 315 lines of Q+(7,2).
* Sign power iteration (psi -> f = sign<P> -> top eigenvector of A_f) + 1-flip annealing reaches
  1575 (W(7,2)), 315 (Q-(7,2)), 315 (Q+(7,2)) in seconds. Known 1575 solution has F spectrum
  {22 + 16 sqrt6, 22 - 16 sqrt6, -2 x14}.
* Pure-state cubic identity: sum_lines s p_u p_v p_w = (D-1)(D-2)/6 for every pure state (p = Pauli vector).

## "5/17 trio"
UBs for W(7,2), Q-(7,2), Q+(9,2) are all exactly 5/17 of the lines; our LB fraction is the same number
0.270939 = 1/2 - sqrt(17)/18 for all three. Implications chain (averaging over sub-configurations):
d(Q-(7,2)) = 315  =>  d(W(7,2)) = 1575  =>  d(Q+(9,2)) = 6975.

## Literature (checked 2026-11-09)

* Cabello, PRA 82, 032110 (2010), arXiv:1002.3135 - claimed d(n) = #negative contexts (Lemma 3) and hence
  exponentially growing violation; Lemma 3 is false at n = 3 (true d = 63, not 90).
* de Boutray, Holweck, Giorgetti, Masson, Saniga, J. Phys. A 55 475301 (2022), arXiv:2105.13798 - contextuality degree.
* Muller, Saniga, Giorgetti, de Boutray, Holweck, MSCS 34 (2024), arXiv:2305.10225 - d(W(5,2)) = 63, hexagon.
* Muller, Saniga, Giorgetti, Holweck, Kelleher, J. Phys. A 58 215302 (2025), arXiv:2407.02928 - heuristic UBs
  N = 4..7 (1575, 31479, 553140, 9406024); LB (4^N-1)(4^(N-1)-1)/15 = L/5.
* Saniga, Holweck, Kelleher, Muller, Giorgetti, Quantum 9, 1601 (2025), arXiv:2312.07738 - hexagons govern 3-qubit contextuality.
* Muller, Giorgetti, J. Math. Phys. 66, 082203 (2025), arXiv:2410.14463 - hypergram.
* Li, Gupta, Ganesh, arXiv:2610.26465 (19 Oct 2026) - d(Q+(7,2)) = 315 (doily averaging, Lean 4), 240 optimal
  sets ~ DW(5,2); open problems: (1) 215<=d(Q-(7,2))<=315, 1071<=d(W(7,2))<=1575; (2) is d(Q+(9,2)) = 4743?;
  (4) is d(Q+) = L/5 whenever 5 | L?  "open question is which of them have a violated fraction strictly above 1/5".
* Muller, Saniga, arXiv:2609.19862 (17 Sep 2026) - record eps = 2d/|H| = 0.707; "whether eps tends to a limit or to 1 ... is open".
* Zhao, Liew, Ho, Liu, Bulchandani, arXiv:2512.16654 - stabilizer-testing games, classical value -> 1/2 exponentially (state-dependent).
* Frembs, arXiv:2608.11993 - frame functions on n-qubit Pauli group (different question).
* Stacey, arXiv:1609.03075 - Hoggar lines; QBic equation (cubic purity condition); fiducial (-1+2i,1,...,1).
* Godsil, Roy (2009) - Pauli-covariant SICs only for N = 1, 3.  Zhu - Hoggar doubly transitive.
* Cuffaro, Fuchs, arXiv:2412.21083 - WH SIC fiducials maximise stabilizer entropy ("maximal magic").
* Howard, Campbell PRL 118, 090501 (2017) - stabilizer norm.

## Stack facts (from the 2026-11-09 audit; label truthfully)
* Moonlab v1.2.1: classical state-vector simulator; prebuilt WASM at mirrors/moonlab/docs/moonlab.wasm (+ moonlab.js glue);
  qubit 0 = LSB; uint64 args are BigInt.
* quantum_rng: classical "quantum-inspired" mixer; seeded stream is libm dependent -> pin the build.
* QGTL: only the diffgeo_* kernels in src/quantum_geometric/distributed/differential_geometry.c are verified.
* Eshkol v1.3.6-evolve at Z:\Tools\eshkol\current\bin\eshkol-run.exe (-r file.esk).

## Lean plan
Model: V = (Fin N -> ZMod 2) x (Fin N -> ZMod 2); Weyl W(a,c)[x,y] = [x = y + a] * eps(c . y);
P = i^k W with k = #{i : a_i = c_i = 1}.  Lemmas: W_u W_v = eps(c_u . a_v) W_{u+v}; tr W = D [u = 0]; P Hermitian.
Analytic: for reals with sum 0 and sum of squares n m: sum of cubes <= n m (n-2) a/(n-1) where a^2 = (n-1) m.
Toolchain: Lean v4.35.0 + Mathlib v4.35.0.

## Status log
* 2026-11-09 Lean 4.35.0 + Mathlib v4.35.0 (56a005855e) installed via elan 4.2.4; project at `lean/` (build through
  `subst H:` drive to avoid the bracket path).  ALL of the following compile, axioms = [propext, Classical.choice, Quot.sound]:
  `Moment.lean` (sum_cube_le, trace_pow_eq_sum_eigenvalues_pow, trace_cube_le), `Pauli.lean` (weyl, pauli, tau,
  context_product, pauli_comm, traces), `Bound.lean` (flags, beta6, opA, trace_opA_cube, **hoggar_bound**),
  `Counting.lean` (violated, beta6_eq_card, card_flags_all, four_qubit_violated, violatedLines, four_qubit_contexts >= 1451),
  `Corollaries.lean` (full_space_bound, full_space_fraction, three_qubit_contexts >= 63, five_qubit_contexts >= 28786),
  `Quadric.lean` (realPoints, card_realPoints, card_flags_real, four_qubit_hyperbolic_contexts >= 315,
  five_qubit_hyperbolic_contexts >= 6426).
* Engine `src/hoggar.c` (table / exhaust2 / lines / verify / search / falsify) built to `build/hoggar.exe`; annealing with
  quantum_rng reproduces 1575, 315, 315 (N=4 f,h,e) and 31479, 6975, 7087 (N=5 f,h,e) = literature upper bounds.
  Witness files in `data/witness/`.
* TODO: Moonlab experiment, QGTL kernel run, Eshkol cross-check, Python structure analysis + figures, Lean witness (N=3)
  and Kramers refinement, falsification suite, paper, GitHub push + Pages.

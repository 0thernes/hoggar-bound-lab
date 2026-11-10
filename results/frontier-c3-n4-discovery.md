# Four-qubit C3: a reproducible cospectral carrier collision

Date: 2026-11-09. This is an exact finite witness for the four-qubit C3
instance of the failure proposed in Jonah's Conjecture E, not a proof for
every dimension or every case in that conjecture. Jonah's earlier note
reports C3 failure for three qubits and leaves higher-dimensional C3 failure
as part of Conjecture E. The precise prior-art scope is documented separately
in `results/frontier-prior-art.md` and the primary
[reach preprint](https://zenodo.org/records/23524332).

## Statement and convention

Let `P(a,c) = i^popcount(a&c) X^a Z^c`, with qubit zero the least
significant basis bit, and encode a four-qubit label by `v = a + 16*c`.
Let `Q` be all 135 nonidentity real symmetric four-qubit Paulis,
`d = Z_top` (label 128), `S = Q intersect d^perp`, and `O = Q minus S`.
There are 71 points in `S` and 64 in `O`.

For a sign carrier `f:S -> {+1,-1}`, define

```
A_f = sum(v in S) f(v) P_v,
J_f(X) = (A_f X + X A_f)/2   on span_R{P_v : v in O}.
```

The two assignments below are +1 at every section point except:

| Carrier | Negative four-qubit labels |
|---|---|
| f | 48, 102, 176, 230 |
| g | 87, 144, 176, 215 |

Both assign +1 to `d`. Their 16-by-16 carrier matrices have identical
characteristic polynomials, while their 64-by-64 completion operators have
different spectra. Thus the ordinary carrier spectrum does not determine
the completion spectrum in this four-qubit C3 configuration.

## Small exact certificate

In the `d=+1` and `d=-1` eigenspaces, each carrier is block diagonal with
8-by-8 blocks `B_+` and `B_-`. Put

```
h(x) = (x+13)(x^3 - 25x^2 - 133x + 1621).
```

Their block characteristic polynomials are:

| Carrier | plus block | minus block |
|---|---|---|
| f | `(x-3)^2 (x+5)^2 h(x)` | `(x+1)^8` |
| g | `(x+1)^4 h(x)` | `(x-3)^2 (x+1)^4 (x+5)^2` |

Multiplying either row gives the same carrier polynomial. The distinction
is the allocation of eigenvalues between the two symmetry sectors.

The completion operator is equivalent to
`(B_+ tensor I + I tensor transpose(B_-))/2` on the top-right matrix block.
Direct construction in the actual outside-Pauli basis gives

```
trace(J_f^2) = trace(J_g^2) = 2240,
trace(J_f^3) = 14976,
trace(J_g^3) = 15360.
```

Unequal cubic traces prove that the completion spectra differ. Both
completion matrices have entries in `{-1,0,1}`. If `lambda` is the largest
root of `x^3 - 25x^2 - 133x + 1621`, their largest completion eigenvalues are
`(lambda-1)/2` and `(lambda+3)/2`; the largest eigenvalues therefore differ
by exactly 2 despite equality of the carrier spectra.

The same phenomenon is visible in a short trace calculation. Both carriers
have `trace(A^3)=18336`, but

```
trace(d A_f^2) = 1120,
trace(d A_g^2) = 992.
```

For these alpha=+1, eight-dimensional blocks,
`trace(J^3) = trace(A^3) - 3 trace(d A^2)`. The unlabelled carrier spectrum
forgets this symmetry-resolved second moment.

## Independent verification and running example

`scripts/frontier_c3_extend.py` found the pair by numeric screening of
restricted sign families, followed by exact characteristic-polynomial
comparison. The first two families contained 65,536 carriers each; the
third produced the witness at candidate 1160. Search output is retained in
`results/frontier-c3-search.log`; matrices, signs, and exact coefficients
are in `results/frontier-c3-n4-pair.json`. The numerical screen is not used
as proof.

`scripts/frontier_c3_verify.py` independently constructs literal 2-by-2
Pauli matrices and their Kronecker products. It checks the exact carrier
polynomials and directly forms the Jordan action on all 64 outside Paulis.
It checks that the images remain in the outside span and that the computed
Pauli coordinates reconstruct every image exactly.

`results/frontier-c3-n4-completions.json` includes both completion matrices
and the integer change of basis `T`, whose columns are the vectorized
top-right blocks of the outside Paulis. The verifier checks

```
transpose(T) T = T transpose(T) = 8 I,
T J = L T,
L = (B_+ tensor I + I tensor transpose(B_-))/2.
```

`scripts/frontier_c3_similarity.py` supplies an additional sparse integer
conjugacy certificate. With `A=A_f`, `B=A_g`, its matrices satisfy

```
A M = M B,
M R = R M = 46656 I.
```

Consequently `M` is invertible over the rationals. This certificate avoids
reliance on a large determinant expansion. Its 16-by-16 `M` has 74 nonzero
entries. Exact matrices are in `results/frontier-c3-n4-similarity.json`.

Run the independent exact verification and the operational Eshkol demo:

```powershell
python scripts/frontier_c3_verify.py
python scripts/frontier_c3_similarity.py
python scripts/frontier_c3_integer_bounds.py
python scripts/frontier_c3_demo.py
```

The Eshkol demo generates an ordinary Eshkol program, runs Eshkol
1.3.6-evolve, and checks the two inverse identities, the intertwining
identity, and the distinct completion cubic traces using integer matrix
arithmetic. It passes. The separate bound checker follows every ordered
dot-product accumulation and scalar operation with unbounded Python
integers: the largest absolute intermediate is **408304**, which fits even
a signed 32-bit integer. The demo runs that check before invoking Eshkol.
The arithmetic bound addresses overflow, not correctness of the Eshkol
compiler. The independent Lean development is responsible for formal
kernel verification; no Lean status is asserted by this discovery report.

The final local Eshkol run returned zero with empty stderr. Its report saves
the complete command, stdout, stderr, return code, and process-local
toolchain settings. The existing LLVM 21.1.8 driver and builtins archive,
together with the existing CUDA 12.9 runtime library directory, resolve the
installation's initial missing-builtins and missing-`cudart.lib` diagnostics.
These settings apply only to the child process; no installed files or
persistent environment variables are changed. The certificate uses serial
integer operations through `eshkol-run -r`. That CLI can link and run a
temporary native executable; this run does not qualify parallel workers,
CUDA computation, or every compiler execution mode.

Assertion-based Python scripts reject optimized `python -O` execution.
The integer-bound checker instead uses explicit exceptions for every
validity gate. Eshkol results and source fingerprints are retained in
`results/frontier-c3-eshkol.json` and `results/frontier-c3-integer-bounds.json`.

## Limits of the extension search

Naively padding the same three-qubit defects by identity into larger
carriers fails the cospectrality test. A five-qubit search in a more
structured family compared all 9,045 two-sign-flip/all-plus-block carriers
against 13,965 carriers formed by moving two diagonal directions into the
minus block and flipping one plus-block sign. No collision was found in
that restricted family; see `results/frontier-c3-n5-sparse-search.json`.
This negative result excludes neither general five-qubit C3 collisions nor
an eventual all-dimension construction.

The result is mathematical and computational. No physical quantum device,
hardware entropy source, hardware speedup, contextuality-degree optimum,
or complete resolution of Conjecture E is claimed here.

# Formal audit of the four-qubit C3 spectral example

**Status: PASS.** The complete concrete example, its connection to the original Pauli model, and its spectral consequences have been checked with Lean 4.35.0 and Mathlib v4.35.0. All 42 declarations requested by `lean/C3Verification.lean` use only `propext`, `Classical.choice`, and `Quot.sound`. The six auxiliary scalar-stability declarations have the same axiom dependencies.

This is a counterexample to the strict law that the carrier spectrum determines the completion spectrum in the specified four-qubit C3 geometry. It establishes the corresponding instance of Conjecture E discussed in the companion manuscript, which predicts failure of that strict law. It is not a counterexample to Conjecture E itself.

## Exact checked statement and model

The coordinate code is `v = a + 16 c`, with four binary coordinates in each of `a,c` and qubit zero the least significant bit. `codePoint` is proved to be a bijection with the original `Pt 4` type and to preserve binary addition. The polar point is code 128. It is proved to belong to the real quadric. The code-defined section is exactly the real nonidentity Pauli points symplectically orthogonal to that polar point, and has 71 points. Its real-quadric complement has 64 points. `outsideLabel` enumerates every outside point exactly once.

The two assignments are positive except on these section labels:

- `signA`: 48, 102, 176, 230.
- `signB`: 87, 144, 176, 215.

The module proves the integral Pauli entry formula agrees with the original complex `HoggarBound.pauli` matrix whenever the code is real. The carriers are sums of those original Pauli operators with the specified signs. The completion adjacency uses the original `HoggarBound.lineSign` on commuting outside-point pairs whose binary sum lies in the section. Its integer implementation is connected to that original real-valued line sign by a proved equality. Thus the certificate concerns the actual Pauli geometry and signed-context operators, rather than an unconnected pair of integer matrices.

The main declarations in namespace `HoggarBound.C3` are:

| Declaration | Checked content |
| --- | --- |
| `four_qubit_C3_counterexample` | Existence of two valid sign assignments on the section, equal complex carrier characteristic polynomials, and real completion cubic traces 14976 and 15360. |
| `pauli_carrier_eigenvalues_eq` | Equality of Mathlib's canonical eigenvalue functions for the Hermitian complex carriers. |
| `pauli_completion_charpoly_ne` | Inequality of the actual real completion characteristic polynomials. |
| `pauli_completion_eigenvalue_multisets_ne` | Inequality of the real root multisets of those characteristic polynomials, including multiplicities. |
| `four_qubit_C3_spectral_counterexample` | A conjunction of carrier characteristic-polynomial equality and completion characteristic-polynomial/root-multiset inequalities. |

The cubic moments differ by 384. The spectral conclusion follows within Lean from the Hermitian spectral theorem and equality of eigenvalue power sums, not from a floating-point eigenvalue comparison.

## Certificate structure

`C3Data.lean` contains explicit integer matrices. `C3Geometry.lean` checks the point encoding, section and outside enumeration, assignments, Pauli entry formula, and the equality of the literal matrices to the carrier/context definitions. `C3Theorem.lean` casts and reindexes the resulting integer identities into the original complex and real operator types. `C3Spectra.lean` supplies the Hermitian trace-power and spectral consequences.

`C3Certificate.lean` kernel-checks `carrierA * intertwiner = intertwiner * carrierB` and `intertwiner * inverseNumerator = 46656 * I`. The latter identity implies a nonzero determinant; Mathlib then proves equality of carrier characteristic polynomials over the integers. Only this direction of the inverse-numerator identity is needed by the Lean proof. The independent executable checks also check the opposite product, but that extra identity is not claimed as a separate Lean theorem here.

For each completion, an explicit intermediate square is checked entry by entry, with row decomposition to control memory. The cube trace is then checked after the proved square identity is substituted. The supplied square values are therefore verified, not assumed. These closed integer facts use `decide +kernel`; no native compiler oracle, external numerical result, `sorry`, `admit`, or custom axiom appears in these modules. A source scan and the declaration-level axiom report both support that boundary.

## Execution evidence and resources

The pinned compiler reports Lean 4.35.0, Windows x86-64 GNU, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. The dependency manifest pins Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The successful local checks were:

- An initial Lake build of `C3Data`.
- A clean Lake build of `C3Geometry`, with 212 seconds reported for that module.
- A direct source check of `C3Certificate` with an explicit `-o` output path. It returned exit code zero and no compiler output, and wrote its 13,938,208-byte `.olean`.
- Direct source checks of `C3Theorem` and `C3Spectra`, each returning zero and writing its `.olean`; the spectral wrapper took 15.938 seconds in its captured subprocess record.
- `lake env lean C3Verification.lean`, returning zero, followed by the parser enforcing all 42 expected declarations and the standard axiom allowlist.
- A fresh Lake build of `Stability`, reporting 12 seconds, and the separate six-declaration axiom audit.

The successful certificate process ran from 15:42:27.986 to 16:43:21.579 on 2026-11-09, UTC-08:00: approximately 60.9 minutes elapsed and 3523.703 CPU seconds. Windows reported a peak working-set counter of 7,741,747,200 bytes and a peak paged-memory counter of 12,402,831,360 bytes in the final sampled process history. The latter is relevant to committed memory; the smaller working-set number should not be treated as the entire memory requirement. These are local observations, not a portable runtime guarantee. Sequential checks on a machine with at least 16 GB memory are appropriate. The hosted CI uses timed sequential builds and retains its own resource evidence.

The direct certificate check was launched through a persistent tool session without a file redirect. Its exact successful return, empty compiler output, invocation and independently collected process exit/CPU timestamps are retained in `frontier-c3-lean-certificate.log` and `frontier-c3-lean-certificate-process.json`. The other final logs capture subprocess output directly. Earlier incomplete development runs and ignored performance probes are not presented as verification results.

Evidence files in `results/`:

- `frontier-c3-lean-geometry.log`
- `frontier-c3-lean-certificate.log` and `frontier-c3-lean-certificate-process.json`
- `frontier-c3-lean-theorem.log`
- `frontier-c3-lean-spectra.log` and `frontier-c3-spectra-check.json`
- `frontier-c3-lean-axioms.log` and the parsed `frontier-c3-axioms.json`
- `frontier-c3-lean-source-sha256.json`
- `stability-lean-build.log`, `stability-lean-axioms.log`, and `stability-axioms.json`

The source manifest hashes 21 source/configuration files, using both exact local bytes and LF-normalized bytes for cross-platform comparison. All 12 files from the earlier general-bound/witness audit still have exactly the same raw hashes. In particular, the original Pauli and real-quadric definitions and integer-line-sign bridge were unchanged during this extension. Unowned concurrent work such as `FlatData`, `Saturated`, and `MaskConfig` is outside this audit.

## Reproduction

From the repository's `lean/` directory, install the pinned toolchain and fetch the pinned Mathlib cache. Execute the following builds separately so the substantial finite checks run sequentially:

```sh
lake build HoggarBound.C3Data
lake build HoggarBound.C3Certificate
lake build HoggarBound.C3Geometry
lake build HoggarBound.C3Theorem
lake build HoggarBound.C3Spectra
lake env lean C3Verification.lean
lake build HoggarBound.Stability
lake env lean StabilityVerification.lean
```

The isolated modules are deliberately explicit targets; the original root library import is not used as a substitute for these checks. The checked Windows session used the existing `H:` mapping for the repository to avoid bracket/space path issues; it did not change that mapping. Local direct checks wrote outputs under `.lake/build/lib/lean/HoggarBound/`, so later imports used the just-checked proof artifacts without repeating the expensive finite arithmetic merely to create an output file. Clean CI builds independently reconstruct the targets from source.

## Limits

The formal artifact proves the specified finite spectral failure. It does not establish every case or dimension of Conjecture E, an exact binary completion optimum, a classification of all cospectral carriers, or historical priority.

The displayed factored carrier polynomial, the block/Jordan formulas used in the manuscript's ordinary proof, the exact largest-eigenvalue gap of two, and the continuous-relaxation gap of 32 have separate algebraic and executable evidence; they are not additional conclusions of this 42-declaration Lean audit. The proof does not certify Python, C, JavaScript, Eshkol, Moonlab, QGTL, QRNG, compiler correctness, or physical quantum hardware. Those systems require their own tested claims and are discussed separately.

The auxiliary `Stability.lean` result concerns real scalar spectra satisfying specified moment hypotheses. Its six audited lemmas include an explicit bound on distance to an extremal two-level spectrum. The matrix/Frobenius and Pauli-coordinate interpretations in `stability-theory.md` remain ordinary mathematical derivations, not additional Lean declarations. No novelty claim follows from checking these proofs.

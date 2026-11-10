# Independent C3 certificate review

Reviewed the four-qubit C3 manuscript, `C3Data.lean`, `C3Geometry.lean`,
`C3Certificate.lean`, `C3Theorem.lean`, and `C3Spectra.lean`. No sign, encoding, matrix-data,
normalization, or scope error was found in the inspected mathematical
certificate. The accompanying JSON records the exact source hashes; this
data audit is distinct from the source-build evidence described below.

Run `python scripts/frontier_c3_certificate_audit.py` to reproduce the data
audit. It constructs literal four-qubit tensors and uses arbitrary-precision
integer arithmetic for all certificate products. The run checked:

- All 135 real Pauli entry formulas against literal tensor products, with
  the least significant bit at the rightmost factor.
- Every one of the 64 outside labels, including its order.
- Both full 16 by 16 Lean carrier matrices against the two fixed four-negative
  sign assignments printed in the paper.
- Both full 64 by 64 Lean completion matrices against all 1120 signed outside
  contexts, with each sign obtained from an actual Pauli product.
- The printed common characteristic polynomial; cubic traces 14976 and
  15360; the integer intertwiner; and both scaled inverse identities.

The geometric connection is explicit in the current Lean source. The
`C3Geometry` definitions select the actual real Pauli section and its complete
outside complement. `realPauliCode_cast` relates its integer entry formula to
the project's complex Pauli operators. `C3Theorem` casts and reindexes the
carriers, relates the completion matrices to the existing Pauli context sign,
and states the result for those actual operators. Its final theorem asserts
carrier characteristic-polynomial equality and unequal completion cubic
moments. `C3Spectra` completes the spectral deduction using Mathlib's
Hermitian spectral theorem: the actual carriers have equal canonical real
eigenvalue lists; the actual completions have different characteristic
polynomials, canonical eigenvalue lists, and real eigenvalue multisets.
The multiset statement retains algebraic multiplicities. Completion
Hermitian symmetry is proved structurally from symmetric point addition and
the Pauli context-sign swap law, without another finite matrix calculation.
The exact maximum-eigenvalue gap and continuous-relaxation gap remain
paper-level algebraic deductions, not claims covered by these Lean theorem
statements. The printed characteristic-polynomial factorization is also
outside the formal statements, which prove equality of the two polynomials.

The paper's completion normalization is correct: each context contributes
twice to the quadratic form, so the number of violated outside contexts is
`560 - y^T Lambda y / 4`. On the sphere of squared norm 64, this yields
`560 - 16 lambda_max`. The maximum-eigenvalue difference 2 therefore gives
a relaxation difference 32. The manuscript correctly refrains from claiming
the same difference for binary optima. The four negative Pauli words and
numeric labels agree with the printed tensor convention.

The literature and novelty language is appropriately bounded: the result is
the four-qubit C3 instance of the failure predicted by Jonah's Conjecture E,
not a counterexample to that conjecture or a resolution for every dimension.
The manuscript attributes the Jordan and block-spectrum mechanisms, and
does not claim absolute historical priority, hardware evidence, a new
contextuality degree, or a statistical meta-analysis.

**Observed spectral source check:** the direct Lean 4.35.0 check of
`HoggarBound/C3Spectra.lean`, importing the completed `C3Theorem` artifact,
returned zero with empty stdout and stderr in 15.938 seconds. The source did
not change during the check, and the resulting `.olean` was written. See
`frontier-c3-lean-spectra.log` and `frontier-c3-spectra-check.json` for the
exact command, source hash, dependency artifact hash, and return code.
The consolidated axiom report is a separate publication requirement;
the manuscript should retain the precise formal boundaries stated above.

## Eshkol execution qualification

The initial default environment produced valid serial results together with
missing compiler-rt and unresolved parallel-worker diagnostics. The narrowly
scoped repair points only the child process at the existing LLVM 21.1.8
driver/builtins and CUDA 12.9 runtime library directory. The final run returns
0, produces all expected exact results, and has empty stderr. The runner now
records the command, return code, separate stdout/stderr, and process-local
settings in `frontier-c3-eshkol.json`; it writes this evidence even on failure.
No installed Eshkol files or persistent environment settings were modified.

The tested operation is serial integer verification through `eshkol-run -r`.
The installed CLI can link and run a temporary native executable, so the
result is not labelled as exclusively JIT execution. It invokes neither GPU
nor parallel-worker APIs and does not qualify those execution modes. The
independent arithmetic bound is 408304 for every product and ordered
accumulation in the generated certificate, below even signed 32-bit capacity.
That bound addresses arithmetic overflow, not compiler correctness.

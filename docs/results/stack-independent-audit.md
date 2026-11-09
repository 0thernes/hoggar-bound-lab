# Independent Tsotchke integration audit

Date: 2026-11-09. Reproduce from the repository root:

```powershell
python scripts/stack_audit.py
```

Machine-readable results are in `results/stack_audit.json`; Eshkol's raw
output is in `results/stack_eshkol.log`. The audit raises an exception on a
failed assertion. An unavailable optional Eshkol installation is explicitly
reported as unavailable. The recorded run used GCC 16.1.0 (MinGW UCRT),
Python 3.9.13, NumPy 2.0.2, Node 25.8.2, and Eshkol 1.3.6-evolve.

## Verified results

- **QGTL:** compiled the vendored differential-geometry C translation unit
  into a shared library and invoked its Fubini-Study and Berry-curvature
  kernels through ctypes. Independent 2-by-2 Pauli matrices and Kronecker
  products generate the Hoggar state's 63 tangent vectors. Metric error
  versus NumPy is at most `1.39e-17`; curvature error is at most `5.56e-17`.
  The 63-by-63 real metric has rank 14, fourteen eigenvalues within `1e-12`
  of 1, and every diagonal entry within `1e-12` of `2/9`.
- **Metric/context relation:** actual dense matrix commutators classify
  1,008 anticommuting pairs, 756 satisfied commuting pairs, and 189 violated
  commuting pairs. On the commuting pairs, the test `abs(g_uv) > 1/12`
  agrees with violation in all cases; each violated context contributes
  three pairs, recovering 63 contexts. This checks the numerical relation;
  it is not a formal proof of a general theorem or a novelty determination.
- **Gauge and random checks:** adding pure phase derivatives `i alpha_u psi`
  preserves the QGTL outputs to `3.50e-15`. Twenty independently generated
  normalized states and derivative arrays agree with the NumPy reference to
  `7.11e-15`. This audits two kernels only, not the full QGTL library.
- **QRNG:** independently rebuilt the legacy seeded byte-stream wrapper.
  Two 4,096-byte runs at seed 20261109 match, and seed 20261110 differs.
  Stream SHA-256 is
  `fe1bd36a75fe8bdc1562d524dcba7865d79251d97737c78bb24df5c3293b3e05`.
  This is a software determinism check, not an entropy-quality claim.
- **Eshkol:** independently executed exact integer rounding certificates
  for full-space lower bounds 63, 1451, and 28786 (N=3,4,5) and real-quadric
  lower bounds 315 and 6426 (N=4,5). Each certificate checks both the allowed
  parity-compatible beta and the excluded next value. Also checked the
  Hoggar spectrum `(21,-3,...,-3)` against the second/cubic trace identities.
- **Moonlab:** independently executed an unchanged runner snapshot in
  `build/stack_moonlab_run`, with an independently rebuilt QRNG wrapper and
  copied pinned Moonlab distribution. Assertions check:
  Pauli expectation error below `1e-12`, repeat-measurement consistency,
  Hoggar witness 63/315, realified witness 315/1575, and all 17,055 ideal
  context trials agreeing with the expected product sign. The isolated run
  cannot overwrite the shared runner's generated files. Its exact source,
  result, and WASM hashes are captured in the JSON; raw outputs are retained
  in `results/stack_moonlab_run.json` and `results/stack_moonlab_run.log`.

## Provenance and review notes

All vendored source/JS/license files match the pinned upstream commits after
line-ending normalization; Moonlab WASM matches byte-for-byte. The only local
compatibility shim is QGTL's explicitly labeled empty `stub/cblas.h`. See the
three `third_party/*/PROVENANCE.md` files for commits and file blob hashes.

The following source-review notes concern the shared experiment runner as
observed during this audit. Items 2 and 3 were subsequently repaired by
targeted patches; the original findings remain recorded for traceability:

1. Moonlab's `five_sigma` field is five times a worst-case binomial standard
   error, used on a seeded software simulation. It is not a demonstrated
   calibrated significance test, p-value, physical observation, or
   noncontextuality loophole analysis. The paper should describe these as
   simulated success frequencies and explicitly qualify any margin.
2. **Fixed:** `src/qgt_hoggar.c` originally printed `|F| = 1/6` in both runs
   even though its second run correctly compared against zero. The realified
   label now says `|F| = 0`; the comparison logic remains unchanged. The
   rerun is recorded in `results/independent-qgt-fixed.log`.
3. **Fixed:** the QGTL and main engine witness readers originally used
   unbounded `%s` conversions and incomplete hex length/type validation.
   Both now use `src/witness_io.h`, a bounded streaming reader that checks
   header numbers, geometry compatibility, exact full assignment length,
   hex digits, and absence of trailing nonwhitespace data. Uppercase hex and
   trailing whitespace are accepted. Same-N full-space assignments may
   still be restricted to either quadric, including search seed files;
   partial assignments cannot be expanded to full space or transferred to
   the other quadric. The header violation count is metadata and is checked
   for numeric validity and the full-space maximum; actual violations are
   independently recomputed in the requested geometry.
4. The Moonlab wrapper accesses a pinned WASM state-structure layout directly;
   it should not be silently upgraded to a different Moonlab artifact.

The engine CLI now validates its supported N=2..7 range before any bit shift,
accepts only exact `f`, `h`, or `e` type arguments, checks unsigned integer
syntax and range, requires positive restarts/trials, and requires finite
positive temperatures. Zero annealing steps remain valid. These checks stop
invalid shifts, uninitialized zero-restart output, and division by zero in
zero-trial reports.

`python tests/independent_input_validation.py` passed **95 cases**, including
all available trusted witness files, both QGTL fixtures, full-space
restriction and search compatibility, oversized/invalid/NUL/truncated files,
trailing data, and invalid CLI inputs. Every malformed input exited 2 rather
than crashing or succeeding. Test results and final source hashes are in
`results/independent-input-validation.json`.

After these repairs, the broader independent mathematical validator was
rerun against `build/hoggar-independent.exe`: all 12 geometries, 138,792
contexts, 8 selected witnesses, and 120 random sparse-support checks passed.
The QGTL rerun reproduced 63 and 315 violated contexts with zero metric/context
mismatches. Compiler warnings were limited to unused upstream variables and
functions; the modified lab source emitted no warnings under
`-Wall -Wextra -Wformat=2`. The shared `build/hoggar.exe` was not overwritten.

The simulation and numerical checks support implementation fidelity. The
Lean development supplies the proof of the stated mathematical lower bounds;
neither simulation nor this audit establishes a hardware quantum advantage,
an experimental discovery, universal correctness of the tool stack, or
priority over all prior literature.

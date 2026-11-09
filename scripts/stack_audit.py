"""Independent, executable audit of the narrowly used Tsotchke stack kernels.

Requires Python 3.9+, NumPy, GCC, and Node. Optional ESHKOL_RUN overrides local
Eshkol executable. This validates software behavior; it is not a physics test.
Run from any directory: python scripts/stack_audit.py
"""
import ctypes as ct
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "build"
RESULTS = ROOT / "results"
BUILD.mkdir(exist_ok=True)
RESULTS.mkdir(exist_ok=True)


def run(args):
    return subprocess.run([str(a) for a in args], cwd=ROOT, text=True,
                          capture_output=True, check=True)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(value, message):
    if not value:
        raise AssertionError(message)


def qgtl_audit():
    """Call actual QGTL C kernels through ctypes; compare independent NumPy."""
    dll = BUILD / ("stack_diffgeo.dll" if os.name == "nt" else "stack_diffgeo.so")
    cmd = ["gcc", "-O2", "-std=gnu11", "-shared", "-fPIC",
           "-Ithird_party/qgtl/include", "-Ithird_party/qgtl/stub",
           "third_party/qgtl/src/quantum_geometric/distributed/differential_geometry.c",
           "-o", dll, "-lm"]
    run(cmd)
    if os.name == "nt" and hasattr(os, "add_dll_directory"):
        # MinGW's runtime may be adjacent to gcc, not on the Python DLL path.
        dll_search = os.add_dll_directory(str(Path(shutil.which("gcc")).parent))
    lib = ct.CDLL(str(dll))
    lib.diffgeo_engine_create.restype = ct.c_void_p
    lib.diffgeo_engine_destroy.argtypes = [ct.c_void_p]
    args = [ct.c_void_p, ct.c_void_p, ct.c_size_t, ct.c_void_p,
            ct.c_size_t, ct.c_void_p]
    for name in ["diffgeo_compute_fubini_study", "diffgeo_compute_berry_curvature"]:
        fn = getattr(lib, name)
        fn.argtypes = args
        fn.restype = ct.c_bool
    engine = lib.diffgeo_engine_create()
    require(bool(engine), "QGTL engine creation failed")

    def kernels(state, deriv):
        state = np.ascontiguousarray(state, dtype=np.complex128)
        deriv = np.ascontiguousarray(deriv, dtype=np.complex128)
        m = deriv.shape[0]
        g, f = np.zeros((m, m)), np.zeros((m, m))
        for name, out in [("diffgeo_compute_fubini_study", g),
                          ("diffgeo_compute_berry_curvature", f)]:
            ok = getattr(lib, name)(engine, state.ctypes.data, state.size,
                                    deriv.ctypes.data, m, out.ctypes.data)
            require(ok, name + " returned false")
        return g, f

    def direct(state, deriv):
        overlaps = deriv.conj() @ state
        q = deriv.conj() @ deriv.T - np.outer(overlaps, overlaps.conj())
        return q.real, -2 * q.imag

    # Tensor products are constructed directly from 2x2 matrices. Qubit zero
    # is the least significant bit, matching the engine's public encoding.
    one = np.eye(2, dtype=np.complex128)
    x = np.array([[0, 1], [1, 0]], dtype=np.complex128)
    y = np.array([[0, -1j], [1j, 0]], dtype=np.complex128)
    z = np.diag([1, -1]).astype(np.complex128)
    paulis = []
    for v in range(1, 64):
        a, c = v & 7, v >> 3
        p = np.array([[1]], dtype=np.complex128)
        for j in reversed(range(3)):
            p = np.kron(p, {(0, 0): one, (1, 0): x,
                            (1, 1): y, (0, 1): z}[(a >> j & 1, c >> j & 1)])
        paulis.append(p)
    paulis = np.array(paulis)
    psi = np.ones(8, dtype=np.complex128)
    psi[0] = -1 + 2j
    psi /= np.sqrt(12)
    deriv = -0.5j * (paulis @ psi)
    g, f = kernels(psi, deriv)
    g0, f0 = direct(psi, deriv)
    gerr = float(np.max(np.abs(g-g0)))
    ferr = float(np.max(np.abs(f-f0)))
    require(max(gerr, ferr) < 1e-12, "QGTL differs from direct inner products")
    eig = np.linalg.eigvalsh(g)
    require(np.max(np.abs(eig - np.r_[np.zeros(49), np.ones(14)])) < 1e-12,
            "Unexpected real tangent metric spectrum")
    require(np.max(np.abs(np.diag(g)-2/9)) < 1e-12, "Hoggar metric diagonal")
    # Classify the metric using actual dense matrix commutators and expectations,
    # independently of the C runner's bit-parity line-sign implementation.
    signs = np.sign(np.einsum('i,vij,j->v', psi.conj(), paulis, psi).real)
    categories = {"anticommuting": 0, "commuting_satisfied": 0, "commuting_violated": 0}
    metric_context_mismatches = 0
    for u in range(63):
        for v in range(u+1, 63):
            uv = paulis[u] @ paulis[v]
            if not np.allclose(uv, paulis[v] @ paulis[u], atol=1e-12):
                categories["anticommuting"] += 1
                continue
            # <P_u P_v> = s f(u xor v)/3 at the Hoggar fiducial.
            sat = signs[u] * signs[v] * np.vdot(psi, uv @ psi).real > 0
            categories["commuting_satisfied" if sat else "commuting_violated"] += 1
            metric_context_mismatches += int((abs(g[u, v]) > 1/12) == sat)
    require(categories == {"anticommuting": 1008, "commuting_satisfied": 756,
                           "commuting_violated": 189}, "Unexpected metric pair counts")
    require(metric_context_mismatches == 0, "Context signs and metric disagree")
    # Pure gauge derivatives i alpha_i psi must vanish after projection.
    alpha = np.linspace(-2, 2, 63)
    gauge_g, gauge_f = kernels(psi, deriv + 1j * alpha[:, None] * psi)
    gauge_error = float(max(np.max(np.abs(g-gauge_g)), np.max(np.abs(f-gauge_f))))
    require(gauge_error < 1e-12, "QGTL failed local phase gauge invariance")
    rng = np.random.default_rng(8614)
    random_error = 0.0
    for _ in range(20):
        state = rng.normal(size=8) + 1j*rng.normal(size=8)
        state /= np.linalg.norm(state)
        tangents = rng.normal(size=(5, 8)) + 1j*rng.normal(size=(5, 8))
        qg, qf = kernels(state, tangents)
        dg, df = direct(state, tangents)
        random_error = max(random_error, float(np.max(np.abs(qg-dg))),
                           float(np.max(np.abs(qf-df))))
    require(random_error < 1e-12, "QGTL random-state mismatch")
    lib.diffgeo_engine_destroy(engine)
    return {"status": "pass", "kernels": ["diffgeo_compute_fubini_study",
              "diffgeo_compute_berry_curvature"], "dimension": 8, "parameters": 63,
            "metric_diagonal": float(g[0, 0]), "metric_rank_tolerance_1e_10": int(sum(eig>1e-10)),
            "metric_nonzero_eigenvalues": eig[eig>1e-10].tolist(),
            "max_metric_reference_error": gerr, "max_curvature_reference_error": ferr,
            "hoggar_pair_categories": categories,
            "metric_context_mismatches": metric_context_mismatches,
            "max_phase_gauge_error": gauge_error, "random_cases": 20,
            "max_random_reference_error": random_error,
            "berry_curvature_convention": "F_ij = -2 Im Q_ij",
            "scope": "Normalized pure-state derivative kernels only; no distributed/GPU or full-library validation",
            "binary_sha256": sha(dll), "build_command": [str(a) for a in cmd]}


def qrng_audit():
    exe = BUILD / ("stack_qrng.exe" if os.name == "nt" else "stack_qrng")
    run(["gcc", "-O2", "-std=gnu11", "src/qrng_stream.c",
         "third_party/quantum_rng/src/quantum_rng/quantum_rng.c",
         "-Ithird_party/quantum_rng/src/quantum_rng", "-o", exe, "-lm"])
    a = bytes.fromhex(run([exe, "20261109", "4096"]).stdout)
    b = bytes.fromhex(run([exe, "20261109", "4096"]).stdout)
    c = bytes.fromhex(run([exe, "20261110", "4096"]).stdout)
    require(len(a) == 4096 and a == b and a != c, "QRNG seeded stream failed")
    return {"status": "pass", "classification": "Classical quantum-inspired software mixer",
            "seed": 20261109, "bytes": len(a), "same_build_reproducible": a == b,
            "different_seed_differs": a != c, "stream_sha256": hashlib.sha256(a).hexdigest(),
            "binary_sha256": sha(exe), "scope": "No hardware entropy or statistical/cryptographic certification"}


def eshkol_audit():
    exe = os.environ.get("ESHKOL_RUN") or shutil.which("eshkol-run")
    if not exe and os.name == "nt":
        exe = r"Z:\Tools\eshkol\current\bin\eshkol-run.exe"
    if not exe or not Path(exe).is_file():
        return {"status": "unavailable", "instruction": "Set ESHKOL_RUN to the Eshkol executable"}
    ver = run([exe, "--version"]).stdout.strip()
    res = run([exe, "-r", "scripts/stack_check.esk"])
    (RESULTS/"stack_eshkol.log").write_text(res.stdout + res.stderr, encoding="utf-8")
    parsed = json.loads(next(line for line in res.stdout.splitlines() if line.startswith('{')))
    require(parsed["pass"], "Eshkol exact arithmetic checks failed")
    return {"status": "pass", "version": ver, "checks": parsed,
            "executable_sha256": sha(exe), "scope": "Integer rounding certificates and Hoggar spectral moment equality"}


def moonlab_audit():
    # Execute an unchanged source snapshot in our own directory so generated
    # JSON/witnesses cannot collide with the independently developed runner.
    src = ROOT/"src/moonlab_experiment.mjs"
    if not src.exists():
        return {"status": "unavailable", "reason": "src/moonlab_experiment.mjs not present"}
    isolated = BUILD/"stack_moonlab_run"
    paths = ["src/moonlab_experiment.mjs", "third_party/moonlab/moonlab.js",
             "third_party/moonlab/moonlab.wasm", "third_party/moonlab/LICENSE",
             "data/witness/n4_f.txt"]
    for rel in paths:
        target = isolated/rel
        target.parent.mkdir(exist_ok=True, parents=True)
        shutil.copyfile(ROOT/rel, target)
    (isolated/"build").mkdir(exist_ok=True)
    # This source snapshot uses the Windows .exe spelling on every platform;
    # POSIX executes the same binary with that suffix without requiring Wine.
    shutil.copyfile(BUILD/("stack_qrng.exe" if os.name == "nt" else "stack_qrng"),
                    isolated/"build/qrng_stream.exe")
    if os.name != "nt":
        (isolated/"build/qrng_stream.exe").chmod(0o755)
    execution = run(["node", isolated/"src/moonlab_experiment.mjs", "20261109"])
    (RESULTS/"stack_moonlab_run.log").write_text(execution.stdout+execution.stderr, encoding="utf-8")
    file = isolated/"results/moonlab_experiment.json"
    shutil.copyfile(file, RESULTS/"stack_moonlab_run.json")
    r = json.loads(file.read_text())
    e = r["experiments"]
    require(e["E0"]["max_expectation_deviation"] < 1e-12, "Moonlab Pauli oracle error")
    require(e["E0"]["repeated_measurement_consistent"], "Moonlab repeatability")
    require(e["E1"]["violated"] == 63 and e["E1"]["contexts"] == 315, "Hoggar witness")
    require(e["E2"]["violated"] == 315 and e["E2"]["contexts"] == 1575, "Realified witness")
    require(all(row["agree"] == row["contexts"] for row in e["E3"]), "Ideal context products")
    require(len(e["E3"]) == 9, "Expected nine ideal-state trials")
    return {"status": "pass", "classification": "Classical state-vector simulation",
            "mode": "Executed unchanged source snapshot in build/stack_moonlab_run",
            "ideal_context_trials": sum(row["contexts"] for row in e["E3"]),
            "result_sha256": sha(file), "runner_sha256": sha(isolated/"src/moonlab_experiment.mjs"),
            "wasm_sha256": sha(ROOT/"third_party/moonlab/moonlab.wasm"),
            "scope": "Simulation cannot establish physical contextuality or hardware quantum advantage; noisy-run sigma labels are not audited as statistical claims"}


if __name__ == "__main__":
    report = {"platform": platform.platform(), "python": sys.version.split()[0],
              "numpy": np.__version__, "gcc": run(["gcc", "--version"]).stdout.splitlines()[0],
              "node": run(["node", "--version"]).stdout.strip(),
              "qgtl": qgtl_audit(), "qrng": qrng_audit(),
              "eshkol": eshkol_audit(), "moonlab": moonlab_audit()}
    (RESULTS/"stack_audit.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(report, indent=2))

#!/usr/bin/env python3
"""
c3_exact_optima_check.py - independent exact verification of BOTH global binary
completion optima for the four-qubit C3 cospectral pair (Corollary 16):

  min_{y in {-1,+1}^64} F(signA, y) = 368   (exact; closes [347, 368] to 368)
  min_{y in {-1,+1}^64} F(signB, y) = 344   (exact; closes [330, 344] to 344)

establishing the exact binary completion separation 368 - 344 = 24.

Each lower bound is certified in pure exact integer arithmetic via a triangle-cut
SDP dual (MET-SDP) paired with a Gershgorin-shifted integer Cholesky factorization:

  M_cert = mu * I_64 - diag(d) - Q * Lambda + sum_{t} w_t * C_t
  K^2 * M_cert = L * L^T + E

where:
  - Q > 0, K > 0 are positive integers,
  - d in Z^64 has sum(d) = 0,
  - every triangle cut t = (i, j, k, s1, s2, s3, w) has distinct i, j, k in 0..63,
    w > 0, s1, s2, s3 in {-1, +1} with s1 * s2 * s3 = -1 (so y^T C_t y <= 2 for
    every y in {-1, +1}^64),
  - E is symmetric and strictly diagonally dominant (sum_{j != i} |E_{ij}| < E_{ii}
    for every i in 0..63), proving M_cert > 0 without floating point or division,
  - 64 * mu + 2 * sum(w_t) < 4 * Q * (560 - (target - 1)), forcing F(sigma, y) >= target.

Default mode verifies the frozen integer certificates in data/c3_exact_optima_certs.json
(plus both witnesses and four negative controls) in < 1 second using exact integer arithmetic.
Pass --regenerate to recompute the sparse certificates via cutting-plane MET-SDP, and
--lean to write lean/HoggarBound/C3ExactOptimaData.lean.

Writes results/c3_exact_optima_check.json.
"""
import json
import sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
CERT_PATH = ROOT / "data" / "c3_exact_optima_certs.json"
OUT_PATH = ROOT / "results" / "c3_exact_optima_check.json"
LEAN_DATA_PATH = ROOT / "lean" / "HoggarBound" / "C3ExactOptimaData.lean"

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}" + (f"   [{detail}]" if detail else ""), flush=True)
    return bool(ok)


def symp(u, v):
    return (((u & 15) & (v >> 4)).bit_count() ^ ((u >> 4) & (v & 15)).bit_count()) & 1


def is_real(v):
    return (((v & 15) & (v >> 4)).bit_count() & 1) == 0


def pauli_matrix(v):
    I = np.array([[1, 0], [0, 1]], dtype=complex)
    X = np.array([[0, 1], [1, 0]], dtype=complex)
    Z = np.array([[1, 0], [0, -1]], dtype=complex)
    Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
    a, c = v & 15, (v >> 4) & 15
    M = np.array([[1.0 + 0j]])
    for q in range(3, -1, -1):
        aq, cq = (a >> q) & 1, (c >> q) & 1
        M = np.kron(M, [I, X, Z, Y][aq + 2 * cq])
    return M


def build_c3_pair():
    d_pt = 128
    pts = [v for v in range(1, 256) if is_real(v)]
    sec = [v for v in pts if symp(v, d_pt) == 0]
    out = [v for v in pts if symp(v, d_pt) == 1]
    assert len(pts) == 135 and len(sec) == 71 and len(out) == 64
    P = {v: pauli_matrix(v) for v in pts}

    def line_sign(u, v):
        prod = P[u] @ P[v]
        w = P[u ^ v]
        idx = int(np.flatnonzero(np.abs(w) > 0.5)[0])
        val = (prod.flat[idx] / w.flat[idx]).real
        assert abs(abs(val) - 1.0) < 1e-9
        return int(round(val))

    def build_lambda(neg_set):
        sig = {v: (-1 if v in neg_set else 1) for v in sec}
        L = [[0] * 64 for _ in range(64)]
        for i, p in enumerate(out):
            for j, q in enumerate(out):
                if i != j and symp(p, q) == 0:
                    L[i][j] = sig[p ^ q] * line_sign(p, q)
        return L

    negA = {48, 102, 176, 230}
    negB = {87, 144, 176, 215}
    return out, build_lambda(negA), build_lambda(negB)


def verify_integer_certificate(name, L_mat, cert, target_F):
    """Pure Python arbitrary-precision integer verification (zero floating point!)."""
    Q = int(cert["Q"])
    mu = int(cert["mu"])
    d = [int(x) for x in cert["d"]]
    cuts = [[int(x) for x in c] for c in cert["cuts"]]
    K = int(cert["K"])
    L_chol = [[int(x) for x in row] for row in cert["L"]]

    if not (Q > 0 and K > 0 and len(d) == 64 and len(L_chol) == 64):
        return False, "invalid dimensions or scales"
    if sum(d) != 0:
        return False, f"sum(d) = {sum(d)} != 0"

    # Build M_cert in exact Python ints
    M = [[0] * 64 for _ in range(64)]
    for i in range(64):
        for j in range(64):
            M[i][j] = -Q * L_mat[i][j]
        M[i][i] += mu - d[i]

    sum_w = 0
    for c in cuts:
        if len(c) != 7:
            return False, "cut must have 7 fields (i,j,k,s1,s2,s3,w)"
        i, j, k, s1, s2, s3, w = c
        if not (0 <= i < 64 and 0 <= j < 64 and 0 <= k < 64):
            return False, "index out of range"
        if i == j or j == k or i == k:
            return False, "non-distinct triple"
        if s1 not in (-1, 1) or s2 not in (-1, 1) or s3 not in (-1, 1):
            return False, "sign not in {-1, +1}"
        if s1 * s2 * s3 != -1:
            return False, "triangle cut not frustrated (s1*s2*s3 != -1)"
        if w <= 0:
            return False, "cut weight not positive"
        sum_w += w
        M[i][j] += w * s1; M[j][i] += w * s1
        M[j][k] += w * s2; M[k][j] += w * s2
        M[i][k] += w * s3; M[k][i] += w * s3

    for i in range(64):
        if len(L_chol[i]) != i + 1:
            return False, f"row {i} of L has length {len(L_chol[i])} != {i + 1}"
        for j in range(64):
            if M[i][j] != M[j][i]:
                return False, "M_cert not symmetric"

    # Strict bound check: 64*mu + 2*sum_w < 4*Q*(560 - (target_F - 1))
    lhs = 64 * mu + 2 * sum_w
    rhs = 4 * Q * (560 - (target_F - 1))
    if not (lhs < rhs):
        return False, f"bound fails: {lhs} >= {rhs}"

    # Check K^2 * M_cert - L * L^T strictly diagonally dominant in exact ints
    K2 = K * K
    min_margin = None
    for i in range(64):
        ri = L_chol[i]
        diag = K2 * M[i][i] - sum(a * a for a in ri)
        off = 0
        for j in range(64):
            if j == i:
                continue
            rj = L_chol[j]
            m_len = i + 1 if i < j else j + 1
            dot = sum(ri[t] * rj[t] for t in range(m_len))
            e_ij = K2 * M[i][j] - dot
            off += abs(e_ij)
        margin = diag - off
        if min_margin is None or margin < min_margin:
            min_margin = margin
    if min_margin <= 0:
        return False, f"not strictly diagonally dominant (min margin = {min_margin})"
    return True, (
        f"Q={Q}, mu={mu}, cuts={len(cuts)}, sum_w={sum_w}, "
        f"{lhs} < {rhs}, K={K}, min_diagdom_margin=+{min_margin}"
    )


def regenerate_certificate(name, L_mat, target_F):
    from scipy.optimize import minimize

    L = np.array(L_mat, dtype=int)
    Lf = L.astype(float)
    B_strict = 4 * (560 - (target_F - 1))

    all_i, all_j, all_k = [], [], []
    for i in range(64):
        for j in range(i + 1, 64):
            for k in range(j + 1, 64):
                all_i.append(i); all_j.append(j); all_k.append(k)
    ALL_I = np.array(all_i, dtype=np.int32)
    ALL_J = np.array(all_j, dtype=np.int32)
    ALL_K = np.array(all_k, dtype=np.int32)
    SIGNS = [(1, 1, -1), (1, -1, 1), (-1, 1, 1), (-1, -1, -1)]

    def separate_cuts(X, top_k=250, min_viol=0.01):
        xij = X[ALL_I, ALL_J]
        xjk = X[ALL_J, ALL_K]
        xik = X[ALL_I, ALL_K]
        V = np.vstack([xij + xjk - xik, xij - xjk + xik, -xij + xjk + xik, -xij - xjk - xik])
        best_s = np.argmax(V, axis=0)
        best_v = V[best_s, np.arange(len(ALL_I))]
        idxs = np.where(best_v > 1.0 + min_viol)[0]
        if len(idxs) == 0:
            return []
        order = idxs[np.argsort(-best_v[idxs])[:top_k]]
        return [(int(ALL_I[idx]), int(ALL_J[idx]), int(ALL_K[idx]), *SIGNS[best_s[idx]]) for idx in order]

    def opt(cuts_l, d_init, u_init, beta=12.0, maxiter=250):
        m = len(cuts_l)
        ai = np.array([c[0] for c in cuts_l], dtype=np.int32)
        aj = np.array([c[1] for c in cuts_l], dtype=np.int32)
        ak = np.array([c[2] for c in cuts_l], dtype=np.int32)
        as1 = np.array([c[3] for c in cuts_l], dtype=float)
        as2 = np.array([c[4] for c in cuts_l], dtype=float)
        as3 = np.array([c[5] for c in cuts_l], dtype=float)
        x0 = np.concatenate([d_init, u_init])
        bounds = [(None, None)] * 64 + [(0.0, None)] * m

        def fg(x):
            dv = x[:64]; dv = dv - dv.mean()
            uv = x[64:]
            A = Lf.copy()
            A[np.arange(64), np.arange(64)] += dv
            if m > 0:
                np.add.at(A, (ai, aj), -uv * as1); np.add.at(A, (aj, ai), -uv * as1)
                np.add.at(A, (aj, ak), -uv * as2); np.add.at(A, (ak, aj), -uv * as2)
                np.add.at(A, (ai, ak), -uv * as3); np.add.at(A, (ak, ai), -uv * as3)
            ev, V = np.linalg.eigh(A)
            em = ev[-1]
            ex = np.exp(beta * (ev - em))
            se = ex.sum()
            lm = em + np.log(se) / beta
            w = ex / se
            P = (V * w) @ V.T
            val = 64.0 * lm + 2.0 * uv.sum()
            gd = 64.0 * np.diag(P); gd -= gd.mean()
            gu = (2.0 - 128.0 * (as1 * P[ai, aj] + as2 * P[aj, ak] + as3 * P[ai, ak])) if m > 0 else np.zeros(0)
            return val, np.concatenate([gd, gu])

        res = minimize(fg, x0, jac=True, method="L-BFGS-B", bounds=bounds, options={"maxiter": maxiter, "ftol": 1e-13})
        dv = res.x[:64]; dv -= dv.mean()
        uv = res.x[64:]
        A = Lf.copy()
        A[np.arange(64), np.arange(64)] += dv
        if m > 0:
            np.add.at(A, (ai, aj), -uv * as1); np.add.at(A, (aj, ai), -uv * as1)
            np.add.at(A, (aj, ak), -uv * as2); np.add.at(A, (ak, aj), -uv * as2)
            np.add.at(A, (ai, ak), -uv * as3); np.add.at(A, (ak, ai), -uv * as3)
        ev, V = np.linalg.eigh(A)
        em = ev[-1]
        ex = np.exp(beta * (ev - em))
        w = ex / ex.sum()
        P = (V * w) @ V.T
        bound = 64.0 * float(em) + 2.0 * float(uv.sum())
        return bound, dv, uv, 64.0 * P

    cuts_list, cuts_set = [], set()
    d = np.zeros(64)
    u = np.zeros(0)
    for rnd in range(15):
        beta = 8.0 if rnd < 3 else (20.0 if rnd < 7 else 50.0)
        bound, d, u, X = opt(cuts_list, d, u, beta=beta, maxiter=250)
        keep_idx = [idx for idx in range(len(cuts_list)) if u[idx] > 1e-4]
        cuts_list = [cuts_list[idx] for idx in keep_idx]
        u = u[keep_idx]
        cuts_set = set(cuts_list)
        if bound < B_strict - 1.5 and rnd >= 4:
            break
        new_cuts = [c for c in separate_cuts(X, top_k=250, min_viol=0.01) if c not in cuts_set]
        if not new_cuts:
            break
        cuts_list.extend(new_cuts)
        cuts_set.update(new_cuts)
        u = np.concatenate([u, np.zeros(len(new_cuts))])

    bound, d, u, _ = opt(cuts_list, d, u, beta=60.0, maxiter=400)
    for thresh in [0.005, 0.015, 0.03, 0.05, 0.08, 0.10]:
        keep = [idx for idx in range(len(cuts_list)) if u[idx] > thresh]
        if len(keep) < 20:
            break
        cl2 = [cuts_list[idx] for idx in keep]
        b2, d2, u2, _ = opt(cl2, d, u[keep], beta=60.0, maxiter=350)
        if b2 < B_strict - 0.6:
            cuts_list, d, u, bound = cl2, d2, u2, b2
        else:
            break

    for Q in [16, 32, 48, 64, 96, 128, 192, 256]:
        d_int = np.round(Q * d).astype(int)
        diff = int(d_int.sum())
        if diff != 0:
            order = np.argsort(Q * d - d_int)
            if diff > 0:
                for idx in order[:diff]:
                    d_int[idx] -= 1
            else:
                for idx in order[diff:]:
                    d_int[idx] += 1
        assert int(d_int.sum()) == 0
        w_int = np.round(Q * u).astype(int)
        cuts_fin = [list(cuts_list[idx]) + [int(w_int[idx])] for idx in range(len(cuts_list)) if w_int[idx] > 0]
        A_int = Q * L.copy()
        for i in range(64):
            A_int[i, i] += d_int[i]
        for (i, j, k, s1, s2, s3, w) in cuts_fin:
            A_int[i, j] -= w * s1; A_int[j, i] -= w * s1
            A_int[j, k] -= w * s2; A_int[k, j] -= w * s2
            A_int[i, k] -= w * s3; A_int[k, i] -= w * s3
        lmax_int = float(np.linalg.eigvalsh(A_int.astype(float))[-1])
        sum_w = sum(c[6] for c in cuts_fin)
        mu_max = (Q * B_strict - 1 - 2 * sum_w) // 64
        mu_min = int(np.floor(lmax_int)) + 1
        if mu_min <= mu_max:
            mu_num = mu_max
            M_cert = mu_num * np.eye(64, dtype=int) - A_int
            lmin = float(np.linalg.eigvalsh(M_cert.astype(float))[0])
            for K in [64, 128, 256, 512, 1024, 2048]:
                try:
                    Lc = np.linalg.cholesky(M_cert.astype(float) - 0.15 * lmin * np.eye(64))
                    Li = np.round(K * Lc).astype(int)
                    L_tri = [Li[i, : i + 1].tolist() for i in range(64)]
                    cert = dict(Q=int(Q), mu=int(mu_num), d=d_int.tolist(), cuts=cuts_fin, K=int(K), L=L_tri)
                    ok, _ = verify_integer_certificate(name, L_mat, cert, target_F)
                    if ok:
                        return cert
                except np.linalg.LinAlgError:
                    pass
    raise RuntimeError(f"Failed to regenerate integer certificate for {name} >= {target_F}")


def write_lean_data(certs):
    def emit_chunked_cuts(label, cuts, chunk_size=80):
        lines = []
        names = []
        for idx in range(0, len(cuts), chunk_size):
            part = cuts[idx : idx + chunk_size]
            cname = f"{label}Cuts_{idx // chunk_size}"
            names.append(cname)
            rows = []
            for j in range(0, len(part), 4):
                ch = part[j : j + 4]
                rows.append("  " + ", ".join(f"⟨{i}, {jj}, {k}, {s1}, {s2}, {s3}, {w}⟩" for (i, jj, k, s1, s2, s3, w) in ch))
            lines.append(f"private def {cname} : List TriCut := [\n" + ",\n".join(rows) + "\n]")
        lines.append(f"def {label}Cuts : List TriCut := " + " ++ ".join(names))
        return lines

    def emit_chunked_L(label, L_tri, chunk_size=8):
        lines = []
        names = []
        for idx in range(0, len(L_tri), chunk_size):
            part = L_tri[idx : idx + chunk_size]
            cname = f"{label}L_{idx // chunk_size}"
            names.append(cname)
            rows = ["  [" + ", ".join(str(x) for x in row) + "]" for row in part]
            lines.append(f"private def {cname} : List (List Int) := [\n" + ",\n".join(rows) + "\n]")
        lines.append(f"def {label}L : List (List Int) := " + " ++ ".join(names))
        return lines

    out = [
        "/-",
        "Generated by scripts/c3_exact_optima_check.py --lean.  Do not edit.",
        "",
        "Pure-integer MET-SDP dual certificates (frustrated triangle cuts + Gershgorin-shifted",
        "lower-triangular integer Cholesky factors) closing BOTH four-qubit C3 completion gaps",
        "to exact global binary optimality: min F(signA) = 368 and min F(signB) = 344.",
        "-/",
        "",
        "namespace HoggarBound.C3ExactOptimaData",
        "",
        "/-- A frustrated triangle cut `(i, j, k, s1, s2, s3, w)` on `{0, ..., 63}` with `s1*s2*s3 = -1` and `w > 0`. -/",
        "structure TriCut where",
        "  i : Nat",
        "  j : Nat",
        "  k : Nat",
        "  s1 : Int",
        "  s2 : Int",
        "  s3 : Int",
        "  w : Int",
        "deriving DecidableEq, Repr",
        "",
    ]
    for label, key in [("certA", "sigmaA_368"), ("certB", "sigmaB_344")]:
        c = certs[key]
        out += [
            f"def {label}Q : Int := {c['Q']}",
            f"def {label}Mu : Int := {c['mu']}",
            f"def {label}K : Int := {c['K']}",
            f"def {label}D : List Int := [{', '.join(str(x) for x in c['d'])}]",
        ]
        out += emit_chunked_cuts(label, c["cuts"])
        out += emit_chunked_L(label, c["L"])
        out.append("")
    out.append("end HoggarBound.C3ExactOptimaData")
    LEAN_DATA_PATH.write_text("\n".join(out) + "\n", encoding="utf-8", newline="\n")
    print(f"wrote {LEAN_DATA_PATH}", flush=True)


def main():
    regen = "--regenerate" in sys.argv
    emit_lean = "--lean" in sys.argv

    out, L0, L1 = build_c3_pair()
    L0_np, L1_np = np.array(L0, dtype=int), np.array(L1, dtype=int)
    check("reconstructed completion cubic traces are 14976 (sigma_0) and 15360 (sigma_1)",
          int(np.trace(L0_np @ L0_np @ L0_np)) == 14976 and int(np.trace(L1_np @ L1_np @ L1_np)) == 15360)

    # Verify both explicit binary witnesses
    witA_neg = {8, 12, 13, 14, 24, 26, 28, 30, 40, 41, 44, 45, 56, 59, 60, 63,
                90, 93, 105, 110, 123, 125, 126, 153, 155, 157, 159, 170, 171,
                174, 175, 189, 190, 217, 219, 234, 235, 255}
    witB_neg = {26, 41, 59, 63, 72, 88, 90, 104, 105, 120, 123, 153, 155, 159,
                170, 171, 175, 204, 205, 206, 217, 219, 220, 222, 234, 235, 236,
                237, 252, 255}
    yA = np.array([-1 if v in witA_neg else 1 for v in out], dtype=int)
    fA = 560 - int(yA @ L0_np @ yA) // 4
    check("binary witness for sigma_0 (signA) violates exactly 368 outside contexts", fA == 368, f"F = {fA}")
    yB = np.array([-1 if v in witB_neg else 1 for v in out], dtype=int)
    fB = 560 - int(yB @ L1_np @ yB) // 4
    check("binary witness for sigma_1 (signB) violates exactly 344 outside contexts", fB == 344, f"F = {fB}")

    if regen or not CERT_PATH.exists():
        print("Regenerating sparse pure-integer MET-SDP certificates...", flush=True)
        certA = regenerate_certificate("sigma_0 (signA)", L0, 368)
        certB = regenerate_certificate("sigma_1 (signB)", L1, 344)
        certs = {"sigmaA_368": certA, "sigmaB_344": certB}
        CERT_PATH.parent.mkdir(parents=True, exist_ok=True)
        CERT_PATH.write_text(json.dumps(certs, separators=(",", ":")), encoding="utf-8", newline="\n")
        print(f"wrote {CERT_PATH}", flush=True)
    else:
        certs = json.loads(CERT_PATH.read_text(encoding="utf-8"))

    okA, detA = verify_integer_certificate("sigmaA", L0, certs["sigmaA_368"], 368)
    check("exact pure-integer MET-SDP certificate proves min F(signA, y) >= 368 (closing [347, 368] to exact 368)",
          okA, detA)
    okB, detB = verify_integer_certificate("sigmaB", L1, certs["sigmaB_344"], 344)
    check("exact pure-integer MET-SDP certificate proves min F(signB, y) >= 344 (closing [330, 344] to exact 344)",
          okB, detB)
    check("exact global binary completion separation is 368 - 344 = 24", okA and okB and fA == 368 and fB == 344)

    # Negative controls (deliberate falsification checks)
    ok_nc1, det_nc1 = verify_integer_certificate("sigmaA_369", L0, certs["sigmaA_368"], 369)
    check("negative control 1: impossible target 369 for signA is rejected", not ok_nc1, det_nc1)
    ok_nc2, det_nc2 = verify_integer_certificate("sigmaB_345", L1, certs["sigmaB_344"], 345)
    check("negative control 2: impossible target 345 for signB is rejected", not ok_nc2, det_nc2)

    bad_cut = json.loads(json.dumps(certs["sigmaA_368"]))
    bad_cut["cuts"][0][3] = -bad_cut["cuts"][0][3]  # flips s1*s2*s3 from -1 to +1
    ok_nc3, det_nc3 = verify_integer_certificate("bad_cut", L0, bad_cut, 368)
    check("negative control 3: non-frustrated triangle cut (s1*s2*s3 = +1) is rejected", not ok_nc3, det_nc3)

    bad_L = json.loads(json.dumps(certs["sigmaB_344"]))
    bad_L["L"][10][5] += 500
    ok_nc4, det_nc4 = verify_integer_certificate("bad_L", L1, bad_L, 344)
    check("negative control 4: perturbed Cholesky entry breaks diagonal dominance and is rejected", not ok_nc4, det_nc4)

    if emit_lean:
        write_lean_data(certs)

    summary = {
        "sigmaA": {
            "exact_binary_min": 368,
            "Q": certs["sigmaA_368"]["Q"],
            "mu": certs["sigmaA_368"]["mu"],
            "K": certs["sigmaA_368"]["K"],
            "num_cuts": len(certs["sigmaA_368"]["cuts"]),
            "sum_w": sum(c[6] for c in certs["sigmaA_368"]["cuts"]),
            "detail": detA,
        },
        "sigmaB": {
            "exact_binary_min": 344,
            "Q": certs["sigmaB_344"]["Q"],
            "mu": certs["sigmaB_344"]["mu"],
            "K": certs["sigmaB_344"]["K"],
            "num_cuts": len(certs["sigmaB_344"]["cuts"]),
            "sum_w": sum(c[6] for c in certs["sigmaB_344"]["cuts"]),
            "detail": detB,
        },
        "exact_binary_gap": 24,
        "checks": {"passed": sum(1 for _, ok in CHECKS if ok), "total": len(CHECKS)},
    }
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")

    npass = sum(1 for _, ok in CHECKS if ok)
    print(f"\n{npass} of {len(CHECKS)} checks passed", flush=True)
    sys.exit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

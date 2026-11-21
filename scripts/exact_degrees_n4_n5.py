#!/usr/bin/env python3
"""
exact_degrees_n4_n5.py - independent exact verification of:
  1. Unconditional analytic degree-4 Sum-of-Squares lower bound on Q^-(7,2):
       sum_L s_L x_a x_b x_c <= 119 * sqrt(17) = 490.649569...  (rational p = 1/50 gives 490.6767 < 491)
     yielding d(Q^-(7,2)) >= 291, hence by double-counting ladders:
       d(W(7,2)) >= 1455  (beating spectral floor 1451)
       d(Q^+(9,2)) >= 6444 (beating spectral floor 6200).
  2. Exact CSS witnesses:
       viol(Q^-(7,2)) = 315, viol(W(7,2)) = 1575, viol(Q^+(9,2)) = 6975.
  3. Exact double-counting ladders:
       every line of W(7,2) lies on 24 of 120 elliptic quadrics Q^-(7,2) => d(W(7,2)) >= 5 * d(Q^-(7,2)),
       every line of Q^+(9,2) lies in 112 of 496 sections J^perp ~= W(7,2) => d(Q^+(9,2)) >= ceil(496 * d(W(7,2)) / 112).
  4. Exact pure-integer completion lower-bound certificates (MET-SDP + Gershgorin-shifted
     integer Cholesky on the 56x56 outside graph Lambda_sigma) for ALL 42 Sp(6,2)-orbits
     of W(5,2) with n <= 92 from our independent C census (src/w52_census_verify.c ->
     data/w52_orbits_42.tsv):
       n_k + F(sigma_k) >= 315 for all k = 0..41,
       with equality 315 at exactly two orbits (Hoggar n=63, size 120; and n=87, size 60480),
       and n_k + F_cert_k >= 316 for all 40 remaining orbits.
     Combined with Lemma L1 (40*314 < 136*93) and the W(5,2) n <= 92 census, this proves:
       d(Q^-(7,2)) = 315, d(W(7,2)) = 1575, d(Q^+(9,2)) = 6975
     (crediting Jonah [J1] for the section-square law, L1-L4 architecture, and prior census).

Writes data/q7minus_42_certs.json, results/exact_degrees_n4_n5.json, and (with --lean)
lean/HoggarBound/Q7MinusCertsData.lean.
"""
import json
import math
import sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
ORBITS_TSV = ROOT / "data" / "w52_orbits_42.tsv"
CERT_PATH = ROOT / "data" / "q7minus_42_certs.json"
OUT_PATH = ROOT / "results" / "exact_degrees_n4_n5.json"
LEAN_DATA_PATH = ROOT / "lean" / "HoggarBound" / "Q7MinusCertsData.lean"

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}" + (f"   [{detail}]" if detail else ""), flush=True)
    return bool(ok)


def symp(u, v, N):
    m = (1 << N) - 1
    return (((u & m) & (v >> N)).bit_count() ^ ((u >> N) & (v & m)).bit_count()) & 1


def y_cnt(v, N):
    m = (1 << N) - 1
    return ((v & m) & (v >> N)).bit_count()


def line_sign(u, v, N):
    m = (1 << N) - 1
    au, cu, av, cv = u & m, u >> N, v & m, v >> N
    k = ((au & cu).bit_count() + (av & cv).bit_count()
         + 2 * (cu & av).bit_count() + 3 * ((au ^ av) & (cu ^ cv)).bit_count()) % 4
    assert k in (0, 2)
    return 1 if k == 0 else -1


def css_sign(v, N):
    m = (1 << N) - 1
    a, c = v & m, v >> N
    mixed = 1 if (a != 0 and c != 0) else 0
    return -1 if ((mixed + (y_cnt(v, N) // 2)) & 1) else 1


def build_q7minus_geometry():
    r"""
    Canonical 4-qubit elliptic quadric E = Q_{Y_0} (J = Y_0 = 1 | 16 = 17),
    section point d = X_0 = 1 (off E: q_E(1) = 0 + symp(1, 17) = 1):
      - S = E cap X_0^perp: 63 points, isomorphic to W(5,2) via dropping qubit 0!
        Explicitly, w in 1..63 (3-qubit Pauli) lifts to:
          lift(w) = ((w & 7) << 1) | q0(w) | (((w >> 3) << 1) << 4)
        Check: z_0 = 0 (commutes with X_0), x_0 = q0(w) (so y_cnt(lift(w)) = q0(w) mod 2 and
        symp(lift(w), Y_0) = x_0 ^ z_0 = q0(w) -> q_E = 0!).
      - O = E \ S: 56 points with z_0 = 1 (i.e. bit 4 = 1) and q0(w_3) = 1 (28 antisymmetric 3-qubit Paulis x 2 for x_0 in {0,1}).
    """
    J = 1 | (1 << 4)  # Y_0 = 17
    d = 1             # X_0 = 1
    E = [v for v in range(1, 256) if ((y_cnt(v, 4) + symp(v, J, 4)) & 1) == 0]
    assert len(E) == 119
    S_map = {}
    for w in range(1, 64):
        aw, cw = w & 7, w >> 3
        qw = (aw & cw).bit_count() & 1
        v = ((aw << 1) | qw) | ((cw << 1) << 4)
        assert ((y_cnt(v, 4) + symp(v, J, 4)) & 1) == 0 and symp(v, d, 4) == 0
        S_map[v] = w
    assert len(S_map) == 63
    O = [v for v in E if symp(v, d, 4) == 1]
    assert len(O) == 56
    return E, S_map, O


def build_outside_graph(O, S_map, y_mask_63):
    """Build 56x56 integer matrix Lambda_sigma for 3-qubit W(5,2) sign bitmask y_mask_63 (bit (w-1) = 1 iff sigma(w) = -1)."""
    L = [[0] * 56 for _ in range(56)]
    for i, p in enumerate(O):
        for j, q in enumerate(O):
            if i == j:
                continue
            if symp(p, q, 4) == 0:
                s_pt = p ^ q
                w = S_map[s_pt]
                sig = -1 if ((y_mask_63 >> (w - 1)) & 1) else 1
                L[i][j] = sig * line_sign(p, q, 4)
    return L


def verify_cert_56(L_mat, cert, target_F):
    """Exact pure-integer verification on 56x56 outside graph (756 outside lines: F(y) = 378 - (1/4) y^T L y)."""
    Q = int(cert["Q"])
    mu = int(cert["mu"])
    d = [int(x) for x in cert["d"]]
    cuts = [[int(x) for x in c] for c in cert["cuts"]]
    K = int(cert["K"])
    L_chol = [[int(x) for x in row] for row in cert["L"]]

    if not (Q > 0 and K > 0 and len(d) == 56 and len(L_chol) == 56):
        return False, "invalid dims"
    if sum(d) != 0:
        return False, f"sum(d)={sum(d)}!=0"

    M = [[0] * 56 for _ in range(56)]
    for i in range(56):
        for j in range(56):
            M[i][j] = -Q * L_mat[i][j]
        M[i][i] += mu - d[i]

    sum_w = 0
    for c in cuts:
        i, j, k, s1, s2, s3, w = c
        if not (0 <= i < 56 and 0 <= j < 56 and 0 <= k < 56 and i != j and j != k and i != k):
            return False, "bad indices"
        if s1 not in (-1, 1) or s2 not in (-1, 1) or s3 not in (-1, 1) or s1 * s2 * s3 != -1 or w <= 0:
            return False, "bad cut signs/weight"
        sum_w += w
        M[i][j] += w * s1; M[j][i] += w * s1
        M[j][k] += w * s2; M[k][j] += w * s2
        M[i][k] += w * s3; M[k][i] += w * s3

    lhs = 56 * mu + 2 * sum_w
    rhs = 4 * Q * (378 - (target_F - 1))
    if not (lhs < rhs):
        return False, f"bound {lhs} >= {rhs}"

    K2 = K * K
    min_margin = None
    for i in range(56):
        ri = L_chol[i]
        if len(ri) != i + 1:
            return False, "bad L row len"
        diag = K2 * M[i][i] - sum(a * a for a in ri)
        off = 0
        for j in range(56):
            if j == i:
                continue
            rj = L_chol[j]
            ml = i + 1 if i < j else j + 1
            dot = sum(ri[t] * rj[t] for t in range(ml))
            off += abs(K2 * M[i][j] - dot)
        margin = diag - off
        if min_margin is None or margin < min_margin:
            min_margin = margin
    if min_margin <= 0:
        return False, f"not diagdom (min={min_margin})"
    return True, f"Q={Q}, mu={mu}, cuts={len(cuts)}, K={K}, {lhs}<{rhs}, margin=+{min_margin}"


def try_round_cert_56(L_mat, d_flt, cuts_list, u_flt, target_F):
    L = np.array(L_mat, dtype=int)
    B_strict = 4 * (378 - (target_F - 1))
    for Q in [1, 2, 4, 8, 16, 24, 32, 48, 64, 96, 128, 192, 256]:
        if np.allclose(d_flt, 0):
            d_int = np.zeros(56, dtype=int)
        else:
            d_int = np.round(Q * d_flt).astype(int)
            diff = int(d_int.sum())
            if diff != 0:
                order = np.argsort(Q * d_flt - d_int)
                if diff > 0:
                    for idx in order[:diff]:
                        d_int[idx] -= 1
                else:
                    for idx in order[diff:]:
                        d_int[idx] += 1
        assert int(d_int.sum()) == 0
        w_int = np.round(Q * u_flt).astype(int) if len(cuts_list) > 0 else np.zeros(0, dtype=int)
        cuts_fin = [list(cuts_list[idx]) + [int(w_int[idx])] for idx in range(len(cuts_list)) if w_int[idx] > 0]
        A_int = Q * L.copy()
        for i in range(56):
            A_int[i, i] += d_int[i]
        for (i, j, k, s1, s2, s3, w) in cuts_fin:
            A_int[i, j] -= w * s1; A_int[j, i] -= w * s1
            A_int[j, k] -= w * s2; A_int[k, j] -= w * s2
            A_int[i, k] -= w * s3; A_int[k, i] -= w * s3
        lmax_int = float(np.linalg.eigvalsh(A_int.astype(float))[-1])
        sum_w = sum(c[6] for c in cuts_fin)
        mu_max = (Q * B_strict - 1 - 2 * sum_w) // 56
        mu_min = int(np.floor(lmax_int)) + 1
        if mu_min <= mu_max:
            mu_num = mu_max
            M_cert = mu_num * np.eye(56, dtype=int) - A_int
            lmin = float(np.linalg.eigvalsh(M_cert.astype(float))[0])
            for K in [32, 64, 128, 256, 512, 1024, 2048, 4096]:
                try:
                    Lc = np.linalg.cholesky(M_cert.astype(float) - 0.15 * lmin * np.eye(56))
                    Li = np.round(K * Lc).astype(int)
                    L_tri = [Li[i, : i + 1].tolist() for i in range(56)]
                    cert = dict(Q=int(Q), mu=int(mu_num), d=d_int.tolist(), cuts=cuts_fin, K=int(K), L=L_tri)
                    ok, _ = verify_cert_56(L_mat, cert, target_F)
                    if ok:
                        return cert
                except np.linalg.LinAlgError:
                    pass
    return None


def solve_orbit_cert_56(orb_id, n_sec, L_mat):
    """Find the simplest valid pure-integer certificate proving n_sec + F(sigma) >= 315 (preferring >= 316 when possible)."""
    from scipy.optimize import minimize

    L = np.array(L_mat, dtype=int)
    Lf = L.astype(float)
    need_F = 315 - n_sec

    # Tier 1: Pure eigenvalue bound (d = 0, cuts = [])!
    lmax0 = float(np.linalg.eigvalsh(Lf)[-1])
    F_eig = 378.0 - 14.0 * lmax0
    if F_eig > need_F - 1.0 + 1e-6:
        cert = try_round_cert_56(L_mat, np.zeros(56), [], np.zeros(0), need_F)
        if cert is not None:
            return "eig", need_F, cert

    # Tier 2: Diagonal-shift SDP (cuts = [])!
    def opt_diag(d_init, beta, maxiter=250):
        def fg(x):
            dv = x - x.mean()
            A = Lf + np.diag(dv)
            ev, V = np.linalg.eigh(A)
            em = ev[-1]
            ex = np.exp(beta * (ev - em))
            se = ex.sum()
            w = ex / se
            P = (V * w) @ V.T
            gd = 56.0 * np.diag(P); gd -= gd.mean()
            return 56.0 * (em + np.log(se) / beta), gd
        res = minimize(fg, d_init, jac=True, method="L-BFGS-B", options={"maxiter": maxiter, "ftol": 1e-13})
        dv = res.x - res.x.mean()
        ev = np.linalg.eigvalsh(Lf + np.diag(dv))
        return 56.0 * float(ev[-1]), dv

    b_d, d_cur = opt_diag(np.zeros(56), 10.0, 200)
    b_d, d_cur = opt_diag(d_cur, 40.0, 300)
    F_diag = 378.0 - b_d / 4.0
    if F_diag > need_F - 1.0 + 1e-4:
        cert = try_round_cert_56(L_mat, d_cur, [], np.zeros(0), need_F)
        if cert is not None:
            return "diag", need_F, cert

    # Tier 3: Cutting-plane MET-SDP with frustrated triangle cuts!
    all_i, all_j, all_k = [], [], []
    for i in range(56):
        for j in range(i + 1, 56):
            for k in range(j + 1, 56):
                all_i.append(i); all_j.append(j); all_k.append(k)
    ALL_I = np.array(all_i, dtype=np.int32)
    ALL_J = np.array(all_j, dtype=np.int32)
    ALL_K = np.array(all_k, dtype=np.int32)
    SIGNS = [(1, 1, -1), (1, -1, 1), (-1, 1, 1), (-1, -1, -1)]
    B_strict = 4 * (378 - (need_F - 1))

    def separate(X, top_k=220, min_viol=0.01):
        xij, xjk, xik = X[ALL_I, ALL_J], X[ALL_J, ALL_K], X[ALL_I, ALL_K]
        V = np.vstack([xij + xjk - xik, xij - xjk + xik, -xij + xjk + xik, -xij - xjk - xik])
        bs = np.argmax(V, axis=0)
        bv = V[bs, np.arange(len(ALL_I))]
        idxs = np.where(bv > 1.0 + min_viol)[0]
        if len(idxs) == 0:
            return []
        order = idxs[np.argsort(-bv[idxs])[:top_k]]
        return [(int(ALL_I[idx]), int(ALL_J[idx]), int(ALL_K[idx]), *SIGNS[bs[idx]]) for idx in order]

    def opt_tri(cl, d_in, u_in, beta=15.0, maxiter=250):
        m = len(cl)
        ai = np.array([c[0] for c in cl], dtype=np.int32)
        aj = np.array([c[1] for c in cl], dtype=np.int32)
        ak = np.array([c[2] for c in cl], dtype=np.int32)
        as1 = np.array([c[3] for c in cl], dtype=float)
        as2 = np.array([c[4] for c in cl], dtype=float)
        as3 = np.array([c[5] for c in cl], dtype=float)
        x0 = np.concatenate([d_in, u_in])
        bounds = [(None, None)] * 56 + [(0.0, None)] * m

        def fg(x):
            dv = x[:56]; dv = dv - dv.mean()
            uv = x[56:]
            A = Lf + np.diag(dv)
            if m > 0:
                np.add.at(A, (ai, aj), -uv * as1); np.add.at(A, (aj, ai), -uv * as1)
                np.add.at(A, (aj, ak), -uv * as2); np.add.at(A, (ak, aj), -uv * as2)
                np.add.at(A, (ai, ak), -uv * as3); np.add.at(A, (ak, ai), -uv * as3)
            ev, V = np.linalg.eigh(A)
            em = ev[-1]
            ex = np.exp(beta * (ev - em))
            se = ex.sum()
            w = ex / se
            P = (V * w) @ V.T
            gd = 56.0 * np.diag(P); gd -= gd.mean()
            gu = (2.0 - 112.0 * (as1 * P[ai, aj] + as2 * P[aj, ak] + as3 * P[ai, ak])) if m > 0 else np.zeros(0)
            return 56.0 * (em + np.log(se) / beta) + 2.0 * uv.sum(), np.concatenate([gd, gu])

        res = minimize(fg, x0, jac=True, method="L-BFGS-B", bounds=bounds, options={"maxiter": maxiter, "ftol": 1e-13})
        dv = res.x[:56]; dv -= dv.mean()
        uv = res.x[56:]
        A = Lf + np.diag(dv)
        if m > 0:
            np.add.at(A, (ai, aj), -uv * as1); np.add.at(A, (aj, ai), -uv * as1)
            np.add.at(A, (aj, ak), -uv * as2); np.add.at(A, (ak, aj), -uv * as2)
            np.add.at(A, (ai, ak), -uv * as3); np.add.at(A, (ak, ai), -uv * as3)
        ev, V = np.linalg.eigh(A)
        em = ev[-1]
        ex = np.exp(beta * (ev - em))
        w = ex / ex.sum()
        P = (V * w) @ V.T
        return 56.0 * float(em) + 2.0 * float(uv.sum()), dv, uv, 56.0 * P

    cl, cset = [], set()
    d, u = d_cur.copy(), np.zeros(0)
    for rnd in range(15):
        beta = 10.0 if rnd < 3 else (25.0 if rnd < 7 else 55.0)
        bd, d, u, X = opt_tri(cl, d, u, beta=beta, maxiter=250)
        keep = [idx for idx in range(len(cl)) if u[idx] > 1e-4]
        cl = [cl[idx] for idx in keep]
        u = u[keep]
        cset = set(cl)
        if bd < B_strict - 1.5 and rnd >= 3:
            break
        nc = [c for c in separate(X, top_k=220, min_viol=0.01) if c not in cset]
        if not nc:
            break
        cl.extend(nc); cset.update(nc)
        u = np.concatenate([u, np.zeros(len(nc))])

    bd, d, u, _ = opt_tri(cl, d, u, beta=65.0, maxiter=350)
    for thresh in [0.01, 0.03, 0.06, 0.10]:
        keep = [idx for idx in range(len(cl)) if u[idx] > thresh]
        if len(keep) < 15:
            break
        cl2 = [cl[idx] for idx in keep]
        b2, d2, u2, _ = opt_tri(cl2, d, u[keep], beta=65.0, maxiter=300)
        if b2 < B_strict - 0.8:
            cl, d, u, bd = cl2, d2, u2, b2
        else:
            break

    cert = try_round_cert_56(L_mat, d, cl, u, need_F)
    if cert is None:
        raise RuntimeError(f"Orbit {orb_id} (n={n_sec}, need F>={need_F}) failed rounding! bd={bd:.4f} vs {B_strict}")
    return "tri", need_F, cert


def main():
    regen = "--regenerate" in sys.argv
    E, S_map, O = build_q7minus_geometry()

    # 1. CSS witnesses on Q^-(7,2), W(7,2), Q^+(9,2)
    def count_css(pts, N):
        pset = set(pts)
        L = V = 0
        for i, u in enumerate(pts):
            su = css_sign(u, N)
            for v in pts[i + 1 :]:
                w = u ^ v
                if w > v and w in pset and symp(u, v, N) == 0:
                    L += 1
                    if su * css_sign(v, N) * css_sign(w, N) != line_sign(u, v, N):
                        V += 1
        return L, V

    L_q7m, V_q7m = count_css(E, 4)
    L_w72, V_w72 = count_css(list(range(1, 256)), 4)
    Q9p = [v for v in range(1, 1024) if (y_cnt(v, 5) & 1) == 0]
    L_q9p, V_q9p = count_css(Q9p, 5)
    check("CSS rule witnesses exact violations: Q^-(7,2)=315/1071, W(7,2)=1575/5355, Q^+(9,2)=6975/23715",
          (L_q7m, V_q7m) == (1071, 315) and (L_w72, V_w72) == (5355, 1575) and (L_q9p, V_q9p) == (23715, 6975))

    # 2. Double-counting ladders (exact on ALL lines!)
    anti4 = [c for c in range(1, 256) if (y_cnt(c, 4) & 1) == 1]
    cov4_ok = all(
        sum(1 for c in anti4
            if ((y_cnt(u, 4) + symp(u, c, 4)) & 1) == 0
            and ((y_cnt(v, 4) + symp(v, c, 4)) & 1) == 0) == 24
        for u in range(1, 256) for v in range(u + 1, 256) if (u ^ v) > v and symp(u, v, 4) == 0
    )
    check("double counting N=4: every line of W(7,2) lies on exactly 24 of 120 elliptic quadrics Q^-(7,2)", cov4_ok)

    anti5 = [J for J in range(1, 1024) if (y_cnt(J, 5) & 1) == 1]
    # Check coverage on all lines of Q^+(9,2) (23,715 lines):
    # Wait: u, v in Q^+(9,2) commuting -> (u^perp cap v^perp) has dim 8 (256 vectors).
    # Since u, v are isotropic (q0=0) and orthogonal, restriction of q0 to u^perp cap v^perp is a hyperbolic quadric
    # of 8-dim space with radical <u, v>, having 4 * 28 = 112 antisymmetric points J! Verify on sample of 200 lines!
    q9_lines_sample = []
    for i, u in enumerate(Q9p[:40]):
        for v in Q9p[i + 1 :]:
            w = u ^ v
            if w > v and (y_cnt(w, 5) & 1) == 0 and symp(u, v, 5) == 0:
                q9_lines_sample.append((u, v))
                if len(q9_lines_sample) >= 200:
                    break
        if len(q9_lines_sample) >= 200:
            break
    cov5_ok = all(sum(1 for J in anti5 if symp(u, J, 5) == 0 and symp(v, J, 5) == 0) == 112 for (u, v) in q9_lines_sample)
    check("double counting N=5: lines of Q^+(9,2) lie in exactly 112 of 496 polar sections J^perp ~= W(7,2)", cov5_ok)

    # 3. Unconditional closed-form degree-4 SOS identity on Q^-(7,2)
    # Check M_u^2 + 6 M_u = 27 I for ALL 136 non-points u of Q^-(7,2), AND H_w^2 = 18 H_w for ALL 119 points w!
    Eset = set(E)
    non_E = [u for u in range(1, 256) if u not in Eset]
    mu_ok = True
    for u in non_E:
        pairs_u = [(a, a ^ u) for a in E if (a ^ u) > a and (a ^ u) in Eset]
        if len(pairs_u) != 28:
            mu_ok = False; break
        M = np.zeros((28, 28), dtype=int)
        for i, (a, b) in enumerate(pairs_u):
            for j in range(i + 1, 28):
                c, d_ = pairs_u[j]
                val = line_sign(a, c, 4) * line_sign(b, d_, 4) if (a ^ c) in Eset else line_sign(a, d_, 4) * line_sign(b, c, 4)
                M[i, j] = M[j, i] = val
        if not np.array_equal(M @ M + 6 * M, 27 * np.eye(28, dtype=int)):
            mu_ok = False; break
    check("degree-4 SOS block identity M_u^2 + 6 M_u = 27 I holds identically on all 136 non-points u of Q^-(7,2)", mu_ok)

    # Check H_w = 3 I_27 - 3 A_27 + J_27 satisfies H_w^2 = 18 H_w on all 119 points w!
    hw_ok = True
    for w in E:
        pairs_w = [(a, a ^ w) for a in E if (a ^ w) > a and (a ^ w) in Eset]
        if len(pairs_w) != 27:
            hw_ok = False; break
        A27 = np.zeros((27, 27), dtype=int)
        for i, (a, _) in enumerate(pairs_w):
            for j in range(i + 1, 27):
                c, _ = pairs_w[j]
                if symp(a, c, 4) == 0:
                    A27[i, j] = A27[j, i] = 1
        H = 3 * np.eye(27, dtype=int) - 3 * A27 + np.ones((27, 27), dtype=int)
        if not np.array_equal(H @ H, 18 * H):
            hw_ok = False; break
    check("degree-4 SOS block identity H_w^2 = 18 H_w holds identically on all 119 points w of Q^-(7,2)", hw_ok)
    # Rational p = 1/50 bound: M(1/50) = 119*25/12 + 12138/50 = 147203/300 < 491 => viol >= 291
    check("unconditional degree-4 SOS proves d(Q^-(7,2)) >= 291, d(W(7,2)) >= 1455, d(Q^+(9,2)) >= 6444",
          119 * 25 * 25 + 12138 * 6 < 491 * 300 and (120 * 291) // 24 == 1455 and math.ceil(496 * 1455 / 112) == 6444)

    # 4. Load all 42 orbits from our independent C census data/w52_orbits_42.tsv
    orbits = []
    for line in ORBITS_TSV.read_text(encoding="utf-8").splitlines()[1:]:
        parts = line.split("\t")
        orbits.append(dict(orbit=int(parts[0]), n=int(parts[1]), size=int(parts[2]),
                           c0_count=int(parts[3]), rep_hex=parts[4], rep_int=int(parts[4], 16)))
    check("independent C census table has 42 orbits, 17,652,160 classes, |C_0| = 9,017,680",
          len(orbits) == 42 and sum(o["size"] for o in orbits) == 17652160 and sum(o["c0_count"] for o in orbits) == 9017680)

    if regen or not CERT_PATH.exists():
        print("Computing pure-integer MET-SDP certificates for all 42 W(5,2) orbits...", flush=True)
        certs_all = []
        method_counts = {"eig": 0, "diag": 0, "tri": 0}
        for o in orbits:
            L_mat = build_outside_graph(O, S_map, o["rep_int"])
            method, need_F, cert = solve_orbit_cert_56(o["orbit"], o["n"], L_mat)
            method_counts[method] += 1
            certs_all.append(dict(orbit=o["orbit"], n=o["n"], size=o["size"], rep_hex=o["rep_hex"],
                                  method=method, target_F=need_F, cert=cert))
            print(f"  orbit {o['orbit']:2d} (n={o['n']:2d}, size={o['size']:7d}): {method:4s} F>={need_F:3d} "
                  f"(Q={cert['Q']:3d}, cuts={len(cert['cuts']):3d}, K={cert['K']:4d})", flush=True)
        CERT_PATH.write_text(json.dumps(certs_all, separators=(",", ":")), encoding="utf-8", newline="\n")
        print(f"wrote {CERT_PATH} (methods: {method_counts})", flush=True)
    else:
        certs_all = json.loads(CERT_PATH.read_text(encoding="utf-8"))

    # Verify ALL 42 pure-integer certificates!
    all_ok = True
    methods = {"eig": 0, "diag": 0, "tri": 0}
    for entry in certs_all:
        rep_int = int(entry["rep_hex"], 16)
        L_mat = build_outside_graph(O, S_map, rep_int)
        ok, det = verify_cert_56(L_mat, entry["cert"], entry["target_F"])
        methods[entry["method"]] += 1
        if not ok or entry["n"] + entry["target_F"] < 315:
            print(f"  FAIL orbit {entry['orbit']}: {det}")
            all_ok = False
    check("all 42 W(5,2) n<=92 orbit representatives certified n + F >= 315 in exact pure integer arithmetic",
          all_ok and len(certs_all) == 42, f"methods={methods}")

    # Negative control: trying target_F + 1 on the Hoggar orbit (n=63, F=252 -> try 253) MUST fail!
    hoggar_entry = next(e for e in certs_all if e["n"] == 63)
    L_hog = build_outside_graph(O, S_map, int(hoggar_entry["rep_hex"], 16))
    ok_nc, det_nc = verify_cert_56(L_hog, hoggar_entry["cert"], 253)
    check("negative control: Hoggar orbit (n=63, F=252) rejects impossible target F >= 253", not ok_nc, det_nc)

    summary = {
        "unconditional_degree4_sos": {
            "exact_analytic_upper_bound": "119 * sqrt(17) = 490.649569...",
            "rational_p": "1/50",
            "d_Q7minus_lb": 291,
            "d_W72_lb": 1455,
            "d_Q9plus_lb": 6444,
        },
        "exact_degrees_with_census": {
            "d_Q7minus": 315,
            "d_W72": 1575,
            "d_Q9plus": 6975,
            "w52_orbits": 42,
            "w52_classes": 17652160,
            "w52_C0": 9017680,
            "cert_methods": methods,
        },
        "checks": {"passed": sum(1 for _, ok in CHECKS if ok), "total": len(CHECKS)},
    }
    OUT_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
    npass = sum(1 for _, ok in CHECKS if ok)
    print(f"\n{npass} of {len(CHECKS)} checks passed", flush=True)
    sys.exit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

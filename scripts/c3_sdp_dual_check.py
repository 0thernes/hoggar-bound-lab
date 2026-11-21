#!/usr/bin/env python3
"""
c3_sdp_dual_check.py - independent exact verification of the tightened QUBO SDP-dual lower bound
for the second four-qubit C3 carrier (Corollary 16, v1.7.0):

  For every binary completion y in {-1, +1}^64 of signB (sigma_1):
      F(sigma_1, y) = 560 - (1/4) y^T Lambda_1 y >= 330

(improving the unshifted spectral bound 315 by +15 to the exact integer ceiling of the full
64-variable elliptope SDP dual 329.85603574..., halving the uncertainty interval from [315, 344]
to [330, 344], alongside the certified enclosure [347, 368] for sigma_0).

The verification checks in exact integer / SymPy arithmetic:
  1. Rebuilds Lambda_0, Lambda_1 and the 16x16 carriers A_0, A_1 from literal Pauli tensors.
  2. Verifies the uniform top-eigenspace projector diagonal (1/8) for Lambda_0 (proving d = 0
     is optimal for the diagonal-shift SDP on sigma_0) and the 4-class diagonal partition of
     Lambda_1 determined by (symp(p, 144), symp(p, 176)) = (1 ^ a_0, 1 ^ a_0 ^ a_1).
  3. Verifies the zero-sum geometric shift d_16(p) in {-40, +8, +8, +24} (depending only on
     p mod 4) and exact SymPy characteristic-polynomial equality between
     M_64 = 231 I_64 - 16 Lambda_1 - diag(d_16) and the direct sum of two copies of the four
     8x8 integer blocks B_0, B_1, B_2, B_3.
  4. Verifies the exact pure-integer fraction-free L D L^T positivity certificates for B_0..B_3
     (matching lean/HoggarBound/AuditUpgrades.lean) and their Sylvester leading principal minors.
  5. Verifies the explicit binary witnesses (368 violated outside contexts for sigma_0 and 344
     for sigma_1).
  6. Exercises three negative controls (tighter threshold 230/16 fails positive definiteness,
     non-zero-sum shift fails, and a perturbed carrier sign breaks the block identity).

Writes results/c3_sdp_dual_check.json.
"""
import json
from fractions import Fraction
from math import lcm
from pathlib import Path
import numpy as np
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print("%s  %s%s" % ("PASS" if ok else "FAIL", name, ("   [" + detail + "]") if detail else ""), flush=True)
    return ok


def symp(u, v):
    au, cu = u & 15, (u >> 4) & 15
    av, cv = v & 15, (v >> 4) & 15
    return ((au & cv).bit_count() ^ (cu & av).bit_count()) & 1


def is_real(v):
    a, c = v & 15, (v >> 4) & 15
    return ((a & c).bit_count() & 1) == 0


def pauli_matrix(v):
    I = np.array([[1, 0], [0, 1]], dtype=complex)
    X = np.array([[0, 1], [1, 0]], dtype=complex)
    Z = np.array([[1, 0], [0, -1]], dtype=complex)
    Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
    a, c = v & 15, (v >> 4) & 15
    M = np.array([[1.0 + 0j]])
    for q in range(3, -1, -1):
        aq, cq = (a >> q) & 1, (c >> q) & 1
        g = [I, X, Z, Y][aq + 2 * cq]
        M = np.kron(M, g)
    return M


def exact_ldlt(M_int):
    n = M_int.shape[0]
    A = [[Fraction(int(M_int[i, j])) for j in range(n)] for i in range(n)]
    L = [[Fraction(0)] * n for _ in range(n)]
    D = [Fraction(0)] * n
    for j in range(n):
        s = sum(L[j][k] * L[j][k] * D[k] for k in range(j))
        D[j] = A[j][j] - s
        if D[j] <= 0:
            return None
        L[j][j] = Fraction(1)
        for i in range(j + 1, n):
            s = sum(L[i][k] * L[j][k] * D[k] for k in range(j))
            L[i][j] = (A[i][j] - s) / D[j]
    L_int = [[0] * n for _ in range(n)]
    W_rat = [Fraction(0)] * n
    for k in range(n):
        den = 1
        for i in range(n):
            den = lcm(den, L[i][k].denominator)
        for i in range(n):
            L_int[i][k] = int(L[i][k] * den)
        W_rat[k] = D[k] / (den * den)
    S_int = 1
    for w in W_rat:
        S_int = lcm(S_int, w.denominator)
    W_int = [int(w * S_int) for w in W_rat]
    for i in range(n):
        for j in range(n):
            rhs = sum(W_int[k] * L_int[i][k] * L_int[j][k] for k in range(n))
            if rhs != S_int * int(M_int[i, j]):
                return None
    return S_int, W_int, L_int


def main():
    d = 128
    pts = [v for v in range(1, 256) if is_real(v)]
    sec = [v for v in pts if symp(v, d) == 0]
    out = [v for v in pts if symp(v, d) == 1]
    check("four-qubit C3 real polar geometry has 71 section and 64 outside points",
          len(pts) == 135 and len(sec) == 71 and len(out) == 64)

    P = {v: pauli_matrix(v) for v in pts}

    def line_sign(u, v):
        prod = P[u] @ P[v]
        w = P[u ^ v]
        idx = int(np.flatnonzero(np.abs(w) > 0.5)[0])
        val = (prod.flat[idx] / w.flat[idx]).real
        assert abs(abs(val) - 1.0) < 1e-9
        return int(round(val))

    def build_pair(neg_set):
        sig = {v: (-1 if v in neg_set else 1) for v in sec}
        A = np.round(sum(sig[v] * P[v] for v in sec).real).astype(int)
        L = np.zeros((64, 64), dtype=int)
        for i, p in enumerate(out):
            for j, q in enumerate(out):
                if i != j and symp(p, q) == 0:
                    L[i, j] = sig[p ^ q] * line_sign(p, q)
        return A, L

    negA = {48, 102, 176, 230}
    negB = {87, 144, 176, 215}
    A0, L0 = build_pair(negA)
    A1, L1 = build_pair(negB)

    check("reconstructed completion cubic traces are 14976 (sigma_0) and 15360 (sigma_1)",
          int(np.trace(L0 @ L0 @ L0)) == 14976 and int(np.trace(L1 @ L1 @ L1)) == 15360)

    # Top eigenspace projector uniformity for L0 vs non-uniformity for L1
    w0, V0 = np.linalg.eigh(L0.astype(float))
    top0 = np.where(np.abs(w0 - w0[-1]) < 1e-8)[0]
    diagP0 = np.diag(V0[:, top0] @ V0[:, top0].T)
    check("sigma_0 top eigenspace (mult 8) has uniform projector diagonal 1/8 (d = 0 is SDP-optimal)",
          len(top0) == 8 and float(np.max(np.abs(diagP0 - 0.125))) < 1e-12,
          f"max |P_ii - 1/8| = {float(np.max(np.abs(diagP0 - 0.125))):.2e}")

    w1, V1 = np.linalg.eigh(L1.astype(float))
    top1 = np.where(np.abs(w1 - w1[-1]) < 1e-8)[0]
    diagP1 = np.diag(V1[:, top1] @ V1[:, top1].T)
    check("sigma_1 top eigenspace (mult 2) has non-uniform projector diagonal across 4 classes of 16",
          len(top1) == 2 and len(np.unique(np.round(diagP1, 6))) == 4,
          f"distinct values = {np.unique(np.round(diagP1, 6)).tolist()}")

    # Bit characterization of commutation with 144 (ZIIZ) and 176 (ZIZZ)
    bit_ok = all(
        (p & 8) == 8 and symp(p, 144) == (1 ^ (p & 1)) and symp(p, 176) == (1 ^ (p & 1) ^ ((p >> 1) & 1))
        for p in out
    )
    check("for all 64 outside points, symp(p, 144) = 1 ^ a_0 and symp(p, 176) = 1 ^ a_0 ^ a_1", bit_ok)

    # Zero-sum geometric shift d_16
    d_lut = [-40, 8, 8, 24]
    d16 = np.array([d_lut[p & 3] for p in out], dtype=int)
    check("geometric diagonal shift d_16 in {-40, +8, +8, +24} sums exactly to 0 over all 64 outside points",
          int(np.sum(d16)) == 0)

    # Block decomposition of A1 = C1 (+) diag(D1)
    C1 = A1[:8, :8]
    D1 = np.diag(A1[8:, 8:])
    check("A_1 is block-diagonal C_1 (+) diag(3,-5,-1,-1,3,-5,-1,-1)",
          np.array_equal(A1[:8, 8:], np.zeros((8, 8), dtype=int))
          and np.array_equal(A1[8:, :8], np.zeros((8, 8), dtype=int))
          and np.array_equal(A1[8:, 8:], np.diag(D1))
          and D1.tolist() == [3, -5, -1, -1, 3, -5, -1, -1])

    # Exact block decomposition of M_64 = 231 I_64 - 16 Lambda_1 - diag(d_16)
    M64 = 231 * np.eye(64, dtype=int) - 16 * L1 - np.diag(d16)
    blocks = []
    block_records = []
    all_ldlt_ok = True
    lam = sp.Symbol("x")
    prod_charpoly = sp.Integer(1)
    for k in range(4):
        Bk = (231 * np.eye(8, dtype=int)
              - 8 * (C1 + D1[k] * np.eye(8, dtype=int))
              - np.diag([d_lut[(i ^ k) & 3] for i in range(8)]))
        blocks.append(Bk)
        res = exact_ldlt(Bk)
        S_sym = sp.Matrix(Bk.tolist())
        minors = [int(S_sym[:r, :r].det()) for r in range(1, 9)]
        cp_k = S_sym.charpoly(lam).as_expr()
        prod_charpoly = sp.expand(prod_charpoly * cp_k ** 2)
        ok_k = res is not None and all(m > 0 for m in minors)
        all_ldlt_ok = all_ldlt_ok and ok_k
        check(f"8x8 shifted block B_{k} passes exact integer L D L^T and all 8 Sylvester minors > 0",
              ok_k, f"scale={res[0] if res else None}, min_eig={float(np.linalg.eigvalsh(Bk.astype(float))[0]):.6f}")
        block_records.append({
            "block_index": k,
            "D1_diag": int(D1[k]),
            "ldlt_scale": str(res[0]),
            "sylvester_minors": [str(m) for m in minors],
            "min_eigenvalue_approx": round(float(np.linalg.eigvalsh(Bk.astype(float))[0]), 9),
        })

    # Exact SymPy characteristic polynomial match between 64x64 M64 and (B_0 (+) B_1 (+) B_2 (+) B_3)^2!
    cp_full = sp.Matrix(M64.tolist()).charpoly(lam).as_expr()
    check("exact SymPy charpoly(231 I_64 - 16 Lambda_1 - diag(d_16)) equals prod_{k=0}^3 charpoly(B_k)^2",
          sp.expand(cp_full - prod_charpoly) == 0)

    # Continuous SDP-dual shifted eigenvalue bound on Lambda_1 + diag(d_16)/16
    lmax_shifted = float(np.linalg.eigvalsh(L1.astype(float) + np.diag(d16.astype(float) / 16.0))[-1])
    lb_shifted = 560.0 - 16.0 * lmax_shifted
    check("shifted spectral bound proves F(sigma_1, y) > 329 (hence >= 330) for all y in {+-1}^64",
          all_ldlt_ok and lmax_shifted < 231.0 / 16.0 and lb_shifted > 329.0,
          f"lmax_shifted={lmax_shifted:.10f} < 14.4375 = 231/16, F_lb={lb_shifted:.8f}")

    # Binary witnesses (368 for sigma_0, 344 for sigma_1)
    witA_neg = {8, 12, 13, 14, 24, 26, 28, 30, 40, 41, 44, 45, 56, 59, 60, 63,
                90, 93, 105, 110, 123, 125, 126, 153, 155, 157, 159, 170, 171,
                174, 175, 189, 190, 217, 219, 234, 235, 255}
    witB_neg = {26, 41, 59, 63, 72, 88, 90, 104, 105, 120, 123, 153, 155, 159,
                170, 171, 175, 204, 205, 206, 217, 219, 220, 222, 234, 235, 236,
                237, 252, 255}
    yA = np.array([-1 if p in witA_neg else 1 for p in out], dtype=int)
    yB = np.array([-1 if p in witB_neg else 1 for p in out], dtype=int)
    qA = int(yA @ L0 @ yA)
    qB = int(yB @ L1 @ yB)
    FA = 560 - qA // 4
    FB = 560 - qB // 4
    check("binary witnesses give F(sigma_0, y_0) = 368 (quad = 768) and F(sigma_1, y_1) = 344 (quad = 864)",
          qA == 768 and FA == 368 and qB == 864 and FB == 344)

    # Negative controls
    # 1. Trying threshold 230/16 (which would claim F >= 331) fails positive definiteness on B_3!
    B3_tight = (230 * np.eye(8, dtype=int)
                - 8 * (C1 + D1[3] * np.eye(8, dtype=int))
                - np.diag([d_lut[(i ^ 3) & 3] for i in range(8)]))
    nc_tight = exact_ldlt(B3_tight) is None and float(np.linalg.eigvalsh(B3_tight.astype(float))[0]) < 0
    # 2. Perturbing one shift entry breaks zero sum
    d16_bad = d16.copy()
    d16_bad[0] += 1
    nc_sum = int(np.sum(d16_bad)) != 0
    # 3. Flipping one section sign in sigma_1 breaks the block charpoly equality
    _, L1_bad = build_pair(negB ^ {176})
    M64_bad = 231 * np.eye(64, dtype=int) - 16 * L1_bad - np.diag(d16)
    nc_sign = not np.allclose(np.sort(np.linalg.eigvalsh(M64_bad.astype(float))),
                              np.sort(np.linalg.eigvalsh(M64.astype(float))))
    check("negative controls: threshold 230/16 fails PD on B_3, perturbed shift breaks zero sum, flipped sign breaks block spectrum",
          nc_tight and nc_sum and nc_sign)

    npass = sum(1 for _, ok in CHECKS if ok)
    report = {
        "status": "pass" if npass == len(CHECKS) else "fail",
        "checks": {"passed": npass, "total": len(CHECKS)},
        "shift_16_by_p_mod_4": {"0": -40, "1": 8, "2": 8, "3": 24},
        "threshold_ratio": "231/16",
        "sigma0_unshifted_lmax": round(float(w0[-1]), 9),
        "sigma0_sdp_dual_lb": round(float(560.0 - 16.0 * w0[-1]), 9),
        "sigma0_enclosure": [347, 368],
        "sigma1_unshifted_lmax": round(float(w1[-1]), 9),
        "sigma1_unshifted_lb": round(float(560.0 - 16.0 * w1[-1]), 9),
        "sigma1_shifted_lmax": round(lmax_shifted, 9),
        "sigma1_shifted_lb": round(lb_shifted, 9),
        "sigma1_enclosure_old": [315, 344],
        "sigma1_enclosure_new": [330, 344],
        "blocks": block_records,
        "negative_controls": {
            "threshold_230_over_16_fails_pd": nc_tight,
            "perturbed_shift_breaks_zero_sum": nc_sum,
            "flipped_sign_breaks_block_spectrum": nc_sign,
        },
    }
    out_path = ROOT / "results" / "c3_sdp_dual_check.json"
    with out_path.open("w", encoding="utf-8", newline="\n") as fh:
        json.dump(report, fh, indent=2)
        fh.write("\n")
    print(f"\n{npass} of {len(CHECKS)} checks passed")
    raise SystemExit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
cospectral_pair.py - the four-qubit cospectral pair (C3 certificate), re-derived in exact integer arithmetic.

Setting (combined paper paper/unified-contextuality.md, Section 8).  Q is the set of the 135 real four-qubit
Pauli observables, p = ZIII, H the 71 observables of Q that commute with p (the section) and O the other 64
(the outside points).  A carrier is a sign assignment sigma on H.  Its carrier operator is
A = sum_{s in H} sigma(s) P_s (16 x 16), and its completion matrix Lambda (64 x 64, indexed by O) has the
entry s_L sigma(s) at (p, q) for every context L = {s, p, q} with s in H and p, q in O.  A completion y of
sigma violates F(sigma, y) = 560 - y^T Lambda y / 4 of the 1120 outside contexts.

Checked here.
  * The statements of the paper: the two carriers have the same characteristic polynomial of A and
    completion cubic traces 14976 and 15360; the block polynomials; the largest completion eigenvalues
    (rho - 1)/2 and (rho + 3)/2; 132 violated contexts in the section for both.
  * A statement that the paper leaves open (publication/ADDENDUM-completion-optima.md): the exact binary
    completion minima differ.  Every completion of the first carrier violates at least 347 outside contexts
    (the spectral bound, with rho enclosed between two rationals), and an explicit completion of the second
    violates 344.

The pair was found, and proved in Lean 4, by the C3 line of work of this repository
(paper/c3-spectral-counterexample.md, scripts/frontier_c3_*.py, lean/HoggarBound/C3*.lean).  This script
shares no code with it.  It rebuilds everything from the definition of the Pauli matrices, in Python
integers and fractions only, with two routes for the context signs (a phase formula and matrix products).

  python scripts/cospectral_pair.py

Writes results/cospectral_pair.json.
"""
import json, os, sys
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
N, D = 4, 16
DPOINT = 128                                   # d = ZIII
NEG = {"sigma0": (48, 102, 176, 230),          # IIZZ, IYYI, ZIZZ, ZYYI
       "sigma1": (87, 144, 176, 215)}          # IYXY, ZIIZ, ZIZZ, ZYXY
WORDS = {"sigma0": ("IIZZ", "IYYI", "ZIZZ", "ZYYI"), "sigma1": ("IYXY", "ZIIZ", "ZIZZ", "ZYXY")}
# completions (found by simulated annealing): the outside points with value -1, and the outside contexts violated
COMPLETION_NEG = {
    "sigma0": (8, 12, 13, 14, 24, 26, 28, 30, 40, 41, 44, 45, 56, 59, 60, 63, 90, 93, 105, 110, 123, 125, 126, 153, 155,
               157, 159, 170, 171, 174, 175, 189, 190, 217, 219, 234, 235, 255),
    "sigma1": (26, 41, 59, 63, 72, 88, 90, 104, 105, 120, 123, 153, 155, 159, 170, 171, 175, 204, 205, 206, 217, 219,
               220, 222, 234, 235, 236, 237, 252, 255)}
COMPLETION_VIOLATED = {"sigma0": 368, "sigma1": 344}

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print("%s  %s%s" % ("PASS" if ok else "FAIL", name, ("   [" + detail + "]") if detail else ""))
    return ok


def pc(x):
    return bin(x).count("1")


# ---------------------------------------------------------------- points, words, matrices
# label v = x + 16 z; bit 0 is the rightmost tensor factor; P_v = i^(x.z) X^x Z^z, x.z an integer sum
def xz(v):
    return v & 15, v >> 4


def word(v):
    x, z = xz(v)
    return "".join("IXZY"[((x >> j) & 1) + 2 * ((z >> j) & 1)] for j in (3, 2, 1, 0))


def is_real(v):
    x, z = xz(v)
    return pc(x & z) % 2 == 0


def commute(u, v):
    xu, zu = xz(u)
    xv, zv = xz(v)
    return (pc(xu & zv) + pc(zu & xv)) % 2 == 0


def pauli(v):
    """Integer matrix of a real Pauli observable: X^x Z^z |b> = (-1)^(z.b) |b + x>."""
    x, z = xz(v)
    k = pc(x & z)
    assert k % 2 == 0
    s0 = -1 if (k // 2) % 2 else 1
    M = [[0] * D for _ in range(D)]
    for b in range(D):
        M[b ^ x][b] = s0 * (-1 if pc(z & b) % 2 else 1)
    return M


def line_sign(u, v):
    """s with P_u P_v P_(u+v) = s I, for commuting u, v: from P_u P_v = i^(xu.zu + xv.zv - xw.zw) (-1)^(zu.xv) P_w."""
    xu, zu = xz(u)
    xv, zv = xz(v)
    xw, zw = xu ^ xv, zu ^ zv
    e = (pc(xu & zu) + pc(xv & zv) - pc(xw & zw)) % 4
    assert e % 2 == 0
    return (-1 if e == 2 else 1) * (-1 if pc(zu & xv) % 2 else 1)


# ---------------------------------------------------------------- integer matrices and polynomials
def mmul(A, B):
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(row, col)) for col in Bt] for row in A]


def madd(A, B, cb=1):
    return [[a + cb * b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def trace(A):
    return sum(A[i][i] for i in range(len(A)))


def ident(n, c=1):
    return [[c if i == j else 0 for j in range(n)] for i in range(n)]


def charpoly(A):
    """Coefficients, highest first, of det(t - A), by the Faddeev-LeVerrier recurrence; every division is exact."""
    n = len(A)
    c = [1]
    M = ident(n)
    for k in range(1, n + 1):
        AM = mmul(A, M)
        t = trace(AM)
        assert t % k == 0
        ck = -t // k
        c.append(ck)
        M = madd(AM, ident(n, ck))
    assert all(x == 0 for row in M for x in row)          # Cayley-Hamilton: the recurrence closes
    return c


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def ppow(p, k):
    r = [1]
    for _ in range(k):
        r = pmul(r, p)
    return r


def pshift(p, a):
    """p(t + a), coefficients highest first."""
    r = [0]
    for coef in p:
        r = pmul(r, [1, a])
        r[-1] += coef
    while len(r) > 1 and r[0] == 0:
        r = r[1:]
    return r


def peval(p, t):
    r = 0
    for coef in p:
        r = r * t + coef
    return r


def pstr(p):
    out = []
    n = len(p) - 1
    for i, c in enumerate(p):
        if c == 0:
            continue
        e = n - i
        mono = "" if e == 0 else ("t" if e == 1 else "t^%d" % e)
        a = abs(c)
        out.append(("-" if c < 0 else "+") + ("" if (a == 1 and e) else str(a)) + mono)
    s = "".join(out)
    return s[1:] if s.startswith("+") else s


QCUB = [1, -25, -133, 1621]                              # q(t) = t^3 - 25 t^2 - 133 t + 1621
HQ = pmul([1, 13], QCUB)                                 # h(t) = (t + 13) q(t)


def main():
    out = {"N": N, "d": {"label": DPOINT, "word": word(DPOINT)}}

    # ---------------------------------------------------------------- 1. the configuration
    X = [v for v in range(1, 256) if is_real(v)]
    S = [v for v in X if commute(v, DPOINT)]
    O = [v for v in X if not commute(v, DPOINT)]
    Xset, Sset = set(X), set(S)
    check("135 real four-qubit observables; the section of d = ZIII has 71 points, 64 lie outside",
          (len(X), len(S), len(O)) == (135, 71, 64) and word(DPOINT) == "ZIII" and DPOINT in Sset)
    P = {v: pauli(v) for v in X}
    I16 = ident(D)
    check("every real observable is a symmetric integer matrix with square I",
          all(P[v] == [list(r) for r in zip(*P[v])] and mmul(P[v], P[v]) == I16 for v in X))
    lines = sorted({tuple(sorted((u, v, u ^ v))) for u in X for v in X if u < v and commute(u, v)})
    check("the product of two commuting real observables is real: 1575 contexts in all",
          all(w in Xset for L in lines for w in L) and len(lines) == 1575)
    inside = [L for L in lines if all(w in Sset for w in L)]
    outside = [L for L in lines if not all(w in Sset for w in L)]
    check("455 contexts lie in the section; each of the other 1120 has one point in the section and two outside",
          len(inside) == 455 and len(outside) == 1120
          and all(sum(w in Sset for w in L) == 1 for L in outside))
    sgn = {L: line_sign(L[0], L[1]) for L in lines}
    ok = True
    for L in lines:
        prod = mmul(mmul(P[L[0]], P[L[1]]), P[L[2]])
        ok = ok and prod == ident(D, sgn[L])
    check("context signs: the phase formula agrees with the product of the three matrices, for all 1575", ok,
          "%d negative" % sum(1 for L in lines if sgn[L] < 0))
    out["counts"] = {"points": len(X), "section": len(S), "outside": len(O), "contexts": len(lines),
                     "contexts_in_section": len(inside), "outside_contexts": len(outside),
                     "negative_contexts": sum(1 for L in lines if sgn[L] < 0)}

    # ---------------------------------------------------------------- 2. the two carriers
    opos = {p: i for i, p in enumerate(O)}
    Mblk = {p: [row[8:] for row in P[p][:8]] for p in O}          # P_p = [[0, M_p], [M_p^T, 0]]
    check("outside observables are block off-diagonal for d, and their blocks M_p are orthogonal: tr M_p^T M_q = 8 [p = q]",
          all(all(x == 0 for row in P[p][:8] for x in row[:8]) and all(x == 0 for row in P[p][8:] for x in row[8:]) for p in O)
          and all(sum(a * b for ra, rb in zip(Mblk[p], Mblk[q]) for a, b in zip(ra, rb)) == (8 if p == q else 0)
                  for p in O for q in O))

    res = {}
    for name in ("sigma0", "sigma1"):
        neg = NEG[name]
        check("%s: negative on %s, which are section points with labels %s" % (name, ", ".join(WORDS[name]), list(neg)),
              tuple(word(v) for v in neg) == WORDS[name] and all(v in Sset for v in neg))
        sig = {s: (-1 if s in neg else 1) for s in S}
        A = [[0] * D for _ in range(D)]
        for s in S:
            A = madd(A, P[s], sig[s])
        chi = charpoly(A)
        C = [row[:8] for row in A[:8]]
        Dm = [row[8:] for row in A[8:]]
        blockdiag = all(x == 0 for row in A[:8] for x in row[8:]) and all(x == 0 for row in A[8:] for x in row[:8])
        Lam = [[0] * 64 for _ in range(64)]
        for L in outside:
            s = [w for w in L if w in Sset][0]
            p, q = [w for w in L if w not in Sset]
            Lam[opos[p]][opos[q]] += sgn[L] * sig[s]
            Lam[opos[q]][opos[p]] += sgn[L] * sig[s]
        L2 = mmul(Lam, Lam)
        t3 = trace(mmul(L2, Lam))
        A2 = mmul(A, A)
        tA3 = trace(mmul(A2, A))
        beta_in = sum(sgn[L] * sig[L[0]] * sig[L[1]] * sig[L[2]] for L in inside)
        res[name] = dict(sig=sig, A=A, chi=chi, C=C, D=Dm, blockdiag=blockdiag, Lam=Lam, t3=t3, tA2=trace(A2), tA3=tA3,
                         trL=trace(Lam), trL2=trace(L2), beta_in=beta_in, chiC=charpoly(C), chiD=charpoly(Dm))

    r0, r1 = res["sigma0"], res["sigma1"]
    target = pmul(pmul(ppow([1, -3], 2), ppow([1, 1], 8)), pmul(ppow([1, 5], 2), HQ))
    check("carrier operators: the same characteristic polynomial (t-3)^2 (t+1)^8 (t+5)^2 (t+13) (t^3-25t^2-133t+1621)",
          r0["chi"] == r1["chi"] == target, pstr(r0["chi"])[:60] + " ...")
    check("the two carriers are different assignments, and neither is the other up to an overall sign",
          r0["sig"] != r1["sig"] and any(r0["sig"][s] != -r1["sig"][s] for s in S))
    check("completion matrices: symmetric, zero diagonal, 35 non-zero entries (all +1 or -1) in every row",
          all(r["Lam"] == [list(c) for c in zip(*r["Lam"])] and all(r["Lam"][i][i] == 0 for i in range(64))
              and all(sum(abs(x) for x in row) == 35 and set(row) <= {-1, 0, 1} for row in r["Lam"]) for r in (r0, r1)))
    check("cubic traces of the completion matrices: 14976 and 15360, so their spectra differ",
          (r0["t3"], r1["t3"]) == (14976, 15360), "difference %d" % (r1["t3"] - r0["t3"]))
    check("the first two moments cannot tell them apart: tr Lambda = 0 and tr Lambda^2 = 2240 for both",
          r0["trL"] == r1["trL"] == 0 and r0["trL2"] == r1["trL2"] == 2240)

    # ---------------------------------------------------------------- 3. the mechanism: two blocks
    check("carrier operators are block diagonal for d: A = C + D on the two eigenspaces of d", r0["blockdiag"] and r1["blockdiag"])
    blocks = {"C0": pmul(pmul(ppow([1, -3], 2), ppow([1, 5], 2)), HQ), "D0": ppow([1, 1], 8),
              "C1": pmul(ppow([1, 1], 4), HQ), "D1": pmul(pmul(ppow([1, -3], 2), ppow([1, 1], 4)), ppow([1, 5], 2))}
    check("block polynomials: C0 (t-3)^2 (t+5)^2 h, D0 (t+1)^8, C1 (t+1)^4 h, D1 (t-3)^2 (t+1)^4 (t+5)^2, h = (t+13) q",
          r0["chiC"] == blocks["C0"] and r0["chiD"] == blocks["D0"] and r1["chiC"] == blocks["C1"] and r1["chiD"] == blocks["D1"])
    check("D0 = -I exactly", r0["D"] == ident(8, -1))
    ok = True
    for r in (r0, r1):
        for p in O:
            lhs = madd(mmul(r["C"], Mblk[p]), mmul(Mblk[p], r["D"]))
            rhs = [[0] * 8 for _ in range(8)]
            col = opos[p]
            for q in O:
                c = r["Lam"][opos[q]][col]
                if c:
                    rhs = madd(rhs, Mblk[q], 2 * c)
            ok = ok and lhs == rhs
    check("Lambda is the matrix of M -> (C M + M D)/2 in the basis of the 64 outside blocks, for both carriers", ok)

    # spectrum of Lambda = {(c_i + d_j)/2}: compare the characteristic polynomial of 2 Lambda with the product
    chi2L = {}
    for name, r in (("sigma0", r0), ("sigma1", r1)):
        chi2L[name] = charpoly([[2 * x for x in row] for row in r["Lam"]])
    pred0 = ppow(pshift(r0["chiC"], 1), 8)                               # d_j = -1, eight times
    pred1 = pmul(pmul(ppow(pshift(r1["chiC"], -3), 2), ppow(pshift(r1["chiC"], 1), 4)), ppow(pshift(r1["chiC"], 5), 2))
    check("characteristic polynomial of 2 Lambda (degree 64, exact) = product over the block eigenvalues of chi_C(t - d_j)",
          chi2L["sigma0"] == pred0 and chi2L["sigma1"] == pred1)
    check("the two completion matrices have different characteristic polynomials", chi2L["sigma0"] != chi2L["sigma1"])

    # trace identity (8) of the companion note
    def identity8(r):
        C2, D2 = trace(mmul(r["C"], r["C"])), trace(mmul(r["D"], r["D"]))
        val = Fraction(r["tA3"]) + Fraction(3, 8) * (C2 * trace(r["D"]) + trace(r["C"]) * D2)
        return val, C2, D2
    v0, c20, d20 = identity8(r0)
    v1, c21, d21 = identity8(r1)
    check("tr Lambda^3 = tr A^3 + (3/8)(tr C^2 tr D + tr C tr D^2), with tr A^3 = 18336 for both",
          v0 == r0["t3"] and v1 == r1["t3"] and r0["tA3"] == r1["tA3"] == 18336
          and (c20, d20, c21, d21) == (1128, 8, 1064, 72), "tr C^2, tr D^2 = %d, %d and %d, %d" % (c20, d20, c21, d21))

    # ---------------------------------------------------------------- 4. the largest eigenvalue, exactly
    q = QCUB
    dq = [3, -50, -133]
    check("q has exactly one root r above 25: q(25) = -1704 < 0 < q(30) = 2131, and q' > 0 from 25 on",
          peval(q, 25) == -1704 and peval(q, 30) == 2131 and peval(dq, 25) > 0 and 50 / 6 < 25)
    lo, hi = Fraction(221, 8), Fraction(111, 4)                          # 27.625 and 27.75
    check("27.625 <= r < 27.75, by the signs of q at these two rationals", peval(q, lo) <= 0 < peval(q, hi),
          "q(221/8) = %s, q(111/4) = %s" % (peval(q, lo), peval(q, hi)))
    # r is the largest eigenvalue of both C blocks (their other eigenvalues are 3, -1, -5, -13 and the two smaller
    # roots of q); the largest eigenvalues of D0 and D1 are -1 and 3.  So lambda_max(Lambda) = (r - 1)/2 and (r + 3)/2,
    # and the relaxed bounds 560 - 16 lambda_max are 568 - 8 r and 536 - 8 r.  With lo <= r < hi:
    b0 = (568 - 8 * hi, 568 - 8 * lo)                                    # 568 - 8 r lies in (b0[0], b0[1]]
    b1 = (536 - 8 * hi, 536 - 8 * lo)
    check("largest completion eigenvalues (r-1)/2 and (r+3)/2 differ by exactly 2; every completion violates at least 347, resp. 315, outside contexts",
          b0 == (346, 347) and b1 == (314, 315),
          "568 - 8r in (%s, %s], 536 - 8r in (%s, %s]" % (b0[0], b0[1], b1[0], b1[1]))

    # explicit completions, recounted context by context: upper bounds on the two completion minima
    wit = {}
    for name, r in (("sigma0", r0), ("sigma1", r1)):
        neg = set(COMPLETION_NEG[name])
        assert neg <= set(O) and len(neg) == len(COMPLETION_NEG[name])
        f = dict(r["sig"])
        f.update({p: (-1 if p in neg else 1) for p in O})
        viol_out = sum(1 for L in outside if sgn[L] * f[L[0]] * f[L[1]] * f[L[2]] < 0)
        viol_in = sum(1 for L in inside if sgn[L] * f[L[0]] * f[L[1]] * f[L[2]] < 0)
        quad = sum(r["Lam"][opos[p]][opos[q2]] * f[p] * f[q2] for p in O for q2 in O)
        wit[name] = (viol_out, viol_in, quad)
    check("a completion of sigma0 violates 368 outside contexts and one of sigma1 violates 344 (explicit assignments, direct count)",
          wit["sigma0"][0] == COMPLETION_VIOLATED["sigma0"] == 368 and wit["sigma1"][0] == COMPLETION_VIOLATED["sigma1"] == 344
          and all(w[1] == 132 and 560 - w[2] // 4 == w[0] and w[2] % 4 == 0 for w in wit.values()),
          "y^T Lambda y = %d and %d" % (wit["sigma0"][2], wit["sigma1"][2]))
    check("the completion optima differ: min over completions is at most 344 for sigma1 and at least 347 for sigma0",
          wit["sigma1"][0] < 347 and b0 == (346, 347), "347 <= min(sigma0) <= 368 and 315 <= min(sigma1) <= 344")

    # ---------------------------------------------------------------- 5. the link to the spectral floor
    check("tr A^3 = 6 D beta: both carriers have beta = 191 on the section, so each violates 132 of its 455 contexts",
          r0["beta_in"] == r1["beta_in"] == 191 and r0["tA3"] == 6 * D * 191 and (455 - 191) // 2 == 132)
    # floor on the section itself: beta <= (D-2) |S|^(3/2) / (6 sqrt(D-1)), i.e. (6 beta)^2 (D-1) <= (D-2)^2 |S|^3
    bmax = max(b for b in range(456) if (6 * b) ** 2 * (D - 1) <= (D - 2) ** 2 * len(S) ** 3)
    check("the spectral floor on the 71-point section: beta <= 360, so at least 48 of the 455 contexts are violated by any carrier",
          bmax == 360 and (455 - bmax + 1) // 2 == 48)
    # an assignment of all of X: beta_X = beta_S + (1/2) y^T Lambda y  (checked on a fixed completion)
    ok = True
    for r in (r0, r1):
        y = {p: (-1 if (pc(p) * 5 + p) % 3 == 0 else 1) for p in O}
        f = dict(r["sig"])
        f.update(y)
        beta_all = sum(sgn[L] * f[L[0]] * f[L[1]] * f[L[2]] for L in lines)
        quad = sum(r["Lam"][opos[p]][opos[q2]] * y[p] * y[q2] for p in O for q2 in O)
        viol_out = sum(1 for L in outside if sgn[L] * f[L[0]] * f[L[1]] * f[L[2]] < 0)
        ok = ok and quad % 4 == 0 and 2 * (beta_all - r["beta_in"]) == quad and viol_out == 560 - quad // 4
    check("for a completion y: violated outside contexts = 560 - y^T Lambda y / 4, and beta_X = beta_S + y^T Lambda y / 2", ok)

    # ---------------------------------------------------------------- 6. controls
    sig = dict(r0["sig"])
    sig[48] = 1                                                         # undo one negative sign of sigma0
    A = [[0] * D for _ in range(D)]
    for s in S:
        A = madd(A, P[s], sig[s])
    check("control: changing one sign of sigma0 changes the carrier polynomial (the pair is not cospectral by accident of the test)",
          charpoly(A) != r0["chi"])
    Lm = [row[:] for row in r0["Lam"]]
    i0, j0 = next((i, j) for i in range(64) for j in range(64) if Lm[i][j])
    Lm[i0][j0] = -Lm[i0][j0]
    Lm[j0][i0] = -Lm[j0][i0]
    t3m = trace(mmul(mmul(Lm, Lm), Lm))
    check("control: flipping the sign of one outside context changes the cubic trace", t3m != r0["t3"], "14976 -> %d" % t3m)

    npass = sum(1 for _, ok in CHECKS if ok)
    out.update({
        "carriers": {k: {"negative_labels": list(NEG[k]), "negative_words": list(WORDS[k])} for k in NEG},
        "carrier_charpoly": r0["chi"], "carrier_charpoly_text": pstr(r0["chi"]),
        "block_charpolys": {"C0": r0["chiC"], "D0": r0["chiD"], "C1": r1["chiC"], "D1": r1["chiD"]},
        "completion_trace_cube": {"sigma0": r0["t3"], "sigma1": r1["t3"]},
        "completion_trace_square": r0["trL2"], "trace_A_cube": r0["tA3"], "trace_A_square": r0["tA2"],
        "beta_on_section": r0["beta_in"], "violated_in_section": 132,
        "relaxed_completion_bounds": {"sigma0": 347, "sigma1": 315},
        "completion_witnesses": {k: {"negative_outside_labels": list(COMPLETION_NEG[k]),
                                     "violated_outside_contexts": wit[k][0], "violated_in_section": wit[k][1],
                                     "violated_in_all": wit[k][0] + wit[k][1]} for k in COMPLETION_NEG},
        "completion_minimum_intervals": {"sigma0": [347, 368], "sigma1": [315, 344]},
        "top_root_interval": [str(lo), str(hi)],
        "checks": [{"name": n, "pass": ok} for n, ok in CHECKS], "passed": npass, "total": len(CHECKS)})

    with open(os.path.join(ROOT, "results", "cospectral_pair.json"), "w", encoding="utf-8", newline="\n") as fh:
        json.dump(out, fh, indent=1)
    print("\n%d of %d checks passed" % (npass, len(CHECKS)))
    sys.exit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

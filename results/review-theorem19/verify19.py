#!/usr/bin/env python3
"""Independent referee check of Theorem 19 (Conjecture E).

Written from the definitions of [J3] (Section 2, Table 1) and the verbal
descriptions in Sections 8.6/8.7 of the paper. No repository code is used.
Exact arithmetic: Pauli matrices are built as Kronecker products of the 2x2
matrices I, X, Y=[[0,-i],[i,0]], Z with Gaussian-integer entries (pairs of
integer arrays); power sums of A use Python big integers.

Usage: python -I verify19.py N [case ...]
"""
import sys
import numpy as np
from fractions import Fraction


def pc(x):
    return bin(x).count("1")


# labels v = (a, c): bit q of a (x-part) and of c (z-part) refer to qubit q;
# qubit 0 is the rightmost tensor factor, qubit N-1 the leftmost.
def add(u, v):
    return (u[0] ^ v[0], u[1] ^ v[1])


def B(u, v):
    return (pc(u[1] & v[0]) + pc(v[1] & u[0])) & 1


def q0(v):
    return pc(v[0] & v[1]) & 1


def qform(cvec, v):
    return (q0(v) + B(cvec, v)) & 1


def Xq(q):
    return (1 << q, 0)


def Zq(q):
    return (0, 1 << q)


def Yq(q):
    return (1 << q, 1 << q)


def word(v, N):
    s = ""
    for q in range(N - 1, -1, -1):
        x = (v[0] >> q) & 1
        z = (v[1] >> q) & 1
        s += "IXZY"[x + 2 * z]
    return s


ONE = {
    "I": ([[1, 0], [0, 1]], [[0, 0], [0, 0]]),
    "X": ([[0, 1], [1, 0]], [[0, 0], [0, 0]]),
    "Z": ([[1, 0], [0, -1]], [[0, 0], [0, 0]]),
    "Y": ([[0, 0], [0, 0]], [[0, -1], [1, 0]]),  # Y = [[0,-i],[i,0]]
}


def dense(v, N):
    R = np.array([[1]], dtype=np.int64)
    I = np.zeros((1, 1), dtype=np.int64)
    for ch in word(v, N):  # leftmost factor = qubit N-1 = most significant index bit
        r2 = np.array(ONE[ch][0], dtype=np.int64)
        i2 = np.array(ONE[ch][1], dtype=np.int64)
        R, I = np.kron(R, r2) - np.kron(I, i2), np.kron(R, i2) + np.kron(I, r2)
    return R, I


PH = {(1, 0): 0, (0, 1): 1, (-1, 0): 2, (0, -1): 3}


def monomial(R, I):
    """P|b> = i^ph[b] |perm[b]>, read off the dense matrix."""
    D = R.shape[0]
    perm = np.zeros(D, dtype=np.int64)
    ph = np.zeros(D, dtype=np.int64)
    for b in range(D):
        nz = [i for i in range(D) if R[i, b] != 0 or I[i, b] != 0]
        assert len(nz) == 1
        i = nz[0]
        perm[b] = i
        ph[b] = PH[(int(R[i, b]), int(I[i, b]))]
    return perm, ph


def mono_mul(P, Q):
    """(P Q)|b> = P( i^phQ[b] |permQ[b]> )."""
    pP, hP = P
    pQ, hQ = Q
    return pP[pQ], (hQ + hP[pQ]) % 4


class Paulis:
    def __init__(self, N):
        self.N = N
        self.D = 1 << N
        self.dense = {}
        self.mono = {}
        b = np.arange(self.D)
        for a in range(self.D):
            for c in range(self.D):
                v = (a, c)
                R, I = dense(v, N)
                self.dense[v] = (R, I)
                m = monomial(R, I)
                self.mono[v] = m
                # sanity: P_v = i^{|a^c|} X^a Z^c with X^a Z^c|b> = (-1)^{c.b}|b+a>
                exp_perm = b ^ a
                exp_ph = (pc(a & c) + 2 * np.array([pc(c & int(x)) for x in b])) % 4
                assert np.array_equal(m[0], exp_perm) and np.array_equal(m[1], exp_ph)

    def line_sign(self, u, v, w):
        M = mono_mul(mono_mul(self.mono[u], self.mono[v]), self.mono[w])
        assert np.array_equal(M[0], np.arange(self.D)), "line product not diagonal"
        assert np.all(M[1] == M[1][0]) and M[1][0] in (0, 2), "line product not +-I"
        s = 1 if M[1][0] == 0 else -1
        # order independence (commuting)
        M2 = mono_mul(mono_mul(self.mono[w], self.mono[u]), self.mono[v])
        assert np.array_equal(M2[0], M[0]) and np.array_equal(M2[1], M[1])
        return s


# ---------------------------------------------------------------- graphs
def graph_data(m):
    """Section 8.6: Theorem 17 graph for m >= 3, triangle of Remark (a) for m = 2."""
    if m >= 3:
        u = {1: 0, 2: 4, 3: 4}
        for a in range(4, 1 << m):
            u[a] = 2
        t = 2
        F = {frozenset((0, 1))}
    elif m == 2:
        u = {1: 0, 2: 1, 3: 0}
        t = 2
        F = {frozenset((0, 1)), frozenset((1, 3)), frozenset((0, 3))}
    else:
        return None
    edges = {a: frozenset((u[a], u[a] ^ a)) for a in range(1, 1 << m)}
    assert len(set(edges.values())) == (1 << m) - 1
    assert F <= set(edges.values())
    moved = {a for a, ed in edges.items() if ed in F}
    VF = set().union(*F)
    # F must be a union of components of G not containing t
    for a, ed in edges.items():
        if ed not in F:
            assert not (ed & VF), "F is not a union of components"
    assert t not in VF
    return u, t, moved


def eps(a, c, u, t):
    if a == 0:
        return -1 if pc(c & t) & 1 else 1
    ac = pc(a & c)
    ex = pc(c & u[a]) + (ac // 2 if ac % 2 == 0 else (ac - 1) // 2)
    return -1 if ex & 1 else 1


# ---------------------------------------------------------------- cases
def case_spec(case, N):
    top, sub = N - 1, N - 2
    if case == "C1":
        return dict(W=True, c=None, e=None, d=Zq(top))
    if case == "C3":
        return dict(W=False, c=(0, 0), e=None, d=Zq(top))
    if case == "C5":
        return dict(W=False, c=Yq(0), e=None, d=Zq(top))
    if case == "C6":
        return dict(W=True, c=None, e=Zq(top), d=Zq(sub))
    if case == "C11":
        return dict(W=False, c=(0, 0), e=Zq(top), d=Zq(sub))
    if case == "C14":
        return dict(W=False, c=Yq(0), e=Zq(top), d=Zq(sub))
    if case == "C12":
        return dict(W=False, c=(0, 0), e=Zq(top), d=Yq(sub))
    if case == "C15":
        return dict(W=False, c=Yq(0), e=Zq(top), d=Yq(sub))
    if case == "C8":
        return dict(W=False, c=(0, 0), e=Yq(top), d=Zq(sub))
    raise ValueError(case)


def c1c3_carrier(N, s, d, g):
    """C1 / C3 carriers of Sections 8.6-8.7 (d = Z on qubit N-1)."""
    u, t, moved = g
    if s == d:
        return 1, 1
    assert (s[0] >> (N - 1)) & 1 == 0
    topZ = (s[1] >> (N - 1)) & 1
    mask = (1 << (N - 1)) - 1
    a, c = s[0] & mask, s[1] & mask
    assert (a, c) != (0, 0)
    sig = eps(a, c, u, t)
    tau = -sig if (topZ and a in moved) else sig
    return sig, tau


def make_carriers(case, N, S, spec):
    d, e = spec["d"], spec["e"]
    car = {}
    if case in ("C1", "C3"):
        g = graph_data(N - 1)
        if g is None:
            return None
        for s in S:
            car[s] = c1c3_carrier(N, s, d, g)
    elif case == "C5":
        g = graph_data(N - 2)
        if g is None:
            return None
        u, t, moved = g
        mask = (1 << (N - 1)) - 1
        for s in S:
            if s == d:
                car[s] = (1, 1)
                continue
            topZ = (s[1] >> (N - 1)) & 1
            ab, cb = s[0] & mask, s[1] & mask
            a2, c2 = ab >> 1, cb >> 1
            if a2 == 0:
                assert (ab & 1, cb & 1) == (0, 0) and c2 != 0
            sig = eps(a2, c2, u, t)  # "the same signs" on f0 (x) P''
            tau = -sig if (topZ and a2 in moved) else sig
            car[s] = (sig, tau)
    elif case in ("C12", "C15"):
        g = graph_data(N - 2)
        if g is None:
            return None
        u, t, moved = g
        mb = (1 << (N - 2)) - 1
        for s in S:
            if s == e:
                car[s] = (1, 1)
                continue
            assert (s[0] >> (N - 1)) & 1 == 0
            alpha = (s[1] >> (N - 1)) & 1
            fq = ((s[0] >> (N - 2)) & 1, (s[1] >> (N - 2)) & 1)
            assert fq in ((0, 0), (1, 1))  # I or Y on qubit N-2
            aw, cw = s[0] & mb, s[1] & mb
            assert (aw, cw) != (0, 0)
            sig = eps(aw, cw, u, t)
            tau = -sig if (alpha and aw in moved) else sig
            car[s] = (sig, tau)
    elif case in ("C6", "C11", "C14"):
        mb = (1 << (N - 2)) - 1
        for s in S:
            assert (s[0] >> (N - 1)) & 1 == 0 and (s[0] >> (N - 2)) & 1 == 0
            alpha = (s[1] >> (N - 1)) & 1
            beta = (s[1] >> (N - 2)) & 1
            w = (s[0] & mb, s[1] & mb)
            if w == (0, 0):
                car[s] = (1, 1)
            else:
                car[s] = ((-1) ** (alpha + beta), (-1) ** beta)
    elif case == "C8":
        g = graph_data(N - 2)  # C1 on N-1 qubits has N-2 graph qubits
        if g is None:
            return None
        m1 = (1 << (N - 1)) - 1
        dprime = Zq(N - 2)
        for s in S:
            P = (s[0] & m1, s[1] & m1)
            car[s] = c1c3_carrier(N - 1, P, dprime, g)
    return car


# ---------------------------------------------------------------- algebra
def cmul(A, Bm):
    ar, ai = A
    br, bi = Bm
    return (ar.dot(br) - ai.dot(bi), ar.dot(bi) + ai.dot(br))


def ctrace(A):
    return (sum(A[0][i, i] for i in range(A[0].shape[0])),
            sum(A[1][i, i] for i in range(A[0].shape[0])))


def power_sums(A, D):
    Ao = (A[0].astype(object), A[1].astype(object))
    P = Ao
    out = []
    for k in range(1, D + 1):
        tr = ctrace(P)
        assert tr[1] == 0
        out.append(int(tr[0]))
        if k < D:
            P = cmul(P, Ao)
    return out


def charpoly_from_power_sums(p):
    D = len(p)
    e = [Fraction(1)]
    for k in range(1, D + 1):
        s = Fraction(0)
        for i in range(1, k + 1):
            s += (-1) ** (i - 1) * e[k - i] * p[i - 1]
        e.append(s / k)
    coeffs = [(-1) ** k * e[k] for k in range(D + 1)]  # t^D, t^{D-1}, ...
    assert all(x.denominator == 1 for x in coeffs)
    return [int(x) for x in coeffs]


def proj_trace(Apow, Pr):
    """tr(Apow * Pr) for Gaussian-integer matrices (object/int)."""
    M = cmul(Apow, Pr)
    return ctrace(M)


# ---------------------------------------------------------------- main routine
def run_case(case, N, PS, verbose=True, theoremA=True):
    spec = case_spec(case, N)
    D = 1 << N
    allv = [(a, c) for a in range(D) for c in range(D) if (a, c) != (0, 0)]
    cvec = spec["c"]
    if spec["W"]:
        Yset = list(allv)
    else:
        Yset = [v for v in allv if qform(cvec, v) == 0]
    e, d = spec["e"], spec["d"]
    X = [v for v in Yset if e is None or B(v, e) == 0]
    Xs = set(X)
    S = [v for v in X if B(v, d) == 0]
    O = [v for v in X if B(v, d) == 1]
    Ss = set(S)

    # ---- identification data (J3 Section 2 and Table 1)
    info = {}
    if not spec["W"]:
        info["Y type"] = "Q+" if q0(cvec) == 0 else "Q-"
        qq = lambda v: qform(cvec, v)
    else:
        info["Y type"] = "W"
        qq = None
    if e is not None:
        info["e"] = word(e, N)
        if qq:
            info["q(e)"] = qq(e)
        info["B(d,e)"] = B(d, e)
        info["d in <e>"] = d in ((0, 0), e)
    info["d"] = word(d, N)
    if qq:
        info["q(d)"] = qq(d)
        if e is not None:
            info["q(d+e)"] = qq(add(d, e))
    info["d in X"] = d in Xs
    verts = [r for r in S if all(B(r, s) == 0 for s in S)]
    info["vertices"] = sorted(word(r, N) for r in verts)
    # radical of span S: elements of span S orthogonal to S
    basis = []
    for s in S:
        x = (s[0] << N) | s[1]
        for bvec in basis:
            x = min(x, x ^ bvec)
        if x:
            basis.append(x)
            basis.sort(reverse=True)
    info["dim span S"] = len(basis)
    # enumerate radical (small): brute force over span
    span = {0}
    for bvec in basis:
        span |= {x ^ bvec for x in span}
    rad = []
    for x in span:
        if x == 0:
            continue
        v = (x >> N, x & ((1 << N) - 1))
        if all(B(v, s) == 0 for s in S):
            rad.append(word(v, N))
    info["rad(span S)"] = sorted(rad)

    # ---- lines of X, closure, signs
    lines = []
    for i, u in enumerate(X):
        for v in X[i + 1:]:
            if B(u, v) == 0:
                w = add(u, v)
                assert w in Xs, "X not line-closed"
                if w > v:  # count each line once (u < v < w)
                    lines.append((u, v, w))
    out_lines = []
    n_sec = 0
    for L in lines:
        k = sum(1 for x in L if x in Ss)
        assert k in (1, 3)
        if k == 3:
            n_sec += 1
        else:
            out_lines.append(L)

    car = make_carriers(case, N, S, spec)
    if car is None:
        return dict(case=case, N=N, S=len(S), O=len(O), Lout=len(out_lines), constructed=False, info=info)
    assert set(car) == Ss
    for s in S:
        assert car[s][0] in (1, -1) and car[s][1] in (1, -1)
    diff_pts = [s for s in S if car[s][0] != car[s][1]]

    oidx = {p: i for i, p in enumerate(O)}
    Lam = [np.zeros((len(O), len(O)), dtype=np.int64) for _ in range(2)]
    for L in out_lines:
        s = [x for x in L if x in Ss][0]
        p, q = [x for x in L if x not in Ss]
        sL = PS.line_sign(*L)
        for j in range(2):
            val = sL * car[s][j]
            i1, i2 = oidx[p], oidx[q]
            assert Lam[j][i1, i2] == 0
            Lam[j][i1, i2] = val
            Lam[j][i2, i1] = val

    res = dict(case=case, N=N, S=len(S), O=len(O), Lout=len(out_lines), Lsec=n_sec,
               X=len(X), constructed=True, info=info, r=len(diff_pts),
               diffpts=sorted(word(s, N) for s in diff_pts))
    A = []
    for j in range(2):
        R = np.zeros((D, D), dtype=np.int64)
        I = np.zeros((D, D), dtype=np.int64)
        for s in S:
            R += car[s][j] * PS.dense[s][0]
            I += car[s][j] * PS.dense[s][1]
        assert np.array_equal(R, R.T) and np.array_equal(I, -I.T)  # Hermitian
        A.append((R, I))
    ps = [power_sums(A[j], D) for j in range(2)]
    res["cospectral"] = ps[0] == ps[1]
    res["charpoly_sigma"] = charpoly_from_power_sums(ps[0])
    res["charpoly_tau"] = charpoly_from_power_sums(ps[1])
    tr3 = []
    for j in range(2):
        L2 = Lam[j].dot(Lam[j])
        tr3.append(int(np.sum(L2 * Lam[j].T)))
    res["trL3"] = tr3
    res["trL2"] = [int(np.sum(Lam[j] * Lam[j])) for j in range(2)]

    # ---- Theorem A cross-check: Lambda = matrix of J_A on V_O
    if theoremA:
        for j in range(2):
            Ao = A[j]
            for p in O:
                Pp = PS.dense[p]
                M1 = cmul(Ao, Pp)
                M2 = cmul(Pp, Ao)
                Mr, Mi = M1[0] + M2[0], M1[1] + M2[1]  # = 2 J_A(P_p)
                # coefficients: tr(P_w M)/D ; M = 2*sum_q Lam[q,p] P_q
                for w in [(a, c) for a in range(D) for c in range(D)]:
                    perm, ph = PS.mono[w]
                    # tr(P_w M) = sum_b (P_w)[perm[b], b] * M[b, perm[b]]
                    tr_r = 0
                    tr_i = 0
                    for bb in range(D):
                        z = ph[bb]
                        mr, mi = int(Mr[bb, perm[bb]]), int(Mi[bb, perm[bb]])
                        # multiply i^z * (mr + i mi)
                        if z == 0:
                            rr, ii = mr, mi
                        elif z == 1:
                            rr, ii = -mi, mr
                        elif z == 2:
                            rr, ii = -mr, -mi
                        else:
                            rr, ii = mi, -mr
                        tr_r += rr
                        tr_i += ii
                    assert tr_i == 0 and tr_r % (2 * D) == 0
                    coef = tr_r // (2 * D)
                    expect = int(Lam[j][oidx[w], oidx[p]]) if w in oidx else 0
                    assert coef == expect, (case, N, word(p, N), word(w, N), coef, expect)
        res["theoremA"] = True

    # ---- block power sums, to test (E8)/(E9) and the paper's intermediate claims
    D_ = D
    Id = (np.eye(D_, dtype=np.int64), np.zeros((D_, D_), dtype=np.int64))

    def proj(vlabel, sign):
        Pr = PS.dense[vlabel]
        return (Id[0] + sign * Pr[0], Id[1] + sign * Pr[1])  # = 2 * projector

    blocks = []
    for j in range(2):
        Ao = (A[j][0].astype(object), A[j][1].astype(object))
        A2 = cmul(Ao, Ao)
        A3 = cmul(A2, Ao)
        pw = {1: Ao, 2: A2, 3: A3}
        bj = {}
        if case in ("C1", "C3", "C5", "C8"):
            dd = d
            for sgn in (1, -1):
                Pr = proj(dd, sgn)
                Pro = (Pr[0].astype(object), Pr[1].astype(object))
                vals = []
                for k in (1, 2, 3):
                    tr = proj_trace(pw[k], Pro)
                    assert tr[1] == 0 and tr[0] % 2 == 0
                    vals.append(int(tr[0]) // 2)
                bj[sgn] = vals
        elif case in ("C6", "C11", "C14"):
            for se in (1, -1):
                for sd in (1, -1):
                    P1 = proj(e, se)
                    P2 = proj(d, sd)
                    Pr = cmul((P1[0].astype(object), P1[1].astype(object)),
                              (P2[0].astype(object), P2[1].astype(object)))
                    vals = []
                    for k in (1, 2, 3):
                        tr = proj_trace(pw[k], Pr)
                        assert tr[1] == 0 and tr[0] % 4 == 0
                        vals.append(int(tr[0]) // 4)
                    bj[(se, sd)] = vals
        elif case in ("C12", "C15"):
            for se in (1, -1):
                Pr = proj(e, se)
                Pro = (Pr[0].astype(object), Pr[1].astype(object))
                vals = []
                for k in (1, 2, 3):
                    tr = proj_trace(pw[k], Pro)
                    # block on Z_e = s is A'_s (+) conj, so tr(A^k Pi_s) = 2 p_k(A'_s)
                    assert tr[1] == 0 and tr[0] % 4 == 0
                    vals.append(int(tr[0]) // 4)
                bj[se] = vals
        blocks.append(bj)
    res["blocks"] = blocks

    # predicted tr Lambda^3 from the block power sums
    pred = []
    for j in range(2):
        bj = blocks[j]
        if case in ("C1", "C3", "C5"):
            kap = 2 if case == "C1" else 1
            k = D // 2
            C, Dm = bj[1], bj[-1]
            val = Fraction(kap, 8) * (k * C[2] + 3 * C[1] * Dm[0] + 3 * C[0] * Dm[1] + k * Dm[2])
        elif case == "C8":
            # on Y=+1 the carrier is the C1 operator on N-1 qubits; its Z_d blocks have
            # half the traces computed above (each block occurs twice)
            kap = 2
            k = D // 4
            C = [x // 2 for x in bj[1]]
            Dm = [x // 2 for x in bj[-1]]
            val = Fraction(kap, 8) * (k * C[2] + 3 * C[1] * Dm[0] + 3 * C[0] * Dm[1] + k * Dm[2])
        elif case in ("C6", "C11", "C14"):
            kap = 2 if case == "C6" else 1
            k = D // 4
            val = 0
            for se in (1, -1):
                C, Dm = bj[(se, 1)], bj[(se, -1)]
                val += Fraction(kap, 8) * (k * C[2] + 3 * C[1] * Dm[0] + 3 * C[0] * Dm[1] + k * Dm[2])
        elif case in ("C12", "C15"):
            k = D // 4
            sg = 4 if case == "C12" else -4
            val = 0
            for se in (1, -1):
                p1, p2, p3 = bj[se]
                val += Fraction(1, 4) * ((k + sg) * p3 + 3 * p1 * p2)
        pred.append(val)
    res["pred_trL3"] = [str(x) for x in pred]
    res["pred_ok"] = all(Fraction(res["trL3"][j]) == pred[j] for j in range(2))
    return res


def main():
    N = int(sys.argv[1])
    cases = sys.argv[2:] or ["C1", "C3", "C5", "C6", "C8", "C11", "C12", "C14", "C15"]
    PS = Paulis(N)
    for case in cases:
        res = run_case(case, N, PS, theoremA=(N <= 4))
        print("=" * 70)
        print(case, "N =", N)
        for k, v in res["info"].items():
            print("   ", k, ":", v)
        print("    |X| =", res.get("X"), " |S| =", res["S"], " |O| =", res["O"],
              " outside lines =", res["Lout"], " section lines =", res.get("Lsec"))
        if not res["constructed"]:
            print("    construction not available at this N")
            continue
        print("    r (points where sigma != tau) =", res["r"])
        if res["r"] <= 8:
            print("    differ at:", res["diffpts"])
        print("    cospectral (p_1..p_D equal):", res["cospectral"])
        print("    tr Lambda^3 sigma, tau =", res["trL3"], " difference =", res["trL3"][0] - res["trL3"][1])
        print("    tr Lambda^2 sigma, tau =", res["trL2"])
        print("    predicted from block traces (E6/E8/E9):", res["pred_trL3"], " match:", res["pred_ok"])
        print("    Theorem A check:", res.get("theoremA", "skipped"))
        print("    block power sums (p1,p2,p3) sigma:", res["blocks"][0])
        print("    block power sums (p1,p2,p3) tau  :", res["blocks"][1])
        print("    charpoly coefficients (sigma):", res["charpoly_sigma"])
        sys.stdout.flush()


if __name__ == "__main__":
    main()

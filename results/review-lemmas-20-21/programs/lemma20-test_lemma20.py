"""Independent numerical test of Lemma 20 (restriction) and the closure property.

Labels v=(a|c), a,c in F_2^n as ints; P_v = i^{a.c} X^a Z^c (Hermitian).
B(u,v) = a.c' + a'.c mod 2.  q_0(a|c) = a.c mod 2.  q_c(v) = q_0(v) + B(c,v).
"""
import itertools, random
import numpy as np

def pc(x): return bin(x).count("1")

def pauli(n, a, c):
    k = 2 ** n
    M = np.zeros((k, k), dtype=complex)
    for b in range(k):
        # X^a Z^c |b> = (-1)^{c.b} |b+a>
        M[b ^ a, b] = (-1) ** pc(c & b)
    return (1j) ** pc(a & c) * M

def B(u, v, n):
    a, c = u >> n, u & ((1 << n) - 1)
    a2, c2 = v >> n, v & ((1 << n) - 1)
    return (pc(a & c2) + pc(a2 & c)) % 2

def q0(v, n):
    a, c = v >> n, v & ((1 << n) - 1)
    return pc(a & c) % 2

def lab(n, word):
    """word: string, leftmost = qubit n-1, rightmost = qubit 0."""
    a = c = 0
    for i, ch in enumerate(reversed(word)):
        if ch in "XY": a |= 1 << i
        if ch in "ZY": c |= 1 << i
    return (a << n) | c

def closed(X, n):
    S = set(X)
    for u, v in itertools.combinations(X, 2):
        if B(u, v, n) == 0 and (u ^ v) not in S:
            return False
    return True

def run(n, X, d, P, trials=3, name=""):
    D = 2 ** n
    H = [s for s in X if B(s, d, n) == 0]
    O = [p for p in X if B(p, d, n) == 1]
    Oi = {p: i for i, p in enumerate(O)}
    Xs = set(X)
    assert closed(X, n), name + " not closed"
    if not O:
        print(f"{name:28s} n={n} O empty, skipped"); return 0
    worst = 0.0
    for _ in range(trials):
        sig = {s: random.choice([-1, 1]) for s in H}
        A = np.zeros((D, D), dtype=complex) + sum((sig[s] * P[s] for s in H), np.zeros((D, D), dtype=complex))
        # Lambda from lines
        L = np.zeros((len(O), len(O)))
        nlines = 0
        for s in H:
            for u, v in itertools.combinations(O, 2):
                if u ^ v == s and B(u, v, n) == 0:
                    prod = P[s] @ P[u] @ P[v]
                    sl = prod[0, 0].real
                    assert np.allclose(prod, sl * np.eye(D))
                    L[Oi[u], Oi[v]] += sl * sig[s]
                    L[Oi[v], Oi[u]] += sl * sig[s]
                    nlines += 1
        # matrix of Psi in basis P_p via HS inner product
        M = np.zeros((len(O), len(O)))
        for p in O:
            T = 0.5 * (A @ P[p] + P[p] @ A)
            coeffs = {}
            resid = T.copy()
            for q in O:
                cq = np.trace(P[q] @ T) / D
                assert abs(cq.imag) < 1e-12
                M[Oi[q], Oi[p]] = cq.real
                resid = resid - cq * P[q]
            assert np.allclose(resid, 0), "Psi leaves V"
        worst = max(worst, np.abs(M - L).max())
        # spectrum check
        ev1 = np.sort(np.linalg.eigvalsh(L))
    print(f"{name:28s} n={n} |X|={len(X)} |H|={len(H)} |O|={len(O)} lines={nlines} max|M-L|={worst}")
    return worst

random.seed(1)
for n in (2, 3):
    pts = list(range(1, 4 ** n))
    P = {v: pauli(n, v >> n, v & ((1 << n) - 1)) for v in pts}
    for v in pts:
        assert np.allclose(P[v], P[v].conj().T)
    W = pts
    Qp = [v for v in pts if q0(v, n) == 0]
    cY = lab(n, "I" * (n - 1) + "Y")
    Qm = [v for v in pts if (q0(v, n) + B(cY, v, n)) % 2 == 0]
    eZ = lab(n, "Z" + "I" * (n - 1))
    eY = lab(n, "Y" + "I" * (n - 1))
    confs = {
        "W": W, "Q+": Qp, "Q-(c=Y0)": Qm,
        "HW=W.eZ": [v for v in W if B(v, eZ, n) == 0],
        "CP=Q+.eZ": [v for v in Qp if B(v, eZ, n) == 0],
        "CM=Q-.eZ": [v for v in Qm if B(v, eZ, n) == 0],
        "PAR=Q+.eY": [v for v in Qp if B(v, eY, n) == 0],
    }
    for nm, X in confs.items():
        for d in random.sample(pts, 4):
            run(n, X, d, P, trials=2, name=nm + f" d={d}")

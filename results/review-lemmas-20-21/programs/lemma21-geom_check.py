"""Build the actual configurations, random sign carriers, and compare tr Lambda^3 with (E8)/(E9)
evaluated on the actual blocks of A_sigma.  Qubit q is bit q; qubit 0 is the rightmost factor."""
import itertools, sys
import numpy as np
from fractions import Fraction

I2 = np.eye(2); Xm = np.array([[0, 1], [1, 0]]); Zm = np.diag([1, -1])

def pauli(N, a, c):
    M = np.array([[1]], dtype=complex)
    for q in reversed(range(N)):  # qubit N-1 leftmost
        f = np.linalg.matrix_power(Xm, (a >> q) & 1) @ np.linalg.matrix_power(Zm, (c >> q) & 1)
        M = np.kron(M, f)
    return (1j) ** bin(a & c).count("1") * M

def symp(u, v):
    return (bin(u[0] & v[1]).count("1") + bin(u[1] & v[0]).count("1")) & 1

def q0(v):
    return bin(v[0] & v[1]).count("1") & 1

def qc(v, c):
    return (q0(v) + (symp(v, c) if c else 0)) & 1

def allpts(N):
    return [(a, c) for a in range(2 ** N) for c in range(2 ** N) if (a, c) != (0, 0)]

def addv(u, v):
    return (u[0] ^ v[0], u[1] ^ v[1])

def Yon(q):
    return (1 << q, 1 << q)

def Zon(q):
    return (0, 1 << q)

def config(case, N):
    P = allpts(N)
    if case == "C1":
        return P, Zon(N - 1), None
    if case == "C3":
        return [v for v in P if q0(v) == 0], Zon(N - 1), None
    if case == "C5":
        c = Yon(0)
        return [v for v in P if qc(v, c) == 0], Zon(N - 1), None
    if case in ("C12", "C15"):
        e = Zon(N - 1); c = None if case == "C12" else Yon(0)
        return [v for v in P if qc(v, c) == 0 and symp(v, e) == 0], Yon(N - 2), e
    if case in ("C6", "C11", "C14"):
        e = Zon(N - 1); mask = (1 << (N - 1)) - 1
        c = Yon(0) if case == "C14" else None
        X = []
        for v in P:
            if v[0] >> (N - 1):  # X or Y on qubit N-1: not in cone
                continue
            y = (v[0] & mask, v[1] & mask)
            if y == (0, 0):
                X.append(v)  # vertex e
            elif case == "C6" or qc(y, c) == 0:
                X.append(v)
        return X, Zon(N - 2), e
    raise ValueError(case)

def run(case, N, trials=3):
    X, d, e = config(case, N)
    Xs = set(X)
    H = [v for v in X if symp(v, d) == 0]
    O = [v for v in X if symp(v, d) == 1]
    idx = {v: i for i, v in enumerate(O)}
    Pm = {v: pauli(N, *v) for v in X}
    D = 2 ** N
    rng = np.random.default_rng(7)
    out = []
    for _ in range(trials):
        sig = {s: int(rng.choice([-1, 1])) for s in H}
        L = np.zeros((len(O), len(O)), dtype=np.int64)
        for s in H:
            for p in O:
                if symp(s, p) == 0:
                    q = addv(s, p)
                    assert q in Xs and q in idx
                    prod = Pm[s] @ Pm[p] @ Pm[q]
                    sL = prod[0, 0].real
                    assert np.allclose(prod, sL * np.eye(D)) and abs(abs(sL) - 1) < 1e-12
                    L[idx[q], idx[p]] = int(round(sL)) * sig[s]
        assert (L == L.T).all()
        t3 = int(np.trace(L @ L @ L))
        A = sum(sig[s] * Pm[s] for s in H)
        Pd = pauli(N, *d)
        def trp(Pr, j):
            return Fraction(int(round(np.trace(Pr @ np.linalg.matrix_power(A, j)).real)), 1)
        if e is None:
            kap = 2 if case == "C1" else 1
            k = D // 2
            Pp, Pn = (np.eye(D) + Pd) / 2, (np.eye(D) - Pd) / 2
            a = [trp(Pp, j) for j in range(4)]; b = [trp(Pn, j) for j in range(4)]
            f = Fraction(kap, 8) * (k * a[3] + 3 * a[2] * b[1] + 3 * a[1] * b[2] + k * b[3])
        elif case in ("C12", "C15"):
            eps = 1 if case == "C12" else -1
            kb = D // 4; Pe = pauli(N, *e)
            f = Fraction(0)
            for sgn in (1, -1):
                Pr = (np.eye(D) + sgn * Pe) / 2 @ (np.eye(D) + Pd) / 2
                p = [trp(Pr, j) for j in range(4)]
                f += Fraction(1, 4) * ((kb + 4 * eps) * p[3] + 3 * p[1] * p[2])
        else:
            kap = 2 if case == "C6" else 1
            kb = D // 4; Pe = pauli(N, *e)
            f = Fraction(0)
            for sgn in (1, -1):
                Pa = (np.eye(D) + sgn * Pe) / 2
                a = [trp(Pa @ (np.eye(D) + Pd) / 2, j) for j in range(4)]
                b = [trp(Pa @ (np.eye(D) - Pd) / 2, j) for j in range(4)]
                f += Fraction(kap, 8) * (kb * a[3] + 3 * a[2] * b[1] + 3 * a[1] * b[2] + kb * b[3])
        out.append((t3, f))
        assert f == t3, (case, N, t3, f)
    return len(H), len(O), out

for case, Ns in [("C1", [3, 4]), ("C3", [3, 4]), ("C5", [3, 4]), ("C12", [3, 4]), ("C15", [3, 4]),
                 ("C6", [3, 4]), ("C11", [3, 4]), ("C14", [3, 4])]:
    for N in Ns:
        h, o, res = run(case, N)
        print(case, N, h, o, [(t, str(f)) for t, f in res])
print("all geometric (E8)/(E9) checks OK")

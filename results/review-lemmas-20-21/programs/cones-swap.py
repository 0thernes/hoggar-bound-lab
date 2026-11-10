import sys, numpy as np
from pauli import *

def qc(v, c):
    return (q0(v) + B(c, v)) & 1

def swap_case(N, kind):
    n1 = N - 1
    if kind == "W":
        Y = allpts(n1); kappa = 2
    elif kind == "Q+":
        Y = [v for v in allpts(n1) if q0(v) == 0]; kappa = 1
    else:
        c = (1, 1)
        Y = [v for v in allpts(n1) if qc(v, c) == 0]; kappa = 1
    E = (0, 1 << (N - 1)); d = (0, 1 << (N - 2))
    assert d in Y
    X = [E] + Y + [add(v, E) for v in Y]
    sg, ta = {}, {}
    dm = 1 << (N - 2)
    for v in X:
        if B(v, d): continue
        if v in (E, d, add(E, d)):
            sg[v] = ta[v] = 1; continue
        al = (v[1] >> (N - 1)) & 1
        be = (v[1] >> (N - 2)) & 1
        assert (v[0] >> (N - 2)) == 0
        sg[v] = (-1) ** (al + be); ta[v] = (-1) ** be
    return X, d, E, sg, ta, kappa

def predicted(A, N, E, d, kappa):
    PE = mat(E, N); Pd = mat(d, N)
    tot = []
    for a in (1, -1):
        blocks = []
        for b in (1, -1):
            Pr = (np.eye(1 << N) + a * PE) @ (np.eye(1 << N) + b * Pd) / 4
            w, V = np.linalg.eigh(Pr)
            B_ = V[:, w > 0.5]
            blocks.append(np.linalg.eigvalsh(B_.conj().T @ A @ B_))
        g, dl = blocks
        tot += [(x + y) / 2 for x in g for y in dl] * kappa
    return np.sort(tot)

for N, kind in ((3, "W"), (3, "Q+"), (4, "W"), (4, "Q+"), (4, "Q-"), (5, "Q-")):
    X, d, E, sg, ta, kappa = swap_case(N, kind)
    out = []
    for s in (sg, ta):
        H, O, L, nl = completion(X, d, s)
        A = carrier(H, s, N)
        ok = np.allclose(np.sort(np.linalg.eigvalsh(L.astype(float))), predicted(A, N, E, d, kappa))
        out.append((len(H), len(O), nl, tr3(L), ok, spec(A)))
    print(N, kind, out[0][:5], out[1][:5], "diff", out[0][3] - out[1][3], "cospec", np.allclose(out[0][5], out[1][5]))

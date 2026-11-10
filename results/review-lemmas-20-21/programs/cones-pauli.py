import numpy as np
from itertools import product

pc = lambda x: bin(x).count("1")

def B(u, v):
    return (pc(u[0] & v[1]) + pc(u[1] & v[0])) & 1

def add(u, v):
    return (u[0] ^ v[0], u[1] ^ v[1])

def mat(v, n):
    a, c = v
    D = 1 << n
    M = np.zeros((D, D), dtype=complex)
    ph = 1j ** pc(a & c)
    for b in range(D):
        M[b ^ a, b] = ph * (-1) ** pc(c & b)
    return M

def prod_sign(u, v):
    """P_u P_v = s P_{u+v} for commuting u,v; return s (int)."""
    w = add(u, v)
    e = pc(u[0] & u[1]) + pc(v[0] & v[1]) - pc(w[0] & w[1]) + 2 * pc(u[1] & v[0])
    e %= 4
    assert e in (0, 2), e
    return 1 if e == 0 else -1

def allpts(n):
    return [(a, c) for a in range(1 << n) for c in range(1 << n) if (a, c) != (0, 0)]

def q0(v):
    return pc(v[0] & v[1]) & 1

def completion(X, d, sigma):
    Xs = set(X)
    H = [v for v in X if B(v, d) == 0]
    O = [v for v in X if B(v, d) == 1]
    idx = {p: i for i, p in enumerate(O)}
    L = np.zeros((len(O), len(O)), dtype=np.int64)
    nlines = 0
    for i, u in enumerate(O):
        for j in range(i + 1, len(O)):
            v = O[j]
            if B(u, v) == 0:
                s = add(u, v)
                assert s in Xs and B(s, d) == 0
                # line sign s_L: P_s P_u P_v = s_L I ; P_u P_v = prod_sign * P_s, P_s^2=I
                sL = prod_sign(u, v)
                L[i, j] = L[j, i] = sL * sigma[s]
                nlines += 1
    return H, O, L, nlines

def carrier(H, sigma, n):
    return sum(sigma[s] * mat(s, n) for s in H)

def tr3(L):
    return int(np.trace(L @ L @ L))

def spec(M):
    return np.round(np.sort(np.linalg.eigvalsh(M)), 6)

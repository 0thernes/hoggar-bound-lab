import sys, numpy as np
sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
from pauli import *

def c3_pair(N, u, t, Fdirs):
    m = N - 1
    top = 1 << m
    pstar = (0, top)
    X = [v for v in allpts(N) if q0(v) == 0]
    sig, tau = {}, {}
    for v in X:
        if B(v, pstar) == 1:
            continue
        if v == pstar:
            sig[v] = tau[v] = 1; continue
        a, c = v[0], v[1] & (top - 1)
        hi = v[1] >> m
        assert v[0] < top
        if a == 0:
            e = (-1) ** pc(c & t)
        else:
            ac = pc(a & c); assert ac % 2 == 0
            e = (-1) ** pc(c & u[a]) * (-1) ** (ac // 2)
        sig[v] = e
        tau[v] = -e if (hi == 1 and a in Fdirs) else e
    return X, pstar, sig, tau

def cone_lift(X, sig, N):
    E = 1 << N  # new qubit index N
    e = (0, E)
    X2 = [e] + list(X) + [add(v, e) for v in X]
    s2 = {e: 1}
    for v, val in sig.items():
        s2[v] = val; s2[add(v, e)] = val
    return X2, s2

N = 3
u = {1: 0, 2: 1, 3: 0}
X, d, sg, ta = c3_pair(N, u, 2, {1, 2, 3})
for name, s in (("sigma", sg), ("tau", ta)):
    H, O, L, nl = completion(X, d, s)
    A = carrier(H, s, N)
    print(name, "base", len(H), len(O), nl, "tr3", tr3(L), "tr2", int(np.trace(L@L)), "spec A", spec(A))
    X2, s2 = cone_lift(X, s, N)
    H2, O2, L2, nl2 = completion(X2, d, s2)
    A2 = carrier(H2, s2, N + 1)
    print(name, "lift", len(H2), len(O2), nl2, "tr3", tr3(L2))
    lam = np.linalg.eigvalsh(L.astype(float))
    pred = np.sort(np.concatenate([2 * lam + 1, -np.ones(len(O))]))
    print("  Lambda' spec matches:", np.allclose(np.sort(np.linalg.eigvalsh(L2.astype(float))), pred))
    predA = np.sort(np.concatenate([2 * np.linalg.eigvalsh(A) + 1, -np.ones(1 << N)]))
    print("  A' spec matches:", np.allclose(np.sort(np.linalg.eigvalsh(A2)), predA))
    # block form check in basis (p, e+p)
    idx = {p: i for i, p in enumerate(O2)}
    E = (0, 1 << N)
    perm = [idx[p] for p in O] + [idx[add(p, E)] for p in O]
    Lb = L2[np.ix_(perm, perm)]
    I = np.eye(len(O), dtype=np.int64)
    print("  block form:", np.array_equal(Lb, np.block([[L, L + I], [L + I, L]])))
print("spec equal base:", np.allclose(spec(carrier(completion(X,d,sg)[0], sg, N)), spec(carrier(completion(X,d,ta)[0], ta, N))))

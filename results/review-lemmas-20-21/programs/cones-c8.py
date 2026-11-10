import numpy as np, random
from pauli import *
random.seed(1)
for N in (4, 5):
    m = N - 1; T = 1 << m; mask = T - 1
    e = (T, T); d = (0, 1 << (N - 2))
    X = [v for v in allpts(N) if q0(v) == 0 and B(v, e) == 0]
    f = lambda v: (v[0] & mask, v[1] & mask)
    W = allpts(m); dd = (0, 1 << (N - 2))
    assert sorted(map(f, X)) == sorted(W)
    for trial in range(3):
        sW = {w: random.choice((1, -1)) for w in W if B(w, dd) == 0}
        sX = {v: sW[f(v)] for v in X if B(v, d) == 0}
        H, O, L, _ = completion(X, d, sX)
        H1, O1, L1, _ = completion(W, dd, sW)
        idx = {p: i for i, p in enumerate(O1)}
        perm = [idx[f(p)] for p in O]
        same = np.array_equal(L, L1[np.ix_(perm, perm)])
        A = carrier(H, sX, N); A1 = carrier(H1, sW, m)
        s1 = np.linalg.eigvalsh(A1)
        dbl = np.allclose(np.sort(np.linalg.eigvalsh(A)), np.sort(np.concatenate([s1, s1])))
        print(N, len(H), len(O), "Lambda equal:", same, "spec doubled:", dbl)

#!/usr/bin/env python3
"""(1) Table 7 cone-lift rows for C11, built on the C11 configuration itself.
(2) Remark (c): lambda_max gap of the Theorem 17 pair (floating point, sanity only)."""
import sys
import numpy as np
sys.path.insert(0, sys.argv[1])
import verify19 as V


def build(case, N, PS, carrier_fn):
    spec = V.case_spec(case, N)
    D = 1 << N
    allv = [(a, c) for a in range(D) for c in range(D) if (a, c) != (0, 0)]
    Yset = allv if spec["W"] else [v for v in allv if V.qform(spec["c"], v) == 0]
    e, d = spec["e"], spec["d"]
    X = [v for v in Yset if e is None or V.B(v, e) == 0]
    Xs = set(X)
    S = [v for v in X if V.B(v, d) == 0]
    O = [v for v in X if V.B(v, d) == 1]
    Ss = set(S)
    car = {s: carrier_fn(s) for s in S}
    oidx = {p: i for i, p in enumerate(O)}
    Lam = [np.zeros((len(O), len(O)), dtype=np.int64) for _ in range(2)]
    nout = 0
    for i, u in enumerate(X):
        for v in X[i + 1:]:
            if V.B(u, v) == 0:
                w = V.add(u, v)
                if w > v and w in Xs:
                    L = (u, v, w)
                    inS = [x for x in L if x in Ss]
                    if len(inS) == 1:
                        nout += 1
                        s = inS[0]
                        p, q = [x for x in L if x not in Ss]
                        sL = PS.line_sign(*L)
                        for j in range(2):
                            Lam[j][oidx[p], oidx[q]] = Lam[j][oidx[q], oidx[p]] = sL * car[s][j]
    A = []
    for j in range(2):
        R = sum(car[s][j] * PS.dense[s][0] for s in S)
        I = sum(car[s][j] * PS.dense[s][1] for s in S)
        A.append((R, I))
    ps = [V.power_sums(A[j], D) for j in range(2)]
    tr3 = [int(np.sum(Lam[j].dot(Lam[j]) * Lam[j].T)) for j in range(2)]
    return len(S), len(O), nout, ps[0] == ps[1], tr3, Lam


for N in (4, 5):
    PS = V.Paulis(N)
    g = V.graph_data(N - 2)  # C3 base on N-1 qubits has N-2 graph qubits
    m1 = (1 << (N - 1)) - 1
    dprime = V.Zq(N - 2)

    def lift(s):
        if s == V.Zq(N - 1):  # e
            return (1, 1)
        base = (s[0] & m1, s[1] & m1)
        return V.c1c3_carrier(N - 1, base, dprime, g)
    res = build("C11", N, PS, lift)
    print("C11 cone lift N=%d: |S|=%d |O|=%d Lout=%d cospectral=%s trL3=%s" % ((N,) + res[:5]))

for N in (4, 5):
    PS = V.Paulis(N)
    g = V.graph_data(N - 1)
    d = V.Zq(N - 1)
    res = build("C3", N, PS, lambda s: V.c1c3_carrier(N, s, d, g))
    lm = [np.linalg.eigvalsh(res[5][j].astype(float)).max() for j in range(2)]
    print("C3 N=%d: lambda_max sigma=%.6f tau=%.6f gap=%.6f (k/2=%d)" % (N, lm[0], lm[1], lm[1] - lm[0], (1 << (N - 1)) // 2))

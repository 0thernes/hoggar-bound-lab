#!/usr/bin/env python3
"""Check the controlled-NOT claims of the pair swap (C6, C11, C14) and Remark (g),
and the general cone-coefficient claim before (E10)."""
import sys
import numpy as np
sys.path.insert(0, sys.argv[1])
import verify19 as V

N = int(sys.argv[2]) if len(sys.argv) > 2 else 4
PS = V.Paulis(N)
D = 1 << N
top, sub = N - 1, N - 2
# U = CNOT(control = qubit N-2 (d), target = qubit N-1 (e)): flips Z_e when Z_d = -1
perm = np.array([b ^ (1 << top) if (b >> sub) & 1 else b for b in range(D)])
U = np.zeros((D, D), dtype=np.int64)
for b in range(D):
    U[perm[b], b] = 1


def conj(P):  # U P U^T (U real orthogonal)
    return (U.dot(P[0]).dot(U.T), U.dot(P[1]).dot(U.T))


def which(M):
    for v, P in PS.dense.items():
        for sgn in (1, -1):
            if np.array_equal(M[0], sgn * P[0]) and np.array_equal(M[1], sgn * P[1]):
                return sgn, V.word(v, N), v
    return None


for name, v in [("Z_e", V.Zq(top)), ("Z_d", V.Zq(sub)), ("X_e", V.Xq(top)), ("X_d", V.Xq(sub))]:
    print("U", name, "U^dag =", which(conj(PS.dense[v]))[:2])

for case in ("C6", "C11", "C14"):
    spec = V.case_spec(case, N)
    allv = [(a, c) for a in range(D) for c in range(D) if (a, c) != (0, 0)]
    Yset = allv if spec["W"] else [v for v in allv if V.qform(spec["c"], v) == 0]
    e, d = spec["e"], spec["d"]
    X = [v for v in Yset if V.B(v, e) == 0]
    S = [v for v in X if V.B(v, d) == 0]
    O = [v for v in X if V.B(v, d) == 1]
    car = V.make_carriers(case, N, S, spec)
    A = []
    for j in range(2):
        R = sum(car[s][j] * PS.dense[s][0] for s in S)
        I = sum(car[s][j] * PS.dense[s][1] for s in S)
        A.append((R, I))
    UA = conj(A[0])
    ok = np.array_equal(UA[0], A[1][0]) and np.array_equal(UA[1], A[1][1])
    gS = {which(conj(PS.dense[s]))[2] for s in S}
    gO = {which(conj(PS.dense[p]))[2] for p in O}
    gX = gS | gO
    print(case, "N=%d: U A_sigma U^dag == A_tau:" % N, ok,
          "| g(S)==S:", gS == set(S), "| g(O)==O:", gO == set(O),
          "| g(X)==X:", gX == set(X), "| |g(O) & X| =", len(gO & set(X)))

# A sign carrier on a cone whose base observable sits in all four blocks with +-2
case = "C6"
spec = V.case_spec(case, N)
w = (1, 0)  # X on qubit 0, a base observable
e, d = spec["e"], spec["d"]
pts = {(al, be): V.add(V.add(w, e) if al else w, d) if be else (V.add(w, e) if al else w)
       for al in (0, 1) for be in (0, 1)}
vals = {(0, 0): 1, (1, 0): 1, (0, 1): 1, (1, 1): -1}
for se in (1, -1):
    for sd in (1, -1):
        coef = sum(vals[(al, be)] * (se ** al) * (sd ** be) for al in (0, 1) for be in (0, 1))
        print("block (Z_e,Z_d)=(%+d,%+d): coefficient of %s = %d" % (se, sd, V.word(w, N), coef))

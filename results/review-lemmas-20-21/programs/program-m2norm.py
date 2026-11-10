#!/usr/bin/env python3
"""Sum of |M2|^2 over every outside Pauli in the C12/C15 symmetry check, as the program builds f and g,
and with g = f (the vacuous variant)."""
import os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "scripts"))
import conjecture_e as ce


def norms(n, cc, use_theta):
    D = 1 << n
    kb = 1 << (n - 2)
    e, dd = ce.letter(n - 1, "Z"), ce.letter(n - 2, "Y")
    X = ce.perp(ce.Q(n, cc), e)
    O = [v for v in X if ce.B(v, dd) == 1]
    c = None if cc == (0, 0) else cc
    Pc = ce.pauli(c, n) if c is not None else (np.eye(D, dtype=np.int64), np.zeros((D, D), dtype=np.int64))
    tot, zero_blocks = 0, 0
    for a in (0, 1):
        F = []
        for w in range(kb):
            vr = np.zeros(D, dtype=np.int64); vi = np.zeros(D, dtype=np.int64)
            base = (a << (n - 1)) | w
            vr[base] = 1; vi[base | (1 << (n - 2))] = 1
            F.append((vr, vi))
        G = [((Pc[0] @ f[0] + Pc[1] @ f[1], Pc[1] @ f[0] - Pc[0] @ f[1]) if use_theta else f) for f in F]
        for v in O:
            Pv = ce.pauli(v, n)
            s = 0
            for g in G:
                y = (Pv[0] @ g[0] - Pv[1] @ g[1], Pv[0] @ g[1] + Pv[1] @ g[0])
                for f in F:
                    re = int(f[0] @ y[0] + f[1] @ y[1]); im = int(f[0] @ y[1] - f[1] @ y[0])
                    s += re * re + im * im
            tot += s
            zero_blocks += (s == 0)
    return len(O), tot, zero_blocks, 2 * len(O) * 4 * kb


for n in (4, 5):
    for name, cc in (("C12", (0, 0)), ("C15", ce.letter(0, "Y"))):
        for th in (True, False):
            print(n, name, "theta" if th else "g=f", norms(n, cc, th))

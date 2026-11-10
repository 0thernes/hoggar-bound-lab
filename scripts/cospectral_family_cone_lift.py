#!/usr/bin/env python3
"""
cospectral_family_cone_lift.py - case C11: the cone lift of the carriers of publication/ADDENDUM-c3-all-qubits.md.

B. W. Jonah, "The reach of the section-square law" (doi:10.5281/zenodo.23524332, version 0.5), Lemma D (D2):
a pair of sign carriers that refutes the strict law in case C3 on N qubits gives a pair that refutes it in
case C11 on N + 1 qubits.  With Theorem 17 of the addendum (C3 for every N >= 4) this gives C11 for every
N >= 5.  This program does not use the lemma.  It builds the lifted configurations from the definitions and
checks the two lifted carriers directly, for the base pairs with N = 3, 4, 5 (lifted: 4, 5, 6 qubits):

  * every observable is a Kronecker product of the literal 2 x 2 matrices;
  * the base carriers are read as sign tables from results/cospectral_family.json (labels a + 2^N c, bit 0 =
    rightmost tensor factor), and nothing else is taken from that file except the recorded cubic traces,
    which are compared with the values computed here;
  * X' = { v (x) t : v real N-qubit observable or identity, t in {I, Z} } without the identity, with the new
    qubit as first tensor factor; e = Z on the new qubit; d' = d = Z on the top old qubit;
  * section S' = points of X' commuting with d', outside O' = the rest; contexts = triples of pairwise
    commuting points of X' with product +I or -I; sign of a context from the matrix product;
  * lifted carrier: +1 at e, and the base value at s and at e + s.

Checks, in integers: X' is the cone e-perp in the hyperbolic quadric of N + 1 qubits; the vertices of S' are
e, d, e + d (the pattern of C11); the two lifted carrier operators have the same characteristic polynomial;
their completion cubic traces differ, by 8 times the base difference; the structure formulas of the lemma.

  python scripts/cospectral_family_cone_lift.py            (about two minutes)
Writes results/cospectral_family_cone_lift.json.
"""
import itertools, json, os, sys
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
I2 = np.array([[1, 0], [0, 1]], dtype=np.int64)
X2 = np.array([[0, 1], [1, 0]], dtype=np.int64)
Z2 = np.array([[1, 0], [0, -1]], dtype=np.int64)
W2 = X2 @ Z2                                   # = -iY; an even number of these factors gives a real observable
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print("%s  %s%s" % ("PASS" if ok else "FAIL", name, ("   [" + detail + "]") if detail else ""), flush=True)


def pc(x):
    return bin(x).count("1")


def matrix(a, c, nq):
    """The real observable i^(a.c) X^a Z^c on nq qubits (a.c even), as a Kronecker product."""
    k = pc(a & c)
    assert k % 2 == 0
    M = np.array([[1]], dtype=np.int64)
    for q in range(nq - 1, -1, -1):
        ab, cb = (a >> q) & 1, (c >> q) & 1
        M = np.kron(M, (I2, Z2, X2, W2)[2 * ab + cb])
    return -M if (k // 2) % 2 else M           # Y = i XZ, so k factors Y contribute i^k = (-1)^(k/2)


def commute(u, v):
    return (pc(u[0] & v[1]) + pc(u[1] & v[0])) % 2 == 0


def add(u, v):
    return (u[0] ^ v[0], u[1] ^ v[1])


def charpoly(M):
    """Exact characteristic polynomial (Faddeev-LeVerrier, Python integers, Cayley-Hamilton as a check)."""
    n = M.shape[0]
    A = M.astype(object)
    Mk = np.zeros((n, n), dtype=object)
    for i in range(n):
        Mk[i, i] = 1
    coeffs = [1]
    for k in range(1, n + 1):
        AM = A.dot(Mk)
        tr = sum(AM[i, i] for i in range(n))
        assert tr % k == 0
        ck = -tr // k
        coeffs.append(ck)
        Mk = AM
        for i in range(n):
            Mk[i, i] += ck
    assert not Mk.any(), "Cayley-Hamilton check failed"
    return coeffs


def analyse(points, d, carrier, nq, mats, full_products):
    """Section, outside set, carrier operator and completion matrix of a configuration, from the definitions."""
    S = [p for p in points if commute(p, d)]
    O = [p for p in points if not commute(p, d)]
    assert set(S) == set(carrier)
    D = 1 << nq
    A = np.zeros((D, D), dtype=np.int64)
    for s in S:
        A += carrier[s] * mats[s]
    idx = {p: i for i, p in enumerate(O)}
    pset = set(points)
    L = np.zeros((len(O), len(O)), dtype=np.int64)
    ordered = 0
    for p in O:
        Pp = mats[p]
        for q in O:
            if p == q or not commute(p, q):
                continue
            s = add(p, q)
            assert s in pset and commute(s, d)
            Ps = mats[s]
            if full_products:
                prod = Ps @ Pp @ mats[q]                        # P_s P_p P_q = s_l I
                sl = int(prod[0, 0])
                assert sl in (1, -1) and np.array_equal(prod, sl * np.eye(D, dtype=np.int64))
            else:                                               # one row of the same product (signed permutations)
                row = (Ps[0] @ Pp) @ mats[q]
                sl = int(row[0])
                assert sl in (1, -1) and not row[1:].any()
            L[idx[p], idx[q]] = sl * carrier[s]
            ordered += 1
    assert np.array_equal(L, L.T) and ordered % 2 == 0
    return {"S": S, "O": O, "contexts": ordered // 2, "A": A, "L": L}


def tr3(L):
    L2 = L @ L
    return int((L2 * L.T).sum())


def run(N, rec, out):
    m, top, full = N - 1, 1 << (N - 1), 1 << N
    Q = [(a, c) for a in range(full) for c in range(full) if (a, c) != (0, 0) and pc(a & c) % 2 == 0]
    d = (0, top)
    mats = {p: matrix(p[0], p[1], N) for p in Q}
    base = {}
    for name in ("A", "B"):
        neg = set(rec["negative_section_labels"][name])
        car = {p: (-1 if p[0] + (p[1] << N) in neg else 1) for p in Q if commute(p, d)}
        assert sum(1 for v in car.values() if v < 0) == len(neg)
        base[name] = (car, analyse(Q, d, car, N, mats, N <= 4))
    bA, bB = base["A"][1], base["B"][1]
    t3 = {k: tr3(base[k][1]["L"]) for k in base}
    t2 = {k: int((base[k][1]["L"] ** 2).sum()) for k in base}
    check("base C3 pair, N = %d: %d section points, %d outside points, %d outside contexts; cubic traces %d and %d as recorded"
          % (N, len(bA["S"]), len(bA["O"]), bA["contexts"], t3["A"], t3["B"]),
          len(bA["S"]) == rec["section"] and len(bA["O"]) == rec["outside"] and bA["contexts"] == rec["outside_contexts"]
          and t3["A"] == rec["completion_trace_cube"]["A"] and t3["B"] == rec["completion_trace_cube"]["B"])

    nq, ebit = N + 1, 1 << N
    e = (0, ebit)
    Xp = [(a, c | tb) for (a, c) in Q + [(0, 0)] for tb in (0, ebit) if (a, c | tb) != (0, 0)]
    full2 = 1 << nq
    quadric = [(a, c) for a in range(full2) for c in range(full2) if (a, c) != (0, 0) and pc(a & c) % 2 == 0]
    cone = [p for p in quadric if commute(p, e)]
    Sp = [p for p in Xp if commute(p, d)]
    verts = sorted(p for p in Sp if all(commute(p, s) for s in Sp))
    check("lift to %d qubits: X' is e-perp in the hyperbolic quadric (%d points); d' is on it, in e-perp, not e; "
          "the vertices of the section are e, d', e + d'" % (nq, len(Xp)),
          len(quadric) == (full2 - 1) * (full2 // 2 + 1) and set(cone) == set(Xp) and d in set(Xp) and d != e
          and commute(d, e) and verts == sorted([e, d, add(e, d)]))
    mats2 = {p: matrix(p[0], p[1], nq) for p in Xp}
    lifted = {}
    for name in ("A", "B"):
        car = base[name][0]
        lc = {e: 1}
        for s, v in car.items():
            lc[s] = v
            lc[add(s, e)] = v
        lifted[name] = analyse(Xp, d, lc, nq, mats2, nq <= 4)
        lifted[name]["carrier"] = lc
    lA, lB = lifted["A"], lifted["B"]
    check("lifted case: %d section points, %d outside points, %d outside contexts"
          % (len(lA["S"]), len(lA["O"]), lA["contexts"]),
          len(lA["S"]) == 2 * len(bA["S"]) + 1 and len(lA["O"]) == 2 * len(bA["O"])
          and lA["contexts"] == 4 * bA["contexts"] + len(bA["O"]) and lB["contexts"] == lA["contexts"])
    Zn = np.kron(Z2, np.eye(1 << N, dtype=np.int64))
    check("lifted carrier operators: A' = Z_e + (1 + Z_e) (x) A for both carriers",
          all(np.array_equal(lifted[k]["A"], Zn + np.kron(I2 + Z2, base[k][1]["A"])) for k in lifted))
    cpA, cpB = charpoly(lA["A"]), charpoly(lB["A"])
    check("the two lifted carrier operators have the same characteristic polynomial (degree %d, exact)" % (1 << nq),
          cpA == cpB and not np.array_equal(lA["A"], lB["A"]))
    l3 = {k: tr3(lifted[k]["L"]) for k in lifted}
    check("lifted completion cubic traces %d and %d differ by %d = 8 * (%d)"
          % (l3["A"], l3["B"], l3["A"] - l3["B"], t3["A"] - t3["B"]),
          l3["A"] != l3["B"] and l3["A"] - l3["B"] == 8 * (t3["A"] - t3["B"]))
    check("as the lemma predicts: tr L'^3 = 8 tr L^3 + 12 tr L^2 + 6 tr L for both carriers",
          all(l3[k] == 8 * t3[k] + 12 * t2[k] + 6 * int(np.trace(base[k][1]["L"])) for k in l3))
    out[str(nq)] = {"qubits": nq, "base_qubits": N, "points": len(Xp), "section": len(lA["S"]), "outside": len(lA["O"]),
                    "outside_contexts": lA["contexts"], "carrier_charpoly": [int(x) for x in cpA],
                    "completion_trace_cube": {"A": l3["A"], "B": l3["B"]}, "difference": l3["A"] - l3["B"],
                    "label_convention": "label = a + 2^N' c on N' = %d qubits, bit 0 = rightmost tensor factor" % nq,
                    "negative_section_labels": {k: sorted(p[0] + (p[1] << nq) for p, v in lifted[k]["carrier"].items() if v < 0)
                                                for k in lifted}}


def main():
    data = json.load(open(os.path.join(ROOT, "results", "cospectral_family.json"), encoding="utf-8"))
    out = {}
    for N in (3, 4, 5):
        run(N, data[str(N)], out)
    npass = sum(1 for _, ok in CHECKS if ok)
    out["checks"] = {"passed": npass, "total": len(CHECKS)}
    with open(os.path.join(ROOT, "results", "cospectral_family_cone_lift.json"), "w", encoding="utf-8", newline="\n") as fh:
        json.dump(out, fh, indent=1)
    print("\n%d of %d checks passed" % (npass, len(CHECKS)))
    sys.exit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

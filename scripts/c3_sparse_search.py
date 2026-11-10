#!/usr/bin/env python3
"""
c3_sparse_search.py - exhaustive search for C3 cospectral sign carriers near the all-plus carrier.

  python scripts/c3_sparse_search.py KMAX BLOCKQUBITS        (BLOCKQUBITS = N - 1, KMAX at most 3)

A sign carrier with sign +1 at the polar point has blocks
        C = I + 2 sum_{P in R_C} e_P P,      D = -I + 2 sum_{P in R_D} e_P P,
where every real non-identity Pauli observable P of BLOCKQUBITS qubits lies in exactly one of R_C, R_D and
e_P = +-1 (publication/ADDENDUM-c3-all-qubits.md, Step 1).  The all-plus carrier has every P in R_C with
e_P = +1.  This program visits every carrier obtained from it by changing at most KMAX observables, each in one
of three ways: 1 sign flip in C; 2 move to D with sign +; 3 move to D with sign -.

What is decided, and why the answer is exact for the visited set

  1. Two cospectral carriers have the same integers p_k = tr C^k + tr D^k for every k.  Each carrier gets a
     64-bit key, a hash of (p_3, p_4, p_5, p_6); p_1 and p_2 are the same for all carriers.  Equal integers
     always give equal keys, so a cospectral pair is never split between two groups of equal key.
  2. With at most three observables in D, the spectrum of D is a function of the two integers
     (tr D^3, tr D^4).  Reason: D = -I + 2E, where E is a sum of r <= 3 distinct signed Pauli observables, and
     the spectrum of E depends only on which pairs anticommute and, for three commuting ones, on whether
     their product is +I or -I or neither:
        r = 0: 0.   r = 1: +-1.   r = 2: {2, 0, 0, -2} (commuting) or +-sqrt 2 (anticommuting).
        r = 3: {3,-1,-1,-1} or {-3,1,1,1} (commuting, product +-I); {+-1 +-1 +-1} (commuting, independent);
               +-sqrt 2 +- 1 (one anticommuting pair); {+-sqrt 5, +-1} (two); +-sqrt 3 (three).
     These ten spectra have ten different pairs (tr D^3, tr D^4).  The program does not rely on this
     paragraph: it lists every matrix D that occurs, computes its characteristic polynomial in integers, and
     checks that equal pairs (tr D^3, tr D^4) always come with equal polynomials ("d_spectrum_table").
  3. The pair (tr D^3, tr D^4) is stored exactly for every carrier, together with r_D, the number of
     observables in D.  A cospectral pair with different block spectra has different spectra of D, hence
     different stored values inside one group.  So if no group holds two different stored values, the
     visited set contains no cospectral pair with different block spectra, and in particular (Step 6 of the
     addendum) no cospectral pair with different completion cubic traces.
  4. Every group that does hold two different stored values is settled exactly: the characteristic
     polynomials of C and D of all its members are computed in Python integers, and the program counts the
     classes of cospectral carriers that contain different polynomials of D, and those that contain
     different r_D.

  5. For four qubits the program also places the pair of Section 8 of the combined paper: it converts the two
     published sign tables into changes of the all-plus carrier and reports the class that contains them.

Recorded runs (results/c3_sparse_search.json):
  KMAX 3, BLOCKQUBITS 3 (four qubits):    182 176 carriers  (a few seconds)
  KMAX 3, BLOCKQUBITS 4 (five qubits): 10 908 676 carriers  (about fifteen minutes)

Arithmetic: the matrices of the main loop are float64 with integer entries.  With r = 1 + 2 |R| >= the
spectral norm of C, every entry of C^2 and C^3 and every partial sum of the products is at most r^3, and the
sums that give tr C^3 .. tr C^6, with mixed signs included, have absolute partial sums at most dim * r^6
(Cauchy-Schwarz), which is below 2^53 for BLOCKQUBITS <= 4; so every value is an exact integer whatever the
order of summation.  The characteristic polynomials of D use int64; their intermediate values are bounded
by 7^16 * 2^16 < 2^63, so nothing overflows, and the Cayley-Hamilton identity at the end is a consistency
check.  The characteristic polynomials of C use Python integers.
"""
import bisect, itertools, json, os, sys, time
from math import comb
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 3
MQ = int(sys.argv[2]) if len(sys.argv) > 2 else 3
assert 0 <= KMAX <= 3, "the argument on the spectrum of D needs at most three observables in D"
assert 3 <= MQ <= 4, "exactness of the float64 traces is shown for BLOCKQUBITS 3 and 4 only"
DIM = 1 << MQ
BATCH = 1500
OFF = 1 << 23


def pc(x):
    return bin(x).count("1")


def real_pauli(v):
    x, z = v & (DIM - 1), v >> MQ
    k = pc(x & z)
    if k % 2:
        return None
    s0 = -1.0 if (k // 2) % 2 else 1.0
    M = np.zeros((DIM, DIM))
    for b in range(DIM):
        M[b ^ x, b] = s0 * (-1.0 if pc(z & b) % 2 else 1.0)
    return M


def word(v):
    x, z = v & (DIM - 1), v >> MQ
    return "".join("IXZY"[((x >> j) & 1) + 2 * ((z >> j) & 1)] for j in range(MQ - 1, -1, -1))


labels, mats = [], []
for v in range(1, DIM * DIM):
    M = real_pauli(v)
    if M is not None:
        labels.append(v)
        mats.append(M)
P = np.array(mats)
PI = np.rint(P).astype(np.int64)
nP = len(labels)
assert nP == (DIM - 1) * (DIM + 2) // 2
assert DIM * (1 + 2 * nP) ** 6 < 2 ** 53
I = np.eye(DIM)
C0 = I + 2 * P.sum(axis=0)
D0 = -I
CC = np.array([0.0, 4.0, 2.0, 2.0])          # subtracted from C, by type
DD = np.array([0.0, 0.0, 2.0, -2.0])         # added to D, by type
M1 = np.array([0x9E3779B97F4A7C15, 0xC2B2AE3D27D4EB4F, 0x165667B19E3779F9, 0x27D4EB2F165667C5], dtype=np.uint64)


def power_traces(X):
    X2 = X @ X
    X3 = X2 @ X
    out = np.empty((X.shape[0], 4), dtype=np.int64)
    out[:, 0] = np.rint(np.einsum("mii->m", X3))
    out[:, 1] = np.rint(np.einsum("mij,mij->m", X2, X2))
    out[:, 2] = np.rint(np.einsum("mij,mij->m", X2, X3))
    out[:, 3] = np.rint(np.einsum("mij,mij->m", X3, X3))
    return out


def build(cb, ty):
    C = np.broadcast_to(C0, (len(cb), DIM, DIM)).copy()
    D = np.broadcast_to(D0, (len(cb), DIM, DIM)).copy()
    for j in range(cb.shape[1]):
        C -= CC[ty[j]] * P[cb[:, j]]
        if DD[ty[j]] != 0:
            D += DD[ty[j]] * P[cb[:, j]]
    return C, D


def d_code(rD, t3, t4):
    """One integer holding (r_D, tr D^3, tr D^4) exactly."""
    assert np.all(np.abs(t3) < OFF) and np.all(t4 >= 0) and np.all(t4 < (1 << 24))
    return (int(rD) << 48) + ((t3 + OFF) << 24) + t4


def charpolys_int64(A):
    """Characteristic polynomials of a stack of integer matrices (Faddeev-LeVerrier, int64)."""
    B, k, _ = A.shape
    eye = np.eye(k, dtype=np.int64)
    M = np.broadcast_to(eye, A.shape).copy()
    coef = np.empty((B, k + 1), dtype=np.int64)
    coef[:, 0] = 1
    for j in range(1, k + 1):
        AM = A @ M
        t = np.einsum("bii->b", AM)
        assert not np.any(t % j)
        c = -(t // j)
        coef[:, j] = c
        M = AM + c[:, None, None] * eye
    assert not M.any(), "Cayley-Hamilton check failed"
    return coef


def charpoly_exact(Mf):
    """Characteristic polynomial of one integer matrix, in Python integers."""
    A = [[int(v) for v in row] for row in np.rint(Mf).astype(np.int64).tolist()]
    k = len(A)
    c = [1]
    M = [[1 if i == j else 0 for j in range(k)] for i in range(k)]
    for j in range(1, k + 1):
        cols = list(zip(*M))
        AM = [[sum(x * y for x, y in zip(row, col)) for col in cols] for row in A]
        t = sum(AM[i][i] for i in range(k))
        assert t % j == 0
        cj = -t // j
        c.append(cj)
        M = [[AM[i][q] + (cj if i == q else 0) for q in range(k)] for i in range(k)]
    assert all(v == 0 for row in M for v in row), "Cayley-Hamilton check failed"
    return tuple(c)


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return tuple(r)


def d_spectrum_table():
    """Every matrix D that occurs: equal (tr D^3, tr D^4) must come with equal characteristic polynomials."""
    eye = np.eye(DIM, dtype=np.int64)
    table, count = {}, 0
    for r in range(0, KMAX + 1):
        if r == 0:
            combos = np.zeros((1, 0), dtype=np.int32)
        else:
            combos = np.array(list(itertools.combinations(range(nP), r)), dtype=np.int32).reshape(-1, r)
        for signs in itertools.product((1, -1), repeat=r):
            for s in range(0, len(combos), 20000):
                cb = combos[s:s + 20000]
                D = np.broadcast_to(-eye, (len(cb), DIM, DIM)).copy()
                for j in range(r):
                    D += 2 * signs[j] * PI[cb[:, j]]
                D2 = D @ D
                t3 = np.einsum("bij,bji->b", D2, D)
                t4 = np.einsum("bij,bij->b", D2, D2)
                rows = np.unique(np.concatenate([d_code(r, t3, t4)[:, None], charpolys_int64(D)], axis=1), axis=0)
                for row in rows:
                    table.setdefault(int(row[0]) & ((1 << 48) - 1), set()).add((r,) + tuple(int(v) for v in row[1:]))
                count += len(cb)
    return {"matrices": count, "pairs_tr_D3_tr_D4": len(table),
            "single_valued": all(len(v) == 1 for v in table.values())}


def main():
    os.makedirs(os.path.join(ROOT, "build"), exist_ok=True)
    t0 = time.time()
    dtable = d_spectrum_table()
    print("matrices D: %d, pairs (tr D^3, tr D^4): %d, each pair has one characteristic polynomial and one r_D: %s"
          % (dtable["matrices"], dtable["pairs_tr_D3_tr_D4"], dtable["single_valued"]), flush=True)
    assert dtable["single_valued"]
    total = sum(comb(nP, k) * 3 ** k for k in range(KMAX + 1))
    fH = os.path.join(ROOT, "build", "c3_sparse_keys_H.npy")
    fK = os.path.join(ROOT, "build", "c3_sparse_keys_K.npy")
    H = np.lib.format.open_memmap(fH, mode="w+", dtype=np.uint64, shape=(total,))
    K = np.lib.format.open_memmap(fK, mode="w+", dtype=np.int64, shape=(total,))
    starts, combos_k, types_k = {}, {}, {}
    pos = 0
    for k in range(0, KMAX + 1):
        if k == 0:
            combos = np.zeros((1, 0), dtype=np.int32)
            types = np.zeros((1, 0), dtype=np.int32)
        else:
            combos = np.array(list(itertools.combinations(range(nP), k)), dtype=np.int32).reshape(-1, k)
            types = np.array(list(itertools.product((1, 2, 3), repeat=k)), dtype=np.int32).reshape(-1, k)
        combos_k[k], types_k[k] = combos, types
        for tcode, ty in enumerate(types):
            starts[(k, tcode)] = pos
            rD = int(np.count_nonzero(ty >= 2))
            for s in range(0, len(combos), BATCH):
                cb = combos[s:s + BATCH]
                C, D = build(cb, ty)
                pC = power_traces(C)
                pD = power_traces(D)
                H[pos:pos + len(cb)] = ((pC + pD).astype(np.uint64) * M1).sum(axis=1)
                K[pos:pos + len(cb)] = d_code(rD, pD[:, 0], pD[:, 1])
                pos += len(cb)
        print("at most %d changes: %d carriers, %.0f s" % (k, pos, time.time() - t0), flush=True)
    assert pos == total
    keys_start = sorted((v, kk) for kk, v in starts.items())
    first = [v for v, _ in keys_start]

    def changes(i):
        st, (k, tcode) = keys_start[bisect.bisect_right(first, i) - 1]
        return [(int(j), int(t)) for j, t in zip(combos_k[k][i - st], types_k[k][tcode])]

    def blocks(ch):
        C, D = C0.copy(), D0.copy()
        for j, t in ch:
            C -= CC[t] * P[j]
            D += DD[t] * P[j]
        return C, D

    order = np.argsort(H, kind="stable")
    hs = H[order]
    bounds = np.concatenate(([0], np.flatnonzero(hs[1:] != hs[:-1]) + 1, [total]))
    del hs
    ks = K[order]
    flagged = np.flatnonzero(np.minimum.reduceat(ks, bounds[:-1]) != np.maximum.reduceat(ks, bounds[:-1]))
    print("carriers %d, distinct keys %d, groups holding two different (r_D, tr D^3, tr D^4): %d"
          % (total, len(bounds) - 1, len(flagged)), flush=True)

    settled, classes_blocks, classes_rd, found, found_polys = 0, 0, 0, [], []
    dcache = {}
    for gi in flagged:
        a, b = int(bounds[gi]), int(bounds[gi + 1])
        by_a = {}
        for idx in order[a:b]:
            ch = changes(int(idx))
            C, D = blocks(ch)
            dkey = tuple((j, t) for j, t in ch if t >= 2)
            if dkey not in dcache:
                dcache[dkey] = charpoly_exact(D)
            pd = dcache[dkey]
            by_a.setdefault(pmul(charpoly_exact(C), pd), {}).setdefault(pd, []).append((len(dkey), ch))
            settled += 1
        for poly_a, by_d in by_a.items():
            if len(by_d) > 1:
                classes_blocks += 1
                reps = [lst[0] for lst in by_d.values()]
                if len({r for r, _ in reps}) > 1:
                    classes_rd += 1
                if len(found) < 60:
                    found.append([{"r_D": r, "members": len(lst),
                                   "changes": [[int(labels[j]), word(labels[j]), t] for j, t in ch]}
                                  for (r, ch), lst in zip(reps, by_d.values())])
                    found_polys.append(poly_a)
    record = {"block_qubits": MQ, "qubits": MQ + 1, "max_changes": KMAX, "real_block_paulis": nP,
              "carriers": int(total), "distinct_keys": int(len(bounds) - 1),
              "d_spectrum_table": dtable,
              "groups_with_two_d_values": int(len(flagged)), "members_settled_exactly": settled,
              "cospectral_classes_with_different_blocks": classes_blocks,
              "cospectral_classes_with_different_rD": classes_rd,
              "classes": found}
    print("members settled by exact characteristic polynomials: %d" % settled)
    print("classes of cospectral carriers with different block spectra: %d; of these with different r_D "
          "(different completion cubic traces): %d" % (classes_blocks, classes_rd))
    for g in found[:8]:
        print("  ", " | ".join("r_D %d: %s" % (c["r_D"], " ".join("%s:%d" % (w, t) for _, w, t in c["changes"])) for c in g))
    if MQ == 3:
        # the pair of Section 8 of the combined paper: negative section labels, label = a + 16 c on four qubits,
        # polar point ZIII = 128
        where = {v: j for j, v in enumerate(labels)}
        pair = {}
        for name, neg in (("sigma0", (48, 102, 176, 230)), ("sigma1", (87, 144, 176, 215))):
            neg = set(neg)
            assert 128 not in neg
            ch = []
            for v in labels:                       # block label v = a + 8 c;  I (x) P = a + 16 c,  Z (x) P = a + 16 (c + 8)
                a_, c_ = v & 7, v >> 3
                si, sz = (a_ + 16 * c_) in neg, (a_ + 16 * (c_ + 8)) in neg
                if si or sz:
                    ch.append((where[v], 1 if (si and sz) else (2 if sz else 3)))
            assert 2 * sum(1 for _, t in ch if t == 1) + sum(1 for _, t in ch if t > 1) == len(neg)
            C, D = blocks(ch)
            pair[name] = {"changes": [[int(labels[j]), word(labels[j]), t] for j, t in ch],
                          "r_D": sum(1 for _, t in ch if t > 1), "poly": pmul(charpoly_exact(C), charpoly_exact(D))}
        same = pair["sigma0"]["poly"] == pair["sigma1"]["poly"]
        visited = all(len(v["changes"]) <= KMAX for v in pair.values())
        cls = found_polys.index(pair["sigma0"]["poly"]) if pair["sigma0"]["poly"] in found_polys else None
        record["section8_pair"] = {"changes": {k: v["changes"] for k, v in pair.items()},
                                   "r_D": {k: v["r_D"] for k, v in pair.items()},
                                   "both_in_the_visited_set": visited, "cospectral": same,
                                   "class_index_in_classes": cls}
        print("the pair of Section 8: %s | %s; in the visited set: %s; cospectral: %s; class number %s of the list above"
              % (" ".join("%s:%d" % (w, t) for _, w, t in pair["sigma0"]["changes"]),
                 " ".join("%s:%d" % (w, t) for _, w, t in pair["sigma1"]["changes"]), visited, same,
                 "none" if cls is None else cls + 1))
        assert same and visited and cls is not None
    print("time: %d s" % round(time.time() - t0))
    del H, K, ks, order
    for f in (fH, fK, os.path.join(ROOT, "build", "c3_sparse_keys_S.npy")):
        try:
            os.remove(f)
        except OSError:
            pass
    path = os.path.join(ROOT, "results", "c3_sparse_search.json")
    runs = {}
    if os.path.exists(path):
        runs = json.load(open(path, encoding="utf-8"))
    runs["kmax%d_block%d" % (KMAX, MQ)] = record
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(runs, fh, indent=1)
    print("SPARSE-SEARCH-DONE")


if __name__ == "__main__":
    main()

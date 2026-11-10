#!/usr/bin/env python3
"""
cospectral_family.py - cospectral sign carriers with different completion spectra, for every number of qubits.

Setting (combined paper, Section 8; Jonah's case C3).  N qubits, m = N - 1, n = 2^m.  Q is the set of real
N-qubit Pauli observables, p = Z I ... I, H the observables of Q that commute with p (the section) and O the
others (the outside points).  A sign carrier sigma : H -> {+1, -1} has the carrier operator
A = sum_{s in H} sigma(s) P_s, which is block diagonal, A = C (+) D with n x n blocks, and the completion matrix
Lambda indexed by O, with the entry s_L sigma(s) at (p, q) for every context L = {s, p, q}, s in H, p, q in O.

Construction (publication/ADDENDUM-c3-all-qubits.md).  Choose a vertex t of F_2^m and, for every non-zero a in
F_2^m, a vertex u_a.  Let G be the graph on F_2^m with the n - 1 edges {u_a, u_a + a}.  On the block observable
P = i^(a.c) X^a Z^c (a.c even) put the sign
        eps(a, c) = (-1)^(c . u_a) (-1)^((a.c)/2)   for a != 0,        eps(0, c) = (-1)^(c . t).
Carrier A:  sigma(p) = +1,  sigma(I (x) P) = sigma(Z (x) P) = eps(P).   Then  C = -I + 2n |t><t| + n Adj(G),  D = -I.
Carrier B:  the same, except sigma(Z (x) P) = -eps(P) for the observables P whose a is the difference of an
            edge of F, where F is a set of edges of G that is a union of connected components of G not
            containing t.  Then  C = -I + 2n |t><t| + n Adj(G - F),  D = -I + n Adj(F).
The two carrier operators have the same spectrum, because moving whole components from one block to the other
does not change the union of the two block spectra.  The completion matrices have different cubic traces:
        tr Lambda_A^3 - tr Lambda_B^3 = -(3/2) n^3 |F|,        |F| the number of edges of F.

Checked here, in exact integer arithmetic (floating point is not used in any comparison):
  * on the full configuration (all Pauli matrices, all contexts, all signs) for the graph of the theorem with
    N = 4, 5 and, with --six, 6, and for the triangle with N = 3;
  * on the full configuration for random graphs with random sets of components, N = 3 and 4;
  * two negative controls on the full configuration: a moved edge that is not a whole component, and a moved
    component that contains t, must destroy the equality of the characteristic polynomials;
  * on the blocks only, for random graphs with m = 2 .. 5: Steps 2 to 4 of the proof and the arithmetic of
    Step 6 (there the trace formula of Step 5 is used, not tested).

Labels in the output: an observable X^a Z^c on N qubits has the label a + 2^N c, and bit 0 is the rightmost
tensor factor (so 2^(2N-1) is Z I ... I; for N = 4 this is 128 = ZIII), as in the combined paper.

  python scripts/cospectral_family.py [--six]

Writes results/cospectral_family.json with --six (the record that CI compares) and
results/cospectral_family_n3-5.json without it, so that a quick run never overwrites the record.
"""
import itertools, json, os, random, sys
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print("%s  %s%s" % ("PASS" if ok else "FAIL", name, ("   [" + detail + "]") if detail else ""), flush=True)
    return ok


def pc(x):
    return bin(x).count("1")


# ---------------------------------------------------------------- exact polynomials (Python integers)
def charpoly(A):
    """Coefficients of det(t - A), highest first, by the Faddeev-LeVerrier recurrence with exact divisions."""
    n = len(A)
    A = [[int(x) for x in row] for row in A]
    c = [1]
    M = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    for k in range(1, n + 1):
        AM = [[sum(a * b for a, b in zip(row, col)) for col in zip(*M)] for row in A]
        t = sum(AM[i][i] for i in range(n))
        assert t % k == 0
        ck = -t // k
        c.append(ck)
        M = [[AM[i][j] + (ck if i == j else 0) for j in range(n)] for i in range(n)]
    assert all(x == 0 for row in M for x in row)
    return c


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


# ---------------------------------------------------------------- graphs on F_2^m with one edge per difference
def default_graph(m):
    """Edge {0, 1} is a component; every other difference b sits on an edge that avoids the vertices 0 and 1.
    This is u_1 = 0, u_2 = u_3 = 4, u_a = 2 for a >= 4."""
    n = 1 << m
    u = {1: 0}
    for b in range(2, n):
        u[b] = next(v for v in range(2, n) if v not in (b, b ^ 1) and (v ^ b) not in (0, 1))
    return u


def components(n, u):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, v in u.items():
        parent[find(v)] = find(v ^ a)
    comp = {}
    for a, v in u.items():
        comp.setdefault(find(v), []).append(a)
    return comp, find


def block_formula(n, u, t, moved):
    C = -np.eye(n, dtype=np.int64)
    Dm = -np.eye(n, dtype=np.int64)
    C[t, t] += 2 * n
    for a, v in u.items():
        T = Dm if a in moved else C
        T[v, v ^ a] += n
        T[v ^ a, v] += n
    return C, Dm


def eps_block(m, u, t, a, c):
    w = t if a == 0 else u[a]
    return (-1 if pc(c & w) % 2 else 1) * (-1 if (pc(a & c) // 2) % 2 else 1)


# ---------------------------------------------------------------- the full configuration
def full_check(N, u, t, moved, out, quiet=False, expect_words=None, require_components=True):
    """All checks of the construction on the full configuration.  Returns {key: passed}.  With quiet=True
    nothing is printed or counted, and `out` is not written."""
    m, n, D = N - 1, 1 << (N - 1), 1 << N
    tag = "N = %d" % N
    result = {}

    def chk(key, name, ok, detail=""):
        result[key] = bool(ok)
        if not quiet:
            check(name, ok, detail)

    def xz(v):
        return v & (D - 1), v >> N

    def word(v):
        x, z = xz(v)
        return "".join("IXZY"[((x >> j) & 1) + 2 * ((z >> j) & 1)] for j in range(N - 1, -1, -1))

    if require_components:
        comp, find = components(n, u)
        roots = {find(u[a]) for a in moved}
        assert find(t) not in roots and set(moved) == {a for r in roots for a in comp[r]}, "moved is not a union of components away from t"

    pts = [v for v in range(1, D * D) if pc((v & (D - 1)) & (v >> N)) % 2 == 0]
    dlabel = (n) << N                                       # c = 2^(N-1), a = 0 : Z I ... I
    xs = {v: xz(v) for v in pts}

    def commute(u_, v_):
        return (pc(xs[u_][0] & xs[v_][1]) + pc(xs[u_][1] & xs[v_][0])) % 2 == 0

    S = [v for v in pts if commute(v, dlabel)]
    O = [v for v in pts if not commute(v, dlabel)]
    Sset = set(S)
    chk("counts", "%s: %d real observables, section %d = 1 + (n-1)(n+2), outside %d = n^2; p = %s"
        % (tag, len(pts), len(S), len(O), word(dlabel)),
        len(pts) == (D - 1) * (D + 2) // 2 and len(S) == 1 + (n - 1) * (n + 2) and len(O) == n * n)

    def sign(u_, v_):
        (xu, zu), (xv, zv) = xs[u_], xs[v_]
        e = (pc(xu & zu) + pc(xv & zv) - pc((xu ^ xv) & (zu ^ zv))) % 4
        assert e % 2 == 0
        return (-1 if e == 2 else 1) * (-1 if pc(zu & xv) % 2 else 1)

    def matrix(v):
        x, z = xs[v]
        s0 = -1 if (pc(x & z) // 2) % 2 else 1
        M = np.zeros((D, D), dtype=np.int64)
        for b in range(D):
            M[b ^ x, b] = s0 * (-1 if pc(z & b) % 2 else 1)
        return M

    # outside contexts: an outside point p and a section point s that commute give the context {s, p, s + p}
    opos = {p: i for i, p in enumerate(O)}
    out_lines = []
    for s in S:
        if s == dlabel:
            continue
        for p in O:
            q = s ^ p
            if p < q and commute(s, p):
                out_lines.append((s, p, q))
    ok = all(q in opos for _, _, q in out_lines)
    L_out = len(out_lines)
    # every outside point lies on the same number of outside contexts
    deg = np.zeros(len(O), dtype=np.int64)
    for s, p, q in out_lines:
        deg[opos[p]] += 1
        deg[opos[q]] += 1
    chk("contexts", "%s: %d = n^2 |R| / 2 outside contexts, each with one section point; %d through every outside point"
        % (tag, L_out, int(deg[0])),
        ok and len(set(deg.tolist())) == 1 and L_out == n * n * ((n - 1) * (n + 2) // 2) // 2)

    PM = {v: matrix(v) for v in S}
    if N <= 5:
        PO = {p: matrix(p) for p in O}
        good = True
        for s, p, q in out_lines:
            good = good and np.array_equal(PM[s] @ PO[p] @ PO[q], sign(s, p) * np.eye(D, dtype=np.int64))
        chk("signs", "%s: context signs from the phase formula agree with the matrix products, all %d" % (tag, L_out), good)

    def carrier(moved_dirs):
        sig = {dlabel: 1}
        for a in range(n):
            for c in range(n):
                if (a, c) == (0, 0) or pc(a & c) % 2:
                    continue
                e = eps_block(m, u, t, a, c)
                sig[a + (c << N)] = e                                   # I (x) P
                sig[a + ((c + n) << N)] = -e if (a in moved_dirs) else e   # Z (x) P
        assert set(sig) == Sset
        return sig

    # the n^2 outside blocks M_p (top right blocks of the outside observables) are orthogonal, of norm n
    MO = np.array([matrix(p)[:n, n:] for p in O], dtype=np.int64)          # (n^2, n, n)
    flat = MO.reshape(len(O), n * n)
    gram = np.array_equal(flat @ flat.T, n * np.eye(len(O), dtype=np.int64))

    res = {}
    for name, mv in (("A", set()), ("B", set(moved))):
        sig = carrier(mv)
        A = np.zeros((D, D), dtype=np.int64)
        for s in S:
            A += sig[s] * PM[s]
        C, Dm = A[:n, :n], A[n:, n:]
        blockdiag = not A[:n, n:].any() and not A[n:, :n].any()
        Cf, Df = block_formula(n, u, t, mv)
        Lam = np.zeros((len(O), len(O)), dtype=np.int64)
        for s, p, q in out_lines:
            val = sign(s, p) * sig[s]
            Lam[opos[p], opos[q]] += val
            Lam[opos[q], opos[p]] += val
        L2 = Lam @ Lam
        tr2 = int(np.trace(L2))
        tr3 = int((L2 * Lam).sum())
        tC = [int(np.trace(np.linalg.matrix_power(C, k))) for k in (1, 2, 3)]
        tD = [int(np.trace(np.linalg.matrix_power(Dm, k))) for k in (1, 2, 3)]
        num = n * tC[2] + 3 * tC[1] * tD[0] + 3 * tC[0] * tD[1] + n * tD[2]
        # Lambda is the matrix of M -> (C M + M D)/2 in the basis of the outside blocks M_p
        lhs = np.einsum("ij,pjk->pik", C, MO) + np.einsum("pij,jk->pik", MO, Dm)
        rhs = 2 * (Lam.T @ flat).reshape(len(O), n, n)
        res[name] = dict(sig=sig, C=C.copy(), D=Dm.copy(), tr2=tr2, tr3=tr3, num=num, blockdiag=blockdiag,
                         formula=np.array_equal(C, Cf) and np.array_equal(Dm, Df), jordan=np.array_equal(lhs, rhs),
                         neg=sum(1 for v in sig.values() if v < 0),
                         chi=pmul(charpoly(C.tolist()), charpoly(Dm.tolist())),
                         chiC=charpoly(C.tolist()))
    a, b = res["A"], res["B"]
    k = len(moved)
    differ = sorted(s for s in S if a["sig"][s] != b["sig"][s])
    words = [word(s) for s in differ]
    chk("blocks", "%s: both carrier operators are block diagonal, with the blocks -I + 2n|t><t| + n Adj and -I + n Adj of the construction" % tag,
        a["blockdiag"] and b["blockdiag"] and a["formula"] and b["formula"])
    if expect_words is None:
        chk("differ", "%s: the two carriers differ at %d = |F| n/2 section points" % (tag, len(differ)), len(differ) == k * n // 2)
    else:
        chk("differ", "%s: the two carriers differ exactly at the %d points Z (x) W (x) X, W a word in I and Z" % (tag, len(differ)),
            len(differ) == k * n // 2 and sorted(words) == sorted(expect_words))
    chk("charpoly", "%s: the carrier operators have the same characteristic polynomial (degree %d: the exact product of the "
        "two block polynomials), and the blocks C have different ones" % (tag, D),
        a["blockdiag"] and b["blockdiag"] and a["chi"] == b["chi"] and a["chiC"] != b["chiC"])
    chk("jordan", "%s: the %d outside blocks M_p are orthogonal of norm n, and each completion matrix is the matrix of "
        "M -> (CM + MD)/2 in this basis" % (tag, len(O)), gram and a["jordan"] and b["jordan"])
    chk("trace_formula", "%s: tr Lambda^3 from the contexts equals (n trC^3 + 3 trC^2 trD + 3 trC trD^2 + n trD^3)/8 for both carriers" % tag,
        8 * a["tr3"] == a["num"] and 8 * b["tr3"] == b["num"], "tr Lambda^3 = %d and %d" % (a["tr3"], b["tr3"]))
    chk("gap", "%s: the cubic traces differ by -(3/2) n^3 |F| = %d, so the completion spectra differ; tr Lambda^2 is the same"
        % (tag, -3 * n ** 3 * k // 2), a["tr3"] - b["tr3"] == -3 * n ** 3 * k // 2 and a["tr2"] == b["tr2"])
    if not quiet:
        out[str(N)] = {"n": n, "section": len(S), "outside": len(O), "outside_contexts": L_out,
                       "label_convention": "label = a + 2^N c for the observable X^a Z^c on N qubits, bit 0 = rightmost tensor factor",
                       "graph_edges": sorted([int(v), int(v ^ a_)] for a_, v in u.items()), "loop_vertex": t,
                       "moved_differences": sorted(moved), "negative_signs": {"A": a["neg"], "B": b["neg"]},
                       "points_where_the_carriers_differ": [int(s) for s in differ],
                       "words_where_the_carriers_differ": words,
                       "carrier_charpoly": [str(x) for x in a["chi"]],
                       "completion_trace_square": a["tr2"], "completion_trace_cube": {"A": a["tr3"], "B": b["tr3"]},
                       "negative_section_labels": {"A": sorted(int(s) for s in S if a["sig"][s] < 0),
                                                   "B": sorted(int(s) for s in S if b["sig"][s] < 0)}}
    return result


def random_graph(n, rng):
    """A random graph with one edge per difference, a random loop vertex, and a random non-empty set of
    components away from the loop vertex (None if there is no such component)."""
    u = {a: rng.randrange(n) for a in range(1, n)}
    t = rng.randrange(n)
    comp, find = components(n, u)
    movable = [dirs for root, dirs in comp.items() if find(t) != root]
    if not movable:
        return None
    chosen = [dirs for dirs in movable if rng.random() < 0.5] or [movable[0]]
    return u, t, sorted(a for dirs in chosen for a in dirs)


def random_full_tests(N, trials, rng):
    """The general statement on the full configuration: every check of full_check, for random graphs."""
    n = 1 << (N - 1)
    done, ok, sizes = 0, True, set()
    while done < trials:
        g = random_graph(n, rng)
        if g is None:
            continue
        u, t, moved = g
        ok = ok and all(full_check(N, u, t, moved, None, quiet=True).values())
        sizes.add(len(moved))
        done += 1
    return ok, sorted(sizes)


def random_block_tests(m, trials, rng):
    """On the blocks only: Steps 2 to 4 and the arithmetic of Step 6, for random graphs."""
    n = 1 << m
    done = 0
    ok = True
    while done < trials:
        g = random_graph(n, rng)
        if g is None:
            continue
        u, t, moved = g
        moved = set(moved)
        CA, DA = block_formula(n, u, t, set())
        CB, DB = block_formula(n, u, t, moved)
        # the blocks really are the signed sums of the real Paulis (Steps 2 and 3, for the second carrier)
        Csum = np.eye(n, dtype=np.int64)
        Dsum = -np.eye(n, dtype=np.int64)
        for a in range(n):
            for c in range(n):
                if (a, c) == (0, 0) or pc(a & c) % 2:
                    continue
                kappa = eps_block(m, u, t, a, c) * (-1 if (pc(a & c) // 2) % 2 else 1)      # coefficient of X^a Z^c
                T = Dsum if a in moved else Csum
                for b in range(n):
                    T[b ^ a, b] += 2 * kappa * (-1 if pc(c & b) % 2 else 1)
        same_blocks = np.array_equal(Csum, CB) and np.array_equal(Dsum, DB)
        chiA = pmul(charpoly(CA.tolist()), charpoly(DA.tolist()))                           # Step 4
        chiB = pmul(charpoly(CB.tolist()), charpoly(DB.tolist()))

        def num(C, Dm):                                                                     # the formula of Step 5
            tC = [int(np.trace(np.linalg.matrix_power(C, k))) for k in (1, 2, 3)]
            tD = [int(np.trace(np.linalg.matrix_power(Dm, k))) for k in (1, 2, 3)]
            return n * tC[2] + 3 * tC[1] * tD[0] + 3 * tC[0] * tD[1] + n * tD[2]
        ok = ok and same_blocks and chiA == chiB and num(CA, DA) - num(CB, DB) == -12 * n ** 3 * len(moved)
        done += 1
    return ok


def main():
    out = {}
    rng = random.Random(20261110)
    for m in (2, 3, 4, 5):
        check("blocks of %d qubits, 25 random graphs with random sets of components: the signed Pauli sums are the graph "
              "blocks, the carrier polynomials agree, and the trace formula gives the difference -(3/2) n^3 |F|"
              % m, random_block_tests(m, 25, rng))
    for N in (4, 5) + ((6,) if "--six" in sys.argv else ()):
        m = N - 1
        u = default_graph(m)
        assert u == {a: (0 if a == 1 else 4 if a in (2, 3) else 2) for a in range(1, 1 << m)}
        words = ["Z" + "".join(w) + "X" for w in itertools.product("IZ", repeat=N - 2)]
        full_check(N, u, 2, [1], out, expect_words=words)
    # three qubits: the triangle {0, 1, 3} is a component, the loop sits on the isolated vertex 2
    full_check(3, {1: 0, 2: 1, 3: 0}, 2, [1, 2, 3], out)
    # the general statement on full configurations
    for N, trials in ((3, 12), (4, 12)):
        ok, sizes = random_full_tests(N, trials, rng)
        check("N = %d: %d random graphs with random sets of components, on the full configuration: every check above holds"
              % (N, trials), ok, "|F| in %s" % sizes)
    # negative controls, on the full configuration with the graph of the theorem, N = 4
    u = default_graph(3)
    r = full_check(4, u, 2, [2], None, quiet=True, require_components=False)
    check("negative control, N = 4: moving the edge {4, 6}, which is not a whole component, destroys the equality of "
          "the characteristic polynomials (the block formulas still hold)", (not r["charpoly"]) and r["blocks"] and r["jordan"])
    r = full_check(4, u, 2, [2, 3, 4, 5, 6, 7], None, quiet=True, require_components=False)
    check("negative control, N = 4: moving the component that contains the loop vertex destroys it too",
          (not r["charpoly"]) and r["blocks"] and r["jordan"])
    npass = sum(1 for _, ok in CHECKS if ok)
    out["checks"] = [{"name": nme, "pass": ok} for nme, ok in CHECKS]
    out["passed"], out["total"] = npass, len(CHECKS)
    record = "cospectral_family.json" if "--six" in sys.argv else "cospectral_family_n3-5.json"
    with open(os.path.join(ROOT, "results", record), "w", encoding="utf-8", newline="\n") as fh:
        json.dump(out, fh, indent=1)
    print("\n%d of %d checks passed" % (npass, len(CHECKS)))
    sys.exit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

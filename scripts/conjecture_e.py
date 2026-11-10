#!/usr/bin/env python3
"""
conjecture_e.py - Jonah's Conjecture E in all nine vertex cases, on the complete configurations.

Conjecture E (B. W. Jonah, "The reach of the section-square law", doi:10.5281/zenodo.23524332, v0.5):
on sign carriers the strict law fails in every vertex case C1, C3, C5, C6, C8, C11, C12, C14, C15 for
every number of qubits n >= 4.  For each case and each n this program builds the configuration from
the definitions of the note, two sign carriers, and checks in exact arithmetic that

  * the case is the one claimed (type of the quadric, of e and d, and the vertex set of the section);
  * the two carrier operators have the same characteristic polynomial (equal power sums tr A^k for
    k = 1 .. 2^n, computed with Python integers on Gaussian-integer matrices);
  * the two completion matrices, filled from the outside lines and their signs, have different
    cubic traces, so different spectra.

Conventions (those of the note): a point v = (x | z) of F_2^{2n} is the Pauli word with factor
I, X, Z, Y = iXZ on qubit q for (x_q, z_q) = (0,0), (1,0), (0,1), (1,1); here x and z are integers,
bit q for qubit q.  q0(v) = |x and z| mod 2, B is the symplectic form, q_c = q0 + B(c, .), and
Q_c = {v != 0 : q_c(v) = 0} is hyperbolic (q0(c) = 0) or elliptic (q0(c) = 1).  For a line
L = {s, p, q}, P_s P_p P_q = s_L I.  The completion matrix has the entry s_L sigma(s) at (p, q) for
each outside line {s, p, q} with s in the section.

  python scripts/conjecture_e.py            (n = 3, 4 and 5; about ten seconds)
  python scripts/conjecture_e.py 6          (n = 6; about thirty seconds)
Writes results/conjecture_e.json for the default sizes and results/conjecture_e_n<sizes>.json
(for example conjecture_e_n6.json) for any other list, so that a run at other sizes never
overwrites the default record.
"""
import itertools, json, os, sys
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHECKS = []
PHASE = [(1, 0), (0, 1), (-1, 0), (0, -1)]          # i^k as (real, imaginary)


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print("%s  %s%s" % ("PASS" if ok else "FAIL", name, ("   [" + detail + "]") if detail else ""), flush=True)
    return ok


def pc(x):
    return bin(x).count("1")


def q0(v):
    return pc(v[0] & v[1]) & 1


def B(u, v):
    return (pc(u[0] & v[1]) + pc(u[1] & v[0])) & 1


def add(u, v):
    return (u[0] ^ v[0], u[1] ^ v[1])


def qc(c, v):
    return q0(v) ^ B(c, v)


def letter(q, ch):
    return ((1 << q) if ch in "XY" else 0, (1 << q) if ch in "ZY" else 0)


def word(v, n):
    return "".join("IXZY"[((v[0] >> q) & 1) + 2 * ((v[1] >> q) & 1)] for q in range(n - 1, -1, -1))


def tau(u, v):
    """P_u P_v = tau(u, v) P_{u+v}, as (real, imaginary)."""
    e = (pc(u[0] & u[1]) + pc(v[0] & v[1]) - pc((u[0] ^ v[0]) & (u[1] ^ v[1]))) % 4
    s = -1 if pc(u[1] & v[0]) & 1 else 1
    return (PHASE[e][0] * s, PHASE[e][1] * s)


def pauli(v, n):
    """The Hermitian Pauli matrix of v as a pair (real part, imaginary part) of integer matrices."""
    D = 1 << n
    x, z = v
    ph = PHASE[pc(x & z) % 4]
    R = np.zeros((D, D), dtype=np.int64)
    I = np.zeros((D, D), dtype=np.int64)
    for b in range(D):
        s = -1 if pc(z & b) & 1 else 1
        R[b ^ x, b] = ph[0] * s
        I[b ^ x, b] = ph[1] * s
    return R, I


# ------------------------------------------------------------------ configurations
def W(n):
    return [(x, z) for x in range(1 << n) for z in range(1 << n) if (x, z) != (0, 0)]


def Q(n, c):
    return [v for v in W(n) if qc(c, v) == 0]


def perp(points, e):
    return [v for v in points if B(v, e) == 0]


def vertices(S):
    return sorted(s for s in S if all(B(s, t) == 0 for t in S))


# ------------------------------------------------------------------ the graph signs
def eps_even(a, c, u, t):
    """Sign of the observable i^{a.c} X^a Z^c with a.c even: (-1)^{c.t} for a = 0, else
    (-1)^{c.u_a} (-1)^{(a.c)/2}; then eps * P = (-1)^{c.w} X^a Z^c."""
    w = t if a == 0 else u[a]
    k = pc(a & c)
    return (-1 if pc(c & w) & 1 else 1) * (-1 if (k // 2) & 1 else 1)


def eps_odd(a, c, u):
    """Sign of i^{a.c} X^a Z^c with a.c odd: then eps * P = (-1)^{c.u_a} i X^a Z^c."""
    k = pc(a & c)
    return (-1 if pc(c & u[a]) & 1 else 1) * (-1 if ((k - 1) // 2) & 1 else 1)


def default_graph(m):
    """One edge {u_a, u_a + a} per non-zero a in F_2^m.  m >= 3: {0, 1} is a component (u_1 = 0,
    u_2 = u_3 = 4, u_a = 2 otherwise); m = 2: the triangle {0, 1, 3} (u_1 = 0, u_2 = 1, u_3 = 0)."""
    n = 1 << m
    if m == 2:
        return {1: 0, 2: 1, 3: 0}, [1, 2, 3]
    u = {1: 0}
    for b in range(2, n):
        u[b] = next(v for v in range(2, n) if v not in (b, b ^ 1) and (v ^ b) not in (0, 1))
    return u, [1]


def components_ok(m, u, t, moved_dirs):
    n = 1 << m
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
        comp.setdefault(find(v), set()).add(a)
    roots = {find(u[a]) for a in moved_dirs}
    return find(t) not in roots and set(moved_dirs) == set().union(*(comp[r] for r in roots))


def block_sign(a, c, u, t, quaternion_letter=None):
    """(sign, unit) of a block observable.  Units: 'z' for a = 0 (never moved), (a, 'r') for the real
    observables of direction a, (a, 'i') for the imaginary ones, (a, k) for sigma_k (x) imaginary."""
    k = pc(a & c)
    if quaternion_letter is not None:
        return eps_odd(a, c, u), (a, quaternion_letter)
    if a == 0:
        return eps_even(a, c, u, t), "z"
    if k % 2 == 0:
        return eps_even(a, c, u, t), (a, "r")
    return eps_odd(a, c, u), (a, "i")


# ------------------------------------------------------------------ the carriers
def carrier_C1_C3(S, n, d, u, t, moved_units):
    """C1 (X = W) and C3 (X = Q+): d = Z on the top qubit n-1; the block is qubits 0 .. n-2."""
    m = n - 1
    mask = (1 << m) - 1
    sig = {}
    for v in S:
        if v == d:
            sig[v] = 1
            continue
        assert (v[0] >> m) & 1 == 0
        e, unit = block_sign(v[0] & mask, v[1] & mask, u, t)
        sig[v] = -e if ((v[1] >> m) & 1 and unit in moved_units) else e
    return sig


def carrier_C5(S, n, d, u, t, moved_units):
    """C5 (X = Q_c with c = Y on qubit 0): d = Z on the top qubit n-1; the block is qubits 0 .. n-2,
    qubit 0 carries the quaternionic structure and qubits 1 .. n-2 carry the graph."""
    m = n - 1
    mask = (1 << m) - 1
    sig = {}
    for v in S:
        if v == d:
            sig[v] = 1
            continue
        a, c = v[0] & mask, v[1] & mask
        p0 = (a & 1, c & 1)
        a2, c2 = a >> 1, c >> 1
        if p0 == (0, 0):
            e, unit = block_sign(a2, c2, u, t)
        else:
            assert pc(a2 & c2) % 2 == 1
            e, unit = block_sign(a2, c2, u, t, {(1, 0): "X", (0, 1): "Z", (1, 1): "Y"}[p0])
        sig[v] = -e if ((v[1] >> m) & 1 and unit in moved_units) else e
    return sig


def carrier_C12_C15(S, n, e_pt, u, t, moved_units):
    """C12 and C15: e = Z on qubit n-1, d = Y on qubit n-2, the base is qubits 0 .. n-3."""
    mb = n - 2
    mask = (1 << mb) - 1
    sig = {}
    for v in S:
        if v == e_pt:
            sig[v] = 1
            continue
        e, unit = block_sign(v[0] & mask, v[1] & mask, u, t)
        sig[v] = -e if ((v[1] >> (n - 1)) & 1 and unit in moved_units) else e
    return sig


def carrier_cone_swap(S, n, moved):
    """C6, C11, C14 with e = Z on qubit n-1 and d = Z on qubit n-2: value 1 at e, d, e + d; at
    Z_e^t Z_d^b (x) w the value (-1)^(t+b) (all base observables in the block Z_e = Z_d = -1), or, for
    the second carrier, (-1)^b (all of them in the block Z_e = +1, Z_d = -1)."""
    low = (1 << (n - 2)) - 1
    sig = {}
    for v in S:
        t, b = (v[1] >> (n - 1)) & 1, (v[1] >> (n - 2)) & 1
        assert (v[0] >> (n - 2)) == 0
        if (v[0] & low, v[1] & low) == (0, 0):
            sig[v] = 1
        else:
            sig[v] = (-1) ** b if moved else (-1) ** (t + b)
    return sig


def cone_lift(Y, d, sig, n):
    """Jonah's Lemma D (D2): from (Y, d) on n qubits to the cone over Y with vertex e = Z on the new
    qubit n; the carrier is 1 at e and sigma(s) at s and at s + e."""
    top = 1 << n
    X = [(x, z | (t * top)) for (x, z) in Y + [(0, 0)] for t in (0, 1) if (x, z | (t * top)) != (0, 0)]
    e = (0, top)
    lifted = {}
    for v in X:
        if B(v, d) == 0:
            base = (v[0], v[1] & (top - 1))
            lifted[v] = 1 if base == (0, 0) else sig[base]
    return X, e, lifted


# ------------------------------------------------------------------ the checks
def power_sums(S, n, sig):
    D = 1 << n
    R = np.zeros((D, D), dtype=object)
    I = np.zeros((D, D), dtype=object)
    for s in S:
        pr, pi = pauli(s, n)
        R = R + sig[s] * pr
        I = I + sig[s] * pi
    out, Rk, Ik = [], R.copy(), I.copy()
    for k in range(1, D + 1):
        if k > 1:
            Rk, Ik = Rk.dot(R) - Ik.dot(I), Rk.dot(I) + Ik.dot(R)
        tr_r = sum(Rk[i, i] for i in range(D))
        tr_i = sum(Ik[i, i] for i in range(D))
        assert tr_i == 0
        out.append(int(tr_r))
    return out


def completion(S, O, sig, verify_products, n):
    pos = {p: i for i, p in enumerate(O)}
    Sset = set(S)
    L = np.zeros((len(O), len(O)), dtype=np.float64)
    lines = 0
    mats = {}
    for i, p in enumerate(O):
        for q in O[i + 1:]:
            if B(p, q):
                continue
            s = add(p, q)
            assert s in Sset
            sr, si = tau(s, p)
            assert si == 0 and sr in (1, -1)
            if verify_products:
                for v in (s, p, q):
                    if v not in mats:
                        mats[v] = pauli(v, n)
                (a1, b1), (a2, b2), (a3, b3) = mats[s], mats[p], mats[q]
                m12r, m12i = a1 @ a2 - b1 @ b2, a1 @ b2 + b1 @ a2
                pr, pi = m12r @ a3 - m12i @ b3, m12r @ b3 + m12i @ a3
                assert np.array_equal(pr, sr * np.eye(1 << n, dtype=np.int64)) and not pi.any()
            L[pos[p], pos[q]] = L[pos[q], pos[p]] = sr * sig[s]
            lines += 1
    L2 = L @ L
    return lines, int(round(np.trace(L2))), int(round((L2 * L).sum()))


def run_case(name, n, X, d, sig, tau_, claims, expect_vertices, out, verify_products):
    S = [v for v in X if B(v, d) == 0]
    O = [v for v in X if B(v, d) == 1]
    ok_sets = set(sig) == set(S) == set(tau_) and all(sig[s] in (1, -1) and tau_[s] in (1, -1) for s in S)
    verts = vertices(S)
    check("%s, n = %d: %s; %d points, section %d, outside %d; vertices of the section %s"
          % (name, n, claims[0], len(X), len(S), len(O), " ".join(word(v, n) for v in verts)),
          claims[1] and ok_sets and verts == sorted(expect_vertices))
    pa, pb = power_sums(S, n, sig), power_sums(S, n, tau_)
    differ = sum(1 for s in S if sig[s] != tau_[s])
    check("%s, n = %d: the carriers differ at %d section points; tr A^k agrees for k = 1 .. %d (equal characteristic polynomials)"
          % (name, n, differ, 1 << n), pa == pb and differ > 0, "tr A^3 = %d" % pa[2])
    la, a2, a3 = completion(S, O, sig, verify_products, n)
    lb, b2, b3 = completion(S, O, tau_, False, n)
    check("%s, n = %d: %d outside lines%s; tr Lambda^2 = %d for both; tr Lambda^3 = %d and %d differ"
          % (name, n, la, " (signs checked by matrix products)" if verify_products else "", a2, a3, b3),
          la == lb and a2 == b2 and a3 != b3)
    out.setdefault(name, {})[str(n)] = {
        "points": len(X), "section": len(S), "outside": len(O), "outside_lines": la,
        "vertices": [word(v, n) for v in verts], "points_where_the_carriers_differ": differ,
        "carrier_power_sums_1_to_4": pa[:4], "completion_trace_cube": [a3, b3], "difference": a3 - b3,
        "label_convention": "a point (x, z) has the label x + 2^n z; bit q is qubit q",
        "negative_section_labels": {"sigma": sorted(v[0] + (v[1] << n) for v in S if sig[v] < 0),
                                    "tau": sorted(v[0] + (v[1] << n) for v in S if tau_[v] < 0)}}


def units(m, u, moved_dirs, kinds):
    return {(a, k) for a in moved_dirs for k in kinds}


def main():
    out = {}
    sizes = [int(a) for a in sys.argv[1:]] or [3, 4, 5]
    record = "conjecture_e.json" if sizes == [3, 4, 5] else "conjecture_e_n%s.json" % "-".join(map(str, sizes))
    for n in sizes:
        vp = n <= 4
        # --- C1: X = W, d = Z on qubit n-1
        m = n - 1
        u, mv = default_graph(m)
        assert components_ok(m, u, 2, mv)
        d = letter(n - 1, "Z")
        X = W(n)
        S = [v for v in X if B(v, d) == 0]
        F = units(m, u, mv, ("r", "i"))
        run_case("C1", n, X, d, carrier_C1_C3(S, n, d, u, 2, set()), carrier_C1_C3(S, n, d, u, 2, F),
                 ("X = W(2n-1,2), d = %s" % word(d, n), True), [d], out, vp)
        # --- C3: X = Q+, q(d) = 0
        X = Q(n, (0, 0))
        S = [v for v in X if B(v, d) == 0]
        F = units(m, u, mv, ("r",))
        run_case("C3", n, X, d, carrier_C1_C3(S, n, d, u, 2, set()), carrier_C1_C3(S, n, d, u, 2, F),
                 ("X = Q+ (c = 0), q(d) = 0", qc((0, 0), d) == 0), [d], out, vp)
        if n == 3:
            # at n = 3 only C1, C3, C6 and C11 have pairs ([J3] finds the other five lawful there)
            nb = 2
            db = letter(1, "Z")
            for name, base_c in (("C6", None), ("C11", (0, 0))):
                Y = W(nb) if base_c is None else Q(nb, base_c)
                X, e_c, _ = cone_lift(Y, db, {v: 1 for v in Y if B(v, db) == 0}, nb)
                S = [v for v in X if B(v, db) == 0]
                run_case(name, n, X, db, carrier_cone_swap(S, n, False), carrier_cone_swap(S, n, True),
                         ("cone with e = %s, d = %s; pair swap" % (word(e_c, n), word(db, n)), True),
                         [e_c, db, add(e_c, db)], out, vp)
            continue
        # --- C5: X = Q- with c = Y on qubit 0, q_c(d) = 0; graph on qubits 1 .. n-2
        c = letter(0, "Y")
        mg = n - 2
        ug, mvg = default_graph(mg)
        assert components_ok(mg, ug, 2, mvg)
        X = Q(n, c)
        S = [v for v in X if B(v, d) == 0]
        F = units(mg, ug, mvg, ("r", "X", "Y", "Z"))
        run_case("C5", n, X, d, carrier_C5(S, n, d, ug, 2, set()), carrier_C5(S, n, d, ug, 2, F),
                 ("X = Q- (c = %s, q0(c) = 1), q_c(d) = 0" % word(c, n), q0(c) == 1 and qc(c, d) == 0),
                 [d], out, vp)
        # --- C12 and C15: e = Z on qubit n-1, d = Y on qubit n-2; graph on the base qubits 0 .. n-3
        e = letter(n - 1, "Z")
        dd = letter(n - 2, "Y")
        mb = n - 2
        ub, mvb = default_graph(mb)
        assert components_ok(mb, ub, 2, mvb)
        F = units(mb, ub, mvb, ("r", "i"))
        for name, cc in (("C12", (0, 0)), ("C15", letter(0, "Y"))):
            X = perp(Q(n, cc), e)
            S = [v for v in X if B(v, dd) == 0]
            kind = "CP = Q+ cut by e-perp" if q0(cc) == 0 else "CM = Q- cut by e-perp"
            ok = qc(cc, e) == 0 and B(dd, e) == 0 and qc(cc, dd) == 1
            run_case(name, n, X, dd, carrier_C12_C15(S, n, e, ub, 2, set()), carrier_C12_C15(S, n, e, ub, 2, F),
                     ("%s, e = %s singular, d = %s in e-perp with q(d) = 1" % (kind, word(e, n), word(dd, n)), ok),
                     [e], out, vp)
        # --- C8: PAR = Q+ cut by e-perp with e = Y on qubit n-1 (nucleus, q(e) = 1); r = d = Z on qubit n-2.
        # Remark 2 of the note: PAR on n qubits is W(2n-3, 2) on qubits 0 .. n-2; the carriers are those of
        # C1 on n - 1 qubits, transported.
        e8 = letter(n - 1, "Y")
        r = letter(n - 2, "Z")
        X = perp(Q(n, (0, 0)), e8)
        S = [v for v in X if B(v, r) == 0]
        m1 = n - 2
        u1, mv1 = default_graph(m1)
        if components_ok(m1, u1, 2, mv1):
            S1 = [v for v in W(n - 1) if B(v, r) == 0]
            F1 = units(m1, u1, mv1, ("r", "i"))
            s1 = carrier_C1_C3(S1, n - 1, r, u1, 2, set())
            t1 = carrier_C1_C3(S1, n - 1, r, u1, 2, F1)
            low = (1 << (n - 1)) - 1
            run_case("C8", n, X, r, {v: s1[(v[0] & low, v[1] & low)] for v in S},
                     {v: t1[(v[0] & low, v[1] & low)] for v in S},
                     ("PAR, e = %s nonsingular (q(e) = 1), d = r = %s in e-perp" % (word(e8, n), word(r, n)),
                      qc((0, 0), e8) == 1 and B(r, e8) == 0 and qc((0, 0), r) == 0), [r], out, vp)
        # --- C6, C11, C14 by the pair swap: cones with vertex e = Z on qubit n-1, d = Z on qubit n-2
        nb = n - 1
        db = letter(nb - 1, "Z")
        for name, base_c in (("C6", None), ("C11", (0, 0)), ("C14", letter(0, "Y"))):
            Y = W(nb) if base_c is None else Q(nb, base_c)
            X, e_c, _ = cone_lift(Y, db, {v: 1 for v in Y if B(v, db) == 0}, nb)
            S = [v for v in X if B(v, db) == 0]
            ok = (base_c is None or (qc(base_c, e_c) == 0 and qc(base_c, db) == 0)) and B(db, e_c) == 0
            kind = "HW = W cut by e-perp" if base_c is None else ("CP" if q0(base_c) == 0 else "CM")
            run_case(name, n, X, db, carrier_cone_swap(S, n, False), carrier_cone_swap(S, n, True),
                     ("%s, e = %s, d = %s in e-perp, q(d) = 0; pair swap" % (kind, word(e_c, n), word(db, n)), ok),
                     [e_c, db, add(e_c, db)], out, vp)
        # --- the same cases again, as cone lifts of the pairs of C1, C3, C5 on n - 1 qubits (Lemma D (D2))
        for name, base_c, kind in (("C6 lift", None, "C1"), ("C11 lift", (0, 0), "C3"), ("C14 lift", letter(0, "Y"), "C5")):
            Y = W(nb) if base_c is None else Q(nb, base_c)
            Sb = [v for v in Y if B(v, db) == 0]
            if kind == "C5":
                mgb = nb - 2
                if mgb < 2:
                    continue
                ugb, mvgb = default_graph(mgb)
                Fb = units(mgb, ugb, mvgb, ("r", "X", "Y", "Z"))
                sb, tb = carrier_C5(Sb, nb, db, ugb, 2, set()), carrier_C5(Sb, nb, db, ugb, 2, Fb)
            else:
                mb2 = nb - 1
                ub2, mvb2 = default_graph(mb2)
                Fb = units(mb2, ub2, mvb2, ("r", "i") if kind == "C1" else ("r",))
                sb, tb = carrier_C1_C3(Sb, nb, db, ub2, 2, set()), carrier_C1_C3(Sb, nb, db, ub2, 2, Fb)
            X, e_c, sl = cone_lift(Y, db, sb, nb)
            _, _, tl = cone_lift(Y, db, tb, nb)
            ok = (base_c is None or qc(base_c, e_c) == 0) and B(db, e_c) == 0 and db != e_c and \
                (base_c is None or qc(base_c, db) == 0)
            run_case(name, n, X, db, sl, tl,
                     ("cone over the %s pair on %d qubits, e = %s, d = %s" % (kind, nb, word(e_c, n), word(db, n)), ok),
                     [e_c, db, add(e_c, db)], out, vp)
    npass = sum(1 for _, ok in CHECKS if ok)
    out["checks"] = {"passed": npass, "total": len(CHECKS)}
    with open(os.path.join(ROOT, "results", record), "w", encoding="utf-8", newline="\n") as fh:
        json.dump(out, fh, indent=1)
    print("\n%d of %d checks passed" % (npass, len(CHECKS)))
    sys.exit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
conjecture_e_lemmas.py - exact checks of Lemmas 20 and 21 of the combined paper (Section 8.7), which
make the proof of Theorem 19 (Conjecture E) independent of the general structure theorems of Jonah's
note [J3, Theorems A and B3].

For every vertex case and n = 3, 4, 5 (n = 3 only for C1, C3, C6, C11), with the carriers of
scripts/conjecture_e.py, the program checks in integer arithmetic:

  Lemma 20   (A P_p + P_p A) / 2 = sum_q Lambda_qp P_q for every outside point p and both carriers,
             where Lambda is filled from the outside lines and their signs; so Lambda is the matrix of
             Jordan multiplication by A on the real span of the outside Paulis.
  Lemma 21, its hypotheses in each case:
    C1       every outside Pauli is X (x) P' or Y (x) P' on the top qubit, and both occur for every
             Pauli P' of the block: |O| = 2 k^2, so the block matrices span all complex matrices;
    C3, C5   exactly one of X (x) P', Y (x) P' is outside, |O| = k^2, and every block matrix M is fixed
             by M -> J conj(M) J with J the block of P_c (a real form of the complex matrices);
    cones    every outside Pauli commutes with P_e and P_{e+y} = +-P_e P_y; the base configuration Y
             on n - 1 qubits satisfies the C1, C3 or C5 conditions above;
    C12, C15 every outside Pauli commutes with P_e and P_e P_p = +-P_(e+p) with e + p outside; the map
             Theta(T) = P_c conj(T) P_c fixes A and P_e and sends P_d to -P_d; with
             f_i = e_a (x) (|0> + i|1>) (x) e_w and g_i = theta f_i, theta(psi) = P_c conj(psi), every
             outside Pauli has a block matrix M (from the g to the f basis) with M^T = eta M,
             eta = theta^2 = P_c conj(P_c), and every such M is twice a unitary (so not zero); f lies in
             P_d = +1 and g in P_d = -1; |O| = 2 k_b (k_b + eta);
    C8       the completion matrix is the C1 completion matrix on n - 1 qubits under the bijection
             I (x) P' -> P', Y (x) P' -> P', and tr A^j = 2 tr A_C1^j for j = 1 .. 6.
  Lemma 21, its conclusion: tr Lambda^j, j = 1 .. 6, equals the power sum of the eigenvalues that
             Lemma 21 predicts from the blocks of A (each 1/2(gamma_i + delta_j) kappa times on a
             preserved pair; each 1/2(mu_i + mu_j), i <= j or i < j, twice on a swapped block),
             for both carriers.

  python scripts/conjecture_e_lemmas.py            (n = 3, 4 and 5; about ten seconds)
  python scripts/conjecture_e_lemmas.py 6          (n = 6; about eight minutes)
Writes results/conjecture_e_lemmas.json for the default sizes, results/conjecture_e_lemmas_n<sizes>.json
otherwise.
"""
import json, os, sys
from fractions import Fraction
from math import comb
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import conjecture_e as ce  # noqa: E402  (building blocks only: configurations, carriers, Pauli matrices)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHECKS = []
JMAX = 6


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print("%s  %s%s" % ("PASS" if ok else "FAIL", name, ("   [" + detail + "]") if detail else ""), flush=True)
    return ok


# ------------------------------------------------------------------ Gaussian-integer matrices
def gmul(a, b):
    return (a[0] @ b[0] - a[1] @ b[1], a[0] @ b[1] + a[1] @ b[0])


def gadd(a, b, s=1):
    return (a[0] + s * b[0], a[1] + s * b[1])


def geq(a, b):
    return np.array_equal(a[0], b[0]) and np.array_equal(a[1], b[1])


def gconj(a):
    return (a[0], -a[1])


def gobj(a):
    return (a[0].astype(object), a[1].astype(object))


def gtrace(a):
    return (sum(a[0][i, i] for i in range(a[0].shape[0])), sum(a[1][i, i] for i in range(a[1].shape[0])))


PAULI = {}


def P(v, n):
    key = (v, n)
    if key not in PAULI:
        PAULI[key] = ce.pauli(v, n)
    return PAULI[key]


def carrier(S, n, sig):
    D = 1 << n
    A = (np.zeros((D, D), dtype=np.int64), np.zeros((D, D), dtype=np.int64))
    for s in S:
        A = gadd(A, P(s, n), sig[s])
    return A


def completion_matrix(S, O, sig):
    pos = {p: i for i, p in enumerate(O)}
    Sset = set(S)
    L = np.zeros((len(O), len(O)), dtype=np.int64)
    for i, p in enumerate(O):
        for q in O[i + 1:]:
            if ce.B(p, q):
                continue
            s = ce.add(p, q)
            assert s in Sset
            sr, si = ce.tau(s, p)
            assert si == 0 and sr in (1, -1)
            L[pos[p], pos[q]] = L[pos[q], pos[p]] = sr * sig[s]
    return L


def lambda_traces(L):
    """tr L^j for j = 1 .. 6, exactly (L2, L3 fit in int64 for these sizes; the last sums in Python)."""
    L2 = L @ L
    L3 = L2 @ L
    assert np.abs(L3).max() < 2 ** 62
    o2, o3 = L2.astype(object), L3.astype(object)
    return [int(np.trace(L)), int(np.trace(L2)), int(np.trace(L3)),
            int((o2 * o2.T).sum()), int((o3 * o2.T).sum()), int((o3 * o3.T).sum())]


def block_power_sums(A, rows):
    """p_m of the principal block of A on the given computational-basis indices, m = 0 .. JMAX."""
    idx = np.array(rows)
    B = (A[0][np.ix_(idx, idx)].astype(object), A[1][np.ix_(idx, idx)].astype(object))
    out, Bk = [len(rows)], B
    for m in range(1, JMAX + 1):
        if m > 1:
            Bk = gmul(Bk, B)
        tr = gtrace(Bk)
        assert tr[1] == 0
        out.append(int(tr[0]))
    return out


def preserved_prediction(pairs, kappa):
    """sum over coupled pairs of kappa * sum_{i,j} (1/2 (gamma_i + delta_j))^j."""
    res = []
    for j in range(1, JMAX + 1):
        tot = Fraction(0)
        for pa, pb in pairs:
            tot += kappa * Fraction(sum(comb(j, m) * pa[m] * pb[j - m] for m in range(j + 1)), 2 ** j)
        res.append(tot)
    return res


def projected_power_sums(A, proj4):
    """p_m(A restricted to the range of the projector proj4 / 4), m = 0 .. JMAX, for A commuting with it."""
    out = []
    Ak = None
    A_o, Pr = gobj(A), gobj(proj4)
    for m in range(0, JMAX + 1):
        if m == 1:
            Ak = A_o
        elif m > 1:
            Ak = gmul(Ak, A_o)
        M = Pr if m == 0 else gmul(Ak, Pr)
        tr = gtrace(M)
        assert tr[1] == 0 and tr[0] % 4 == 0
        out.append(int(tr[0]) // 4)
    return out


def swapped_prediction(blocks, eta):
    """sum over the two P_e-blocks of 2^-j [ sum_m C(j,m) p_m p_{j-m} + eta 2^j p_j ]."""
    res = []
    for j in range(1, JMAX + 1):
        tot = Fraction(0)
        for p in blocks:
            tot += Fraction(sum(comb(j, m) * p[m] * p[j - m] for m in range(j + 1)) + eta * 2 ** j * p[j], 2 ** j)
        res.append(tot)
    return res


# ------------------------------------------------------------------ Lemma 20
def lemma20(name, n, S, O, sig, label):
    A = carrier(S, n, sig)
    L = completion_matrix(S, O, sig)
    ok = True
    for i, p in enumerate(O):
        Pp = P(p, n)
        J2 = gadd(gmul(A, Pp), gmul(Pp, A))
        acc = (np.zeros_like(J2[0]), np.zeros_like(J2[1]))
        for k in np.nonzero(L[:, i])[0]:
            acc = gadd(acc, P(O[k], n), 2 * int(L[k, i]))
        if not geq(J2, acc):
            ok = False
            break
    check("%s, n = %d, carrier %s: Lemma 20, (A P_p + P_p A)/2 = sum_q Lambda_qp P_q for all %d outside points"
          % (name, n, label, len(O)), ok)
    return A, L


# ------------------------------------------------------------------ hypotheses of Lemma 21
def base_hypotheses(name, n, X, d, c):
    """X on n qubits, d = Z on the top qubit n - 1; c = None for W, else X = Q_c with c on qubit 0."""
    k = 1 << (n - 1)
    D = 1 << n
    Xs = set(X)
    O = [v for v in X if ce.B(v, d) == 1]
    top = 1 << (n - 1)
    forms_ok = all((v[0] & top) for v in O)        # factor X or Y on the top qubit
    off_ok = True
    for v in O:
        Pv = P(v, n)
        if Pv[0][:k, :k].any() or Pv[1][:k, :k].any() or Pv[0][k:, k:].any() or Pv[1][k:, k:].any():
            off_ok = False
            break
    if c is None:
        both = all(((top | x, z) in Xs) and ((top | x, top | z) in Xs) for x in range(k) for z in range(k))
        return check("%s, n = %d: every outside Pauli is X or Y on the top qubit times a block Pauli, both occur "
                     "for every block Pauli, |O| = 2k^2 = %d (the block matrices span all complex matrices)"
                     % (name, n, 2 * k * k), forms_ok and off_ok and both and len(O) == 2 * k * k)
    one = all((((top | x, z) in Xs) + ((top | x, top | z) in Xs)) == 1 for x in range(k) for z in range(k))
    Pc = P(c, n)
    J = (Pc[0][:k, :k], Pc[1][:k, :k])
    fixed = True
    for v in O:
        Pv = P(v, n)
        M = (Pv[0][:k, k:], Pv[1][:k, k:])
        if not geq(gmul(gmul(J, gconj(M)), J), M):
            fixed = False
            break
    JJ = gmul(J, gconj(J))
    inv = geq(JJ, (np.eye(k, dtype=np.int64), np.zeros((k, k), dtype=np.int64))) or \
        geq(JJ, (-np.eye(k, dtype=np.int64), np.zeros((k, k), dtype=np.int64)))
    return check("%s, n = %d: exactly one of X (x) P', Y (x) P' is outside, |O| = k^2 = %d, and every block matrix "
                 "is fixed by M -> J conj(M) J (J conj(J) = +-I: a real form)" % (name, n, k * k),
                 forms_ok and off_ok and one and len(O) == k * k and fixed and inv)


def cone_hypotheses(name, n, X, e, d, base_c, Y):
    O = [v for v in X if ce.B(v, d) == 1]
    comm = all(ce.B(v, e) == 0 for v in O)
    pair = True
    Pe = P(e, n)
    Oset = set(O)
    for v in O:
        if v == e:
            continue
        w = ce.add(e, v)
        sr, si = ce.tau(e, v)
        if si != 0 or not geq(gmul(Pe, P(v, n)), (sr * P(w, n)[0], sr * P(w, n)[1])) or w not in Oset:
            pair = False
            break
    check("%s, n = %d: every outside Pauli commutes with P_e, and P_e P_y = +-P_(e+y) with e + y outside"
          % (name, n), comm and pair)
    return base_hypotheses("%s base" % name, n - 1, Y, d, base_c)


def f_basis(n, a):
    """f_w = |a> on qubit n-1 (Z_e = +1 for a = 0) (x) (|0> + i|1>) on qubit n-2 (Y_d = +1) (x) |w>, unnormalized."""
    D = 1 << n
    F = []
    for w in range(1 << (n - 2)):
        vr = np.zeros(D, dtype=np.int64)
        vi = np.zeros(D, dtype=np.int64)
        base = (a << (n - 1)) | w
        vr[base] = 1
        vi[base | (1 << (n - 2))] = 1
        F.append((vr, vi))
    return F


def theta_vec(Pc, f):
    """theta_c f = P_c conj(f)."""
    return (Pc[0] @ f[0] + Pc[1] @ f[1], Pc[1] @ f[0] - Pc[0] @ f[1])


def apply(Mat, x):
    return (Mat[0] @ x[0] - Mat[1] @ x[1], Mat[0] @ x[1] + Mat[1] @ x[0])


def outside_blocks(O, n, F, G, eta):
    """(every block M, 2 M_ji = <f_j, P_v g_i>, has M^T = eta M; every block is twice a unitary, so none is zero)."""
    kb = len(F)
    four = 4 * np.eye(kb, dtype=np.complex128)
    for v in O:
        Pv = P(v, n)
        M2 = np.zeros((kb, kb), dtype=np.complex128)
        for i, g in enumerate(G):
            y = apply(Pv, g)
            for jx, f in enumerate(F):
                M2[jx, i] = complex(int(f[0] @ y[0] + f[1] @ y[1]), int(f[0] @ y[1] - f[1] @ y[0]))
        if not np.array_equal(M2.T, eta * M2):
            return False, True
        if not np.array_equal(M2 @ M2.conj().T, four):
            return True, False
    return True, True


def swap_hypotheses(name, n, X, e, d, c, eta, A_list):
    D = 1 << n
    kb = 1 << (n - 2)
    O = [v for v in X if ce.B(v, d) == 1]
    Pc = P(c, n) if c is not None else (np.eye(D, dtype=np.int64), np.zeros((D, D), dtype=np.int64))

    def theta(T):
        return gmul(gmul(Pc, gconj(T)), Pc)

    Pe, Pd = P(e, n), P(d, n)
    # every outside Pauli commutes with P_e, and P_e P_p = +-P_(e+p) with e + p outside (the P_e splitting)
    Oset = set(O)
    ok_split = all(ce.B(v, e) == 0 for v in O)
    for v in O:
        w = ce.add(e, v)
        sr, si = ce.tau(e, v)
        if si != 0 or w not in Oset or not geq(gmul(Pe, P(v, n)), (sr * P(w, n)[0], sr * P(w, n)[1])):
            ok_split = False
            break
    ok_theta = all(geq(theta(A), A) for A in A_list) and geq(theta(Pe), Pe) and geq(theta(Pd), (-Pd[0], -Pd[1]))
    # theta_c^2 = P_c conj(P_c) on vectors
    T2 = gmul(Pc, gconj(Pc))
    ok_eta = geq(T2, (eta * np.eye(D, dtype=np.int64), np.zeros((D, D), dtype=np.int64)))
    ok_basis = ok_sym = ok_unit = True
    for a in (0, 1):                                     # bit of qubit n-1: Z_e = +1 for a = 0
        F = f_basis(n, a)
        G = [theta_vec(Pc, f) for f in F]
        # f in the eigenspace P_d = +1 and g in P_d = -1, both in P_e = (-1)^a
        sgn = 1 - 2 * a
        for f, g in zip(F, G):
            pf, pg, ef, eg = apply(Pd, f), apply(Pd, g), apply(Pe, f), apply(Pe, g)
            if not (np.array_equal(pf[0], f[0]) and np.array_equal(pf[1], f[1]) and
                    np.array_equal(pg[0], -g[0]) and np.array_equal(pg[1], -g[1]) and
                    np.array_equal(ef[0], sgn * f[0]) and np.array_equal(ef[1], sgn * f[1]) and
                    np.array_equal(eg[0], sgn * g[0]) and np.array_equal(eg[1], sgn * g[1])):
                ok_basis = False
        sym, unit = outside_blocks(O, n, F, G, eta)
        ok_sym, ok_unit = ok_sym and sym, ok_unit and unit
    count_ok = len(O) == 2 * kb * (kb + eta)
    return check("%s, n = %d: every outside Pauli commutes with P_e and P_e P_p = +-P_(e+p) with e + p outside; "
                 "Theta fixes A and P_e and sends P_d to -P_d, theta^2 = %+d; f in P_d = +1 and g = theta f in "
                 "P_d = -1; every block matrix has M^T = %+d M and is twice a unitary; |O| = 2 k_b (k_b %s 1) = %d"
                 % (name, n, eta, eta, "+" if eta > 0 else "-", 2 * kb * (kb + eta)),
                 ok_split and ok_theta and ok_eta and ok_basis and ok_sym and ok_unit and count_ok)


# ------------------------------------------------------------------ conclusion of Lemma 21
def preserved_conclusion(name, n, A, L, blocks_of_pairs, kappa, label):
    t = lambda_traces(L)
    pairs = [(block_power_sums(A, r1), block_power_sums(A, r2)) for r1, r2 in blocks_of_pairs]
    pred = preserved_prediction(pairs, kappa)
    return check("%s, n = %d, carrier %s: tr Lambda^j = sum over coupled pairs of kappa * sum (gamma_i + delta_j)^j / 2^j, "
                 "j = 1 .. %d (kappa = %d)" % (name, n, label, JMAX, kappa),
                 [Fraction(x) for x in t] == pred, "tr Lambda^3 = %d" % t[2]), t


def indices(n, fixed):
    """Computational-basis indices with the given bits fixed: fixed = {qubit: bit}."""
    return [b for b in range(1 << n) if all(((b >> q) & 1) == bit for q, bit in fixed.items())]


# ------------------------------------------------------------------ the cases
def run(n, out):
    rec = out.setdefault(str(n), {})
    m = n - 1
    d = ce.letter(n - 1, "Z")
    u, mv = ce.default_graph(m)
    base_pairs = [(indices(n, {n - 1: 0}), indices(n, {n - 1: 1}))]

    def base_case(name, X, c, kappa, sig, tau_):
        S = [v for v in X if ce.B(v, d) == 0]
        O = [v for v in X if ce.B(v, d) == 1]
        base_hypotheses(name, n, X, d, c)
        res = {}
        for label, s in (("sigma", sig), ("tau", tau_)):
            A, L = lemma20(name, n, S, O, s, label)
            _, t = preserved_conclusion(name, n, A, L, base_pairs, kappa, label)
            res[label] = t
        rec[name] = {"outside": len(O), "trace_powers_1_to_6": res}

    X = ce.W(n)
    S = [v for v in X if ce.B(v, d) == 0]
    F = ce.units(m, u, mv, ("r", "i"))
    base_case("C1", X, None, 2, ce.carrier_C1_C3(S, n, d, u, 2, set()), ce.carrier_C1_C3(S, n, d, u, 2, F))
    X = ce.Q(n, (0, 0))
    S = [v for v in X if ce.B(v, d) == 0]
    F = ce.units(m, u, mv, ("r",))
    base_case("C3", X, (0, 0), 1, ce.carrier_C1_C3(S, n, d, u, 2, set()), ce.carrier_C1_C3(S, n, d, u, 2, F))

    def cone_case(name, nb, base_c, kappa):
        db = ce.letter(nb - 1, "Z")
        Y = ce.W(nb) if base_c is None else ce.Q(nb, base_c)
        X, e_c, _ = ce.cone_lift(Y, db, {v: 1 for v in Y if ce.B(v, db) == 0}, nb)
        S = [v for v in X if ce.B(v, db) == 0]
        O = [v for v in X if ce.B(v, db) == 1]
        cone_hypotheses(name, n, X, e_c, db, base_c, Y)
        # the base hypotheses for C14 use c = Y on qubit 0 of the base; for C11 c = 0
        pairs = [(indices(n, {n - 1: 0, n - 2: 0}), indices(n, {n - 1: 0, n - 2: 1})),
                 (indices(n, {n - 1: 1, n - 2: 0}), indices(n, {n - 1: 1, n - 2: 1}))]
        res = {}
        for label, moved in (("sigma", False), ("tau", True)):
            s = ce.carrier_cone_swap(S, n, moved)
            A, L = lemma20(name, n, S, O, s, label)
            _, t = preserved_conclusion(name, n, A, L, pairs, kappa, label)
            res[label] = t
        rec[name] = {"outside": len(O), "trace_powers_1_to_6": res}

    if n == 3:
        cone_case("C6", 2, None, 2)
        cone_case("C11", 2, (0, 0), 1)
        return
    # C5
    c5 = ce.letter(0, "Y")
    mg = n - 2
    ug, mvg = ce.default_graph(mg)
    X = ce.Q(n, c5)
    S = [v for v in X if ce.B(v, d) == 0]
    F = ce.units(mg, ug, mvg, ("r", "X", "Y", "Z"))
    base_case("C5", X, c5, 1, ce.carrier_C5(S, n, d, ug, 2, set()), ce.carrier_C5(S, n, d, ug, 2, F))
    # C12, C15
    e = ce.letter(n - 1, "Z")
    dd = ce.letter(n - 2, "Y")
    ub, mvb = ce.default_graph(n - 2)
    F = ce.units(n - 2, ub, mvb, ("r", "i"))
    for name, cc, eta in (("C12", (0, 0), 1), ("C15", ce.letter(0, "Y"), -1)):
        X = ce.perp(ce.Q(n, cc), e)
        S = [v for v in X if ce.B(v, dd) == 0]
        O = [v for v in X if ce.B(v, dd) == 1]
        sig, tau_ = ce.carrier_C12_C15(S, n, e, ub, 2, set()), ce.carrier_C12_C15(S, n, e, ub, 2, F)
        As = [carrier(S, n, sig), carrier(S, n, tau_)]
        swap_hypotheses(name, n, X, e, dd, None if cc == (0, 0) else cc, eta, As)
        D = 1 << n
        Pe, Pd = P(e, n), P(dd, n)
        I = (np.eye(D, dtype=np.int64), np.zeros((D, D), dtype=np.int64))
        res = {}
        for label, s in (("sigma", sig), ("tau", tau_)):
            A, L = lemma20(name, n, S, O, s, label)
            blocks = []
            for a in (1, -1):
                proj4 = gmul(gadd(I, Pe, a), gadd(I, Pd, 1))
                blocks.append(projected_power_sums(A, proj4))
            t = lambda_traces(L)
            pred = swapped_prediction(blocks, eta)
            check("%s, n = %d, carrier %s: tr Lambda^j = sum over the P_e-blocks of 2 * sum_{i %s j} (mu_i + mu_j)^j / 2^j, "
                  "j = 1 .. %d" % (name, n, label, "<=" if eta > 0 else "<", JMAX),
                  [Fraction(x) for x in t] == pred, "tr Lambda^3 = %d" % t[2])
            res[label] = t
        rec[name] = {"outside": len(O), "trace_powers_1_to_6": res}
    # C8: through C1 on n - 1 qubits
    e8 = ce.letter(n - 1, "Y")
    r = ce.letter(n - 2, "Z")
    X = ce.perp(ce.Q(n, (0, 0)), e8)
    S = [v for v in X if ce.B(v, r) == 0]
    O = [v for v in X if ce.B(v, r) == 1]
    m1 = n - 2
    u1, mv1 = ce.default_graph(m1)
    if ce.components_ok(m1, u1, 2, mv1):
        low = (1 << (n - 1)) - 1
        X1 = ce.W(n - 1)
        S1 = [v for v in X1 if ce.B(v, r) == 0]
        O1 = [v for v in X1 if ce.B(v, r) == 1]
        F1 = ce.units(m1, u1, mv1, ("r", "i"))
        phi = {v: (v[0] & low, v[1] & low) for v in X}
        bij = len(set(phi.values())) == len(X) == len(X1) and set(phi.values()) == set(X1)
        res = {}
        ok_all = bij
        for label, moved in (("sigma", set()), ("tau", F1)):
            s1 = ce.carrier_C1_C3(S1, n - 1, r, u1, 2, moved)
            s = {v: s1[phi[v]] for v in S}
            A, L = lemma20("C8", n, S, O, s, label)
            L1 = completion_matrix(S1, [phi[v] for v in O], s1)
            same = np.array_equal(L, L1)
            A1 = carrier(S1, n - 1, s1)
            pa = block_power_sums(A, list(range(1 << n)))
            p1 = block_power_sums(A1, list(range(1 << (n - 1))))
            ok_all = ok_all and same and all(pa[j] == 2 * p1[j] for j in range(1, JMAX + 1))
            res[label] = lambda_traces(L)
        check("C8, n = %d: the map I (x) P' -> P', Y (x) P' -> P' is a bijection onto W(%d, 2), the completion matrix "
              "is the C1 completion matrix on %d qubits, and tr A^j = 2 tr A_C1^j, j = 1 .. %d"
              % (n, 2 * n - 3, n - 1, JMAX), ok_all)
        rec["C8"] = {"outside": len(O), "trace_powers_1_to_6": res}
    # cones
    nb = n - 1
    for name, base_c, kappa in (("C6", None, 2), ("C11", (0, 0), 1), ("C14", ce.letter(0, "Y"), 1)):
        cone_case(name, nb, base_c, kappa)


def negative_controls(out):
    """Four changes that must make a check fail, at four qubits."""
    n = 4
    d = ce.letter(n - 1, "Z")
    u, mv = ce.default_graph(n - 1)
    X = ce.W(n)
    S = [v for v in X if ce.B(v, d) == 0]
    O = [v for v in X if ce.B(v, d) == 1]
    sig = ce.carrier_C1_C3(S, n, d, u, 2, set())
    A = carrier(S, n, sig)
    L = completion_matrix(S, O, sig)
    pairs = [(block_power_sums(A, indices(n, {n - 1: 0})), block_power_sums(A, indices(n, {n - 1: 1})))]
    wrong_kappa = [Fraction(x) for x in lambda_traces(L)] != preserved_prediction(pairs, 1)
    # one flipped sign in Lambda (and its mirror entry) breaks Lemma 20 at that column
    Lb = L.copy()
    i, k = next((i, k) for i in range(len(O)) for k in range(len(O)) if L[k, i] != 0)
    Lb[k, i] *= -1
    Lb[i, k] *= -1
    Pp = P(O[i], n)
    J2 = gadd(gmul(A, Pp), gmul(Pp, A))
    acc = (np.zeros_like(J2[0]), np.zeros_like(J2[1]))
    for kk in np.nonzero(Lb[:, i])[0]:
        acc = gadd(acc, P(O[kk], n), 2 * int(Lb[kk, i]))
    flipped = not geq(J2, acc)
    # C12 with the wrong symmetry type
    e = ce.letter(n - 1, "Z")
    dd = ce.letter(n - 2, "Y")
    ub, mvb = ce.default_graph(n - 2)
    X = ce.perp(ce.Q(n, (0, 0)), e)
    S = [v for v in X if ce.B(v, dd) == 0]
    O = [v for v in X if ce.B(v, dd) == 1]
    sig = ce.carrier_C12_C15(S, n, e, ub, 2, set())
    A = carrier(S, n, sig)
    L = completion_matrix(S, O, sig)
    D = 1 << n
    I = (np.eye(D, dtype=np.int64), np.zeros((D, D), dtype=np.int64))
    blocks = [projected_power_sums(A, gmul(gadd(I, P(e, n), a), gadd(I, P(dd, n), 1))) for a in (1, -1)]
    wrong_eta = [Fraction(x) for x in lambda_traces(L)] != swapped_prediction(blocks, -1)
    # C12 with the second basis equal to the first: every block vanishes, so the block test must fail
    F = f_basis(n, 0)
    same_basis = outside_blocks(O, n, F, F, 1) != (True, True)
    check("negative controls, n = 4: kappa = 1 for C1, one flipped sign in Lambda, eta = -1 for C12, and g = f "
          "for C12 each make the corresponding check fail", wrong_kappa and flipped and wrong_eta and same_basis)
    out["negative_controls"] = {"C1_kappa_1_fails": wrong_kappa, "flipped_sign_fails_lemma_20": flipped,
                                "C12_eta_minus_1_fails": wrong_eta, "C12_g_equal_f_fails": same_basis}


def main():
    out = {}
    sizes = [int(a) for a in sys.argv[1:]] or [3, 4, 5]
    record = "conjecture_e_lemmas.json" if sizes == [3, 4, 5] else "conjecture_e_lemmas_n%s.json" % "-".join(map(str, sizes))
    for n in sizes:
        run(n, out)
    if 4 in sizes:
        negative_controls(out)
    npass = sum(1 for _, ok in CHECKS if ok)
    out["checks"] = {"passed": npass, "total": len(CHECKS)}
    with open(os.path.join(ROOT, "results", record), "w", encoding="utf-8", newline="\n") as fh:
        json.dump(out, fh, indent=1)
    print("\n%d of %d checks passed" % (npass, len(CHECKS)))
    sys.exit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
conjecture_e_trace_formula.py - exact checks of the cubic trace formula of the combined paper
(Section 8.7, Theorem 22) in every vertex case.

For a configuration X that contains u + v whenever it contains two distinct commuting points u, v, a
point d, the section H = X cap d-perp, the outside points O = X minus H, and any real carrier sigma,

    4 D tr Lambda^3 = |O| tr A^3 + 3 sum_{u in H} S_O(u) sigma(u) tr(A^2 P_u),
    S_O(u) = sum_{p in O} (-1)^<p, u>,

with D = 2^n, A the carrier operator and Lambda the completion matrix.  The program checks, in integer
arithmetic on the complete configurations:

  T    the formula, for both carriers of every pair of Table 6 and for random sign carriers;
  S    the values of S_O on the section given by the paper for each case (Table 8);
  M    for the pair swap (C6, C11, C14): the six moments tr(A^2 P_v), v in {e, d, e + d}, of both
       carriers, and the difference of cubic traces -3 K (|H| - 3), K = D^2/4 (C6) or D^2/8;
  and three negative controls (a wrong coefficient, a wrong value of S_O, a missing point of O).

  python scripts/conjecture_e_trace_formula.py        (n = 3, 4 and 5)
Writes results/conjecture_e_trace_formula.json for the default sizes, otherwise
results/conjecture_e_trace_formula_n<sizes>.json.
"""
import json, os, random, sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import conjecture_e as ce            # noqa: E402  configurations, carriers, Pauli matrices
import conjecture_e_lemmas as cl     # noqa: E402  carrier operator, completion matrix, traces

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print("%s  %s%s" % ("PASS" if ok else "FAIL", name, ("   [" + detail + "]") if detail else ""), flush=True)
    return ok


def tr_prod_real(Ar, Ai, Pr, Pi):
    """Real part of tr(A P) for A = Ar + i Ai, P = Pr + i Pi (exact integer arithmetic)."""
    # For n <= 6, |Ar|, |Ai| <= 4096^2 and |Pr|, |Pi| <= 1, so elementwise products and sums
    # fit safely inside signed 64-bit integers; guard explicitly and fall back to Python ints otherwise.
    bound = int(max(int(np.abs(Ar).max()), int(np.abs(Ai).max()))) * int(Ar.size)
    if bound < (1 << 61):
        return int((Ar * Pr.T).sum(dtype=np.int64) - (Ai * Pi.T).sum(dtype=np.int64))
    return int((Ar.astype(object) * Pr.T.astype(object)).sum() - (Ai.astype(object) * Pi.T.astype(object)).sum())


def tr_lambda_cube(L):
    """Exact tr(Lambda^3) for symmetric integer matrix Lambda with entries in {-1, 0, 1}."""
    L2 = L @ L
    # Since L is symmetric, tr(L^3) = sum_{i,j} (L^2)_{ij} L_{ij}.
    max_abs = int(np.abs(L2).max()) if L2.size else 0
    if max_abs * int(L2.size) < (1 << 61):
        return int((L2 * L).sum(dtype=np.int64))
    return int((L2.astype(object) * L.astype(object)).sum())


def moments(A, H, n):
    """tr(A^2 P_u) for every u in H, and tr A^3 (all real, exact)."""
    A2 = cl.gmul(A, A)
    A3 = cl.gmul(A2, A)
    m = {u: tr_prod_real(A2[0], A2[1], *cl.P(u, n)) for u in H}
    t3 = int(sum(A3[0][i, i] for i in range(A3[0].shape[0])))
    return m, t3


def S_O(O, H):
    return {u: sum(1 - 2 * ce.B(p, u) for p in O) for u in H}


def formula_holds(n, H, O, sig, S, coef=3):
    D = 1 << n
    A = cl.carrier(H, n, sig)
    L = cl.completion_matrix(H, O, sig)
    t3L = tr_lambda_cube(L)
    m, t3 = moments(A, H, n)
    rhs = len(O) * t3 + coef * sum(S[u] * sig[u] * m[u] for u in H)
    return 4 * D * t3L == rhs, t3L, m, t3


def closed_form(case, n, u, e, d, c0):
    """S_O(u) on the section, as stated in the paper."""
    D = 1 << n
    de, dd = int(u == e) if e else 0, int(u == d)
    ded = int(e is not None and u == ce.add(e, d))
    if case == "C1":
        return -(D * D // 2) * dd
    if case in ("C3", "C5"):
        return -(D * D // 4) * dd
    if case == "C6":
        return (D * D // 4) * (de - dd - ded)
    if case in ("C11", "C14"):
        return (D * D // 8) * (de - dd - ded)
    if case in ("C12", "C15"):
        return (D * D // 8) * de + (D // 2) * (1 - 2 * c0)
    if case == "C8":
        return -(D * D // 8) * dd
    raise ValueError(case)


def run_case(case, n, X, d, e, c0, pairs, rng, out):
    H = [v for v in X if ce.B(v, d) == 0]
    O = [v for v in X if ce.B(v, d) == 1]
    S = S_O(O, H)
    ok_S = all(S[u] == closed_form(case, n, u, e, d, c0) for u in H)
    check("%s, n = %d: S_O on the section (%d points) has the closed form of the paper" % (case, n, len(H)), ok_S)
    rec = {"section": len(H), "outside": len(O)}
    for label, sig in pairs:
        ok, t3L, m, t3 = formula_holds(n, H, O, sig, S)
        check("%s, n = %d, carrier %s: 4 D tr Lambda^3 = |O| tr A^3 + 3 sum S_O(u) sigma(u) tr(A^2 P_u)" % (case, n, label),
              ok, "tr Lambda^3 = %d" % t3L)
        rec[label] = {"tr_Lambda3": t3L, "tr_A3": t3}
    oks = []
    for k in range(3):
        sig = {u: rng.choice((1, -1)) for u in H}
        oks.append(formula_holds(n, H, O, sig, S)[0])
    check("%s, n = %d: the formula for three random sign carriers" % (case, n), all(oks))
    out.setdefault(str(n), {})[case] = rec
    return H, O, S


def pair_swap_moments(case, n, H, O, sig, tau_, e, d, kappa_W):
    D = 1 << n
    ed = ce.add(e, d)
    ms, _ = moments(cl.carrier(H, n, sig), H, n)
    mt, _ = moments(cl.carrier(H, n, tau_), H, n)
    h = len(H)
    want_s = {e: D * (5 - h), d: D * (5 - h), ed: D * (h - 1)}
    want_t = {e: D * (h - 1), d: D * (5 - h), ed: D * (5 - h)}
    ok_m = all(ms[v] == want_s[v] and mt[v] == want_t[v] for v in (e, d, ed))
    K = D * D // 4 if kappa_W else D * D // 8
    gap = tr_lambda_cube(cl.completion_matrix(H, O, sig)) - tr_lambda_cube(cl.completion_matrix(H, O, tau_))
    return check("%s, n = %d: tr(A^2 P_v) = D(5 - |H|), D(5 - |H|), D(|H| - 1) for sigma and D(|H| - 1), D(5 - |H|), "
                 "D(5 - |H|) for tau at v = e, d, e + d; difference -3K(|H| - 3) = %d" % (case, n, -3 * K * (h - 3)),
                 ok_m and gap == -3 * K * (h - 3), "difference %d" % gap)


def run(n, out, rng):
    m = n - 1
    d = ce.letter(n - 1, "Z")
    u, mv = ce.default_graph(m)
    X = ce.W(n)
    S = [v for v in X if ce.B(v, d) == 0]
    F = ce.units(m, u, mv, ("r", "i"))
    run_case("C1", n, X, d, None, 0, [("sigma", ce.carrier_C1_C3(S, n, d, u, 2, set())),
                                       ("tau", ce.carrier_C1_C3(S, n, d, u, 2, F))], rng, out)
    X = ce.Q(n, (0, 0))
    S = [v for v in X if ce.B(v, d) == 0]
    F = ce.units(m, u, mv, ("r",))
    run_case("C3", n, X, d, None, 0, [("sigma", ce.carrier_C1_C3(S, n, d, u, 2, set())),
                                       ("tau", ce.carrier_C1_C3(S, n, d, u, 2, F))], rng, out)

    def cone(name, nb, base_c, kappa_W):
        db = ce.letter(nb - 1, "Z")
        Y = ce.W(nb) if base_c is None else ce.Q(nb, base_c)
        Xc, e_c, _ = ce.cone_lift(Y, db, {v: 1 for v in Y if ce.B(v, db) == 0}, nb)
        Sc = [v for v in Xc if ce.B(v, db) == 0]
        sig, tau_ = ce.carrier_cone_swap(Sc, n, False), ce.carrier_cone_swap(Sc, n, True)
        H, O, _ = run_case(name, n, Xc, db, e_c, 0, [("sigma", sig), ("tau", tau_)], rng, out)
        pair_swap_moments(name, n, H, O, sig, tau_, e_c, db, kappa_W)

    if n == 3:
        cone("C6", 2, None, True)
        cone("C11", 2, (0, 0), False)
        return
    c5 = ce.letter(0, "Y")
    ug, mvg = ce.default_graph(n - 2)
    X = ce.Q(n, c5)
    S = [v for v in X if ce.B(v, d) == 0]
    F = ce.units(n - 2, ug, mvg, ("r", "X", "Y", "Z"))
    run_case("C5", n, X, d, None, 0, [("sigma", ce.carrier_C5(S, n, d, ug, 2, set())),
                                       ("tau", ce.carrier_C5(S, n, d, ug, 2, F))], rng, out)
    e = ce.letter(n - 1, "Z")
    dd = ce.letter(n - 2, "Y")
    ub, mvb = ce.default_graph(n - 2)
    F = ce.units(n - 2, ub, mvb, ("r", "i"))
    for name, cc, c0 in (("C12", (0, 0), 0), ("C15", ce.letter(0, "Y"), 1)):
        X = ce.perp(ce.Q(n, cc), e)
        S = [v for v in X if ce.B(v, dd) == 0]
        run_case(name, n, X, dd, e, c0, [("sigma", ce.carrier_C12_C15(S, n, e, ub, 2, set())),
                                          ("tau", ce.carrier_C12_C15(S, n, e, ub, 2, F))], rng, out)
    # C8: the transported C1 carriers, as in scripts/conjecture_e.py
    e8 = ce.letter(n - 1, "Y")
    r = ce.letter(n - 2, "Z")
    X = ce.perp(ce.Q(n, (0, 0)), e8)
    S = [v for v in X if ce.B(v, r) == 0]
    m1 = n - 2
    u1, mv1 = ce.default_graph(m1)
    if ce.components_ok(m1, u1, 2, mv1):
        low = (1 << (n - 1)) - 1
        X1 = ce.W(n - 1)
        S1 = [v for v in X1 if ce.B(v, r) == 0]
        F1 = ce.units(m1, u1, mv1, ("r", "i"))
        pairs = []
        for label, moved in (("sigma", set()), ("tau", F1)):
            s1 = ce.carrier_C1_C3(S1, n - 1, r, u1, 2, moved)
            pairs.append((label, {v: s1[(v[0] & low, v[1] & low)] for v in S}))
        run_case("C8", n, X, r, e8, 0, pairs, rng, out)
    cone("C6", n - 1, None, True)
    cone("C11", n - 1, (0, 0), False)
    cone("C14", n - 1, ce.letter(0, "Y"), False)


def negative_controls(out, rng):
    """At four qubits, case C11: a wrong coefficient, a wrong value of S_O at e, a point dropped from O."""
    n = 4
    db = ce.letter(n - 2, "Z")
    Y = ce.Q(n - 1, (0, 0))
    Xc, e_c, _ = ce.cone_lift(Y, db, {v: 1 for v in Y if ce.B(v, db) == 0}, n - 1)
    H = [v for v in Xc if ce.B(v, db) == 0]
    O = [v for v in Xc if ce.B(v, db) == 1]
    S = S_O(O, H)
    sig = ce.carrier_cone_swap(H, n, False)
    wrong_coef = not formula_holds(n, H, O, sig, S, coef=1)[0]
    S2 = dict(S)
    S2[e_c] += 1
    wrong_S = not formula_holds(n, H, O, sig, S2)[0]
    dropped = not formula_holds(n, H, O[1:], sig, S_O(O[1:], H))[0]
    check("negative controls, n = 4, C11: coefficient 1 instead of 3, S_O(e) off by one, and one outside point "
          "dropped each break the formula", wrong_coef and wrong_S and dropped)
    out["negative_controls"] = {"coefficient_1_fails": wrong_coef, "wrong_S_O_fails": wrong_S,
                                "dropped_outside_point_fails": dropped}


def main():
    out = {}
    rng = random.Random(20261110)
    sizes = [int(a) for a in sys.argv[1:]] or [3, 4, 5]
    record = ("conjecture_e_trace_formula.json" if sizes == [3, 4, 5]
              else "conjecture_e_trace_formula_n%s.json" % "-".join(map(str, sizes)))
    for n in sizes:
        run(n, out, rng)
    if 4 in sizes:
        negative_controls(out, rng)
    npass = sum(1 for _, ok in CHECKS if ok)
    out["checks"] = {"passed": npass, "total": len(CHECKS)}
    with open(os.path.join(ROOT, "results", record), "w", encoding="utf-8", newline="\n") as fh:
        json.dump(out, fh, indent=1)
    print("\n%d of %d checks passed" % (npass, len(CHECKS)))
    sys.exit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

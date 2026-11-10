#!/usr/bin/env python3
"""
flat_states.py - configurations on which the spectral floor is attained, in exact integer arithmetic.

A pure N-qubit state is *flat on S* if <P_v> = +-mu for the points v of a set S of Pauli observables and
<P_v> = 0 for every other non-identity Pauli observable.  Then mu^2 = (D-1)/|S|, the signs of the
expectation values are an optimal noncontextual assignment of S, and the contextuality degree of S (with
all contexts it contains, whether or not S is closed under products) is exactly

    d(S) = ( L_S - (D-2) |S|^(3/2) / (6 sqrt(D-1)) ) / 2 .

This script checks that statement on six states, with amplitudes in Z[i] and no floating point:

    N=2  the Liu-Low-Yin state (i,i,i,1)/2                       12 points,     8 contexts, degree   0
    N=3  CCZ|+++>                                                28 points,    56 contexts, degree   0
    N=3  the Hoggar fiducial                                     63 points,   315 contexts, degree  63
    N=4  (-3,1,...,1)/sqrt(24)   (real Hoggar; quadric)         135 points,  1575 contexts, degree 315
    N=4  the pivot state  (|3>+|7>+|11>+|12>+|13>+i|14>)/sqrt6  135 points,  1095 contexts, degree  75
    N=5  Cieslinski's state |s5>                                496 points, 10880 contexts, degree 480

and the structural statements made in the paper about the fifth one.  It writes data/flat/*.txt (support
and sign masks), results/flat_states.json and, with --lean, lean/HoggarBound/FlatData.lean.

  python scripts/flat_states.py [--lean] [--quick]
"""
import collections, itertools, json, math, os, random, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
pc = lambda x: bin(x).count("1")
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print("%s  %s%s" % ("PASS" if ok else "FAIL", name, ("   [" + detail + "]") if detail else ""))
    return ok


# ---------------------------------------------------------------- Gaussian integers
def gmul(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


I_POW = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def expectations(amp, N):
    """amp: 2^N Gaussian integers (re, im), unnormalised.  Returns (n, p) with <P_v> = p[v] / n exactly,
    where P_v = i^{|a&c|} X^a Z^c, v = a + 2^N c, and X^a Z^c |x> = (-1)^{c.x} |x xor a>."""
    D = 1 << N
    n = sum(a[0] * a[0] + a[1] * a[1] for a in amp)
    p = {}
    for a in range(D):
        w = [gmul((amp[x ^ a][0], -amp[x ^ a][1]), amp[x]) for x in range(D)]
        for c in range(D):
            re = im = 0
            for x in range(D):
                if pc(c & x) & 1:
                    re -= w[x][0]; im -= w[x][1]
                else:
                    re += w[x][0]; im += w[x][1]
            val = gmul(I_POW[pc(a & c) % 4], (re, im))
            assert val[1] == 0, "a Hermitian operator has a real expectation value"
            p[a | (c << N)] = val[0]
    return n, p


# ---------------------------------------------------------------- geometry
def commute(u, v, N):
    m = (1 << N) - 1
    return (pc((u & m) & (v >> N)) + pc((u >> N) & (v & m))) % 2 == 0


def line_sign(u, v, N):
    """P_u P_v P_{u+v} = sign * I for commuting u, v."""
    m = (1 << N) - 1
    au, cu, av, cv = u & m, u >> N, v & m, v >> N
    k = (pc(au & cu) + pc(av & cv) + 2 * pc(cu & av) + 3 * pc((au ^ av) & (cu ^ cv))) % 4
    assert k in (0, 2)
    return 1 if k == 0 else -1


def lines_of(S, N):
    Sset = set(S)
    out = []
    for i, u in enumerate(S):
        for v in S[i + 1:]:
            w = u ^ v
            if w > v and w in Sset and commute(u, v, N):
                out.append((u, v, w, line_sign(u, v, N)))
    return out


def isqrt_exact(x):
    r = math.isqrt(x)
    return r if r * r == x else None


def analyse(name, amp, N, expect):
    """Exact analysis of one state.  expect = (points, lines, degree)."""
    D = 1 << N
    n, p = expectations(amp, N)
    assert p[0] == n
    mods = sorted(set(abs(x) for v, x in p.items() if v and x))
    flat = len(mods) == 1
    S = sorted(v for v, x in p.items() if v and x)
    f = {v: (1 if p[v] > 0 else -1) for v in S}
    check("%s: all nonzero Pauli expectation values have one modulus" % name, flat, "moduli/n = %s/%d" % (mods, n))
    mu_num = mods[0]                                   # mu = mu_num / n
    check("%s: mu^2 = (D-1)/|S|" % name, mu_num * mu_num * len(S) == (D - 1) * n * n, "|S| = %d, mu = %d/%d" % (len(S), mu_num, n))
    L = lines_of(S, N)
    viol = sum(1 for u, v, w, s in L if f[u] * f[v] * f[w] != s)
    m = isqrt_exact((D - 1) * len(S))
    check("%s: (D-1)|S| is a perfect square, so the floor is rational" % name, m is not None)
    num = (D - 2) * len(S) * m                          # beta_max = num / (6 (D-1))
    check("%s: the floor value of beta is an integer" % name, num % (6 * (D - 1)) == 0)
    beta = num // (6 * (D - 1))
    floor_deg = (len(L) - beta + 1) // 2
    check("%s: the signs of the state violate exactly the floor number of contexts" % name,
          len(L) - 2 * viol == beta and viol == floor_deg, "contexts %d, violated %d, beta %d" % (len(L), viol, beta))
    check("%s: points, contexts, degree as stated" % name, (len(S), len(L), viol) == expect, str((len(S), len(L), viol)))
    # local excess: every point lies on the same number of satisfied-minus-violated contexts
    exc = collections.Counter()
    deg = collections.Counter(); vdeg = collections.Counter()
    for u, v, w, s in L:
        good = f[u] * f[v] * f[w] == s
        for t in (u, v, w):
            exc[t] += 1 if good else -1
            deg[t] += 1
            vdeg[t] += 0 if good else 1
    want = (D - 2) * m
    check("%s: every point lies on (D-2)sqrt|S| / (2 sqrt(D-1)) more satisfied than violated contexts" % name,
          all(2 * (D - 1) * exc[t] == want for t in S), "excess %s" % sorted(set(exc.values())))
    # outside balance: for w outside S the signed commuting pairs of S with product w cancel
    Sset = set(S)
    bal = collections.Counter()
    for i, u in enumerate(S):
        for v in S[i + 1:]:
            w = u ^ v
            if w not in Sset and commute(u, v, N):
                bal[w] += line_sign(u, v, N) * f[u] * f[v]
    check("%s: for every observable outside S the signed commuting pairs of S with that product cancel" % name,
          all(x == 0 for x in bal.values()), "%d outside products" % len(bal))
    closed = all(((u ^ v) in Sset) for i, u in enumerate(S) for v in S[i + 1:] if commute(u, v, N))
    hist = sorted(collections.Counter((deg[t], vdeg[t]) for t in S).items())
    return dict(name=name, N=N, n=n, mu="%d/%d" % (mu_num // math.gcd(mu_num, n), n // math.gcd(mu_num, n)),
                points=len(S), contexts=len(L), degree=viol, beta=beta, line_closed=closed,
                degree_histogram=[[list(k), c] for k, c in hist], S=S, f=f, lines=L)


def mask_of(vs):
    m = 0
    for v in vs:
        m |= 1 << v
    return m


# ---------------------------------------------------------------- the six states
def states():
    one, i, zero = (1, 0), (0, 1), (0, 0)
    out = []
    out.append(("lly", 2, [i, i, i, one], (12, 8, 0)))
    out.append(("ccz", 3, [((-1) ** ((x & 1) * ((x >> 1) & 1) * ((x >> 2) & 1)), 0) for x in range(8)], (28, 56, 0)))
    out.append(("hoggar", 3, [(-1, 2)] + [one] * 7, (63, 315, 63)))
    out.append(("quadric", 4, [(-3, 0)] + [one] * 15, (135, 1575, 315)))
    T = [x for x in range(16) if ((x & 1) * ((x >> 1) & 1) + ((x >> 2) & 1) * ((x >> 3) & 1)) % 2 == 1]
    assert T == [3, 7, 11, 12, 13, 14]
    out.append(("pivot", 4, [(i if x == 14 else one) if x in T else zero for x in range(16)], (135, 1095, 75)))
    a1, a2, a3, a4 = (-1, -2), (2, -1), (5, 0), (-3, 4)
    neg = lambda z: (-z[0], -z[1])
    s5 = [a1, neg(a2), a1, neg(a2), neg(a1), neg(a2), neg(a1), a2, gmul(i, a3), a1, a2, a3, a2, a4, neg(a2), a3,
          a2, a3, neg(a2), neg(a1), a2, neg(a4), neg(a2), neg(a1), a1, neg(gmul(i, a3)), neg(a1), a2, neg(a3), a2,
          neg(a1), neg(a2)]
    out.append(("cieslinski5", 5, s5, (496, 10880, 480)))
    return out, T


def anneal(S, L, floor, trials, steps, seed):
    """Search for an assignment below the floor (there must be none)."""
    rng = random.Random(seed)
    idx = {v: k for k, v in enumerate(S)}
    inc = [[] for _ in S]
    LL = [(idx[u], idx[v], idx[w], s) for u, v, w, s in L]
    for li, (a, b, c, s) in enumerate(LL):
        inc[a].append(li); inc[b].append(li); inc[c].append(li)
    best_all = None
    for t in range(trials):
        f = [rng.choice((1, -1)) for _ in S]
        bad = [f[a] * f[b] * f[c] != s for a, b, c, s in LL]
        cur = sum(bad); best = cur
        for step in range(steps):
            T = 1.2 * (1 - step / steps) + 0.02
            k = rng.randrange(len(S))
            delta = sum(1 - 2 * bad[li] for li in inc[k])
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                f[k] = -f[k]
                for li in inc[k]:
                    bad[li] = not bad[li]
                cur += delta
                best = min(best, cur)
        best_all = best if best_all is None else min(best_all, best)
        assert best >= floor, "COUNTEREXAMPLE: an assignment below the floor"
    return best_all


def main():
    quick = "--quick" in sys.argv
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    table, results = [], {}
    sts, T = states()
    os.makedirs(os.path.join(ROOT, "data", "flat"), exist_ok=True)
    for name, N, amp, expect in sts:
        r = analyse(name, amp, N, expect)
        results[name] = r
        neg = [v for v in r["S"] if r["f"][v] < 0]
        with open(os.path.join(ROOT, "data", "flat", "n%d_%s.txt" % (N, name)), "w", newline="\n") as fh:
            fh.write("%d %d %d %d\n%x\n%x\n" % (N, r["points"], r["contexts"], r["degree"], mask_of(r["S"]), mask_of(neg)))
        table.append((name, N, r["points"], r["contexts"], r["degree"], r["mu"], r["line_closed"]))

    # ---- the pivot configuration S_B in detail
    N = 4
    rb, ra = results["pivot"], results["quadric"]
    S = rb["S"]; Sset = set(S); f = rb["f"]
    hyp = collections.Counter()
    for w in range(1, 256):
        hyp[(sum(1 for u in S if commute(u, w, N)), w in Sset)] += 1
    check("pivot: every hyperplane w-perp meets S in 71 points (w in S) or 63 points (w outside S), as for Q+(7,2)",
          dict(hyp) == {(71, True): 135, (63, False): 120}, str(sorted(hyp.items())))
    ind = lambda v: 0 if v == 0 or v in Sset else 1
    quad = all((ind(u ^ v) + ind(u) + ind(v) + (0 if commute(u, v, N) else 1)) % 2 == 0 for u in range(256) for v in range(u + 1, 256))
    check("pivot: S is not a quadric", not quad)
    check("pivot: S is not closed under products of commuting pairs", not rb["line_closed"])
    check("quadric: its support is closed under products of commuting pairs", ra["line_closed"])
    E = sorted(14 ^ x for x in T if x != 14)
    Sdesc = sorted(v for v in range(1, 256) if ((v & 15) == 0) or ((v & 15) != 0 and pc((v & 15) & (v >> 4)) % 2 == (1 if (v & 15) in E else 0)))
    check("pivot: S = {Z-type} + {(a|c): a != 0, a.c = [a in E]} with E = (14 + T) minus 0, five values of a", Sdesc == S, "E = %s" % E)
    Qstd = sorted(v for v in range(1, 256) if pc((v & 15) & (v >> 4)) % 2 == 0)
    check("quadric: its support is the standard hyperbolic quadric a.c = 0", Qstd == ra["S"])
    check("pivot: S and the quadric differ in 80 points (40 removed, 40 added), all with a in E",
          len(Sset ^ set(Qstd)) == 80 and all((v & 15) in E for v in Sset ^ set(Qstd)))
    Bf = lambda x, y: (((x >> 0) & 1) * ((y >> 1) & 1) + ((x >> 1) & 1) * ((y >> 0) & 1) + ((x >> 2) & 1) * ((y >> 3) & 1) + ((x >> 3) & 1) * ((y >> 2) & 1)) % 2
    check("pivot: the five vectors of E are pairwise non-orthogonal for the form of the bent function (an ovoid of the doily)",
          all(Bf(x, y) == 1 for x in E for y in E if x != y))
    bad = [(u, v, w) for u, v, w, s in rb["lines"] if f[u] * f[v] * f[w] != s]
    zt = lambda v: (v & 15) == 0
    kinds = collections.Counter(sum(1 for t in l if zt(t)) for l in bad)
    check("pivot: the 75 violated contexts are 15 Z-type contexts and 60 with exactly one Z-type point", dict(kinds) == {3: 15, 1: 60}, str(dict(kinds)))
    zl = sorted(tuple(sorted(t >> 4 for t in l)) for l in bad if all(zt(t) for t in l))
    doily = sorted(tuple(sorted((x, y, x ^ y))) for x in range(1, 16) for y in range(x + 1, 16) if (x ^ y) > y and Bf(x, y) == 0)
    check("pivot: the 15 violated Z-type contexts are the 15 lines of the doily W(3,2) of that form", zl == doily)
    check("pivot: degree histogram (contexts through a point, violated ones): 120 points (23,1), 15 points (35,7)",
          rb["degree_histogram"] == [[[23, 1], 120], [[35, 7], 15]], str(rb["degree_histogram"]))

    # ---- all 4^6 phase patterns on the bent support
    cache = {}
    counts = collections.Counter()
    ok_parity = True
    pats = list(itertools.product(range(4), repeat=6))
    if quick:
        pats = [k for k in pats if k[0] == 0 and all(x in (0, 1) for x in k)]
    for k in pats:
        amp = [(0, 0)] * 16
        for x, kx in zip(T, k):
            amp[x] = I_POW[kx]
        n, p = expectations(amp, 4)
        Sk = tuple(sorted(v for v, x in p.items() if v and x))
        if not (n == 6 and len(Sk) == 135 and all(abs(p[v]) == 2 for v in Sk)):
            ok_parity = False; break
        if Sk not in cache:
            cache[Sk] = len(lines_of(list(Sk), 4))
        Lk = cache[Sk]
        odd = sum(x & 1 for x in k) % 2
        counts[(Lk, odd)] += 1
        if (Lk, odd) not in ((1575, 0), (1095, 1)):
            ok_parity = False; break
    check("bent support: all %d patterns of fourth-root-of-unity amplitudes give states flat on 135 points; the support has"
          " 1575 contexts if the number of imaginary amplitudes is even and 1095 if it is odd" % len(pats),
          ok_parity, "%s; %d distinct supports" % (dict(counts), len(cache)))

    # ---- superpositions of two mutually unbiased stabiliser states (Proposition 9)
    plus3 = [(1, 0)] * 8
    hog = [(-1, 2)] + [(1, 0)] * 7
    check("two stabiliser states, N=3: Hoggar fiducial = sqrt8 |+++> + (-2+2i) |000>, equal weights, relative phase 3 pi/4",
          all(hog[x] == ((plus3[x][0] + (-2 if x == 0 else 0)), (2 if x == 0 else 0)) for x in range(8)))
    check("two stabiliser states, N=4: (-3,1,...,1) = 4 |++++> - 4 |0000>, equal weights, relative phase pi",
          all(((-3, 0) if x == 0 else (1, 0)) == (1 - (4 if x == 0 else 0), 0) for x in range(16)))
    n2, p2 = expectations([(2, 1), (0, 1), (0, 1), (0, 1)], 2)        # 2 |00> + 2i |++>
    S2 = sorted(v for v, x in p2.items() if v and x)
    check("two stabiliser states, N=2: |00> + i |++> is flat on 12 observables with modulus 1/2, zero on a commuting triple",
          len(S2) == 12 and all(2 * abs(p2[v]) == n2 for v in S2)
          and all(commute(u, v, 2) for u in range(1, 16) for v in range(1, 16) if u not in S2 and v not in S2))
    okN1 = True
    for cosphi in ((6 ** 0.5 - 2 ** 0.5) / 4, -(6 ** 0.5 + 2 ** 0.5) / 4):
        ph = complex(cosphi, (1 - cosphi * cosphi) ** 0.5)
        psi1 = [1 + ph / 2 ** 0.5, ph / 2 ** 0.5]                      # |0> + e^{i phi} |+>
        nn = sum(abs(z) ** 2 for z in psi1)
        ex = [2 * (psi1[0].conjugate() * psi1[1]).real / nn, 2 * (psi1[0].conjugate() * psi1[1]).imag / nn,
              (abs(psi1[0]) ** 2 - abs(psi1[1]) ** 2) / nn]
        okN1 &= all(abs(abs(e) - 3 ** -0.5) < 1e-12 for e in ex)
    check("two stabiliser states, N=1 (floating point): |0> + e^{i phi} |+> has all three expectation values of modulus 1/sqrt3 for the two stated phases", okN1)

    # ---- the observables outside a maximal commuting set
    okND = True
    for Nq in (2, 3, 4):
        Dq = 1 << Nq
        nd = [v for v in range(1, Dq * Dq) if v & (Dq - 1)]
        okND &= len(nd) == Dq * Dq - Dq and 12 * len(lines_of(nd, Nq)) == (Dq - 1) * (Dq - 2) * Dq * Dq
    check("non-diagonal observables: D^2 - D points and (D-1)(D-2)D^2/12 contexts for N = 2, 3, 4", okND)
    check("lly: its support is the set of all non-diagonal two-qubit observables", results["lly"]["S"] == [v for v in range(1, 16) if v & 3])

    # ---- falsification: search for assignments below the floor
    trials, steps = (2, 20000) if quick else (12, 120000)
    b4 = anneal(rb["S"], rb["lines"], 75, trials, steps, 20261109)
    check("pivot: annealing from random starts never goes below 75 violated contexts", b4 >= 75, "best found %d" % b4)
    r5 = results["cieslinski5"]
    b5 = anneal(r5["S"], r5["lines"], 480, 2 if quick else 4, 60000 if quick else 400000, 20261110)
    check("cieslinski5: annealing from random starts never goes below 480 violated contexts", b5 >= 480, "best found %d" % b5)

    print()
    print("%-12s %2s %7s %9s %7s %6s %s" % ("state", "N", "points", "contexts", "degree", "mu", "line-closed"))
    for row in table:
        print("%-12s %2d %7d %9d %7d %6s %s" % row)
    summary = {name: {k: v for k, v in r.items() if k not in ("S", "f", "lines")} for name, r in results.items()}
    summary["_checks"] = {"passed": sum(ok for _, ok in CHECKS), "total": len(CHECKS)}
    summary["_annealing_best"] = {"pivot": b4, "cieslinski5": b5}
    if not quick:
        json.dump(summary, open(os.path.join(ROOT, "results", "flat_states.json"), "w"), indent=1)

    if "--lean" in sys.argv:
        lines = ["/-", "Generated by scripts/flat_states.py --lean.  Do not edit.",
                 "", "Supports and optimal sign patterns of six Pauli-flat states, as bit masks: bit `v` of a support mask is set",
                 "when the observable with code `v = a + 2^N * c` belongs to the configuration (`a` the X-part, `c` the Z-part,",
                 "bit `k` for qubit `k`); bit `v` of a sign mask is set when the assignment takes the value `-1` there.", "-/",
                 "", "namespace HoggarBound.FlatData", ""]
        for name, N, amp, expect in sts:
            r = results[name]
            neg = [v for v in r["S"] if r["f"][v] < 0]
            lines.append("/-- %s: %d qubits, %d observables, %d contexts, degree %d. -/" % (name, N, r["points"], r["contexts"], r["degree"]))
            lines.append("def %sMask : Nat := 0x%x" % (name, mask_of(r["S"])))
            lines.append("def %sNeg : Nat := 0x%x" % (name, mask_of(neg)))
            lines.append("")
        lines.append("end HoggarBound.FlatData")
        open(os.path.join(ROOT, "lean", "HoggarBound", "FlatData.lean"), "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")
        print("wrote lean/HoggarBound/FlatData.lean")

        # five qubits: the double sums have 2^20 terms; they are evaluated in 16 blocks of 64 rows
        r5 = results["cieslinski5"]
        S5, f5 = r5["S"], r5["f"]
        S5set = set(S5)
        frow = [0] * 1024; vrow = [0] * 1024
        for z in S5:
            for w in S5:
                x = z ^ w
                if x in S5set and commute(z, w, 5):
                    frow[z] += 1
                    if f5[z] * f5[w] * f5[x] != line_sign(z, w, 5):
                        vrow[z] += 1
        fb = [sum(frow[64 * k: 64 * k + 64]) for k in range(16)]
        vb = [sum(vrow[64 * k: 64 * k + 64]) for k in range(16)]
        assert sum(fb) == 6 * r5["contexts"] and sum(vb) == 6 * r5["degree"]
        L = ["/-", "Generated by scripts/flat_states.py --lean.  Do not edit.", "",
             "Five qubits: the configuration of 496 observables coded by `cieslinski5Mask`.  Its flag count and the",
             "number of flags violated by the assignment `cieslinski5Neg` are sums over 2^20 pairs of codes.  Each is",
             "evaluated by the kernel in 16 blocks of 64 rows (one theorem per block, so that no single evaluation",
             "is large) and the blocks are added.  No `native_decide`.", "-/",
             "import HoggarBound.MaskConfig", "import HoggarBound.FlatData", "", "open Finset Matrix", "",
             "namespace HoggarBound", "", "open FlatData", "",
             "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
             "theorem cieslinski5_card : (cfg 5 cieslinski5Mask).card = 496 := by",
             "  rw [card_cfg, card_codes]; decide +kernel", ""]
        for k in range(16):
            L += ["theorem c5_flags_%d : block (flagRow 5 cieslinski5Mask) 64 %d = %d := by decide +kernel" % (k, k, fb[k])]
        L += ["", "theorem cieslinski5_flags : (flags (cfg 5 cieslinski5Mask)).card = %d := by" % sum(fb),
              "  have h := loop_blocks (flagRow 5 cieslinski5Mask) 64 16",
              "  rw [loop_sixteen, " + ", ".join("c5_flags_%d" % k for k in range(16)) + "] at h",
              "  have e : (2 : ℕ) ^ (2 * 5) = 64 * 16 := by norm_num",
              "  rw [card_flags_cfg, e]",
              "  exact h.trans (by norm_num)", ""]
        for k in range(16):
            L += ["theorem c5_viol_%d : block (violRow 5 cieslinski5Mask cieslinski5Neg) 64 %d = %d := by decide +kernel" % (k, k, vb[k])]
        L += ["", "theorem cieslinski5_witness :",
              "    (violated (cfg 5 cieslinski5Mask) (fun u => ((sgnOf 5 cieslinski5Neg u : ℤ) : ℝ))).card = 6 * %d := by" % r5["degree"],
              "  have h := loop_blocks (violRow 5 cieslinski5Mask cieslinski5Neg) 64 16",
              "  rw [loop_sixteen, " + ", ".join("c5_viol_%d" % k for k in range(16)) + "] at h",
              "  have e : (2 : ℕ) ^ (2 * 5) = 64 * 16 := by norm_num",
              "  rw [card_violated_cfg, e]",
              "  exact h.trans (by norm_num)", "", "end HoggarBound"]
        open(os.path.join(ROOT, "lean", "HoggarBound", "SaturatedFive.lean"), "w", encoding="utf-8", newline="\n").write("\n".join(L) + "\n")
        print("wrote lean/HoggarBound/SaturatedFive.lean")

    npass = sum(ok for _, ok in CHECKS)
    print("\n%d of %d checks passed" % (npass, len(CHECKS)))
    sys.exit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
phase_states.py - flat third-level phase states, in exact integer arithmetic.

A diagonal gate of the third level of the Clifford hierarchy multiplies |x> by exp(i pi p(x)/4), with

    p(x) = sum a_j x_j + 2 sum b_jk x_j x_k + 4 sum c_jkl x_j x_k x_l   (mod 8)      (T, CS and CCZ gates).

Its third difference is a symmetric trilinear form T over F_2 (t_jjj = a_j, t_jjk = t_jkk = b_jk,
t_jkl = c_jkl).  For the state U|+...+>, the expectation values of the observables X^a Z^c with a fixed
a != 0 are 0 or of modulus 2^(-r_a/2), r_a the rank of the symmetric matrix T(a,.,.).  So the state has a
single non-zero modulus exactly when that rank is the same for every a != 0, and then it attains the
spectral floor on its Pauli support (paper, Section 5.3).

This script checks, without floating point:

  * the census of such forms for N <= 4 (the C program src/third_level.c does N <= 5);
  * five explicit states:  CS|++>,  CCZ|+++>,  CS CS|+++>,  the five-qubit state Phi5 (3 CS + 2 CCZ) and the
    seven-qubit state Phi7 (3 CS + 8 CCZ): flatness, support, contexts, exact contextuality degree;
  * that the support of every flat state in this repository is a two-character set, with the two
    intersection numbers of Proposition 10;
  * the structure of the supports of the phase states (an involution rho of the non-zero vectors);
  * an explicit symplectic map from the support of Phi5 onto the support of Cieslinski's state s5;
  * the finite-field descriptions of the five- and seven-qubit forms.

It writes data/flat/n5_phase5.txt, data/flat/n7_phase7.txt, results/phase_states.json and, with --lean,
lean/HoggarBound/PhaseData.lean and lean/HoggarBound/SaturatedPhaseFive.lean.

  python scripts/phase_states.py [--lean] [--quick]
"""
import collections, itertools, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import flat_states as fs  # noqa: E402

ROOT = fs.ROOT
pc = fs.pc
check = fs.check

# the two new states: gates on |+...+>
PHI5 = dict(N=5, cs=[(0, 1), (1, 3), (2, 4)], ccz=[(0, 1, 4), (0, 2, 3)])
PHI7 = dict(N=7, cs=[(0, 1), (2, 3), (4, 5)],
            ccz=[(0, 1, 2), (0, 3, 5), (1, 2, 4), (0, 4, 6), (0, 5, 6), (1, 3, 6), (2, 3, 6), (2, 5, 6)])


# ---------------------------------------------------------------- trilinear forms over F_2
def trilinear(N, tg=(), cs=(), ccz=()):
    """M[j][k] = bit mask over l of T(e_j, e_k, e_l)."""
    M = [[0] * N for _ in range(N)]
    for j in tg:
        M[j][j] ^= 1 << j
    for j, k in cs:
        for p in set(itertools.permutations((j, j, k))) | set(itertools.permutations((j, k, k))):
            M[p[0]][p[1]] ^= 1 << p[2]
    for t in ccz:
        for p in itertools.permutations(t):
            M[p[0]][p[1]] ^= 1 << p[2]
    return M


def contraction(M, N, v):
    rows = [0] * N
    for j in range(N):
        if (v >> j) & 1:
            for k in range(N):
                rows[k] ^= M[j][k]
    return rows


def rank_f2(rows, n):
    rows = list(rows)
    rank = 0
    for col in range(n):
        piv = None
        for i in range(rank, n):
            if (rows[i] >> col) & 1:
                piv = i
                break
        if piv is None:
            continue
        rows[piv], rows[rank] = rows[rank], rows[piv]
        for i in range(n):
            if i != rank and (rows[i] >> col) & 1:
                rows[i] ^= rows[rank]
        rank += 1
    return rank


def kernel(rows, n):
    return [z for z in range(1, 1 << n) if all(pc(r & z) % 2 == 0 for r in rows)]


def rank_profile(M, N):
    return collections.Counter(rank_f2(contraction(M, N, v), N) for v in range(1, 1 << N))


def phase_amp(N, cs, ccz):
    """amplitudes i^{q(x)},  q = sum_cs x_j x_k + 2 sum_ccz x_j x_k x_l  (mod 4);  p = 2q."""
    amp = []
    for x in range(1 << N):
        b = lambda j: (x >> j) & 1
        q = sum(b(j) * b(k) for j, k in cs) + 2 * sum(b(j) * b(k) * b(l) for j, k, l in ccz)
        amp.append(fs.I_POW[q % 4])
    return amp


# ---------------------------------------------------------------- two-character sets
def walsh(S, N):
    """W[w] = sum over v in S of (-1)^<v,w>  (symplectic pairing), for all w."""
    n2 = 2 * N
    g = [0] * (1 << n2)
    for v in S:
        g[v] = 1
    h = 1
    while h < len(g):
        for i in range(0, len(g), 2 * h):
            for j in range(i, i + h):
                x, y = g[j], g[j + h]
                g[j], g[j + h] = x + y, x - y
        h *= 2
    m = (1 << N) - 1
    return [g[(w >> N) | ((w & m) << N)] for w in range(1 << n2)]


def two_character(name, S, N):
    """Proposition 10: |w-perp meet S| = (D-2)|S| / (2(D-1)) + (D/2) [w in S]."""
    D = 1 << N
    W = walsh(S, N)
    Sset = set(S)
    ok = (len(S) % (D - 1) == 0)
    k2 = len(S) // (D - 1)
    ok = ok and all(W[w] == (D - k2 if w in Sset else -k2) for w in range(1, D * D))
    check("%s: the support is a two-character set: sum over S of (-1)^<v,w> is D - |S|/(D-1) on S and -|S|/(D-1) off S" % name,
          ok, "|S| = %d, values %s" % (len(S), sorted(set(W[1:]))))
    return k2


# ---------------------------------------------------------------- symplectic equivalence of supports
def point_types(S, N):
    Sset = set(S)
    L = fs.lines_of(S, N)
    deg = collections.Counter()
    for u, v, w, s in L:
        deg[u] += 1; deg[v] += 1; deg[w] += 1
    typ = {}
    for w in range(1, 1 << (2 * N)):
        if w in Sset:
            typ[w] = ("in", deg[w])
        else:
            cm = sum(1 for u in S if (u ^ w) in Sset and u < (u ^ w) and fs.commute(u, u ^ w, N))
            ac = sum(1 for u in S if (u ^ w) in Sset and u < (u ^ w) and not fs.commute(u, u ^ w, N))
            typ[w] = ("out", cm, ac)
    return typ


def find_symplectic_map(S1, S2, N, limit=200000):
    """Depth-first search for a linear map preserving the symplectic form with g(S1) = S2.
    Returns the images of the basis vectors, None if there is none, or 'limit'."""
    t1, t2 = point_types(S1, N), point_types(S2, N)
    if collections.Counter(t1.values()) != collections.Counter(t2.values()):
        return None
    by2 = collections.defaultdict(list)
    for w, t in t2.items():
        by2[t].append(w)
    cnt = collections.Counter(t1.values())
    basis = sorted((1 << j for j in range(2 * N)), key=lambda b: cnt[t1[b]])
    sy = lambda u, v: 0 if fs.commute(u, v, N) else 1
    img = {0: 0}
    nodes = [0]

    def dfs(k):
        nodes[0] += 1
        if nodes[0] > limit:
            raise OverflowError
        if k == len(basis):
            return True
        b = basis[k]
        span = list(img.keys())
        for cand in by2[t1[b]]:
            if any(sy(basis[i], b) != sy(img[basis[i]], cand) for i in range(k)):
                continue
            new = {}
            ok = True
            for x in span:
                y, gy = x ^ b, img[x] ^ cand
                if gy == 0 or t1[y] != t2[gy]:
                    ok = False
                    break
                new[y] = gy
            if not ok:
                continue
            img.update(new)
            if dfs(k + 1):
                return True
            for y in new:
                del img[y]
        return False

    try:
        found = dfs(0)
    except OverflowError:
        return "limit"
    return [img[1 << j] for j in range(2 * N)] if found else None


def verify_symplectic_map(g, S1, S2, N):
    n2 = 2 * N
    full = [0] * (1 << n2)
    for x in range(1 << n2):
        y = 0
        for j in range(n2):
            if (x >> j) & 1:
                y ^= g[j]
        full[x] = y
    sy = lambda u, v: 0 if fs.commute(u, v, N) else 1
    sympl = all(sy(1 << i, 1 << j) == sy(g[i], g[j]) for i in range(n2) for j in range(n2))
    return sympl and len(set(full)) == 1 << n2 and {full[x] for x in S1} == set(S2)


# ---------------------------------------------------------------- finite-field models
class Field:
    PRIM = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101}

    def __init__(self, m):
        self.m, self.size = m, 1 << m
        self.exp, self.log = [0] * (2 * self.size), [0] * self.size
        x = 1
        for i in range(self.size - 1):
            self.exp[i], self.log[x] = x, i
            x <<= 1
            if x & self.size:
                x ^= self.PRIM[m]
        for i in range(self.size - 1, 2 * self.size):
            self.exp[i] = self.exp[i - (self.size - 1)]

    def mul(self, a, b):
        return 0 if a == 0 or b == 0 else self.exp[self.log[a] + self.log[b]]

    def tr(self, a):
        t, x = 0, a
        for _ in range(self.m):
            t ^= x
            x = self.mul(x, x)
        return t


def torus_model(n, a, e3=0):
    """V = F_q x F_q x F_2, q = 2^n:
       T = Tr[x1 y1 z2^2 + x1 y2^2 z1 + x2^2 y1 z1 + x2 y2 z1^2 + x2 y1^2 z2 + x1^2 y2 z2] + e3 Det(x1,y1,z1)
           + alpha S(y,z) + beta S(x,z) + gamma S(x,y),   S(y,z) = Tr[a (y1 z2 + y2 z1)]."""
    F = Field(n)
    N = 2 * n + 1
    mul, tr = F.mul, F.tr
    sq = lambda u: mul(u, u)
    basis = [(1 << j, 0, 0) for j in range(n)] + [(0, 1 << j, 0) for j in range(n)] + [(0, 0, 1)]
    S = lambda y, z: tr(mul(a, mul(y[0], z[1]) ^ mul(y[1], z[0])))

    def det3(x, y, z):
        span = {0}
        for v in (x, y, z):
            span |= {s ^ v for s in span}
        return 1 if len(span) == 8 else 0

    def T(X, Y, Z):
        (x1, x2, al), (y1, y2, be), (z1, z2, ga) = X, Y, Z
        v = mul(mul(x1, y1), sq(z2)) ^ mul(mul(x1, sq(y2)), z1) ^ mul(mul(sq(x2), y1), z1)
        v ^= mul(mul(x2, y2), sq(z1)) ^ mul(mul(x2, sq(y1)), z2) ^ mul(mul(sq(x1), y2), z2)
        t = tr(v) ^ (det3(x1, y1, z1) if e3 else 0)
        return t ^ (al & S(Y, Z)) ^ (be & S(X, Z)) ^ (ga & S(X, Y))

    M = [[0] * N for _ in range(N)]
    for j in range(N):
        for k in range(N):
            for l in range(N):
                if T(basis[j], basis[k], basis[l]):
                    M[j][k] |= 1 << l
    return M, N, F


def realizable(M, N):
    """totally symmetric, and T(x,x,z) symmetric in (x,z): the third difference of some p."""
    t = lambda j, k, l: (M[j][k] >> l) & 1
    return all(t(j, k, l) == t(k, j, l) == t(j, l, k) for j in range(N) for k in range(N) for l in range(N)) \
        and all(t(j, j, k) == t(k, k, j) for j in range(N) for k in range(N))


# ---------------------------------------------------------------- one phase state
def study(name, N, cs, ccz, expect):
    D = 1 << N
    M = trilinear(N, (), cs, ccz)
    prof = rank_profile(M, N)
    r = max(prof)
    check("%s: the rank of T(a,.,.) is the same for every a != 0" % name, len(prof) == 1, "ranks %s" % dict(prof))
    res = fs.analyse(name, phase_amp(N, cs, ccz), N, expect)
    S, Sset = res["S"], set(res["S"])
    num, den = (int(x) for x in res["mu"].split("/"))
    check("%s: |S| = (D-1) 2^r and mu = 2^(-r/2)" % name, len(S) == (D - 1) << r and num * num << r == den * den,
          "r = %d, |S| = %d, mu = %s" % (r, len(S), res["mu"]))
    # structure of the support: for a != 0 the set {c : (a|c) in S} is a coset of the orthogonal complement of
    # the radical of T(a,.,.); no diagonal observable belongs to S
    m = D - 1
    ok = not any((v & m) == 0 for v in S)
    rho = {}
    for a in range(1, D):
        ker = kernel(contraction(M, N, a), N)
        cset = sorted(v >> N for v in S if (v & m) == a)
        ok = ok and len(cset) == 1 << r and len(ker) == (1 << (N - r)) - 1
        c0 = cset[0]
        ok = ok and all(all(pc((c ^ c0) & z) % 2 == 0 for z in ker) for c in cset)
        if len(ker) == 1:
            rho[a] = ker[0]
    check("%s: no diagonal observable in S; for each a != 0 the c with (a|c) in S form a coset of rad T(a,.,.)-perp" % name, ok)
    if r == N - 1:
        fixed = [a for a in rho if rho[a] == a]
        check("%s: the radical map rho is an involution of the non-zero vectors (S is the support of a Maiorana-McFarland bent function)" % name,
              len(rho) == D - 1 and all(rho[rho[a]] == a for a in rho), "%d fixed point(s)" % len(fixed))
    two_character(name, S, N)
    res["rank"] = r
    return res


def main():
    quick = "--quick" in sys.argv
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    results = {}

    # ---- census for N <= 4, independent of the C program
    census = {}
    for N in range(1, 5):
        pairs = list(itertools.combinations(range(N), 2))
        trips = list(itertools.combinations(range(N), 3))
        found = collections.Counter()
        for code in range(1, 1 << (N + len(pairs) + len(trips))):
            tg = [j for j in range(N) if (code >> j) & 1]
            cs = [pairs[i] for i in range(len(pairs)) if (code >> (N + i)) & 1]
            cz = [trips[i] for i in range(len(trips)) if (code >> (N + len(pairs) + i)) & 1]
            prof = rank_profile(trilinear(N, tg, cs, cz), N)
            if len(prof) == 1:
                found[max(prof)] += 1
        census[N] = dict(found)
    check("census: non-zero forms with constant rank: N=1 one (rank 1), N=2 one (rank 2), N=3 eight (rank 2), N=4 none",
          census == {1: {1: 1}, 2: {2: 1}, 3: {2: 8}, 4: {}}, str(census))

    # ---- the five states
    results["cs2"] = study("N=2 CS", 2, [(0, 1)], [], (12, 8, 0))
    results["ccz3"] = study("N=3 CCZ", 3, [], [(0, 1, 2)], (28, 56, 0))
    results["cscs3"] = study("N=3 CS CS", 3, [(0, 1), (0, 2)], [], (28, 56, 0))
    results["phase5"] = study("N=5 Phi5", 5, PHI5["cs"], PHI5["ccz"], (496, 10880, 480))
    if not quick:
        results["phase7"] = study("N=7 Phi7", 7, PHI7["cs"], PHI7["ccz"], (8128, 2824192, 729344))
        check("N=7 Phi7: |S| = 8128 = 2^6 (2^7 - 1), and the floor gives d = (2824192 - 1365504)/2 = 729344",
              results["phase7"]["beta"] == 1365504 and results["phase7"]["degree"] == 729344)

    # ---- the six states of flat_states.py are two-character sets as well
    sts, _ = fs.states()
    old = {}
    for name, N, amp, expect in sts:
        n, p = fs.expectations(amp, N)
        old[name] = sorted(v for v, x in p.items() if v and x)
        two_character(name, old[name], N)

    # ---- Phi5 and Cieslinski's state have equivalent supports
    g = find_symplectic_map(results["phase5"]["S"], old["cieslinski5"], 5)
    check("N=5: a symplectic map of F_2^10 takes the support of Phi5 onto the support of Cieslinski's state",
          isinstance(g, list) and verify_symplectic_map(g, results["phase5"]["S"], old["cieslinski5"], 5),
          "images of the basis vectors: %s" % (g,))
    check("N=5: the two supports are different sets", results["phase5"]["S"] != old["cieslinski5"])
    g3 = find_symplectic_map(results["cscs3"]["S"], results["ccz3"]["S"], 3)
    check("N=3: a symplectic map of F_2^6 takes the support of CS CS|+++> onto the support of CCZ|+++>",
          isinstance(g3, list) and verify_symplectic_map(g3, results["cscs3"]["S"], results["ccz3"]["S"], 3),
          "images of the basis vectors: %s" % (g3,))

    # ---- finite-field descriptions
    M2, N2, F2 = torus_model(2, 2)
    check("field model, N=5: F_4 x F_4 x F_2 with a a generator of F_4: realizable, rank 4 for every v != 0",
          realizable(M2, N2) and dict(rank_profile(M2, N2)) == {4: 31})
    M2b, _, _ = torus_model(2, 1)
    check("field model, N=5: with a = 1 the rank is not constant", len(rank_profile(M2b, 5)) > 1, str(dict(rank_profile(M2b, 5))))
    F3 = Field(3)
    good = [a for a in range(1, 8) if dict(rank_profile(torus_model(3, a, 1)[0], 7)) == {6: 127}]
    check("field model, N=7: F_8 x F_8 x F_2 with the determinant term: rank 6 for every v != 0 exactly for the three roots a of x^3 + x^2 + 1",
          sorted(good) == sorted(a for a in range(1, 8) if F3.mul(a, F3.mul(a, a)) ^ F3.mul(a, a) ^ 1 == 0), "a in %s" % good)
    check("field model, N=7: the form is realizable", realizable(torus_model(3, good[0], 1)[0], 7))
    none3 = all(len(rank_profile(torus_model(3, a, 0)[0], 7)) > 1 for a in range(1, 8))
    check("field model, N=7: without the determinant term the rank is never constant", none3)
    if not quick:
        none45 = all(len(rank_profile(torus_model(n, a)[0], 2 * n + 1)) > 1 for n in (4, 5) for a in range(1, 1 << n))
        check("field model, N=9 and N=11: no member of the torus-invariant family has constant rank", none45)

    # ---- data files
    os.makedirs(os.path.join(ROOT, "data", "flat"), exist_ok=True)
    for key in ("phase5", "phase7"):
        if key not in results:
            continue
        r = results[key]
        neg = [v for v in r["S"] if r["f"][v] < 0]
        with open(os.path.join(ROOT, "data", "flat", "n%d_%s.txt" % (r["N"], key)), "w", newline="\n") as fh:
            fh.write("%d %d %d %d\n%x\n%x\n" % (r["N"], r["points"], r["contexts"], r["degree"], fs.mask_of(r["S"]), fs.mask_of(neg)))

    print()
    print("%-10s %2s %7s %9s %8s %6s %5s" % ("state", "N", "points", "contexts", "degree", "mu", "rank"))
    for key, r in results.items():
        print("%-10s %2d %7d %9d %8d %6s %5d" % (key, r["N"], r["points"], r["contexts"], r["degree"], r["mu"], r["rank"]))
    if not quick:
        summary = {k: {kk: vv for kk, vv in r.items() if kk not in ("S", "f", "lines")} for k, r in results.items()}
        summary["_gates"] = {"phase5": PHI5, "phase7": PHI7}
        summary["_census"] = {str(k): v for k, v in census.items()}
        summary["_map_phase5_to_cieslinski5"] = g
        summary["_checks"] = {"passed": sum(ok for _, ok in fs.CHECKS), "total": len(fs.CHECKS)}
        json.dump(summary, open(os.path.join(ROOT, "results", "phase_states.json"), "w"), indent=1)

    if "--lean" in sys.argv:
        write_lean(results)

    npass = sum(ok for _, ok in fs.CHECKS)
    print("\n%d of %d checks passed" % (npass, len(fs.CHECKS)))
    sys.exit(0 if npass == len(fs.CHECKS) else 1)


def write_lean(results):
    lines = ["/-", "Generated by scripts/phase_states.py --lean.  Do not edit.", "",
             "Supports and optimal sign patterns of two flat third-level phase states, as bit masks (same conventions",
             "as `FlatData.lean`).", "-/", "", "namespace HoggarBound.PhaseData", ""]
    for key in ("phase5", "phase7"):
        if key not in results:
            continue
        r = results[key]
        neg = [v for v in r["S"] if r["f"][v] < 0]
        lines.append("/-- %s: %d qubits, %d observables, %d contexts, degree %d. -/" % (key, r["N"], r["points"], r["contexts"], r["degree"]))
        lines.append("def %sMask : Nat := 0x%x" % (key, fs.mask_of(r["S"])))
        lines.append("def %sNeg : Nat := 0x%x" % (key, fs.mask_of(neg)))
        lines.append("")
    lines.append("end HoggarBound.PhaseData")
    open(os.path.join(ROOT, "lean", "HoggarBound", "PhaseData.lean"), "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")
    print("wrote lean/HoggarBound/PhaseData.lean")

    r5 = results["phase5"]
    S5, f5, S5set = r5["S"], r5["f"], set(r5["S"])
    frow, vrow = [0] * 1024, [0] * 1024
    for z in S5:
        for w in S5:
            x = z ^ w
            if x in S5set and fs.commute(z, w, 5):
                frow[z] += 1
                if f5[z] * f5[w] * f5[x] != fs.line_sign(z, w, 5):
                    vrow[z] += 1
    fb = [sum(frow[64 * k: 64 * k + 64]) for k in range(16)]
    vb = [sum(vrow[64 * k: 64 * k + 64]) for k in range(16)]
    assert sum(fb) == 6 * r5["contexts"] and sum(vb) == 6 * r5["degree"]
    L = ["/-", "Generated by scripts/phase_states.py --lean.  Do not edit.", "",
         "Five qubits: the configuration of 496 observables coded by `phase5Mask`, the Pauli support of the state",
         "CCZ(0,1,4) CCZ(0,2,3) CS(0,1) CS(1,3) CS(2,4) |+++++>.  Flag count and violated flags of the assignment",
         "`phase5Neg`, each evaluated by the kernel in 16 blocks of 64 rows.  No `native_decide`.", "-/",
         "import HoggarBound.MaskConfig", "import HoggarBound.PhaseData", "", "open Finset Matrix", "",
         "namespace HoggarBound", "", "open PhaseData", "",
         "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
         "theorem phase5_card : (cfg 5 phase5Mask).card = 496 := by",
         "  rw [card_cfg, card_codes]; decide +kernel", ""]
    for k in range(16):
        L += ["theorem p5_flags_%d : block (flagRow 5 phase5Mask) 64 %d = %d := by decide +kernel" % (k, k, fb[k])]
    L += ["", "theorem phase5_flags : (flags (cfg 5 phase5Mask)).card = %d := by" % sum(fb),
          "  have h := loop_blocks (flagRow 5 phase5Mask) 64 16",
          "  rw [loop_sixteen, " + ", ".join("p5_flags_%d" % k for k in range(16)) + "] at h",
          "  have e : (2 : ℕ) ^ (2 * 5) = 64 * 16 := by norm_num",
          "  rw [card_flags_cfg, e]",
          "  exact h.trans (by norm_num)", ""]
    for k in range(16):
        L += ["theorem p5_viol_%d : block (violRow 5 phase5Mask phase5Neg) 64 %d = %d := by decide +kernel" % (k, k, vb[k])]
    L += ["", "theorem phase5_witness :",
          "    (violated (cfg 5 phase5Mask) (fun u => ((sgnOf 5 phase5Neg u : ℤ) : ℝ))).card = 6 * %d := by" % r5["degree"],
          "  have h := loop_blocks (violRow 5 phase5Mask phase5Neg) 64 16",
          "  rw [loop_sixteen, " + ", ".join("p5_viol_%d" % k for k in range(16)) + "] at h",
          "  have e : (2 : ℕ) ^ (2 * 5) = 64 * 16 := by norm_num",
          "  rw [card_violated_cfg, e]",
          "  exact h.trans (by norm_num)", "",
          "/-- **Five qubits, the phase state.**  The 496 observables with non-zero expectation value in",
          "`CCZ(0,1,4) CCZ(0,2,3) CS(0,1) CS(1,3) CS(2,4) |+++++>`, with their 10880 contexts: every noncontextual",
          "assignment violates at least 480 contexts, and some assignment violates exactly 480. -/",
          "theorem phase5_degree :",
          "    (∀ f : Pt 5 → ℝ, (∀ u ∈ cfg 5 phase5Mask, f u = 1 ∨ f u = -1) →",
          "        480 ≤ (violatedLines (cfg 5 phase5Mask) f).card) ∧",
          "      ∃ f : Pt 5 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧",
          "        (violatedLines (cfg 5 phase5Mask) f).card = 480 :=",
          "  degree_of_certificate (by norm_num) phase5Mask phase5Neg 496 65280 480 124",
          "    (by norm_num) (by decide) phase5_card phase5_flags phase5_witness",
          "    (by norm_num) (by norm_num)", "",
          "theorem phase5_contexts : (contexts (cfg 5 phase5Mask)).card = 10880 :=",
          "  contexts_of_flags phase5Mask 10880 (by decide) phase5_flags", "",
          "end HoggarBound"]
    open(os.path.join(ROOT, "lean", "HoggarBound", "SaturatedPhaseFive.lean"), "w", encoding="utf-8", newline="\n").write("\n".join(L) + "\n")
    print("wrote lean/HoggarBound/SaturatedPhaseFive.lean")


if __name__ == "__main__":
    main()

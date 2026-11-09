#!/usr/bin/env python3
"""
analysis.py - independent NumPy re-implementation and structural analysis for the Hoggar Bound Lab.

Checks (each is a test that can fail; the script exits non-zero if any does):
  1. witness files: violation counts recomputed from the definitions;
  2. third-moment identity  tr A^3 = 6 D beta  on random assignments and random point sets;
  3. spectra of the witness operators, compared with the extremal spectra of the theorem;
  4. Kramers degeneracy on elliptic quadrics and the quaternionic form of the bound;
  5. pure-state identity  sum_lines s p_u p_v p_w = (D-1)(D-2)/6  on random states;
  6. geometry of the violated contexts: split Cayley hexagon (N=3), DW(5,2) (N=4 hyperbolic),
     degree patterns (N=4 full and elliptic);
  7. table of bounds.
Writes results/analysis.json and the figures in paper/figures/.
"""
import json, math, os, sys, collections, itertools
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RES = os.path.join(ROOT, "results")
FIG = os.path.join(ROOT, "paper", "figures")
os.makedirs(RES, exist_ok=True); os.makedirs(FIG, exist_ok=True)
failures = []
report = {}

def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name + (" :: " + str(detail) if detail != "" else ""))
    if not cond:
        failures.append(name)
    return cond

POP = np.array([bin(i).count("1") for i in range(1 << 14)], dtype=np.int64)

class Geo:
    def __init__(self, N):
        self.N = N; self.D = D = 1 << N; self.n = n = 1 << (2 * N)
        v = np.arange(n)
        self.A = v & (D - 1); self.C = v >> N
        self.k = POP[self.A & self.C]
        U, V, W, S = [], [], [], []
        A, C = self.A, self.C
        for u in range(1, n):
            vs = np.arange(u + 1, n)
            w = vs ^ u
            ok = (w > vs) & (((POP[A[u] & C[vs]] + POP[C[u] & A[vs]]) & 1) == 0)
            vs = vs[ok]; w = w[ok]
            kk = (POP[A[u] & C[u]] + POP[A[vs] & C[vs]] + 2 * POP[C[u] & A[vs]] + 3 * POP[(A[u] ^ A[vs]) & (C[u] ^ C[vs])]) & 3
            U.append(np.full(len(vs), u)); V.append(vs); W.append(w); S.append(np.where(kk == 0, 1, -1))
        self.U = np.concatenate(U); self.V = np.concatenate(V); self.W = np.concatenate(W); self.S = np.concatenate(S)
        self._P = None

    def mask(self, t):
        m = np.ones(self.n, bool)
        if t == "h":
            m = (self.k % 2 == 0)
        elif t == "e":
            N = self.N
            m = ((self.k + ((self.A >> (N - 1)) & 1) + ((self.C >> (N - 1)) & 1)) % 2 == 0)
        m = m.copy(); m[0] = False
        return m

    def lines(self, m):
        keep = m[self.U] & m[self.V] & m[self.W]
        return self.U[keep], self.V[keep], self.W[keep], self.S[keep]

    def paulis(self):
        if self._P is None:
            D, n = self.D, self.n
            P = np.zeros((n, D, D), dtype=complex)
            xs = np.arange(D)
            for v in range(n):
                a, c = int(self.A[v]), int(self.C[v])
                P[v, xs ^ a, xs] = (1j ** int(self.k[v])) * np.where(POP[c & xs] & 1, -1, 1)
            self._P = P
        return self._P

    def op(self, f, m):
        ff = np.where(m, f, 0).astype(float)
        return np.einsum("v,vij->ij", ff, self.paulis())

    def expvals(self, psi):
        return np.real(np.einsum("i,vij,j->v", psi.conj(), self.paulis(), psi))

def viol(ln, f):
    U, V, W, S = ln
    return int(np.sum(f[U] * f[V] * f[W] != S))

def read_assignment(path, n):
    with open(path) as fh:
        head = fh.readline().split(); hexs = fh.readline().strip()
    f = np.ones(n, dtype=np.int64)
    bits = int(hexs, 16)
    for v in range(n):
        if (bits >> v) & 1:
            f[v] = -1
    return int(head[0]), head[1], int(head[2]), f

def bound(npts, L, n):
    beta = (n - 2) * npts ** 1.5 / (6.0 * math.sqrt(n - 1))
    b = int(math.floor(beta + 1e-9))
    # exact integer test: 36 (n-1) b^2 <= (n-2)^2 npts^3, b = L mod 2
    while b >= 0 and (((b - L) % 2) or 36 * (n - 1) * b * b > (n - 2) ** 2 * npts ** 3):
        b -= 1
    return beta, b, max(0, (L - b) // 2)

geos = {N: Geo(N) for N in (2, 3, 4, 5)}
rng = np.random.default_rng(20261109)

# ------------------------------------------------------------------ 1. witnesses
wit = {}
for fn in sorted(os.listdir(os.path.join(ROOT, "data", "witness"))):
    if not fn.endswith(".txt"):
        continue
    with open(os.path.join(ROOT, "data", "witness", fn)) as fh:
        N = int(fh.readline().split()[0])
    if N not in geos:
        continue
    g = geos[N]
    N, t, claimed, f = read_assignment(os.path.join(ROOT, "data", "witness", fn), g.n)
    m = g.mask(t); ln = g.lines(m)
    v = viol(ln, f)
    n_eff = g.D // 2 if t == "e" else g.D
    beta, b, dlow = bound(int(m.sum()), len(ln[0]), n_eff)
    check(f"witness {fn}: recount {v} == recorded {claimed}", v == claimed)
    check(f"witness {fn}: respects the bound (violated {v} >= {dlow})", v >= dlow)
    wit[fn] = dict(N=N, type=t, points=int(m.sum()), lines=len(ln[0]), violated=v, lower_bound=dlow, f=f, mask=m, ln=ln)
report["witnesses"] = {k: {kk: vv for kk, vv in w.items() if kk not in ("f", "mask", "ln")} for k, w in wit.items()}

# ------------------------------------------------------------------ 2. third-moment identity
ok = True; worst = 0.0
for N in (2, 3, 4):
    g = geos[N]
    for trial in range(6):
        m = g.mask("f") if trial < 2 else (rng.random(g.n) < 0.6)
        m = m.copy(); m[0] = False
        f = rng.choice([-1, 1], size=g.n)
        A = g.op(f, m); ln = g.lines(m)
        beta = len(ln[0]) - 2 * viol(ln, f)
        t1 = abs(np.trace(A)); t2 = abs(np.trace(A @ A) - g.D * m.sum()); t3 = abs(np.trace(A @ A @ A) - 6 * g.D * beta)
        worst = max(worst, t1, t2, t3)
        ok &= max(t1, t2, t3) < 1e-7
        # the bound itself
        w = np.linalg.eigvalsh(A)
        bnd = (g.D - 2) * m.sum() ** 1.5 / (6 * math.sqrt(g.D - 1))
        ok &= beta <= bnd + 1e-9
check("third-moment identities tr A = 0, tr A^2 = D|S|, tr A^3 = 6 D beta on random data", ok, f"max residual {worst:.2e}")

# ------------------------------------------------------------------ 3. spectra of the witness operators
spectra = {}
for fn, w in wit.items():
    g = geos[w["N"]]
    ev = np.linalg.eigvalsh(g.op(w["f"], w["mask"]))
    vals, counts = np.unique(np.round(ev, 6), return_counts=True)
    spectra[fn] = [[float(a), int(c)] for a, c in zip(vals, counts)]
report["spectra"] = spectra
def spec_is(fn, expected):
    got = sorted(spectra[fn]); exp = sorted([[round(a, 6), c] for a, c in expected])
    return len(got) == len(exp) and all(abs(a[0] - b[0]) < 1e-5 and a[1] == b[1] for a, b in zip(got, exp))
if "n3_f_hoggar_moonlab.txt" in spectra:
    check("N=3 full witness: spectrum of A is {21, -3 x7} (rank-one + scalar: a SIC fiducial)", spec_is("n3_f_hoggar_moonlab.txt", [(21, 1), (-3, 7)]), spectra["n3_f_hoggar_moonlab.txt"])
if "n4_h_hoggar_moonlab.txt" in spectra:
    check("N=4 hyperbolic witness: spectrum of A is {45, -3 x15}", spec_is("n4_h_hoggar_moonlab.txt", [(45, 1), (-3, 15)]), spectra["n4_h_hoggar_moonlab.txt"])
if "n4_f.txt" in spectra:
    r6 = math.sqrt(6)
    check("N=4 full witness (1575): spectrum of A is {21 + 16 sqrt6, 21 - 16 sqrt6, -3 x14}", spec_is("n4_f.txt", [(21 + 16 * r6, 1), (21 - 16 * r6, 1), (-3, 14)]), spectra["n4_f.txt"])

# ------------------------------------------------------------------ 4. Kramers degeneracy (elliptic quadrics)
ok = True
for N in (3, 4, 5):
    g = geos[N]; m = g.mask("e")
    for _ in range(3):
        f = rng.choice([-1, 1], size=g.n)
        ev = np.linalg.eigvalsh(g.op(f, m))
        ok &= np.allclose(ev[0::2], ev[1::2], atol=1e-8)
        ln = g.lines(m); beta = len(ln[0]) - 2 * viol(ln, f)
        n = g.D // 2
        ok &= beta <= (n - 2) * m.sum() ** 1.5 / (6 * math.sqrt(n - 1)) + 1e-9
check("elliptic quadrics: every eigenvalue of A is doubly degenerate (Kramers) and the D/2 bound holds", ok)
g3 = geos[3]
psiH = np.array([-1 + 2j, 1, 1, 1, 1, 1, 1, 1], dtype=complex); psiH /= np.linalg.norm(psiH)
evH = g3.expvals(psiH); fH = np.where(evH >= 0, 1, -1)
ell3 = g3.mask("e"); lnE = g3.lines(ell3)
evE = np.round(np.linalg.eigvalsh(g3.op(fH, ell3)), 6)
check("N=3 elliptic: Hoggar signs violate exactly 9 of 45 contexts (bound is tight)", viol(lnE, fH) == 9, viol(lnE, fH))
check("N=3 elliptic: spectrum {9 x2, -3 x6} (rank-two Kramers projector + scalar)", sorted(evE.tolist()) == [-3.0] * 6 + [9.0] * 2, evE.tolist())
hyp3 = g3.mask("h")
report["hoggar_restrictions"] = dict(full=viol(g3.lines(g3.mask("f")), fH), hyperbolic=viol(g3.lines(hyp3), fH), elliptic=viol(lnE, fH))

# ------------------------------------------------------------------ 5. pure-state cubic identity
ok = True; worst = 0.0
for N in (2, 3, 4, 5):
    g = geos[N]; ln = g.lines(g.mask("f"))
    for _ in range(4):
        psi = rng.normal(size=g.D) + 1j * rng.normal(size=g.D); psi /= np.linalg.norm(psi)
        p = g.expvals(psi)
        T = float(np.sum(ln[3] * p[ln[0]] * p[ln[1]] * p[ln[2]]))
        worst = max(worst, abs(T - (g.D - 1) * (g.D - 2) / 6))
ok = worst < 1e-9
check("pure states: sum over contexts of s p_u p_v p_w = (D-1)(D-2)/6", ok, f"max residual {worst:.2e}")

# ------------------------------------------------------------------ 6. geometry of the violated contexts
def incidence_stats(lines_list):
    adj = collections.defaultdict(set)
    for i, ln in enumerate(lines_list):
        for p in ln:
            adj[("p", p)].add(("l", i)); adj[("l", i)].add(("p", p))
    diam = 0; girth = 10 ** 9
    for src in adj:
        dist = {src: 0}; par = {src: None}; q = collections.deque([src])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1; par[y] = x; q.append(y)
                elif par[x] != y:
                    girth = min(girth, dist[x] + dist[y] + 1)
        diam = max(diam, max(dist.values()))
    return diam, girth

if "n3_f_hoggar_moonlab.txt" in wit:
    w = wit["n3_f_hoggar_moonlab.txt"]; f = w["f"]; U, V, W, S = w["ln"]
    bad = f[U] * f[V] * f[W] != S
    VL = list(zip(U[bad].tolist(), V[bad].tolist(), W[bad].tolist()))
    deg = collections.Counter(p for ln in VL for p in ln)
    diam, girth = incidence_stats(VL)
    check("N=3: 63 violated contexts through 63 points, 3 per point", len(VL) == 63 and len(deg) == 63 and set(deg.values()) == {3})
    check("N=3: incidence graph has diameter 6 and girth 12 (generalized hexagon of order (2,2))", diam == 6 and girth == 12, (diam, girth))
    # classical embedding: the three violated lines through each point lie in one totally isotropic plane
    g = geos[3]; coplanar = True
    def commute(u, v):
        return ((POP[g.A[u] & g.C[v]] + POP[g.C[u] & g.A[v]]) & 1) == 0
    for p in range(1, 64):
        pts = set(x for ln in VL if p in ln for x in ln)
        coplanar &= len(pts) == 7 and all(commute(a, b) for a in pts for b in pts) and all((a ^ b) in pts or a == b for a in pts for b in pts)
    check("N=3: the three violated lines through every point span a totally isotropic plane (classically embedded split Cayley hexagon)", coplanar)
    report["n3_hexagon"] = dict(lines=len(VL), diameter=diam, girth=girth, coplanar=bool(coplanar))

if "n4_h_hoggar_moonlab.txt" in wit:
    w = wit["n4_h_hoggar_moonlab.txt"]; f = w["f"]; U, V, W, S = w["ln"]
    bad = f[U] * f[V] * f[W] != S
    VL = list(zip(U[bad].tolist(), V[bad].tolist(), W[bad].tolist()))
    deg = collections.Counter(p for ln in VL for p in ln)
    # collinearity graph and its distance distribution
    nb = collections.defaultdict(set)
    for a, b, c in VL:
        nb[a] |= {b, c}; nb[b] |= {a, c}; nb[c] |= {a, b}
    dists = set()
    arrays = set()
    for src in nb:
        dist = {src: 0}; q = collections.deque([src])
        while q:
            x = q.popleft()
            for y in nb[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1; q.append(y)
        cnt = collections.Counter(dist.values()); dists.add(tuple(cnt[i] for i in range(max(cnt) + 1)))
        # intersection numbers b_i, c_i from src
        for x, dx in dist.items():
            bi = sum(1 for y in nb[x] if dist[y] == dx + 1); ci = sum(1 for y in nb[x] if dist[y] == dx - 1)
            arrays.add((dx, bi, ci))
    arr = sorted(arrays)
    check("N=4 hyperbolic: 315 violated contexts, 7 through each of the 135 points", len(VL) == 315 and len(deg) == 135 and set(deg.values()) == {7})
    check("N=4 hyperbolic: collinearity graph is distance-regular with distribution (1,14,56,64) and array {14,12,8;1,3,7} (dual polar space DW(5,2))",
          dists == {(1, 14, 56, 64)} and arr == [(0, 14, 0), (1, 12, 1), (2, 8, 3), (3, 0, 7)], (sorted(dists), arr))
    report["n4_hyperbolic_violated"] = dict(lines=len(VL), distance_distribution=sorted(dists), intersection=arr)

if "n4_f.txt" in wit:
    w = wit["n4_f.txt"]; f = w["f"]; U, V, W, S = w["ln"]
    bad = f[U] * f[V] * f[W] != S
    deg = collections.Counter(np.concatenate([U[bad], V[bad], W[bad]]).tolist())
    hist = collections.Counter(deg.values())
    check("N=4 full (1575): violated-lines-per-point pattern {7:30, 19:105, 21:120}", dict(hist) == {7: 30, 19: 105, 21: 120}, dict(hist))
    # the 135 points of degree 7 or 19 form a hyperbolic quadric
    g = geos[4]
    low = np.array([deg[v] in (7, 19) for v in range(g.n)]); low[0] = False
    found = None
    for a in range(g.n):
        # quadric q_a(v) = q0(v) + <a, v>
        q = (g.k + POP[g.A[a] & g.C] + POP[g.C[a] & g.A]) & 1
        mq = (q == 0); mq[0] = False
        if np.array_equal(mq, low):
            found = a
    check("N=4 full (1575): the 135 points of degree 7 or 19 are exactly one hyperbolic quadric", found is not None, found)
    if found is not None:
        lnq = g.lines(low)
        report["n4_full_structure"] = dict(degree_pattern=dict(hist), quadric_index=int(found), violated_inside_quadric=viol(lnq, f), violated_outside=w["violated"] - viol(lnq, f))
        check("N=4 full (1575): 315 violated contexts inside that quadric + 1260 mixed ones", viol(lnq, f) == 315)

if "n4_e.txt" in wit:
    w = wit["n4_e.txt"]; f = w["f"]; U, V, W, S = w["ln"]
    bad = f[U] * f[V] * f[W] != S
    deg = collections.Counter(np.concatenate([U[bad], V[bad], W[bad]]).tolist())
    hist = dict(collections.Counter(deg.values()))
    report["n4_elliptic_degree_pattern"] = hist
    check("N=4 elliptic (315): violated-lines-per-point pattern {3:14, 7:21, 9:84}", hist == {3: 14, 7: 21, 9: 84}, hist)

# ------------------------------------------------------------------ 6b. orbits of the optimal violated sets
def orbit_size(g, VL, generators):
    """size of the orbit of a set of lines under transvections v -> v + <a,v> a"""
    A, C = g.A, g.C
    def tv(a):
        s = (POP[A[a] & C] + POP[C[a] & A]) & 1
        return np.where(s == 1, np.arange(g.n) ^ a, np.arange(g.n))
    maps = [tv(a) for a in generators]
    start = frozenset(tuple(sorted(ln)) for ln in VL)
    seen = {start}; frontier = [start]
    while frontier:
        nxt = []
        for S_ in frontier:
            for mp in maps:
                img = frozenset(tuple(sorted((int(mp[a]), int(mp[b]), int(mp[c])))) for a, b, c in S_)
                if img not in seen:
                    seen.add(img); nxt.append(img)
        frontier = nxt
    return len(seen)

def gf2_rank(rows):
    rows = list(rows); rank = 0
    while rows:
        piv = rows.pop()
        if piv == 0:
            continue
        rank += 1
        low = piv & -piv
        rows = [r ^ piv if r & low else r for r in rows]
    return rank

if "n3_f_hoggar_moonlab.txt" in wit:
    g = geos[3]; w = wit["n3_f_hoggar_moonlab.txt"]; f = w["f"]; U, V, W, S = w["ln"]
    bad = f[U] * f[V] * f[W] != S
    VL = list(zip(U[bad].tolist(), V[bad].tolist(), W[bad].tolist()))
    orb = orbit_size(g, VL, range(1, g.n))
    rk = gf2_rank([(1 << int(a)) | (1 << int(b)) | (1 << int(c)) for a, b, c in zip(U, V, W)])
    check("N=3: the optimal violated set has exactly 120 images under Sp(6,2) (the 120 classically embedded hexagons)", orb == 120, orb)
    check("N=3: the context-point incidence matrix has rank 56 over GF(2), so each violated set comes from 2^7 = 128 assignments", rk == 56, rk)
    report["n3_optimal_family"] = dict(violated_sets=orb, assignments_per_set=2 ** (63 - rk), assignments=orb * 2 ** (63 - rk))
    check("N=3: 120 * 128 = 15360 = 240 * 64 optimal assignments (240 Hoggar-type SICs of 64 vectors each)", orb * 2 ** (63 - rk) == 15360)

if "n4_h_hoggar_moonlab.txt" in wit:
    g = geos[4]; w = wit["n4_h_hoggar_moonlab.txt"]; f = w["f"]; U, V, W, S = w["ln"]
    bad = f[U] * f[V] * f[W] != S
    VL = list(zip(U[bad].tolist(), V[bad].tolist(), W[bad].tolist()))
    refl = [a for a in range(1, g.n) if g.k[a] % 2 == 1]          # reflections preserving the real quadric
    orb = orbit_size(g, VL, refl)
    pts = np.nonzero(w["mask"])[0]; idx = {int(p): i for i, p in enumerate(pts)}
    rk = gf2_rank([(1 << idx[int(a)]) | (1 << idx[int(b)]) | (1 << idx[int(c)]) for a, b, c in zip(U, V, W)])
    check("N=4 hyperbolic: the optimal violated set has exactly 240 images under the reflections of O+(8,2)", orb == 240, orb)
    report["n4_hyperbolic_optimal_family"] = dict(violated_sets=orb, incidence_rank=rk, assignments_per_set=2 ** (135 - rk))

# ------------------------------------------------------------------ 7. table
known = {  # (N, type): (exact or None, best upper bound, previously best lower bound)
    (2, "f"): (3, 3, 3), (2, "h"): (1, 1, 1),
    (3, "f"): (63, 63, 63), (3, "h"): (21, 21, 21), (3, "e"): (9, 9, 9),
    (4, "f"): (None, 1575, 1071), (4, "h"): (315, 315, 315), (4, "e"): (None, 315, 215),
    (5, "f"): (None, 31479, 17391), (5, "h"): (None, 6975, 4743), (5, "e"): (None, 7087, 3927),
    (6, "f"): (None, 553140, 279279), (6, "h"): (None, 132391, 73043), (6, "e"): (None, 131700, 66495),
    (7, "f"): (None, 9406024, 4472559), (7, "h"): (None, 2331191, 1144143), (7, "e"): (None, 2294580, 1091727),
}
table = []
def counts(N, t):
    D = 2 ** N
    if t == "f":
        pts = D * D - 1; L = (D * D - 1) * (D * D - 4) // 12
    elif t == "h":
        pts = (D - 1) * (D + 2) // 2; L = (D - 1) * (D + 2) * (D - 2) * (D + 4) // 48
    else:
        pts = (D + 1) * (D - 2) // 2; L = (D + 1) * (D - 2) * (D + 2) * (D - 4) // 48
    return pts, L
for N in range(2, 11):
    for t in "fhe":
        pts, L = counts(N, t)
        if L == 0:
            continue
        D = 2 ** N; n = D // 2 if t == "e" else D
        beta, b, dlow = bound(pts, L, n)
        ex, ub, oldlb = known.get((N, t), (None, None, None))
        # doily bound L/5 as the previously known general lower bound
        table.append(dict(N=N, type=t, points=pts, lines=L, beta_bound=beta, beta_bound_int=b, lower=dlow,
                          frac_lower=dlow / L, exact=ex, upper=ub, old_lower=oldlb if oldlb is not None else -(-L // 5)))
report["table"] = table
# cross-check the closed-form counts against the enumerated geometry
ok = True
for N in (2, 3, 4, 5):
    g = geos[N]
    for t in "fhe":
        m = g.mask(t); pts, L = counts(N, t)
        ok &= int(m.sum()) == pts and len(g.lines(m)[0]) == L
check("closed-form point and line counts agree with enumeration for N = 2..5", ok)
tf = os.path.join(RES, "table.txt")
if os.path.exists(tf):
    ok = True
    for line in open(tf):
        if line.startswith("#"):
            continue
        s = line.split(); N, t = int(s[0]), s[1]
        row = next((r for r in table if r["N"] == N and r["type"] == t), None)
        if row is None:
            continue
        ok &= row["points"] == int(s[2]) and row["lines"] == int(s[3]) and row["beta_bound_int"] == int(s[6]) and row["lower"] == int(s[7])
    check("bound table from the C engine (exact 128-bit integer arithmetic) agrees with Python", ok)
for r in table:
    if r["exact"] is not None:
        check(f"N={r['N']} {r['type']}: bound {r['lower']} <= exact degree {r['exact']}", r["lower"] <= r["exact"])
    if r["upper"] is not None:
        check(f"N={r['N']} {r['type']}: bound {r['lower']} <= best known assignment {r['upper']}", r["lower"] <= r["upper"])

# ------------------------------------------------------------------ figures
try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    ink, grid, accent, warm, cool = "#1b1f27", "#c9ced6", "#0f9d7a", "#c8553d", "#3a6ea5"
    plt.rcParams.update({"font.size": 10, "axes.edgecolor": ink, "axes.labelcolor": ink, "xtick.color": ink, "ytick.color": ink,
                         "axes.spines.top": False, "axes.spines.right": False, "figure.dpi": 150, "savefig.bbox": "tight"})
    # Figure 1: violated fraction, full space
    fig, ax = plt.subplots(figsize=(6.4, 3.8))
    Ns = np.arange(2, 11)
    D = 2.0 ** Ns
    ax.plot(Ns, 0.5 - np.sqrt(D + 1) / (D + 2), color=accent, lw=2, marker="o", ms=4, label="proved here: 1/2 − √(D+1)/(D+2)")
    ax.axhline(0.2, color=cool, lw=1.3, ls="--", label="previous lower bound: 1/5")
    ub = [(r["N"], r["upper"] / r["lines"]) for r in table if r["type"] == "f" and r["upper"] is not None]
    ax.plot([u[0] for u in ub], [u[1] for u in ub], color=warm, lw=0, marker="v", ms=6, label="best assignments known (upper bounds)")
    ax.axhline(0.5, color=grid, lw=1)
    ax.text(10.05, 0.5, "random guessing", va="center", ha="left", fontsize=8, color="#5b6370")
    ax.set_xlabel("number of qubits N"); ax.set_ylabel("fraction of contexts violated")
    ax.set_ylim(0, 0.55); ax.set_xlim(1.8, 10.2); ax.grid(color=grid, lw=0.5, alpha=0.6)
    ax.legend(frameon=False, loc="lower right", fontsize=8)
    ax.set_title("Every noncontextual assignment violates at least this fraction\nof the commuting triples of N-qubit Pauli observables", fontsize=10, loc="left")
    fig.savefig(os.path.join(FIG, "fig1_fraction.png")); plt.close(fig)

    # Figure 2: Moonlab noise sweep
    mj = os.path.join(RES, "moonlab_experiment.json")
    if os.path.exists(mj):
        E4 = json.load(open(mj))["experiments"]["E4"]
        fig, axes = plt.subplots(1, 3, figsize=(9.6, 3.1), sharey=True)
        for ax, N in zip(axes, (2, 3, 4)):
            rows = [r for r in E4 if r["N"] == N]
            x = [r["noise_per_qubit_per_measurement"] for r in rows]; y = [r["quantum_success"] for r in rows]
            err = [math.sqrt(max(r["quantum_success"] * (1 - r["quantum_success"]), 1e-9) / r["shots"]) for r in rows]
            ax.errorbar(x, y, yerr=err, color=accent, marker="o", ms=4, lw=1.5, capsize=2, label="simulated quantum device")
            ax.axhline(rows[0]["ceiling_proven"], color=warm, lw=1.5, label="proved classical ceiling")
            if abs(rows[0]["ceiling_best_known"] - rows[0]["ceiling_proven"]) > 1e-9:
                ax.axhline(rows[0]["ceiling_best_known"], color=cool, lw=1.2, ls="--", label="best classical model known")
            ax.set_title(f"N = {N}", fontsize=10, loc="left"); ax.set_xlabel("Pauli error probability per qubit")
            ax.grid(color=grid, lw=0.5, alpha=0.6); ax.set_ylim(0.5, 1.02)
        axes[0].set_ylabel("fraction of contexts satisfied"); axes[2].legend(frameon=False, fontsize=7, loc="upper right")
        fig.savefig(os.path.join(FIG, "fig2_noise.png")); plt.close(fig)

    # Figure 3: spectra of the extremal operators
    fig, ax = plt.subplots(figsize=(6.4, 2.9))
    rows = [("W(5,2): 63", "n3_f_hoggar_moonlab.txt"), ("Q+(7,2): 315", "n4_h_hoggar_moonlab.txt"), ("W(7,2): 1575", "n4_f.txt"), ("Q-(7,2): 315", "n4_e.txt")]
    yy = 0; ticks = []
    for label, fn in rows:
        if fn not in spectra:
            continue
        for val, mult in spectra[fn]:
            ax.scatter([val], [yy], s=22 + 14 * mult, color=accent if mult == 1 else ink, zorder=3)
            ax.annotate(f"×{mult}", (val, yy), textcoords="offset points", xytext=(0, 9), ha="center", fontsize=7, color="#5b6370")
        ticks.append((yy, label)); yy += 1
    ax.set_yticks([t[0] for t in ticks]); ax.set_yticklabels([t[1] for t in ticks]); ax.set_ylim(-0.6, yy - 0.3)
    ax.axvline(0, color=grid, lw=0.8); ax.grid(axis="x", color=grid, lw=0.5, alpha=0.6); ax.set_xlabel("eigenvalues of A = Σ f(v) P_v for the best assignments")
    fig.savefig(os.path.join(FIG, "fig3_spectra.png")); plt.close(fig)
    report["figures"] = sorted(os.listdir(FIG))
except Exception as exc:  # figures are optional
    print("figure generation skipped:", exc)

report["failures"] = failures
json.dump(report, open(os.path.join(RES, "analysis.json"), "w"), indent=1, default=lambda o: int(o) if isinstance(o, np.integer) else str(o))
print(("ANALYSIS-PASS" if not failures else "ANALYSIS-FAIL: " + "; ".join(failures)))
sys.exit(1 if failures else 0)

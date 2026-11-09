#!/usr/bin/env python3
"""
ladder.py - the averaging ("ladder") inequalities between the three families, verified by
direct enumeration.

  (a) N = 4: there are 136 hyperbolic and 120 elliptic quadrics q_a(v) = q_0(v) + <a,v>;
      every context of W(7,2) lies on exactly 24 elliptic quadrics; on each elliptic quadric the
      operator A_f has a doubly degenerate spectrum.  Hence
          d(W(7,2)) >= ceil(120 * 291 / 24) = 1455.
  (b) N = 5: the real quadric Q+(9,2) contains 496 sub-configurations S_J (observables commuting
      with an imaginary Pauli J), each with 255 points and 5355 contexts; every context of
      Q+(9,2) lies in exactly 112 of them; on each S_J the operator A_f is doubly degenerate.
      Hence d(Q+(9,2)) >= ceil(496 * d(W(7,2)) / 112) >= 6444.
  (c) N = 5: every context of W(9,2) lies on exactly 112 of the 496 elliptic quadrics, hence
          d(W(9,2)) >= ceil(496 * 6501 / 112) = 28791.
"""
import json, math, os, sys
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
POP = np.array([bin(i).count("1") for i in range(1 << 12)], dtype=np.int64)
failures = []
def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name + (" :: " + str(detail) if detail != "" else ""))
    if not cond:
        failures.append(name)

def geometry(N):
    D = 1 << N; n = 1 << (2 * N)
    v = np.arange(n); A = v & (D - 1); C = v >> N; k = POP[A & C]
    U, V, W, S = [], [], [], []
    for u in range(1, n):
        vs = np.arange(u + 1, n); w = vs ^ u
        ok = (w > vs) & (((POP[A[u] & C[vs]] + POP[C[u] & A[vs]]) & 1) == 0)
        vs = vs[ok]; w = w[ok]
        kk = (POP[A[u] & C[u]] + POP[A[vs] & C[vs]] + 2 * POP[C[u] & A[vs]] + 3 * POP[(A[u] ^ A[vs]) & (C[u] ^ C[vs])]) & 3
        U.append(np.full(len(vs), u)); V.append(vs); W.append(w); S.append(np.where(kk == 0, 1, -1))
    return dict(N=N, D=D, n=n, A=A, C=C, k=k, U=np.concatenate(U), V=np.concatenate(V), W=np.concatenate(W), S=np.concatenate(S))

def symp_with(g, a):
    return (POP[g["A"][a] & g["C"]] + POP[g["C"][a] & g["A"]]) & 1

def operator(g, f, mask):
    """A = sum_{v in mask} f_v P_v as a dense matrix, built column by column."""
    D, n = g["D"], g["n"]
    M = np.zeros((D, D), dtype=complex)
    xs = np.arange(D)
    for v in np.nonzero(mask)[0]:
        a, c = int(g["A"][v]), int(g["C"][v])
        M[xs ^ a, xs] += f[v] * (1j ** int(g["k"][v])) * np.where(POP[c & xs] & 1, -1, 1)
    return M

def bound_int(npts, L, n):
    b = int(math.floor((n - 2) * npts ** 1.5 / (6.0 * math.sqrt(n - 1)) + 1e-9))
    while b >= 0 and (((b - L) % 2) or 36 * (n - 1) * b * b > (n - 2) ** 2 * npts ** 3):
        b -= 1
    return (L - b) // 2

rng = np.random.default_rng(4)
out = {}

# ---------------------------------------------------------------- (a) four qubits
g = geometry(4); n = g["n"]; L = len(g["U"])
q0 = g["k"] & 1
ell, hyp = [], []
for a in range(n):
    (ell if q0[a] else hyp).append(a)
check("N=4: 136 hyperbolic and 120 elliptic quadrics", len(hyp) == 136 and len(ell) == 120)
cover = np.zeros(L, dtype=int); pts_ok = True; lines_ok = True; kramers_ok = True; dmin = None
for a in ell:
    m = ((q0 + symp_with(g, a)) & 1) == 0; m[0] = False
    on = m[g["U"]] & m[g["V"]] & m[g["W"]]
    cover += on
    pts_ok &= int(m.sum()) == 119; lines_ok &= int(on.sum()) == 1071
    f = rng.choice([-1, 1], size=n)
    ev = np.linalg.eigvalsh(operator(g, f, m))
    kramers_ok &= bool(np.allclose(ev[0::2], ev[1::2], atol=1e-8))
check("N=4: every elliptic quadric has 119 points and 1071 contexts", pts_ok and lines_ok)
check("N=4: every context of W(7,2) lies on exactly 24 elliptic quadrics", bool(np.all(cover == 24)), (int(cover.min()), int(cover.max())))
check("N=4: on every one of the 120 elliptic quadrics the spectrum of A_f is doubly degenerate", kramers_ok)
d_ell4 = bound_int(119, 1071, 8)
d_full4_direct = bound_int(255, 5355, 16)
d_full4_avg = -(-120 * d_ell4 // 24)
check("N=4: d(Q-(7,2)) >= 291 and d(W(7,2)) >= max(1451, ceil(120*291/24)) = 1455", d_ell4 == 291 and d_full4_direct == 1451 and d_full4_avg == 1455, (d_ell4, d_full4_direct, d_full4_avg))
out["N4"] = dict(elliptic_quadrics=len(ell), hyperbolic_quadrics=len(hyp), contexts_per_elliptic=1071, elliptic_per_context=24,
                 d_elliptic_lower=d_ell4, d_full_direct=d_full4_direct, d_full_averaged=d_full4_avg)
# hyperbolic quadrics: every context on exactly 40 of them (reproduces the 1071 bound from 315)
cover = np.zeros(L, dtype=int)
for a in hyp:
    m = ((q0 + symp_with(g, a)) & 1) == 0; m[0] = False
    cover += m[g["U"]] & m[g["V"]] & m[g["W"]]
check("N=4: every context of W(7,2) lies on exactly 40 hyperbolic quadrics", bool(np.all(cover == 40)))

# ---------------------------------------------------------------- (b), (c) five qubits
g = geometry(5); n = g["n"]; L = len(g["U"])
q0 = g["k"] & 1
real = (q0 == 0); real[0] = False
onQ = real[g["U"]] & real[g["V"]] & real[g["W"]]
check("N=5: the real quadric has 527 points and 23715 contexts", int(real.sum()) == 527 and int(onQ.sum()) == 23715)
Js = [a for a in range(1, n) if q0[a] == 1]
check("N=5: 496 imaginary (non-singular) observables J", len(Js) == 496)
cover = np.zeros(L, dtype=int); ok_counts = True; deg_ok = True
for idx, J in enumerate(Js):
    m = real & (symp_with(g, J) == 0)
    on = m[g["U"]] & m[g["V"]] & m[g["W"]]
    cover += on
    ok_counts &= int(m.sum()) == 255 and int(on.sum()) == 5355
    if idx % 31 == 0:      # spectral check on a sample of 16 sub-configurations
        f = rng.choice([-1, 1], size=n)
        ev = np.linalg.eigvalsh(operator(g, f, m))
        deg_ok &= bool(np.allclose(ev[0::2], ev[1::2], atol=1e-8))
check("N=5: every S_J has 255 points and 5355 contexts (a copy of the four-qubit space)", ok_counts)
check("N=5: every context of Q+(9,2) lies in exactly 112 of the 496 S_J", bool(np.all(cover[onQ] == 112)), (int(cover[onQ].min()), int(cover[onQ].max())))
check("N=5: on the sampled S_J the spectrum of A_f is doubly degenerate (complex structure J)", deg_ok)
d_hyp5_direct = bound_int(527, 23715, 32)
d_hyp5_avg = -(-496 * d_full4_avg // 112)
check("N=5: d(Q+(9,2)) >= max(6426, ceil(496*1455/112)) = 6444", d_hyp5_direct == 6426 and d_hyp5_avg == 6444, (d_hyp5_direct, d_hyp5_avg))
ells5 = [a for a in range(n) if q0[a] == 1]
cover = np.zeros(L, dtype=int); ok5 = True
for a in ells5:
    m = ((q0 + symp_with(g, a)) & 1) == 0; m[0] = False
    on = m[g["U"]] & m[g["V"]] & m[g["W"]]
    cover += on; ok5 &= int(m.sum()) == 495 and int(on.sum()) == 19635
check("N=5: 496 elliptic quadrics, each with 495 points and 19635 contexts; every context of W(9,2) on exactly 112", len(ells5) == 496 and ok5 and bool(np.all(cover == 112)))
d_ell5 = bound_int(495, 19635, 16)
d_full5_direct = bound_int(1023, 86955, 32)
d_full5_avg = -(-496 * d_ell5 // 112)
check("N=5: d(Q-(9,2)) >= 6501 and d(W(9,2)) >= max(28786, ceil(496*6501/112)) = 28791", d_ell5 == 6501 and d_full5_direct == 28786 and d_full5_avg == 28791, (d_ell5, d_full5_direct, d_full5_avg))
out["N5"] = dict(sub_spaces=len(Js), sub_spaces_per_context=112, d_hyperbolic_direct=d_hyp5_direct, d_hyperbolic_averaged=d_hyp5_avg,
                 elliptic_quadrics=len(ells5), d_elliptic_lower=d_ell5, d_full_direct=d_full5_direct, d_full_averaged=d_full5_avg)
out["failures"] = failures
json.dump(out, open(os.path.join(ROOT, "results", "ladder.json"), "w"), indent=1)
print("LADDER-PASS" if not failures else "LADDER-FAIL")
sys.exit(1 if failures else 0)

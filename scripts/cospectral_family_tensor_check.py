#!/usr/bin/env python3
"""
cospectral_family_tensor_check.py - a second route to the carriers of publication/ADDENDUM-c3-all-qubits.md.

Its only input from scripts/cospectral_family.py is the pair of sign tables (lists of negative section labels)
in results/cospectral_family.json.  It rebuilds everything else differently, and at the end compares its own
counts and traces with the numbers recorded in that file:

  * every Pauli observable is a Kronecker product of the literal 2 x 2 matrices I, X, Y, Z;
  * "real", "commutes" and the sign of a context are read off matrix entries and matrix products, with no
    symplectic form and no phase formula;
  * the carrier operators are compared through their power sums tr A^k, k = 1 .. 2^N, in Python integers
    (equal power sums for all k up to the size are equivalent to equal characteristic polynomials);
  * the completion matrices are filled from the contexts found by matrix multiplication;
  * the points where the two tables differ are compared, as words, with the points Z (x) W (x) X named in the
    theorem, which also pins the label convention (label a + 2^N c, bit 0 = rightmost letter).

  python scripts/cospectral_family_tensor_check.py          (N = 3, 4 and 5; a few seconds)
"""
import itertools, json, os, sys
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
I2 = np.array([[1, 0], [0, 1]], dtype=complex)
X2 = np.array([[0, 1], [1, 0]], dtype=complex)
Y2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z2 = np.array([[1, 0], [0, -1]], dtype=complex)
LETTER = {"I": I2, "X": X2, "Y": Y2, "Z": Z2}
CODE = {"I": (0, 0), "X": (1, 0), "Z": (0, 1), "Y": (1, 1)}
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print("%s  %s%s" % ("PASS" if ok else "FAIL", name, ("   [" + detail + "]") if detail else ""))


def run(N, rec):
    D = 1 << N
    words = ["".join(w) for w in itertools.product("IXZY", repeat=N)][1:]

    def mat(w):
        M = np.array([[1]], dtype=complex)
        for ch in w:
            M = np.kron(M, LETTER[ch])
        return M

    def label(w):                                    # the repository's label a + 2^N c, bit 0 = rightmost letter
        a = c = 0
        for k, ch in enumerate(reversed(w)):
            a |= CODE[ch][0] << k
            c |= CODE[ch][1] << k
        return a + (c << N)

    real = {}
    for w in words:
        M = mat(w)
        if not np.any(M.imag):
            real[w] = np.rint(M.real).astype(np.int64)
    dword = "Z" + "I" * (N - 1)
    Pd = real[dword]
    sec = [w for w in real if np.array_equal(real[w] @ Pd, Pd @ real[w])]
    outs = [w for w in real if w not in set(sec)]
    n = D // 2
    check("N = %d: %d real words, %d = 1 + (n-1)(n+2) commute with %s, %d = n^2 do not; as recorded"
          % (N, len(real), len(sec), dword, len(outs)),
          len(real) == rec["section"] + rec["outside"] and len(sec) == rec["section"] and len(outs) == rec["outside"]
          and len(sec) == 1 + (n - 1) * (n + 2) and len(outs) == n * n)
    lab = {w: label(w) for w in real}
    opos = {w: i for i, w in enumerate(outs)}
    by_matrix = {}
    for w in outs:
        by_matrix[real[w].tobytes()] = (w, 1)
        by_matrix[(-real[w]).tobytes()] = (w, -1)
    # contexts with one section point: s and p commute, and P_s P_p = +- P_q for an outside q
    ctx = []
    for s in sec:
        if s == dword:
            continue
        Ps = real[s]
        for p in outs:
            Pp = real[p]
            prod = Ps @ Pp
            if not np.array_equal(prod, Pp @ Ps):
                continue
            q, sg = by_matrix[prod.tobytes()]
            if opos[p] < opos[q]:
                ctx.append((s, p, q, sg))            # P_s P_p P_q = sg I
    check("N = %d: %d contexts with one section point, found by matrix products" % (N, len(ctx)),
          len(ctx) == rec["outside_contexts"])
    res, sigs, fits = {}, {}, True
    for name in ("A", "B"):
        neg = set(rec["negative_section_labels"][name])
        sig = {w: (-1 if lab[w] in neg else 1) for w in sec}
        fits = fits and sum(1 for v in sig.values() if v < 0) == len(neg) and sig[dword] == 1
        sigs[name] = sig
        A = np.zeros((D, D), dtype=object)
        for w in sec:
            A = A + sig[w] * real[w].astype(object)
        powers, M = [], np.eye(D, dtype=object)
        for _ in range(D):
            M = M.dot(A)
            powers.append(int(np.trace(M)))
        Lam = np.zeros((len(outs), len(outs)), dtype=np.int64)
        for s, p, q, sg in ctx:
            Lam[opos[p], opos[q]] += sg * sig[s]
            Lam[opos[q], opos[p]] += sg * sig[s]
        L2 = Lam @ Lam
        res[name] = (powers, int(np.trace(L2)), int((L2 * Lam).sum()))
    differ = sorted(w for w in sec if sigs["A"][w] != sigs["B"][w])
    check("N = %d: every recorded negative label is a section observable, for both tables, and both have +1 at %s"
          % (N, dword), fits)
    if N >= 4:
        expect = sorted("Z" + "".join(v) + "X" for v in itertools.product("IZ", repeat=N - 2))
        check("N = %d: the two tables differ exactly at the %d words Z (x) W (x) X, W a word in I and Z" % (N, len(expect)),
              differ == expect, " ".join(differ[:4]) + (" ..." if len(differ) > 4 else ""))
    else:
        check("N = %d: the two tables differ at %d points, all of the form Z (x) P" % (N, len(differ)),
              len(differ) == 6 and all(w[0] == "Z" for w in differ), " ".join(differ))
    edges = 2 * len(differ) // n                       # |F|: every moved edge accounts for n/2 points
    check("N = %d: tr A^k agrees for the two carriers for every k = 1 .. %d (so the characteristic polynomials agree)" % (N, D),
          res["A"][0] == res["B"][0], "tr A^3 = %d" % res["A"][0][2])
    check("N = %d: tr Lambda^2 = %d for both; tr Lambda^3 = %d and %d, as recorded; the difference is -(3/2) n^3 |F| = %d"
          % (N, res["A"][1], res["A"][2], res["B"][2], -3 * n ** 3 * edges // 2),
          res["A"][1] == res["B"][1] == rec["completion_trace_square"]
          and res["A"][2] == rec["completion_trace_cube"]["A"] and res["B"][2] == rec["completion_trace_cube"]["B"]
          and res["A"][2] != res["B"][2] and res["A"][2] - res["B"][2] == -3 * n ** 3 * edges // 2)


def main():
    data = json.load(open(os.path.join(ROOT, "results", "cospectral_family.json"), encoding="utf-8"))
    for N in (3, 4, 5):
        run(N, data[str(N)])
    npass = sum(1 for _, ok in CHECKS if ok)
    print("\n%d of %d checks passed" % (npass, len(CHECKS)))
    sys.exit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

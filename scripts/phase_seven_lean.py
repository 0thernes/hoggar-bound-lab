#!/usr/bin/env python3
"""
phase_seven_lean.py - the seven-qubit counts, by the evaluation that the Lean kernel carries out.

The configuration is the Pauli support of the seven-qubit phase state Phi7 (8128 observables, mask and
optimal sign pattern in data/flat/n7_phase7.txt and lean/HoggarBound/PhaseData.lean).  Its number of flags
and the number of flags violated by the sign pattern are double sums over the 4^7 codes, 2^28 terms each.

lean/HoggarBound/MaskRows.lean evaluates one row of such a sum with a bounded number of operations on
large natural numbers ("packed sets": one digit of b bits per code, the digit being 0 or 1), and proves
for every number of qubits that the result is the row of the double sum.  This script

  * carries out the same evaluation in Python (same functions, same names);
  * compares it with the direct double loop over the definitions of lean/HoggarBound/MaskConfig.lean
    on random small configurations, on the five-qubit phase state (whose 32 block totals the kernel has
    checked by the direct double sum) and on sampled rows of the seven-qubit configuration;
  * computes the 16 block totals of the seven-qubit sums and the totals 16945152 and 4376064;
  * shows by two negative controls that the totals react to a change of one bit of the data;
  * writes (--write) or compares (default) lean/HoggarBound/SaturatedPhaseSeven.lean, in which the
    kernel evaluates the same 16 blocks.

The Lean file does not depend on this script: every number in it is evaluated by the kernel.

  python scripts/phase_seven_lean.py [--write]
"""
import json
import os
import random
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHECKS = []


def check(name, ok):
    CHECKS.append((name, bool(ok)))
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name))


def tb(x, i):
    return (x >> i) & 1


# ------------------------------------------------------------ the definitions of MaskConfig.lean
def common(z, i, w, j, n):
    """Number of k < n for which bit i + k of z and bit j + k of w are both set."""
    return bin((z >> i) & (w >> j) & ((1 << n) - 1)).count("1")


def commB(N, z, w):
    return (common(z, N, w, 0, N) + common(w, N, z, 0, N)) % 2 == 0


def flagB(N, mask, z, w):
    return bool(tb(mask, z) and tb(mask, w) and tb(mask, z ^ w) and commB(N, z, w))


def sInt(neg, z):
    return -1 if tb(neg, z) else 1


def iPowRe(k):
    return 1 if k % 4 == 0 else (-1 if k % 4 == 2 else 0)


def lineSignCode(N, z, w):
    return iPowRe(common(z, 0, z, N, N) + common(w, 0, w, N, N) + 3 * common(z ^ w, 0, z ^ w, N, N)) \
        * (1 if common(z, N, w, 0, N) % 2 == 0 else -1)


def violB(N, mask, neg, z, w):
    return flagB(N, mask, z, w) and sInt(neg, z) * sInt(neg, w) * sInt(neg, z ^ w) != lineSignCode(N, z, w)


def flagRow(N, mask, z):
    return sum(1 for w in range(4 ** N) if flagB(N, mask, z, w))


def violRow(N, mask, neg, z):
    return sum(1 for w in range(4 ** N) if violB(N, mask, neg, z, w))


# ------------------------------------------------------------ the evaluation of MaskRows.lean
def pack(b, p, k, lo):
    if k == 0:
        return 1 if p(lo) else 0
    return pack(b, p, k - 1, lo) | (pack(b, p, k - 1, lo + 2 ** (k - 1)) << (b * 2 ** (k - 1)))


def ones(b, k):
    if k == 0:
        return 1
    x = ones(b, k - 1)
    return x | (x << (b * 2 ** (k - 1)))


def stripe(b, j, k):
    if k == 0:
        return 0
    k -= 1
    if k < j:
        return 0
    if k == j:
        return ones(b, k) << (b * 2 ** k)
    x = stripe(b, j, k)
    return x | (x << (b * 2 ** k))


def swapBlocks(b, k, L, A):
    return ((A & L) << (b * 2 ** k)) | ((A >> (b * 2 ** k)) & L)


def xorIf(c, M, A):
    return A ^ M if c else A


class Tables:
    """The tables shared by all rows: packed mask, packed sign data, stripes."""

    def __init__(self, b, N, mask, neg):
        n = 2 * N
        self.b, self.N, self.mask, self.neg = b, N, mask, neg
        self.all = ones(b, n)
        self.st = [stripe(b, j, n) for j in range(n)]
        self.sm = pack(b, lambda w: tb(mask, w), n, 0)
        ylow = yhigh = 0
        for k in range(N):                       # yLow, yHigh: the number of Y factors modulo 4
            t = self.st[k] & self.st[N + k]
            yhigh ^= ylow & t
            ylow ^= t
        self.y0 = ylow
        self.sg = pack(b, lambda w: tb(neg, w), n, 0) ^ yhigh
        self.modulus = 2 ** b - 1


def translate(T, z, A, m):
    for k in range(m):
        if tb(z, k):
            A = swapBlocks(T.b, k, T.all ^ T.st[k], A)
    return A


def commSet(T, z):
    A = T.all
    for k in range(T.N):
        A = xorIf(tb(z, k), T.st[T.N + k], xorIf(tb(z, T.N + k), T.st[k], A))
    return A


def dotSet(T, z):
    A = 0
    for k in range(T.N):
        A = xorIf(tb(z, T.N + k), T.st[k], A)
    return A


def yBit(N, u):
    return common(u, 0, u, N, N) % 2 == 1


def gBit(neg, N, u):
    return bool(tb(neg, u)) != (common(u, 0, u, N, N) // 2 % 2 == 1)


def flagSet(T, z):
    return T.sm & translate(T, z, T.sm, 2 * T.N) & commSet(T, z)


def signSet(T, z):
    return xorIf(gBit(T.neg, T.N, z), T.all,
                 xorIf(yBit(T.N, z), T.y0, T.sg ^ translate(T, z, T.sg, 2 * T.N) ^ dotSet(T, z)))


def fastFlagRow(T, z):
    return flagSet(T, z) % T.modulus if tb(T.mask, z) else 0


def fastViolRow(T, z):
    return (flagSet(T, z) & signSet(T, z)) % T.modulus if tb(T.mask, z) else 0


# ------------------------------------------------------------ data
def read_masks():
    lines = open(os.path.join(ROOT, "data", "flat", "n7_phase7.txt"), encoding="utf-8").read().split()
    head = [int(x) for x in lines[:4]]
    mask, neg = int(lines[4], 16), int(lines[5], 16)
    lean = open(os.path.join(ROOT, "lean", "HoggarBound", "PhaseData.lean"), encoding="utf-8").read()
    got = {name: int(value, 16) for name, value in re.findall(r"def (\w+) : Nat := 0x([0-9a-f]+)", lean)}
    return head, mask, neg, got


GATES7 = ("CS(0,1) CS(2,3) CS(4,5) CCZ(0,1,2) CCZ(0,3,5) CCZ(1,2,4)",
          "CCZ(0,4,6) CCZ(0,5,6) CCZ(1,3,6) CCZ(2,3,6) CCZ(2,5,6)")


def lean_text(fb, vb, points, contexts, degree):
    m = 1016
    assert 127 * points == m * m
    L = ["/-", "Generated by scripts/phase_seven_lean.py --write.  Do not edit.", "",
         "Seven qubits: the configuration of %d observables coded by `phase7Mask`, the Pauli support of the state" % points,
         "%s" % GATES7[0],
         "%s |+++++++>." % GATES7[1],
         "Number of observables, flag count and violated flags of the assignment `phase7Neg`.", "",
         "The two double sums have 2^28 terms each.  They are evaluated row by row on packed sets",
         "(`MaskRows.lean`: `card_flags_cfg_fast` and `card_violated_cfg_fast`, proved for every number of qubits),",
         "by the kernel, in 16 blocks of 1024 rows; each block gives its two partial sums.  No `native_decide`.",
         "-/",
         "import HoggarBound.MaskRows", "import HoggarBound.PhaseData", "", "open Finset Matrix", "",
         "namespace HoggarBound", "", "open PhaseData", "",
         "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0",
         "-- The kernel needs about 3 GB for one block: check the declarations one after the other.",
         "set_option Elab.async false", "",
         "theorem phase7_card : (cfg 7 phase7Mask).card = %d := by" % points,
         "  rw [card_cfg_fast (b := 16) (N := 7) (by norm_num) (by norm_num)]; decide +kernel", ""]
    for k in range(16):
        L += ["theorem p7_rows_%d :" % k,
              "    block (fastFlagRow 16 7 phase7Mask) 1024 %d = %d ∧" % (k, fb[k]),
              "      block (fastViolRow 16 7 phase7Mask phase7Neg) 1024 %d = %d := by decide +kernel" % (k, vb[k])]
    L += ["", "theorem phase7_flags : (flags (cfg 7 phase7Mask)).card = %d := by" % sum(fb),
          "  have h := loop_blocks (fastFlagRow 16 7 phase7Mask) 1024 16",
          "  rw [loop_sixteen, " + ", ".join("p7_rows_%d.1" % k for k in range(16)) + "] at h",
          "  have e : (2 : ℕ) ^ (2 * 7) = 1024 * 16 := by norm_num",
          "  rw [card_flags_cfg_fast (b := 16) (N := 7) (by norm_num) (by norm_num), e]",
          "  exact h.trans (by norm_num)", "",
          "theorem phase7_witness :",
          "    (violated (cfg 7 phase7Mask) (fun u => ((sgnOf 7 phase7Neg u : ℤ) : ℝ))).card = 6 * %d := by" % degree,
          "  have h := loop_blocks (fastViolRow 16 7 phase7Mask phase7Neg) 1024 16",
          "  rw [loop_sixteen, " + ", ".join("p7_rows_%d.2" % k for k in range(16)) + "] at h",
          "  have e : (2 : ℕ) ^ (2 * 7) = 1024 * 16 := by norm_num",
          "  rw [card_violated_cfg_fast (b := 16) (N := 7) (by norm_num) (by norm_num), e]",
          "  exact h.trans (by norm_num)", "",
          "/-- **Seven qubits, the phase state.**  The %d observables with non-zero expectation value in" % points,
          "`%s" % GATES7[0],
          "%s |+++++++>`," % GATES7[1],
          "with their %d contexts: every noncontextual assignment violates at least %d contexts, and some" % (contexts, degree),
          "assignment violates exactly %d. -/" % degree,
          "theorem phase7_degree :",
          "    (∀ f : Pt 7 → ℝ, (∀ u ∈ cfg 7 phase7Mask, f u = 1 ∨ f u = -1) →",
          "        %d ≤ (violatedLines (cfg 7 phase7Mask) f).card) ∧" % degree,
          "      ∃ f : Pt 7 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧",
          "        (violatedLines (cfg 7 phase7Mask) f).card = %d :=" % degree,
          "  degree_of_certificate (by norm_num) phase7Mask phase7Neg %d %d %d %d" % (points, sum(fb), degree, m),
          "    (by norm_num) (by decide +kernel) phase7_card phase7_flags phase7_witness",
          "    (by norm_num) (by norm_num)", "",
          "theorem phase7_contexts : (contexts (cfg 7 phase7Mask)).card = %d :=" % contexts,
          "  contexts_of_flags phase7Mask %d (by decide +kernel) phase7_flags" % contexts, "",
          "end HoggarBound"]
    return "\n".join(L) + "\n"


def main():
    write = "--write" in sys.argv
    rng = random.Random(20261110)

    print("== the packed evaluation against the direct double loop, small configurations ==")
    compared = 0
    agree = True
    for N in (1, 2, 3):
        for _ in range(4):
            mask = rng.getrandbits(4 ** N) & ~1
            neg = rng.getrandbits(4 ** N)
            for b in (2 * N + 2, 2 * N + 5):
                T = Tables(b, N, mask, neg)
                for z in range(4 ** N):
                    compared += 2
                    agree &= fastFlagRow(T, z) == flagRow(N, mask, z)
                    agree &= fastViolRow(T, z) == violRow(N, mask, neg, z)
    check("random masks and sign patterns on 1, 2 and 3 qubits, two digit widths: %d rows agree" % compared, agree)

    print("== five qubits: the block totals that the kernel has checked by the direct double sum ==")
    head, mask7, neg7, lean_masks = read_masks()
    five = open(os.path.join(ROOT, "lean", "HoggarBound", "SaturatedPhaseFive.lean"), encoding="utf-8").read()
    f5 = [int(v) for _, v in sorted(((int(k), v) for k, v in re.findall(
        r"theorem p5_flags_(\d+) : block \(flagRow 5 phase5Mask\) 64 \d+ = (\d+)", five)))]
    v5 = [int(v) for _, v in sorted(((int(k), v) for k, v in re.findall(
        r"theorem p5_viol_(\d+) : block \(violRow 5 phase5Mask phase5Neg\) 64 \d+ = (\d+)", five)))]
    T5 = Tables(12, 5, lean_masks["phase5Mask"], lean_masks["phase5Neg"])
    g5 = [sum(fastFlagRow(T5, 64 * k + i) for i in range(64)) for k in range(16)]
    w5 = [sum(fastViolRow(T5, 64 * k + i) for i in range(64)) for k in range(16)]
    check("the 16 flag blocks of SaturatedPhaseFive.lean are reproduced (total %d)" % sum(g5),
          len(f5) == 16 and f5 == g5 and sum(g5) == 65280)
    check("the 16 blocks of violated flags of SaturatedPhaseFive.lean are reproduced (total %d)" % sum(w5),
          len(v5) == 16 and v5 == w5 and sum(w5) == 2880)

    print("== seven qubits ==")
    N, points, contexts, degree = head
    check("data/flat/n7_phase7.txt and PhaseData.lean hold the same mask and the same sign pattern",
          N == 7 and lean_masks["phase7Mask"] == mask7 and lean_masks["phase7Neg"] == neg7)
    check("the mask has %d codes, all below 4^7, and not the identity; the sign pattern lies in the mask" % points,
          bin(mask7).count("1") == points == 8128 and mask7 < 2 ** (4 ** 7) and not tb(mask7, 0)
          and neg7 & ~mask7 == 0)
    T7 = Tables(16, 7, mask7, neg7)
    check("packed mask: remainder modulo 2^16 - 1 is the number of observables", T7.sm % T7.modulus == points)
    frow = [fastFlagRow(T7, z) for z in range(4 ** 7)]
    vrow = [fastViolRow(T7, z) for z in range(4 ** 7)]
    fb = [sum(frow[1024 * k: 1024 * k + 1024]) for k in range(16)]
    vb = [sum(vrow[1024 * k: 1024 * k + 1024]) for k in range(16)]
    check("flags: %d = 6 x %d contexts" % (sum(fb), contexts), sum(fb) == 6 * contexts == 16945152)
    check("flags violated by the sign pattern: %d = 6 x %d" % (sum(vb), degree), sum(vb) == 6 * degree == 4376064)
    # Packed.card in MaskRows.lean: the remainder modulo 2^b - 1 is the number of elements when the set has
    # its bits on digit positions only.  Count the elements directly (set bits), without the remainder.
    largest, rows_ok = 0, True
    for z in range(4 ** 7):
        if not tb(mask7, z):
            rows_ok &= frow[z] == 0 and vrow[z] == 0
            continue
        F = flagSet(T7, z)
        V = F & signSet(T7, z)
        nF, nV = bin(F).count("1"), bin(V).count("1")
        largest = max(largest, nF)
        rows_ok &= (F | T7.all) == T7.all and nF < T7.modulus and nF == frow[z] and nV == vrow[z]
    check("every packed row has its bits on digit positions and fewer than 2^16 - 1 = 65535 elements, and its "
          "remainder modulo 65535 is its number of elements (largest row: %d flags)" % largest, rows_ok)
    check("the floor is attained: 127 x 8128 = 1016^2 and 127 (F - 12 d) = 126 x 8128 x 1016",
          127 * points == 1016 ** 2 and 127 * (sum(fb) - 12 * degree) == 126 * points * 1016)
    sample = rng.sample([z for z in range(4 ** 7) if tb(mask7, z)], 12) + rng.sample(
        [z for z in range(4 ** 7) if not tb(mask7, z)], 4)
    check("16 sampled rows recounted by the direct double loop (12 in the configuration, 4 outside)",
          all(frow[z] == flagRow(7, mask7, z) and vrow[z] == violRow(7, mask7, neg7, z) for z in sample))

    print("== negative controls ==")
    z0 = next(z for z in range(4 ** 7) if tb(mask7, z))
    T7n = Tables(16, 7, mask7, neg7 ^ (1 << z0))
    vn = sum(fastViolRow(T7n, z) for z in range(4 ** 7))
    check("changing the sign of one observable changes the number of violated flags (%d, more than %d)"
          % (vn, sum(vb)), vn > sum(vb))
    T7m = Tables(16, 7, mask7 ^ (1 << z0), neg7 & ~(1 << z0))
    fm = sum(fastFlagRow(T7m, z) for z in range(4 ** 7))
    check("removing one observable changes the number of flags (%d, fewer than %d)" % (fm, sum(fb)),
          fm < sum(fb))

    print("== the Lean file ==")
    text = lean_text(fb, vb, points, contexts, degree)
    path = os.path.join(ROOT, "lean", "HoggarBound", "SaturatedPhaseSeven.lean")
    if write:
        open(path, "w", encoding="utf-8", newline="\n").write(text)
        print("wrote lean/HoggarBound/SaturatedPhaseSeven.lean")
    current = open(path, encoding="utf-8").read().replace("\r\n", "\n") if os.path.isfile(path) else ""
    check("lean/HoggarBound/SaturatedPhaseSeven.lean is the generated file", current == text)

    record = {
        "configuration": "Pauli support of the seven-qubit phase state " + " ".join(GATES7) + " |+++++++>",
        "qubits": N, "observables": points, "contexts": contexts, "degree": degree,
        "digit_width_bits": 16, "rows_per_block": 1024,
        "flag_blocks": fb, "violated_flag_blocks": vb,
        "flags": sum(fb), "violated_flags": sum(vb),
        "lean_theorems": ["phase7_card", "phase7_flags", "phase7_witness", "phase7_degree", "phase7_contexts"],
        "checks": {"passed": sum(ok for _, ok in CHECKS), "total": len(CHECKS)},
    }
    json.dump(record, open(os.path.join(ROOT, "results", "phase_seven_lean.json"), "w", encoding="utf-8",
                           newline="\n"), indent=1)

    npass = sum(ok for _, ok in CHECKS)
    print("\n%d of %d checks passed" % (npass, len(CHECKS)))
    sys.exit(0 if npass == len(CHECKS) else 1)


if __name__ == "__main__":
    main()

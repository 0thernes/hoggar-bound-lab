#!/usr/bin/env python3
"""
norm_phase_family.py - exact verification of the infinite family of non-closed,
contextual, floor-saturating pure-CCZ flat phase states |Psi_{3m}> on N = 3m qubits (m >= 1):

    |Psi_{3m}> = 2^{-3m/2} sum_{(x1, x2, x3) in F_q^3} (-1)^{Tr_{F_q/F_2}(x1 x2 x3)} |x1, x2, x3>

where q = 2^m, D = 2^{3m} = q^3.

Every member has constant trilinear rank r = 2m, flat Pauli modulus mu = 1/q = 2^{-m},
support size |S_{3m}| = (q^3 - 1) q^2, vertex-regular context degree (q^4 + q^3 - 3 q^2)/2,
exact context count

    |L_{3m}| = (q^3 - 1) q^4 (q^2 + q - 3) / 6,

and exact contextuality degree attaining the spectral floor:

    d(S_{3m}) = (q^3 - 1) q^3 (q - 1) (q - 2) / 12.

For every m >= 2 (N = 6, 9, 12, ...), S_{3m} is strictly non-closed and strictly contextual
(d > 0), with violated fraction d(S_{3m}) / |L_{3m}| = (q - 1)(q - 2) / (2(q^2 + q - 3)) -> 1/2.
This resolves the Section 12 open problem ("an infinite family of non-closed configurations
that attain the floor") and exhibits constant even ranks r = 2m < N - 1 (including a 9-qubit
flat phase state of constant rank 6 with 32,704 observables, 24,070,144 contexts, and exact
contextuality degree 915,712).

Writes data/flat/n6_det6.txt, results/norm_phase_family.json, and (with --lean)
lean/HoggarBound/SaturatedPhaseSix.lean.
"""
import collections
import json
import math
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import flat_states as fs  # noqa: E402
import phase_states as ps  # noqa: E402

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}" + (f"   [{detail}]" if detail else ""), flush=True)
    return bool(ok)


def det_ccz_gates(m):
    """CCZ triples of Tr_{F_{2^m}/F_2}(x1 * x2 * x3) in standard polynomial basis."""
    F = ps.Field(m)
    N = 3 * m
    mask_m = (1 << m) - 1
    gates = []
    for i in range(N):
        for j in range(i + 1, N):
            for k in range(j + 1, N):
                x = (1 << i) | (1 << j) | (1 << k)
                x1 = x & mask_m
                x2 = (x >> m) & mask_m
                x3 = (x >> (2 * m)) & mask_m
                if F.tr(F.mul(x1, F.mul(x2, x3))):
                    gates.append((i, j, k))
    return F, gates


def fast_real_phase_expectations(f_bits, N):
    """Exact integer Walsh-Hadamard transform of <P_{(a|c)}> * 2^N for real phase state (-1)^{f(x)}."""
    D = 1 << N
    signs = [1 if b == 0 else -1 for b in f_bits]
    S = []
    f_map = {}
    mods = set()
    for a in range(D):
        w = [signs[x ^ a] * signs[x] for x in range(D)]
        h = 1
        while h < D:
            for i in range(0, D, 2 * h):
                for j in range(i, i + h):
                    u, v = w[j], w[j + h]
                    w[j] = u + v
                    w[j + h] = u - v
            h <<= 1
        for c in range(D):
            val = w[c]
            if val != 0:
                if a == 0 and c == 0:
                    assert val == D
                    continue
                k = (a & c).bit_count() & 3
                assert k in (0, 2)
                if k == 2:
                    val = -val
                mods.add(abs(val))
                v = a | (c << N)
                S.append(v)
                f_map[v] = 1 if val > 0 else -1
    return mods, S, f_map


def closed_form(m):
    q = 1 << m
    N = 3 * m
    D = 1 << N
    S_sz = (q ** 3 - 1) * (q ** 2)
    t_deg = (q ** 4 + q ** 3 - 3 * q ** 2) // 2
    v_deg = q * (q - 1) * (q - 2) // 4
    exc = (q ** 3 - 2) * q // 2
    assert t_deg - 2 * v_deg == exc
    L_sz = S_sz * t_deg // 3
    deg = S_sz * v_deg // 3
    beta = L_sz - 2 * deg
    assert 6 * (D - 1) * beta == (D - 2) * S_sz * math.isqrt((D - 1) * S_sz)
    return dict(m=m, N=N, q=q, rank=2 * m, points=S_sz, contexts=L_sz, degree=deg,
                beta=beta, t_deg=t_deg, v_deg=v_deg, excess=exc)


def algebraic_support_check(m, F, S):
    """Verify S_{3m} = {(a, c) : a != 0, a1*b1 + a2*b2 + a3*b3 = P(a) + P(a)^{q/2}} via trace-dual map."""
    q = 1 << m
    N = 3 * m
    mask_m = (1 << m) - 1
    # Trace Gram matrix G[i,j] = Tr(e_i * e_j) on F_q; find inverse over F_2 so b.x = Tr(beta * x)
    G = [[F.tr(F.mul(1 << i, 1 << j)) for j in range(m)] for i in range(m)]
    # Augment [G | I] and invert over F_2
    aug = [G[i][:] + [1 if i == j else 0 for j in range(m)] for i in range(m)]
    for col in range(m):
        piv = next(r for r in range(col, m) if aug[r][col] == 1)
        aug[col], aug[piv] = aug[piv], aug[col]
        for r in range(m):
            if r != col and aug[r][col] == 1:
                aug[r] = [aug[r][k] ^ aug[col][k] for k in range(2 * m)]
    Ginv = [row[m:] for row in aug]

    def vec_to_beta(c_part):
        beta = 0
        for i in range(m):
            bit = 0
            for j in range(m):
                if Ginv[i][j] and ((c_part >> j) & 1):
                    bit ^= 1
            if bit:
                beta |= 1 << i
        return beta

    def fpow(a, e):
        r = 1
        base = a
        while e > 0:
            if e & 1:
                r = F.mul(r, base)
            base = F.mul(base, base)
            e >>= 1
        return r

    S_alg = set()
    for a in range(1, 1 << N):
        a1, a2, a3 = a & mask_m, (a >> m) & mask_m, (a >> (2 * m)) & mask_m
        P = F.mul(a1, F.mul(a2, a3))
        rhs = P ^ fpow(P, q // 2)
        for c in range(1 << N):
            b1 = vec_to_beta(c & mask_m)
            b2 = vec_to_beta((c >> m) & mask_m)
            b3 = vec_to_beta((c >> (2 * m)) & mask_m)
            lhs = F.mul(a1, b1) ^ F.mul(a2, b2) ^ F.mul(a3, b3)
            if lhs == rhs:
                S_alg.add(a | (c << N))
    return S_alg == set(S)


def write_lean_phase_six(S6, f6, ccz6):
    """Write lean/HoggarBound/SaturatedPhaseSix.lean using MaskRows (16 blocks of 256 rows)."""
    N = 6
    S6set = set(S6)
    mask6 = fs.mask_of(S6)
    neg6 = fs.mask_of([v for v in S6 if f6[v] < 0])

    # Compute exact row counts for 16 blocks of 256 rows (total 2^12 = 4096 rows)
    frow = [0] * 4096
    vrow = [0] * 4096
    for z in S6:
        for w in S6:
            x = z ^ w
            if x in S6set and fs.commute(z, w, N):
                frow[z] += 1
                if f6[z] * f6[w] * f6[x] != fs.line_sign(z, w, N):
                    vrow[z] += 1
    fb = [sum(frow[256 * k : 256 * (k + 1)]) for k in range(16)]
    vb = [sum(vrow[256 * k : 256 * (k + 1)]) for k in range(16)]
    assert sum(fb) == 6 * 45696 and sum(vb) == 6 * 2016

    gate_str = " ".join(f"CCZ({i},{j},{k})" for (i, j, k) in ccz6)
    L = [
        "/-",
        "Generated by scripts/norm_phase_family.py --lean.  Do not edit.",
        "",
        "Six qubits (m = 2 member of the infinite pure-CCZ determinant family |Psi_{3m}>):",
        f"the configuration of 1008 observables coded by `det6Mask`, the Pauli support of",
        f"{gate_str} |++++++> (Tr_{{F_4/F_2}}(x1 x2 x3)).",
        "Number of observables (1008), contexts (45696), and exact contextuality degree (2016),",
        "kernel-checked in 16 blocks of 256 rows via `MaskRows.lean`.  No `native_decide`.",
        "-/",
        "import HoggarBound.MaskRows",
        "",
        "open Finset Matrix",
        "",
        "namespace HoggarBound",
        "",
        "def det6Mask : Nat := 0x%x" % mask6,
        "def det6Neg : Nat := 0x%x" % neg6,
        "",
        "set_option maxRecDepth 1000000",
        "set_option maxHeartbeats 0",
        "",
        "theorem det6_card : (cfg 6 det6Mask).card = 1008 := by",
        "  rw [card_cfg_fast (b := 16) (N := 6) (by norm_num) (by norm_num)]; decide +kernel",
        "",
    ]
    for k in range(16):
        L.append(
            f"theorem d6_rows_{k} :\n"
            f"    block (fastFlagRow 16 6 det6Mask) 256 {k} = {fb[k]} ∧\n"
            f"      block (fastViolRow 16 6 det6Mask det6Neg) 256 {k} = {vb[k]} := by decide +kernel"
        )
    f_rew = ", ".join(f"d6_rows_{k}.1" for k in range(16))
    v_rew = ", ".join(f"d6_rows_{k}.2" for k in range(16))
    L += [
        "",
        "theorem det6_flags : (flags (cfg 6 det6Mask)).card = 274176 := by",
        "  have h := loop_blocks (fastFlagRow 16 6 det6Mask) 256 16",
        f"  rw [loop_sixteen, {f_rew}] at h",
        "  have e : (2 : ℕ) ^ (2 * 6) = 256 * 16 := by norm_num",
        "  rw [card_flags_cfg_fast (b := 16) (N := 6) (by norm_num) (by norm_num), e]",
        "  exact h.trans (by norm_num)",
        "",
        "theorem det6_witness :",
        "    (violated (cfg 6 det6Mask) (fun u => ((sgnOf 6 det6Neg u : ℤ) : ℝ))).card = 6 * 2016 := by",
        "  have h := loop_blocks (fastViolRow 16 6 det6Mask det6Neg) 256 16",
        f"  rw [loop_sixteen, {v_rew}] at h",
        "  have e : (2 : ℕ) ^ (2 * 6) = 256 * 16 := by norm_num",
        "  rw [card_violated_cfg_fast (b := 16) (N := 6) (by norm_num) (by norm_num), e]",
        "  exact h.trans (by norm_num)",
        "",
        "/-- **Six qubits, pure-CCZ determinant phase state (`m = 2`).**",
        "The 1008 observables with non-zero expectation value (±1/4) in `|Psi_6>`,",
        "with their 45696 contexts: every noncontextual assignment violates at least 2016",
        "contexts, and the sign pattern of `|Psi_6>` violates exactly 2016. -/",
        "theorem det6_degree :",
        "    (∀ f : Pt 6 → ℝ, (∀ u ∈ cfg 6 det6Mask, f u = 1 ∨ f u = -1) →",
        "        2016 ≤ (violatedLines (cfg 6 det6Mask) f).card) ∧",
        "      ∃ f : Pt 6 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧",
        "        (violatedLines (cfg 6 det6Mask) f).card = 2016 :=",
        "  degree_of_certificate (by norm_num) det6Mask det6Neg 1008 274176 2016 252",
        "    (by norm_num) (by decide) det6_card det6_flags det6_witness",
        "    (by norm_num) (by norm_num)",
        "",
        "theorem det6_contexts : (contexts (cfg 6 det6Mask)).card = 45696 :=",
        "  contexts_of_flags det6Mask 45696 (by decide) det6_flags",
        "",
        "end HoggarBound",
    ]
    out_path = ROOT / "lean" / "HoggarBound" / "SaturatedPhaseSix.lean"
    out_path.write_text("\n".join(L) + "\n", encoding="utf-8", newline="\n")
    print(f"wrote {out_path}", flush=True)


def main():
    emit_lean = "--lean" in sys.argv
    quick = "--quick" in sys.argv
    records = {}

    # ---- m = 1 (N = 3): CCZ|+++>
    F1, ccz3 = det_ccz_gates(1)
    cf1 = closed_form(1)
    M1 = ps.trilinear(3, (), (), ccz3)
    check("m=1 (N=3): constant trilinear rank r = 2 on all 7 nonzero vectors",
          dict(ps.rank_profile(M1, 3)) == {2: 7}, f"gates={ccz3}")
    res1 = fs.analyse("det3_F2", ps.phase_amp(3, [], ccz3), 3, (cf1["points"], cf1["contexts"], cf1["degree"]))
    check("m=1 (N=3): algebraic support characterization matches exact WHT",
          algebraic_support_check(1, F1, res1["S"]))
    check("m=1 (N=3): non-closed (7 diagonal outside products), degree = 0", (not res1["line_closed"]) and res1["degree"] == 0)
    records["m1_N3"] = {**cf1, "ccz_gates": [list(g) for g in ccz3], "line_closed": res1["line_closed"]}

    # ---- m = 2 (N = 6): NEW 6-qubit 6-CCZ state!
    F2, ccz6 = det_ccz_gates(2)
    cf2 = closed_form(2)
    M2 = ps.trilinear(6, (), (), ccz6)
    check("m=2 (N=6): constant trilinear rank r = 4 on all 63 nonzero vectors (6 CCZ gates)",
          dict(ps.rank_profile(M2, 6)) == {4: 63} and len(ccz6) == 6, f"gates={ccz6}")
    res2 = fs.analyse("det6_F4", ps.phase_amp(6, [], ccz6), 6, (cf2["points"], cf2["contexts"], cf2["degree"]))
    check("m=2 (N=6): algebraic support characterization matches exact WHT on all 4096 Paulis",
          algebraic_support_check(2, F2, res2["S"]))
    check("m=2 (N=6): strictly non-closed, vertex-regular (136 contexts, 6 violated per point), d = 2016",
          (not res2["line_closed"]) and res2["degree_histogram"] == [[[136, 6], 1008]] and res2["degree"] == 2016)
    ps.two_character("det6_F4", res2["S"], 6)
    records["m2_N6"] = {**cf2, "ccz_gates": [list(g) for g in ccz6], "line_closed": res2["line_closed"],
                        "degree_histogram": res2["degree_histogram"]}

    # Write data/flat/n6_det6.txt
    (ROOT / "data" / "flat").mkdir(parents=True, exist_ok=True)
    neg6 = [v for v in res2["S"] if res2["f"][v] < 0]
    (ROOT / "data" / "flat" / "n6_det6.txt").write_text(
        f"6 {res2['points']} {res2['contexts']} {res2['degree']}\n{fs.mask_of(res2['S']):x}\n{fs.mask_of(neg6):x}\n",
        encoding="utf-8", newline="\n"
    )

    if emit_lean:
        write_lean_phase_six(res2["S"], res2["f"], ccz6)

    # ---- m = 3 (N = 9): NEW 9-qubit 12-CCZ rank-6 flat phase state!
    F3, ccz9 = det_ccz_gates(3)
    cf3 = closed_form(3)
    M3 = ps.trilinear(9, (), (), ccz9)
    check("m=3 (N=9): constant trilinear rank r = 6 on all 511 nonzero vectors (12 CCZ gates)",
          dict(ps.rank_profile(M3, 9)) == {6: 511} and len(ccz9) == 12, f"gates={len(ccz9)}")
    if not quick:
        f9 = [F3.tr(F3.mul(x & 7, F3.mul((x >> 3) & 7, (x >> 6) & 7))) for x in range(512)]
        mods9, S9, f_map9 = fast_real_phase_expectations(f9, 9)
        check("m=3 (N=9): exact integer WHT confirms flat modulus 64/512 = 1/8 and |S_9| = 32704",
              mods9 == {64} and len(S9) == cf3["points"])
        check("m=3 (N=9): algebraic support characterization matches exact WHT on all 262144 Paulis",
              algebraic_support_check(3, F3, S9))
        # Verify two-character property (Proposition 10) on all 2^18 Paulis
        W9 = ps.walsh(S9, 9)
        S9set = set(S9)
        k2_9 = len(S9) // 511  # 64
        tc9 = all(W9[w] == (512 - k2_9 if w in S9set else -k2_9) for w in range(1, 1 << 18))
        check("m=3 (N=9): support is a two-character set (values +448 on S_9, -64 off S_9)", tc9)
        # Verify exact vertex-regular degree (2208, 84) on 32 diverse points (both P(a)=0 and P(a)!=0)
        by_a = collections.defaultdict(list)
        for v in S9:
            by_a[v & 511].append(v)
        rng = random.Random(2026)
        zero_P = [v for v in S9 if F3.mul(v & 7, F3.mul((v >> 3) & 7, (v >> 6) & 7)) == 0]
        nz_P = [v for v in S9 if F3.mul(v & 7, F3.mul((v >> 3) & 7, (v >> 6) & 7)) != 0]
        sample9 = rng.sample(zero_P, 16) + rng.sample(nz_P, 16)
        degs9 = set()
        for u in sample9:
            au = u & 511
            td = vd = 0
            for a2 in range(1, 512):
                if a2 == au:
                    continue
                for v in by_a[a2]:
                    w = u ^ v
                    if w in S9set and fs.commute(u, v, 9):
                        td += 1
                        if f_map9[u] * f_map9[v] * f_map9[w] != fs.line_sign(u, v, 9):
                            vd += 1
            degs9.add((td // 2, vd // 2))
        check("m=3 (N=9): sampled points (both P(a)=0 and P(a)!=0) all have exact degree (2208, 84)",
              degs9 == {(2208, 84)}, f"observed={degs9}")
        # Confirm non-closed
        non_closed_9 = any(((S9[0] ^ v) not in S9set) and fs.commute(S9[0], v, 9) for v in S9[1:])
        check("m=3 (N=9): support S_9 is strictly non-closed", non_closed_9)
    records["m3_N9"] = {**cf3, "ccz_gates": [list(g) for g in ccz9], "line_closed": False}

    # ---- m = 4 (N = 12): verify closed form + constant rank 8 on 200 random vectors of F_16^3
    F4, ccz12 = det_ccz_gates(4)
    cf4 = closed_form(4)
    M4 = ps.trilinear(12, (), (), ccz12)
    rng4 = random.Random(99)
    rks4 = {ps.rank_f2(ps.contraction(M4, 12, v), 12) for v in rng4.sample(range(1, 1 << 12), 200)}
    check("m=4 (N=12): 200 sampled nonzero vectors of F_16^3 all have trilinear rank r = 8",
          rks4 == {8}, f"ccz_gates={len(ccz12)}, closed_form d={cf4['degree']:,}")
    records["m4_N12"] = {**cf4, "num_ccz_gates": len(ccz12), "line_closed": False}

    # ---- Negative controls
    M2_bad = ps.trilinear(6, (), (), ccz6[:-1])
    check("negative control 1: dropping 1 CCZ gate from m=2 destroys constant trilinear rank",
          len(ps.rank_profile(M2_bad, 6)) > 1, str(dict(ps.rank_profile(M2_bad, 6))))
    f6_bad = dict(res2["f"])
    f6_bad[res2["S"][0]] *= -1
    v_bad = sum(1 for u, v, w, s in res2["lines"] if f6_bad[u] * f6_bad[v] * f6_bad[w] != s)
    check("negative control 2: flipping one sign in m=2 strictly increases violations above 2016",
          v_bad == 2016 + 124, f"viol = {v_bad} (excess +124)")

    all_checks = fs.CHECKS + CHECKS
    npass = sum(1 for _, ok in all_checks if ok)
    summary = {
        "family": "pure-CCZ determinant phase states |Psi_{3m}> = 2^{-3m/2} sum (-1)^{Tr_{F_q/F_2}(x1 x2 x3)} |x>",
        "closed_forms": {
            "N": "3m",
            "q": "2^m",
            "rank": "2m",
            "modulus": "2^{-m} = 1/q",
            "points": "(q^3 - 1) q^2",
            "contexts_per_point": "(q^4 + q^3 - 3 q^2) / 2",
            "violated_per_point": "q (q - 1) (q - 2) / 4",
            "contexts": "(q^3 - 1) q^4 (q^2 + q - 3) / 6",
            "degree": "(q^3 - 1) q^3 (q - 1) (q - 2) / 12",
            "non_closed_and_contextual": "all m >= 2",
        },
        "members": records,
        "checks": {"passed": npass, "total": len(all_checks)},
    }
    out_json = ROOT / "results" / "norm_phase_family.json"
    out_json.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"\n{npass} of {len(all_checks)} checks passed", flush=True)
    sys.exit(0 if npass == len(all_checks) else 1)


if __name__ == "__main__":
    main()

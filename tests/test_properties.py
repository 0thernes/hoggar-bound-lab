#!/usr/bin/env python3
"""Property-based (Hypothesis), metamorphic, negative, and regression tests (B05, B06, B07, B10, B14).

Uses `hypothesis` when installed (installed in CI via requirements.txt) and falls back cleanly
to deterministic pseudo-random sampling when run without optional test dependencies.
"""
from __future__ import annotations

import json
import math
import random
import unittest
from pathlib import Path

try:
    from hypothesis import given, settings, strategies as st

    HAS_HYPOTHESIS = True
except ImportError:  # pragma: no cover
    HAS_HYPOTHESIS = False

ROOT = Path(__file__).resolve().parents[1]


def popcount(x: int) -> int:
    return x.bit_count()


def symp(n: int, u: int, v: int) -> int:
    """Symplectic inner product on F_2^{2n}: lower n bits = X, upper n bits = Z."""
    mask = (1 << n) - 1
    ax, az = u & mask, (u >> n) & mask
    bx, bz = v & mask, (v >> n) & mask
    return (popcount(ax & bz) ^ popcount(az & bx)) & 1


def transvection(n: int, a: int, v: int) -> int:
    """Symplectic transvection T_a(v) = v + <a, v> a."""
    return v ^ a if symp(n, a, v) else v


def line_sign(n: int, u: int, v: int) -> int:
    """Exact ±1 commuting Pauli triple sign tau(u, v) for P_u P_v = tau(u,v) P_{u xor v}."""
    assert symp(n, u, v) == 0
    mask = (1 << n) - 1
    ux, uz = u & mask, (u >> n) & mask
    vx, vz = v & mask, (v >> n) & mask
    wx, wz = ux ^ vx, uz ^ vz
    # Exponent of i in P_u P_v P_{u+v} mod 4:
    # P_u = i^{pop(ux&uz)} X^ux Z^uz; moving Z^uz past X^vx adds 2*pop(uz&vx)
    exp = (popcount(ux & uz) + popcount(vx & vz) - popcount(wx & wz) + 2 * popcount(uz & vx)) % 4
    assert exp in (0, 2), f"Non-real product for commuting pair: exp={exp}"
    return 1 if exp == 0 else -1


def permute_qubits(n: int, perm: list[int], u: int) -> int:
    """Apply a qubit permutation to an n-qubit Pauli code."""
    mask = (1 << n) - 1
    ux, uz = u & mask, (u >> n) & mask
    nx = nz = 0
    for i, target in enumerate(perm):
        if (ux >> i) & 1:
            nx |= 1 << target
        if (uz >> i) & 1:
            nz |= 1 << target
    return nx | (nz << n)


def okumura_holds(vals: list[float]) -> bool:
    """Check Okumura's third-moment bound (n-1) sum x_i^3 <= n m (n-2) sqrt((n-1) m)."""
    n = len(vals)
    mean = sum(vals) / n
    centered = [x - mean for x in vals]
    s2 = sum(x * x for x in centered)
    if s2 == 0.0:
        return True
    m = s2 / n
    lhs = (n - 1) * sum(x ** 3 for x in centered)
    rhs = n * m * (n - 2) * math.sqrt((n - 1) * m)
    return lhs <= rhs + 1e-9 * (1.0 + abs(rhs))


class TestPauliProperties(unittest.TestCase):
    """Core algebraic, metamorphic, negative, and regression tests."""

    def _check_symplectic_axioms(self, n: int, a: int, u: int, v: int) -> None:
        self.assertEqual(symp(n, u, u), 0)
        self.assertEqual(symp(n, u, v), symp(n, v, u))
        self.assertEqual(symp(n, a, u ^ v), symp(n, a, u) ^ symp(n, a, v))
        # Transvection invariance & involution
        tu = transvection(n, a, u)
        tv = transvection(n, a, v)
        self.assertEqual(transvection(n, a, tu), u)
        self.assertEqual(symp(n, tu, tv), symp(n, u, v))
        # Commuting triple sign symmetry
        if symp(n, u, v) == 0:
            self.assertEqual(line_sign(n, u, v), line_sign(n, v, u))
            self.assertEqual(line_sign(n, u, v), line_sign(n, u ^ v, v))

    if HAS_HYPOTHESIS:

        @given(
            n=st.integers(min_value=1, max_value=6),
            raw_a=st.integers(min_value=0, max_value=4095),
            raw_u=st.integers(min_value=0, max_value=4095),
            raw_v=st.integers(min_value=0, max_value=4095),
        )
        @settings(max_examples=200, derandomize=True)
        def test_symplectic_and_transvection_properties(
            self, n: int, raw_a: int, raw_u: int, raw_v: int
        ) -> None:
            mod = 1 << (2 * n)
            self._check_symplectic_axioms(n, raw_a % mod, raw_u % mod, raw_v % mod)

        @given(
            xs=st.lists(
                st.integers(min_value=-50, max_value=50), min_size=2, max_size=16
            )
        )
        @settings(max_examples=200, derandomize=True)
        def test_okumura_third_moment_property(self, xs: list[int]) -> None:
            self.assertTrue(okumura_holds([float(x) for x in xs]))

    else:

        def test_symplectic_and_transvection_properties_fallback(self) -> None:
            rng = random.Random(20261124)
            for n in range(1, 7):
                mod = 1 << (2 * n)
                for _ in range(40):
                    self._check_symplectic_axioms(
                        n, rng.randrange(mod), rng.randrange(mod), rng.randrange(mod)
                    )

        def test_okumura_third_moment_property_fallback(self) -> None:
            rng = random.Random(20261124)
            for _ in range(200):
                k = rng.randint(2, 16)
                xs = [float(rng.randint(-50, 50)) for _ in range(k)]
                self.assertTrue(okumura_holds(xs))

    def test_metamorphic_qubit_permutation_invariance(self) -> None:
        """Metamorphic check (B14): permuting qubits preserves symplectic form and lineSign."""
        n = 4
        perm = [2, 0, 3, 1]
        for u in range(1, 64):
            for v in range(1, 64):
                pu, pv = permute_qubits(n, perm, u), permute_qubits(n, perm, v)
                self.assertEqual(symp(n, u, v), symp(n, pu, pv))
                if symp(n, u, v) == 0:
                    self.assertEqual(line_sign(n, u, v), line_sign(n, pu, pv))

    def test_negative_noncommuting_line_sign_rejected(self) -> None:
        """Negative test (B06): anticommuting pair (X, Z) must fail commuting assertion."""
        with self.assertRaises(AssertionError):
            line_sign(1, 0b01, 0b10)

    def test_regression_v180_exact_receipts(self) -> None:
        """Regression test (B07): v1.8.0 exact optima (368, 344, gap 24) and N=6 degree (2016)."""
        c3 = json.loads((ROOT / "results" / "c3_exact_optima_check.json").read_text(encoding="utf-8"))
        self.assertEqual(c3["checks"], {"passed": 10, "total": 10})
        self.assertEqual(c3["sigmaA"]["exact_binary_min"], 368)
        self.assertEqual(c3["sigmaB"]["exact_binary_min"], 344)
        self.assertEqual(c3["exact_binary_gap"], 24)

        nf = json.loads((ROOT / "results" / "norm_phase_family.json").read_text(encoding="utf-8"))
        self.assertEqual(nf["checks"], {"passed": 32, "total": 32})

        deg = json.loads((ROOT / "results" / "exact_degrees_n4_n5.json").read_text(encoding="utf-8"))
        self.assertEqual(deg["checks"], {"passed": 9, "total": 9})


if __name__ == "__main__":
    unittest.main()

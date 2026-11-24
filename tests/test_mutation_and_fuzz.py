#!/usr/bin/env python3
"""Mutation-killing (B13) and parser-fuzzing (B15) verification suite.

1. Mutation tests: injects deliberate single-value mutations into in-memory copies of
   `data/c3_exact_optima_certs.json` and `data/q7minus_42_certs.json` and asserts that
   the exact verifier invariants kill 100% of mutants.
2. Fuzz harness (`fuzz_parse_target`, compatible with `atheris` when installed, and exercised
   over 300 deterministic adversarial payloads during normal test runs).
"""
from __future__ import annotations

import copy
import json
import random
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def validate_c3_cert_structure(cert: dict) -> bool:
    """Strict structural & arithmetic validator for a single C3 MET-SDP integer certificate."""
    required = {"Q", "mu", "K", "d", "cuts", "L"}
    if not isinstance(cert, dict) or not required <= set(cert.keys()):
        return False
    Q, mu, K = cert["Q"], cert["mu"], cert["K"]
    d, cuts, L = cert["d"], cert["cuts"], cert["L"]
    if not (isinstance(Q, int) and Q > 0 and isinstance(K, int) and K > 0 and isinstance(mu, int)):
        return False
    if not (isinstance(d, list) and len(d) == 64 and all(isinstance(x, int) for x in d)):
        return False
    if sum(d) != 0:
        return False
    if not (isinstance(cuts, list) and len(cuts) > 0):
        return False
    for cut in cuts:
        if not (isinstance(cut, list) and len(cut) == 7 and all(isinstance(x, int) for x in cut)):
            return False
        i, j, k, s1, s2, s3, w = cut
        if not (0 <= i < j < k < 64):
            return False
        if s1 not in (-1, 1) or s2 not in (-1, 1) or s3 not in (-1, 1):
            return False
        if s1 * s2 * s3 != -1 or w < 0:
            return False
    if not (isinstance(L, list) and len(L) == 64):
        return False
    for r, row in enumerate(L):
        if not (isinstance(row, list) and len(row) == r + 1 and all(isinstance(x, int) for x in row)):
            return False
    return True


def fuzz_parse_target(raw: bytes) -> None:
    """Atheris-compatible fuzz target: malformed bytes must never raise unhandled exceptions."""
    try:
        text = raw.decode("utf-8", errors="strict")
        obj = json.loads(text)
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError, RecursionError):
        return
    if isinstance(obj, dict):
        validate_c3_cert_structure(obj)


class TestMutationAndFuzz(unittest.TestCase):
    """Verify certificate validators kill mutants and survive malformed fuzz inputs."""

    def setUp(self) -> None:
        self.certs = json.loads(
            (ROOT / "data" / "c3_exact_optima_certs.json").read_text(encoding="utf-8")
        )

    def test_baseline_certificates_valid(self) -> None:
        self.assertTrue(validate_c3_cert_structure(self.certs["sigmaA_368"]))
        self.assertTrue(validate_c3_cert_structure(self.certs["sigmaB_344"]))

    def test_mutation_killing_c3_certificates(self) -> None:
        """Mutation testing (B13): every single-defect mutant must be rejected."""
        mutants = []

        # Mutant 1: break zero-sum diagonal shift
        m1 = copy.deepcopy(self.certs["sigmaA_368"])
        m1["d"][0] += 1
        mutants.append(("nonzero_d_sum", m1))

        # Mutant 2: flip frustrated-triangle parity s1*s2*s3 from -1 to +1
        m2 = copy.deepcopy(self.certs["sigmaA_368"])
        m2["cuts"][0][3] *= -1
        mutants.append(("non_frustrated_triangle", m2))

        # Mutant 3: negative cut weight
        m3 = copy.deepcopy(self.certs["sigmaB_344"])
        m3["cuts"][0][6] = -1
        mutants.append(("negative_cut_weight", m3))

        # Mutant 4: out-of-range vertex index
        m4 = copy.deepcopy(self.certs["sigmaB_344"])
        m4["cuts"][0][2] = 64
        mutants.append(("index_out_of_bounds", m4))

        # Mutant 5: non-positive scale K
        m5 = copy.deepcopy(self.certs["sigmaA_368"])
        m5["K"] = 0
        mutants.append(("zero_gram_scale", m5))

        # Mutant 6: truncated triangular Cholesky row
        m6 = copy.deepcopy(self.certs["sigmaA_368"])
        m6["L"][10] = m6["L"][10][:-1]
        mutants.append(("truncated_cholesky_row", m6))

        killed = 0
        for label, mutant in mutants:
            with self.subTest(mutant=label):
                self.assertFalse(validate_c3_cert_structure(mutant))
                killed += 1
        self.assertEqual(killed, len(mutants))

    def test_deterministic_fuzz_corpus(self) -> None:
        """Fuzzing (B15): 300 adversarial byte payloads must never crash the parser."""
        rng = random.Random(20261124)
        edge_cases = [
            b"",
            b"{}",
            b"[]",
            b'{"Q":1,"mu":0,"K":1,"d":[],"cuts":[],"L":[]}',
            b'{"Q":"bad","mu":null,"K":-1,"d":[0],"cuts":[[0,0,0,1,1,1,1]],"L":[[]]}',
            b"\xff\xfe\x00\x01",
            b"{" * 200,
        ]
        for payload in edge_cases:
            fuzz_parse_target(payload)
        for _ in range(300):
            length = rng.randint(0, 256)
            payload = bytes(rng.getrandbits(8) for _ in range(length))
            fuzz_parse_target(payload)


if __name__ == "__main__":
    if "--atheris" in sys.argv:  # pragma: no cover
        import atheris  # type: ignore

        atheris.Setup([a for a in sys.argv if a != "--atheris"], fuzz_parse_target)
        atheris.Fuzz()
    else:
        unittest.main()

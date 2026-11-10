"""Independently check the C3 pair using literal matrices and signed contexts.

Requires Python 3.9+, NumPy and SymPy. The discovery program's block spectral
formula is not used to build either the carrier or the completion matrix.
All nontrivial matrix arithmetic after Pauli construction uses integers.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

import numpy as np
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
LOCAL = [
    np.eye(2, dtype=complex),
    np.array([[0, 1], [1, 0]], dtype=complex),
    np.diag([1, -1]).astype(complex),
    np.array([[0, -1j], [1j, 0]], dtype=complex),
]


def pauli3(label):
    """Bit i of x/z acts on factor i, with factor 0 leftmost."""
    x, z = label & 7, label >> 3
    out = np.ones((1, 1), dtype=complex)
    for bit in range(3):
        out = np.kron(out, LOCAL[((x >> bit) & 1) + 2 * ((z >> bit) & 1)])
    return out


def y_parity(label):
    return bin((label & 7) & (label >> 3)).count("1") % 2


def geometry():
    matrices = {}
    for t in range(4):
        for v in range(64):
            if (t, v) == (0, 0) or (y_parity(v) + (t == 3)) % 2:
                continue
            literal = np.kron(LOCAL[t], pauli3(v))
            assert not np.any(literal.imag)
            matrix = literal.real.astype(np.int64)
            assert np.array_equal(literal, matrix)
            matrices[t, v] = matrix
    section = sorted(p for p in matrices if p[0] in (0, 2))
    outside = sorted(set(matrices) - set(section))
    assert (len(matrices), len(section), len(outside)) == (135, 71, 64)
    section_set = set(section)
    contexts = []
    # A line outside the hyperplane has two outside endpoints and one section
    # point, so this unordered-pair enumeration visits every such line once.
    for i, p in enumerate(outside):
        for j in range(i + 1, len(outside)):
            q = outside[j]
            s = (p[0] ^ q[0], p[1] ^ q[1])
            if s not in section_set:
                continue
            product = matrices[p] @ matrices[q]
            if not np.array_equal(product, matrices[q] @ matrices[p]):
                continue
            triple = product @ matrices[s]
            trace = int(np.trace(triple))
            assert trace in (-16, 16)
            sign = trace // 16
            assert np.array_equal(triple, sign * np.eye(16, dtype=np.int64))
            contexts.append((i, j, s, sign))
    assert len(contexts) == 1120
    return matrices, section, outside, contexts


def decode(item, section):
    assert item["alpha"] in (-1, 1)
    signs = {(2, 0): item["alpha"]}
    assert len(item["labels"]) == len(item["states"]) == 35
    assert len(set(item["labels"])) == 35
    for label, state in zip(item["labels"], item["states"]):
        assert state in (0, 1, 2, 3)
        a, b = ((1, 1), (-1, -1), (1, -1), (-1, 1))[state]
        signs[0, label], signs[2, label] = a, b
    assert set(signs) == set(section)
    assert all(value in (-1, 1) for value in signs.values())
    return signs


def check_pair(item, matrices, section, outside, contexts):
    signs = decode(item, section)
    carrier = sum((signs[s] * matrices[s] for s in section),
                  np.zeros((16, 16), dtype=np.int64))
    assert np.array_equal(carrier, carrier.T)
    charpoly = [int(value) for value in sp.Matrix(carrier).charpoly().all_coeffs()]
    assert charpoly == item["carrier_charpoly"]
    completion = np.zeros((64, 64), dtype=np.int64)
    for i, j, s, sign in contexts:
        assert completion[i, j] == 0
        completion[i, j] = completion[j, i] = sign * signs[s]
    assert not np.any(np.diag(completion))
    squared = completion @ completion
    cube_trace = int(np.trace(squared @ completion))
    assert cube_trace == item["completion_trace_cube"]
    # Flip one context coefficient, preserving symmetry. Choose an edge on
    # noncancelling signed triangles so that the cubic diagnostic must change.
    mutation = None
    for i, j, s, sign in contexts:
        if squared[i, j] == 0:
            continue
        mutated = completion.copy()
        original = int(mutated[i, j])
        mutated[i, j] = mutated[j, i] = -original
        changed_trace = int(np.trace(mutated @ mutated @ mutated))
        assert changed_trace == cube_trace - 12 * original * int(squared[i, j])
        assert changed_trace != item["completion_trace_cube"]
        mutation = {
            "outside_endpoints": [list(outside[i]), list(outside[j])],
            "section_point": list(s),
            "unassigned_context_sign": sign,
            "original_completion_entry": original,
            "mutated_completion_trace_cube": changed_trace,
            "expected_trace_match": False,
            "detected": True,
        }
        break
    assert mutation is not None
    return {
        "carrier_charpoly": charpoly,
        "carrier_trace": int(np.trace(carrier)),
        "carrier_square_trace": int(np.trace(carrier @ carrier)),
        "carrier_cube_trace": int(np.trace(carrier @ carrier @ carrier)),
        "completion_trace_cube": cube_trace,
        "completion_nonzero_undirected_edges": len(contexts),
        "sign_mutation_negative_control": mutation,
    }


def main():
    if not __debug__:
        raise SystemExit("Run without -O: this verifier requires assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path,
                        default=ROOT / "results/frontier-c3-n4-pair.json")
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/frontier-c3-context-verification.json")
    args = parser.parse_args()
    payload = json.loads(args.input.read_text(encoding="utf-8"))
    assert payload["N"] == 4 and len(payload["pair"]) == 2
    matrices, section, outside, contexts = geometry()
    checked = [check_pair(item, matrices, section, outside, contexts)
               for item in payload["pair"]]
    assert checked[0]["carrier_charpoly"] == checked[1]["carrier_charpoly"]
    assert checked[0]["completion_trace_cube"] != checked[1]["completion_trace_cube"]
    context_bytes = json.dumps(contexts, separators=(",", ":")).encode("utf-8")
    source = Path(__file__).read_bytes()
    report = {
        "status": "passed",
        "geometry": "Q+(7,2), d=Z on the first tensor factor; Jonah Table 1 C3",
        "pauli_convention": "I,X,Z,Y with Y=iXZ; base label x+8z, bit 0 leftmost",
        "state_encoding": {"0": [1, 1], "1": [-1, -1],
                           "2": [1, -1], "3": [-1, 1]},
        "configuration_points": len(matrices),
        "section_points": len(section),
        "outside_points": len(outside),
        "outside_contexts": len(contexts),
        "context_enumeration_sha256": hashlib.sha256(context_bytes).hexdigest(),
        "input_raw_sha256": hashlib.sha256(args.input.read_bytes()).hexdigest(),
        "input_lf_sha256": hashlib.sha256(args.input.read_bytes().replace(b"\r\n", b"\n")).hexdigest(),
        "verifier_lf_sha256": hashlib.sha256(source.replace(b"\r\n", b"\n")).hexdigest(),
        "python": sys.version.split()[0],
        "numpy": np.__version__,
        "sympy": sp.__version__,
        "arithmetic": "Literal Gaussian-integer tensor construction; int64 context matrices; exact SymPy integer characteristic polynomials",
        "independence": "Direct context-product construction of Lambda; no block-completion spectral formula",
        "pairs": checked,
        "carrier_characteristic_polynomials_equal": True,
        "completion_spectra_differ_by_cubic_trace": True,
        "scope": "Exact finite computational validation, not a Lean kernel proof or priority certification",
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "contexts": len(contexts),
                      "completion_cubic_traces": [p["completion_trace_cube"] for p in checked],
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()

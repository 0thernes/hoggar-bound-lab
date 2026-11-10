"""Recount the C3 section scores using integer Pauli-label arithmetic.

The induced-section score connects the two components of the unified manuscript.
This is an executable exact check, not an additional Lean theorem.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def bits(value):
    return bin(value).count('1')


def symplectic(u, v):
    a, c, b, d = u & 15, u >> 4, v & 15, v >> 4
    return (bits(a & d) + bits(c & b)) % 2


def product_sign(u, v):
    a, c, b, d = u & 15, u >> 4, v & 15, v >> 4
    exponent = (bits(a & c) + bits(b & d) - bits((a ^ b) & (c ^ d)) + 2 * bits(c & b)) % 4
    assert exponent in (0, 2), 'Only commuting Hermitian products have real signs'
    return 1 if exponent == 0 else -1


def contexts(points):
    ordered = sorted(points)
    triples = []
    for i, u in enumerate(ordered):
        for v in ordered[i + 1:]:
            w = u ^ v
            if w > v and w in points and symplectic(u, v) == 0:
                triples.append((u, v, w, product_sign(u, v)))
    return triples


def score(triples, negative):
    products = [sign * (-1 if sum(label in negative for label in (u, v, w)) % 2 else 1)
                for u, v, w, sign in triples]
    return {'contexts': len(products), 'violated': products.count(-1),
            'satisfied': products.count(1), 'signed_score': sum(products),
            'trace_cube_from_score': 6 * 16 * sum(products)}


def main():
    quadric = {v for v in range(1, 256) if bits((v & 15) & (v >> 4)) % 2 == 0}
    section = {v for v in quadric if symplectic(v, 128) == 0}
    full, induced = contexts(quadric), contexts(section)
    outside = [line for line in full if not set(line[:3]) <= section]
    assert (len(quadric), len(section), len(quadric - section)) == (135, 71, 64)
    assert (len(full), len(induced), len(outside)) == (1575, 455, 1120)
    assert all(sum(v in section for v in line[:3]) == 1 for line in outside)
    witnesses = {'A': {48, 102, 176, 230}, 'B': {87, 144, 176, 215}}
    results = {}
    for name, negative in witnesses.items():
        assert negative <= section
        results[name] = score(induced, negative)
        assert results[name]['violated'] == 132
        assert results[name]['signed_score'] == 191
        assert results[name]['trace_cube_from_score'] == 18336
    mutation = score(induced, witnesses['A'] ^ {min(section)})
    assert mutation['violated'] != 132, 'Chosen sign mutation must break the claimed section score'
    report = {'status': 'pass', 'arithmetic': 'Integer Pauli-label phases; no numerical eigensolver',
              'quadric_points': len(quadric), 'quadric_contexts': len(full),
              'section_points': len(section), 'section_contexts': len(induced),
              'outside_points': len(quadric - section), 'outside_contexts': len(outside),
              'witnesses': results, 'negative_control': {'flipped_label': min(section), **mutation},
              'scope': 'Exact executable check of section violations and the trace-score identity; not a Lean specialization or a binary completion optimum.'}
    (ROOT / 'results/unified-section-score.json').write_bytes((json.dumps(report, indent=2) + '\n').encode('utf-8'))
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()

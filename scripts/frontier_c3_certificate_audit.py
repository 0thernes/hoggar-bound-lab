"""Audit the literal Lean data against the paper's four-negative-word witnesses.

This is a data/geometry audit, not a replacement for compiling the Lean proof.
All validity checks use explicit exceptions and all certificate products use
Python's arbitrary-precision integers. Literal Pauli tensor entries are exactly
representable in complex128 because they are only 0, +/-1 and +/-i.
"""
from pathlib import Path
import hashlib
import json
import re
import numpy as np
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def literal_pauli(v):
    one = {(0, 0): [[1, 0], [0, 1]], (1, 0): [[0, 1], [1, 0]],
           (0, 1): [[1, 0], [0, -1]], (1, 1): [[0, -1j], [1j, 0]]}
    out = np.array([[1]], dtype=complex)
    for j in reversed(range(4)):
        out = np.kron(out, one[((v & 15) >> j & 1, (v >> 4) >> j & 1)])
    require(np.isin(out, [0, 1, -1, 1j, -1j]).all(), 'Unexpected Pauli entry')
    return out


def main():
    names = ['lean/HoggarBound/C3Data.lean', 'lean/HoggarBound/C3Geometry.lean',
             'lean/HoggarBound/C3Certificate.lean', 'paper/c3-spectral-counterexample.md',
             'lean/HoggarBound/C3Theorem.lean']
    sources = {name: (ROOT / name).read_bytes() for name in names}
    lean = sources[names[0]].decode('utf8')
    geometry = sources[names[1]].decode('utf8')
    paper = sources[names[3]].decode('utf8')
    require('\ufffd' not in paper, 'Paper contains Unicode replacement characters')
    require(not any(ord(c) < 32 and c not in '\n\r\t' for c in paper),
            'Paper contains unexpected control characters')

    def matrix(name, n, text=lean):
        match = re.search(r'def ' + name + r'\s*:.*?:=\s*!!\[(.*?)\]', text, re.S)
        require(match is not None, 'Missing Lean matrix ' + name)
        rows = [[int(x.strip()) for x in row.strip().split(',')]
                for row in match.group(1).strip().split(';')]
        require(len(rows) == n and all(len(row) == n for row in rows),
                'Wrong dimensions for ' + name)
        return np.array(rows, dtype=object)

    carriers = [matrix('carrierA', 16), matrix('carrierB', 16)]
    completions = [matrix('completionA', 64), matrix('completionB', 64)]
    certificate = sources['lean/HoggarBound/C3Certificate.lean'].decode('utf8')
    for suffix, completion in zip(['A','B'], completions):
        square = matrix('completionSquare'+suffix,64,certificate)
        require(np.array_equal(completion @ completion,square),
                'Incorrect intermediate Lean square '+suffix)
    intertwiner = matrix('intertwiner', 16)
    inverse = matrix('inverseNumerator', 16)
    match = re.search(r'def outsideLabel.*?:= !\[(.*?)\]', lean, re.S)
    require(match is not None, 'Missing outside-label vector')
    labels = [int(x.strip()) for x in match.group(1).split(',')]

    pauli = [literal_pauli(v) for v in range(256)]
    real = [v for v in range(1, 256) if not pauli[v].imag.any()]
    section = [v for v in real if np.array_equal(pauli[v] @ pauli[128], pauli[128] @ pauli[v])]
    outside = [v for v in real if v not in section]
    require((len(real), len(section), len(outside)) == (135, 71, 64), 'Wrong geometry sizes')
    require(labels == outside, 'Lean outside-label vector differs from the full sorted geometry')
    integer_pauli = {v: np.array([[int(x.real) for x in row] for row in pauli[v]], dtype=object)
                     for v in real}

    # Audit the entry formula used by the geometry bridge against literal
    # tensor products, including all real points, not merely the two carriers.
    popcount = lambda x: bin(x).count('1')
    for v in real:
        a, c = v & 15, v >> 4
        coded = np.array([[(-1) ** (popcount(a & c) // 2 + popcount(c & j))
                           if i == j ^ a else 0 for j in range(16)] for i in range(16)], dtype=object)
        require(np.array_equal(coded, integer_pauli[v]), 'Pauli entry convention mismatch')

    negatives = [[48, 102, 176, 230], [87, 144, 176, 215]]
    records = []
    x = sp.Symbol('x')
    for variant, negative in enumerate(negatives):
        require(set(negative) <= set(section), 'Negative label lies outside the section')
        name = 'signA' if variant == 0 else 'signB'
        sign_match = re.search(r'def ' + name + r'.*?\(\{([^}]+)\}', geometry)
        require(sign_match is not None, 'Missing explicit Lean sign definition')
        require([int(z.strip()) for z in sign_match.group(1).split(',')] == negative,
                'Lean sign definition differs from the paper witness')
        require(', '.join(map(str, negative)) in paper, 'Paper numeric witness table changed')
        sign = {v: -1 if v in negative else 1 for v in section}
        expected_carrier = sum((sign[v] * integer_pauli[v] for v in section),
                               np.zeros((16, 16), dtype=object))
        require(np.array_equal(expected_carrier, carriers[variant]), 'Lean carrier data disagree with signed Pauli sum')
        completion = np.zeros((64, 64), dtype=object)
        contexts = 0
        for i, u in enumerate(outside):
            for j in range(i + 1, 64):
                v = outside[j]
                s = u ^ v
                if s not in sign:
                    continue
                uv = integer_pauli[u] @ integer_pauli[v]
                if not np.array_equal(uv, integer_pauli[v] @ integer_pauli[u]):
                    continue
                if np.array_equal(uv, integer_pauli[s]):
                    context_sign = 1
                elif np.array_equal(uv, -integer_pauli[s]):
                    context_sign = -1
                else:
                    raise ValueError('Commuting Pauli context has no signed-identity product')
                completion[i, j] = completion[j, i] = sign[s] * context_sign
                contexts += 1
        require(contexts == 1120, 'Wrong outside-context count')
        require(np.array_equal(completion, completions[variant]),
                'Lean completion data disagree with literal signed contexts')
        cube = int(np.trace(completion @ completion @ completion))
        require(cube == [14976, 15360][variant], 'Wrong cubic trace')
        polynomial = [int(c) for c in sp.Matrix(expected_carrier.tolist()).charpoly(x).all_coeffs()]
        records.append({'negative_labels': negative, 'outside_contexts': contexts,
                        'completion_trace_cube': cube, 'carrier_charpoly': polynomial})
    require(records[0]['carrier_charpoly'] == records[1]['carrier_charpoly'], 'Carriers are not cospectral')
    expected_polynomial = (x - 3) ** 2 * (x + 1) ** 8 * (x + 5) ** 2 * (x + 13) * (x ** 3 - 25 * x ** 2 - 133 * x + 1621)
    require(records[0]['carrier_charpoly'] == [int(c) for c in sp.Poly(expected_polynomial, x).all_coeffs()],
            'Common carrier polynomial differs from the printed factorization')
    require(np.array_equal(carriers[0] @ intertwiner, intertwiner @ carriers[1]), 'Intertwining fails')
    identity = 46656 * np.eye(16, dtype=object)
    require(np.array_equal(intertwiner @ inverse, identity), 'Right inverse fails')
    require(np.array_equal(inverse @ intertwiner, identity), 'Left inverse fails')
    report = {'status': 'pass', 'scope': 'Exact data and geometric-convention audit; Lean compilation is a separate check',
              'checks': ['All 135 real Pauli entry formulas agree with literal tensors',
                         'All 64 outside labels agree, in order',
                         'Both Lean carriers equal the fixed signed Pauli sums',
                         'Both Lean completions equal all 1120 literal signed contexts',
                         'Both intermediate Lean matrix squares equal exact integer products',
                         'Exact characteristic polynomials, cubic traces, intertwiner and both inverse identities'],
              'runs': records,
              'source_sha256': {name: hashlib.sha256(data).hexdigest() for name, data in sources.items()},
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'arithmetic': 'Python arbitrary-precision integers for every certificate product; exact literal entries 0,+/-1,+/-i during tensor construction'}
    (ROOT / 'results/frontier-c3-certificate-audit.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()

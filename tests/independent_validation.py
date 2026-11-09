"""Independent matrix-level validation of the contextuality artifact.

This checker builds tensor products of literal 2x2 Pauli matrices. It does not
import or translate the C engine's bit-phase formula. Random checks supplement,
and do not replace, the Lean proof. Run from any directory with Python + NumPy.
"""
from pathlib import Path
import collections
import hashlib
import itertools
import json
import math
import platform
import subprocess
import sys

import numpy as np

if sys.flags.optimize:
    raise RuntimeError('Run this scientific checker without -O: its assertions must be enabled.')

ROOT = Path(__file__).resolve().parents[1]
I = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Z = np.diag([1, -1]).astype(complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
LOCAL = [I, X, Z, Y]  # code x + 2*z
MUL = {}
for a, b in itertools.product(range(4), repeat=2):
    prod = LOCAL[a] @ LOCAL[b]
    for c in range(4):
        coeff = np.trace(LOCAL[c].conj().T @ prod) / 2
        if abs(coeff) > 0.5:
            MUL[a, b] = c, coeff


def codes(n, v):
    return tuple(((v >> j) & 1) + 2 * ((v >> (n + j)) & 1) for j in range(n))


def matrices(n):
    out = []
    for v in range(4**n):
        p = np.ones((1, 1), dtype=complex)
        for c in reversed(codes(n, v)):
            p = np.kron(p, LOCAL[c])
        out.append(p)
    return np.asarray(out)


def geometry(n, kind):
    words = [codes(n, v) for v in range(4**n)]
    def member(v):
        if not v:
            return False
        if kind == 'f':
            return True
        parity = words[v].count(3) % 2
        if kind == 'h':
            return parity == 0
        return (parity + (words[v][-1] in (1, 2))) % 2 == 0
    points = [v for v in range(1, 4**n) if member(v)]
    pointset = set(points)
    lines = []
    for a, u in enumerate(points):
        for v in points[a+1:]:
            sign = 1 + 0j
            w = 0
            for j, (cu, cv) in enumerate(zip(words[u], words[v])):
                cw, coeff = MUL[cu, cv]
                sign *= coeff
                w += (cw & 1) * (2**j) + (cw >> 1) * (2**(n+j))
            if w > v and w in pointset and sign.imag == 0:
                lines.append((u, v, w, int(sign.real)))
    return points, lines


def degree(lines, signs):
    return int(sum(signs[u] * signs[v] * signs[w] != s for u, v, w, s in lines))


def exact_bound(points, lines, effective_dimension):
    d = effective_dimension
    if d < 2 or not lines:
        return 0
    square_numerator = (d-2)**2 * points**3
    square_denominator = 36 * (d-1)
    beta = math.isqrt(square_numerator // square_denominator)
    if (beta - lines) % 2:
        beta -= 1
    return max(0, (lines - beta)//2)


def load_witness(path):
    n, kind, claimed, hexdata = path.read_text().split()
    n, claimed = int(n), int(claimed)
    assert len(hexdata) == 4**n//4
    bits = int(hexdata, 16)
    signs = np.array([-1 if (bits >> v) & 1 else 1 for v in range(4**n)], dtype=int)
    return n, kind, claimed, signs


def graph_statistics(points, violated):
    graph = {('p', p): [] for p in points}
    for i, line in enumerate(violated):
        node = ('l', i)
        graph[node] = [('p', p) for p in line[:3]]
        for p in line[:3]:
            graph['p', p].append(node)
    diameter, girth = 0, len(graph)+1
    for source in graph:
        distances, parent = {source: 0}, {source: None}
        queue = collections.deque([source])
        while queue:
            u = queue.popleft()
            for v in graph[u]:
                if v not in distances:
                    distances[v] = distances[u]+1
                    parent[v] = u
                    queue.append(v)
                elif parent[u] != v:
                    girth = min(girth, distances[u]+distances[v]+1)
        assert len(distances) == len(graph)
        diameter = max(diameter, max(distances.values()))
    return {'vertices': len(graph), 'edges': sum(map(len, graph.values()))//2,
            'regular_degree': sorted(set(map(len, graph.values()))),
            'diameter': diameter, 'girth': girth}


def main():
    engine = Path(sys.argv[1]) if len(sys.argv)>1 else ROOT/'build'/'hoggar.exe'
    report = {'checker': 'literal tensor-product Pauli matrices', 'python': platform.python_version(),
              'numpy': np.__version__, 'geometries': [], 'witnesses': [], 'checks': {}}
    geometries = {}
    for n in range(2, 6):
        for kind in 'fhe':
            pts, lines = geometry(n, kind)
            geometries[n, kind] = pts, lines
            out = subprocess.run([str(engine), 'lines', str(n), kind], text=True,
                                 capture_output=True, check=True).stdout
            engine_lines = [tuple(map(int, row.split())) for row in out.splitlines() if not row.startswith('#')]
            assert lines == engine_lines, (n, kind, 'C geometry disagrees with tensor multiplication')
            report['geometries'].append({'qubits': n, 'family': kind, 'points': len(pts),
                'lines': len(lines), 'lower_bound': exact_bound(len(pts), len(lines), 2**n if kind != 'e' else 2**(n-1)),
                'formal_scope': 'elliptic Kramers refinement not Lean-checked' if kind == 'e' else 'general cubic theorem'})
    report['checks']['all_C_contexts_match_independent_tensor_algebra'] = True
    for path in sorted((ROOT/'data'/'witness').glob('*.txt')):
        n, kind, claimed, signs = load_witness(path)
        if (n,kind) not in geometries:
            continue
        pts, lines = geometries[n,kind]
        actual = degree(lines, signs)
        assert actual == claimed, (path.name, claimed, actual)
        report['witnesses'].append({'file': str(path.relative_to(ROOT)).replace('\\','/'),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'violations': actual,
            'contexts': len(lines), 'verified': True})
    # Exact Gaussian-integer Hoggar vector: all operations below are integral
    # before the final division by the exactly represented squared norm 12.
    p3 = matrices(3)
    raw = np.array([-1+2j] + [1]*7)
    numerator = np.einsum('i,vij,j->v', raw.conj(), p3, raw)
    assert numerator[0] == 12 and np.all(numerator[1:].imag == 0)
    assert np.all(abs(numerator[1:]) == 4)
    signs = np.where(numerator.real < 0, -1, 1)
    pts, lines = geometries[3,'f']
    assert degree(lines, signs) == 63
    A = np.einsum('v,vij->ij', signs[1:], p3[1:])
    assert np.trace(A) == 0 and np.trace(A@A) == 504 and np.trace(A@A@A) == 9072
    spectrum = np.linalg.eigvalsh(A)
    assert np.allclose(spectrum, [-3]*7+[21])
    violated = [line for line in lines if signs[line[0]]*signs[line[1]]*signs[line[2]] != line[3]]
    graph = graph_statistics(pts, violated)
    assert graph == {'vertices':126, 'edges':189, 'regular_degree':[3], 'diameter':6, 'girth':12}
    report['hoggar'] = {'norm_squared':12, 'Pauli_numerator_modulus':4, 'violations':63,
        'trace_A2':504, 'trace_A3':9072, 'spectrum':spectrum.tolist(), 'incidence_graph':graph}
    # Realification checks the 4-qubit real quadric upper bound independently.
    p4 = matrices(4)
    real_raw = np.concatenate([raw.real,raw.imag]).astype(complex)
    pnums = np.einsum('i,vij,j->v', real_raw.conj(),p4,real_raw)
    rpts, rlines = geometries[4,'h']
    assert np.all(abs(pnums[rpts]) == 4)
    assert all(pnums[v] == 0 for v in range(1,256) if v not in set(rpts))
    rsigns = np.where(pnums.real < 0,-1,1)
    assert degree(rlines,rsigns) == 315
    report['realified_hoggar'] = {'points':135,'contexts':1575,'violations':315,'expectation_modulus':'1/3'}
    # Random sparse supports test the actual general theorem and trace bridge.
    rng = np.random.default_rng(20261109)
    max_error = 0.0
    for trial in range(120):
        n = 3 if trial < 80 else 4
        ops = p3 if n == 3 else p4
        allpts, alllines = geometries[n,'f']
        support = set(v for v in allpts if rng.random() < 0.55)
        ss = np.zeros(4**n,dtype=int)
        for v in support:
            ss[v] = rng.choice([-1,1])
        contained = [l for l in alllines if set(l[:3]) <= support]
        beta = len(contained)-2*degree(contained,ss)
        op = np.einsum('v,vij->ij',ss,ops)
        error = abs(np.trace(op@op@op)-6*(2**n)*beta)
        max_error = max(max_error,float(error))
        assert error == 0
        assert beta <= (2**n-2)*len(support)**1.5/(6*math.sqrt(2**n-1))+1e-9
    report['checks']['random_sparse_supports'] = 120
    report['checks']['trace_identity_max_error'] = max_error
    # Positive falsification controls: a deliberate context-sign error breaks
    # the trace bridge; a fake 4743 target lies below the exact rounded bound.
    beta = len(lines)-2*degree(lines,signs)
    mutated = list(lines)
    u,v,w,s = mutated[0]
    mutated[0] = (u,v,w,-s)
    bad_beta = len(mutated)-2*degree(mutated,signs)
    assert bad_beta != beta and np.trace(A@A@A) != 48*bad_beta
    assert exact_bound(527,23715,32) == 6426 > 4743
    report['checks']['sign_mutation_detected'] = True
    report['checks']['candidate_4743_excluded_by_integer_bound'] = True
    report['source_sha256'] = {name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
        for name in ['src/hoggar.c','tests/independent_validation.py']}
    report['status'] = 'passed'
    dest = ROOT/'results'/'independent_validation.json'
    dest.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'passed','geometries':len(geometries),
        'contexts_compared':sum(len(v[1]) for v in geometries.values()),
        'witnesses':len(report['witnesses']),'random_sparse_supports':120,
        'hoggar_incidence_graph':graph,'output':str(dest)},indent=2))


if __name__ == '__main__':
    main()

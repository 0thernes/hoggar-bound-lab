"""Exact independent verification of the four-qubit C3 carrier collision.

Constructs all operators by Kronecker products of literal 2x2 matrices,
independently of the search's bit-action construction. No floating-point
eigenvalues are used in this verifier. Python/SymPy integer arithmetic checks
the carrier polynomial; integral Pauli coordinates check the completion map.
"""
from pathlib import Path
import hashlib
import json
import numpy as np
import sympy as sp

if not __debug__:
    raise RuntimeError('Verification requires assertions: run Python without -O')

ROOT=Path(__file__).resolve().parents[1]

def all_paulis(n):
    I=np.array([[1,0],[0,1]],dtype=complex)
    X=np.array([[0,1],[1,0]],dtype=complex)
    Z=np.array([[1,0],[0,-1]],dtype=complex)
    Y=np.array([[0,-1j],[1j,0]],dtype=complex)
    one={(0,0):I,(1,0):X,(0,1):Z,(1,1):Y}
    out=[]
    for v in range(1<<(2*n)):
        a,c=v&((1<<n)-1),v>>n
        p=np.array([[1]],dtype=complex)
        for j in reversed(range(n)):p=np.kron(p,one[(a>>j&1,c>>j&1)])
        # Every entry is in {0,+1,-1,+i,-i}; these are represented exactly.
        out.append(p)
    return np.array(out)

def main():
    p=all_paulis(4);d=128
    real=[v for v in range(1,256) if not np.any(p[v].imag)]
    section=[v for v in real if np.array_equal(p[v]@p[d],p[d]@p[v])]
    outside=[v for v in real if v not in section]
    assert len(real)==135 and len(section)==71 and len(outside)==64
    embed=lambda v:(v&7)+((v>>3)<<4)
    oldreal=[v for v in range(1,64) if not np.any(all_paulis(3)[v].imag)]
    assert set(section)=={d}|{embed(v) for v in oldreal}|{d^embed(v) for v in oldreal}
    x=sp.Symbol('x');runs=[];completion_certificates=[]
    for variant in [0,1]:
        f={v:1 for v in section}
        if variant==0:
            for v in [24,54]:f[embed(v)]=f[d^embed(v)]=-1
        else:
            for v in [8,24]:f[d^embed(v)]=-1
            f[embed(47)]=f[d^embed(47)]=-1
        a=sum(f[v]*p[v].real.astype(np.int64) for v in section)
        assert np.array_equal(a,a.T) and np.trace(a)==0
        carrier=sp.Matrix(a.tolist()).charpoly(x).as_expr()
        op=p[outside].real.astype(np.int64)
        numerator=a@op+op@a
        assert np.all(numerator%2==0)
        jordan=numerator//2
        coord_numer=op.reshape(64,256)@jordan.reshape(64,256).T
        assert np.all(coord_numer%16==0)
        completion=coord_numer//16
        # Reconstruct every image from its Pauli coordinates: no projection
        # error can be hidden in the trace computation.
        assert np.array_equal(np.einsum('ij,ikl->jkl',completion,op),jordan)
        assert np.array_equal(completion,completion.T)
        basis=op[:,:8,8:].reshape(64,64).T
        assert np.array_equal(basis.T@basis,8*np.eye(64,dtype=np.int64))
        assert np.array_equal(basis@basis.T,8*np.eye(64,dtype=np.int64))
        kron_numer=np.kron(a[:8,:8],np.eye(8,dtype=np.int64))+np.kron(np.eye(8,dtype=np.int64),a[8:,8:].T)
        assert np.all(kron_numer%2==0)
        kron_jordan=kron_numer//2
        assert np.array_equal(basis@completion,kron_jordan@basis)
        completion_certificates.append({'outside_labels':outside,
            'completion_matrix':completion.tolist(),'kron_jordan':kron_jordan.tolist(),
            'basis_T':basis.tolist(),'inverse_scale':8,
            'identities':['T transpose(T) = transpose(T) T = 8 I',
                          'T completion_matrix = kron_jordan T'],
            'vectorization':'row-major top-right 8x8 block of each outside Pauli is a column of T'})
        trace3=int(np.trace(completion@completion@completion))
        coeffs=[int(c) for c in sp.Poly(carrier,x).all_coeffs()]
        runs.append({'negative_section_labels':sorted(v for v in f if f[v]<0),
                     'carrier_charpoly':coeffs,'carrier_factorization':str(sp.factor(carrier)),
                     'plus_factorization':str(sp.factor(sp.Matrix(a[:8,:8].tolist()).charpoly(x).as_expr())),
                     'minus_factorization':str(sp.factor(sp.Matrix(a[8:,8:].tolist()).charpoly(x).as_expr())),
                     'completion_dimension':64,'completion_trace_cube':trace3,
                     'completion_trace_square':int(np.trace(completion@completion)),
                     'completion_entries':sorted(set(int(v) for v in completion.flat))})
    assert runs[0]['carrier_charpoly']==runs[1]['carrier_charpoly']
    assert [r['completion_trace_cube'] for r in runs]==[14976,15360]
    report={'status':'pass','N':4,'type':'hyperbolic Q+(7,2)','case':'C3, isotropic d=Z_top',
            'section_points':71,'outside_points':64,'runs':runs,
            'conclusion':'Equal carrier characteristic polynomial, unequal completion spectra',
            'method':'Exact integer Pauli matrices; SymPy polynomial; direct Jordan action',
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'results/frontier-c3-n4-verification.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'results/frontier-c3-n4-completions.json').write_text(json.dumps(completion_certificates,indent=1)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()

"""Regenerate a C3 cospectral carrier collision exactly after numeric screening.

An exploratory experiment, not an exhaustive classification. N=3 is prior
existence reported in Jonah J3; a found pair is a reproducible witness only.
"""
from pathlib import Path
import json
import itertools
import numpy as np
import sympy as sp

if not __debug__:
    raise RuntimeError('Verification requires assertions: run Python without -O')

ROOT=Path(__file__).resolve().parents[1]

def paulis(n, real_only=True):
    D=1<<n
    ans=[]
    for v in range(1,D*D):
        a,c=v&(D-1),v>>n
        k=(a&c).bit_count() if hasattr(int,'bit_count') else bin(a&c).count('1')
        if real_only and k%2: continue
        p=np.zeros((D,D),dtype=complex)
        for x in range(D):
            p[x^a,x]=(1j**k)*(-1)**(bin(c&x).count('1'))
        ans.append((v,p.real.astype(np.int64) if real_only else p))
    return ans

def charpoly(a):
    return [int(x) for x in sp.Matrix(a.tolist()).charpoly().all_coeffs()]

def describe(i, ps):
    states=np.array([(i>>(2*j))&3 for j in range(len(ps))])
    plus=np.eye(ps[0][1].shape[0],dtype=np.int64)
    minus=-plus.copy()
    for state,(_,p) in zip(states,ps):
        if state<2: plus+=(2 if state==0 else -2)*p
        else: minus+=(2 if state==2 else -2)*p
    # a=(coefficient_plus+coefficient_minus)/2;
    # b=(coefficient_plus-coefficient_minus)/2.
    signs={str(v):{'I':1 if s%2==0 else -1,
                   'Z':(1 if s%2==0 else -1)*(1 if s<2 else -1)}
           for s,(v,_) in zip(states,ps)}
    d=len(plus)
    comp=np.kron(plus,np.eye(d,dtype=np.int64))+np.kron(np.eye(d,dtype=np.int64),minus)
    assert np.all(comp%2==0)
    comp//=2
    return {'index':int(i),'alpha':1,'base_pauli_labels':[v for v,_ in ps],
            'signs':signs,'plus':plus.tolist(),'minus':minus.tolist(),
            'carrier_charpoly': [int(x) for x in sp.polys.polytools.mul(
                sp.Poly.from_list(charpoly(plus),sp.Symbol('x')),
                sp.Poly.from_list(charpoly(minus),sp.Symbol('x'))).all_coeffs()],
            'plus_charpoly':charpoly(plus),'minus_charpoly':charpoly(minus),
            'completion_charpoly':charpoly(comp),
            'completion_trace_cube':int(np.trace(comp@comp@comp))}

def main():
    ps=paulis(2)
    mats=np.array([p for v,p in ps])
    seen={}
    for start in range(0,1<<(2*len(ps)),4096):
        indices=np.arange(start,min(start+4096,1<<(2*len(ps))),dtype=np.uint64)
        digits=((indices[:,None]>>(2*np.arange(len(ps),dtype=np.uint64)))&3).astype(int)
        plus=np.einsum('bi,ijk->bjk',np.where(digits<2,np.where(digits%2==0,2,-2),0),mats)+np.eye(4,dtype=np.int64)
        minus=np.einsum('bi,ijk->bjk',np.where(digits>=2,np.where(digits%2==0,2,-2),0),mats)-np.eye(4,dtype=np.int64)
        ep=np.linalg.eigvalsh(plus);em=np.linalg.eigvalsh(minus)
        union=np.sort(np.concatenate([ep,em],axis=1),axis=1)
        partition=np.sum(digits<2,axis=1)
        for offset in range(len(indices)):
            key=tuple(np.round(union[offset],7))
            i=int(indices[offset]); k=int(partition[offset])
            if key in seen and seen[key][1]!=k:
                a=describe(seen[key][0],ps);b=describe(i,ps)
                if a['carrier_charpoly']==b['carrier_charpoly'] and a['completion_charpoly']!=b['completion_charpoly']:
                    report={'status':'exact collision found','N':3,'searched_until':i,
                            'meaning':'Reproduces a prior reported existence; not claimed novel',
                            'pair':[a,b]}
                    (ROOT/'results/frontier-c3-pair.json').write_text(json.dumps(report,indent=2)+'\n')
                    print(json.dumps(report,indent=2))
                    return
            elif key not in seen: seen[key]=(i,k)
        print('screened',start+len(indices),'spectra',len(seen),flush=True)
    raise RuntimeError('No partition-count collision found')

if __name__=='__main__':main()

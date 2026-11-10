"""Screen restricted four-qubit C3 carrier families; certify any pair exactly."""
from pathlib import Path
import json
import numpy as np
import sympy as sp
from frontier_c3_search import paulis, charpoly
if not __debug__:
    raise RuntimeError('Verification requires assertions: run Python without -O')
ROOT=Path(__file__).resolve().parents[1]

def certify(plus,minus,labels,digits):
    x=sp.Symbol('x')
    cp=(sp.Poly.from_list(charpoly(plus),x)*sp.Poly.from_list(charpoly(minus),x)).all_coeffs()
    d=len(plus)
    p2=int(np.trace(plus@plus));m2=int(np.trace(minus@minus))
    p3=int(np.trace(plus@plus@plus));m3=int(np.trace(minus@minus@minus))
    numerator=d*(p3+m3)+3*int(np.trace(minus))*p2+3*int(np.trace(plus))*m2
    assert numerator%8==0
    return {'alpha':1,'labels':labels,'states':digits.tolist(),'plus':plus.tolist(),'minus':minus.tolist(),
            'carrier_charpoly':[int(c) for c in cp],'completion_trace_cube':numerator//8,
            'plus_charpoly':charpoly(plus),'minus_charpoly':charpoly(minus)}

def main():
    n=3;d=1<<n;ps=paulis(n);labels=[v for v,p in ps];mats=np.array([p for v,p in ps])
    rng=np.random.default_rng(42513)
    families=[list(range(8)),[labels.index(v) for v in [1,2,3,8,16,24,27,40]]]
    families += [[int(v) for v in rng.choice(35,8,replace=False)] for _ in range(8)]
    reports=[]
    for family, positions in enumerate(families):
        seen={}
        for start in range(0,4**len(positions),4096):
            indices=np.arange(start,min(start+4096,4**len(positions)),dtype=np.uint64)
            digits=np.zeros((len(indices),len(ps)),dtype=np.int8)
            digits[:,positions]=((indices[:,None]>>(2*np.arange(len(positions),dtype=np.uint64)))&3).astype(int)
            plus=np.einsum('bi,ijk->bjk',np.where(digits<2,np.where(digits%2==0,2,-2),0),mats)+np.eye(d,dtype=np.int64)
            minus=np.einsum('bi,ijk->bjk',np.where(digits>=2,np.where(digits%2==0,2,-2),0),mats)-np.eye(d,dtype=np.int64)
            union=np.sort(np.concatenate([np.linalg.eigvalsh(plus),np.linalg.eigvalsh(minus)],axis=1),axis=1)
            partition=np.sum(digits<2,axis=1)
            for offset in range(len(indices)):
                key=tuple(np.round(union[offset],6));i=int(indices[offset]);k=int(partition[offset])
                if key in seen and seen[key][0]!=k:
                    _,p0,m0,s0=seen[key]
                    a=certify(p0,m0,labels,s0);b=certify(plus[offset],minus[offset],labels,digits[offset])
                    if a['carrier_charpoly']==b['carrier_charpoly'] and a['completion_trace_cube']!=b['completion_trace_cube']:
                        report={'N':4,'status':'exact collision found','family':family,'positions':positions,
                                'candidate':i,'pair':[a,b]}
                        (ROOT/'results/frontier-c3-n4-pair.json').write_text(json.dumps(report,indent=2)+'\n')
                        print(json.dumps(report,indent=2),flush=True);return
                elif key not in seen:
                    seen[key]=(k,plus[offset].copy(),minus[offset].copy(),digits[offset].copy())
        reports.append({'family':family,'positions':positions,'screened':4**len(positions),'unique_spectra':len(seen)})
        print(reports[-1],flush=True)
    (ROOT/'results/frontier-c3-n4-search.json').write_text(json.dumps({'status':'no collision in restricted families','families':reports},indent=2)+'\n')

if __name__=='__main__':main()

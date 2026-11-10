"""Test the n4 witness's sparse-defect construction in a higher dimension.

Family A: all real Pauli directions in B+, with two negative coefficients.
Family B: two diagonal Z directions in B-, one negative coefficient in B+.
Numeric eigenvalues screen; every reported collision has exact polynomials.
"""
from pathlib import Path
import itertools
import json
import sys
import numpy as np
from frontier_c3_search import paulis
from frontier_c3_extend import certify
if not __debug__:
    raise RuntimeError('Verification requires assertions: run Python without -O')
ROOT=Path(__file__).resolve().parents[1]

def main():
    n=int(sys.argv[1]) if len(sys.argv)>1 else 4
    ps=paulis(n);labels=[v for v,p in ps];mats=np.array([p for v,p in ps]);D=1<<n
    base=2*mats.sum(axis=0)+np.eye(D,dtype=np.int64)
    minus=-np.eye(D,dtype=np.int64)
    seen={};count_a=0;count_b=0
    for i in range(len(ps)):
        js=np.arange(i+1,len(ps))
        if not len(js):continue
        plus=base-4*mats[i]-4*mats[js]
        spectra=np.linalg.eigvalsh(plus)
        for row,j in zip(spectra,js):
            key=tuple(np.round(np.sort(np.r_[row,-np.ones(D)]),6))
            seen.setdefault(key,(i,int(j)))
            count_a+=1
    print('A screened',count_a,'unique spectra',len(seen),flush=True)
    diagonals=[i for i,v in enumerate(labels) if (v&(D-1))==0]
    for i,j in itertools.combinations(diagonals,2):
        ks=[k for k in range(len(ps)) if k not in [i,j]]
        plus=base-2*mats[i]-2*mats[j]-4*mats[ks]
        mb=minus+2*mats[i]+2*mats[j]
        me=np.linalg.eigvalsh(mb)
        spectra=np.linalg.eigvalsh(plus)
        for row,k in zip(spectra,ks):
            count_b+=1
            key=tuple(np.round(np.sort(np.r_[row,me]),6))
            if key in seen:
                ia,ja=seen[key]
                sa=np.zeros(len(ps),dtype=int);sa[[ia,ja]]=1
                sb=np.zeros(len(ps),dtype=int);sb[[i,j]]=2;sb[k]=1
                ca=certify(base-4*mats[ia]-4*mats[ja],minus,labels,sa)
                cb=certify(plus[ks.index(k)],mb,labels,sb)
                if ca['carrier_charpoly']==cb['carrier_charpoly'] and ca['completion_trace_cube']!=cb['completion_trace_cube']:
                    report={'status':'exact collision found','N':n+1,'A_screened':count_a,'B_screened':count_b,
                            'first_negative_labels':[labels[ia],labels[ja]],
                            'second_minus_labels':[labels[i],labels[j]],'second_negative_label':labels[k],
                            'pair':[ca,cb]}
                    (ROOT/f'results/frontier-c3-n{n+1}-sparse-pair.json').write_text(json.dumps(report,indent=2)+'\n')
                    print({k:v for k,v in report.items() if k!='pair'},flush=True);return
    report={'status':'no collision in restricted sparse family','N':n+1,'A_screened':count_a,
            'A_unique_spectra':len(seen),'B_screened':count_b,
            'meaning':'Does not rule out collisions in the full sign-carrier space'}
    (ROOT/f'results/frontier-c3-n{n+1}-sparse-search.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report,flush=True)

if __name__=='__main__':main()

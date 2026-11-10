"""Build an exact rational conjugacy certificate for the n4 C3 carrier pair."""
from pathlib import Path
import json
import math
import functools
import sympy as s
if not __debug__:
    raise RuntimeError('Verification requires assertions: run Python without -O')
ROOT=Path(__file__).resolve().parents[1]

def lcm(x,y):return x*y//math.gcd(x,y)
def clear_denominators(m):
    d=functools.reduce(lcm,[int(x.q) for x in m],1)
    return m*d,d

def main():
    pair=json.loads((ROOT/'results/frontier-c3-n4-pair.json').read_text())['pair']
    matrices=[s.diag(s.Matrix(r['plus']),s.Matrix(r['minus'])) for r in pair]
    bases=[]
    for a in matrices:
        columns=[]
        for lam,count in [(-1,8),(3,2),(-5,2),(-13,1)]:
            basis=(a-lam*s.eye(16)).nullspace()
            assert len(basis)==count
            columns.extend(basis)
        cub=a**3-25*a**2-133*a+1621*s.eye(16)
        v=cub.nullspace()[0]
        columns.extend([v,a*v,a*a*v])
        q=s.Matrix.hstack(*columns)
        assert q.det()!=0
        bases.append(q)
    a,b=matrices;qa,qb=bases
    assert qa.inv()*a*qa==qb.inv()*b*qb
    m,dm=clear_denominators(qa*qb.inv())
    inv,di=clear_denominators(qb*qa.inv())
    assert a*m==m*b and m*inv==dm*di*s.eye(16) and inv*m==dm*di*s.eye(16)
    report={'status':'pass','dimension':16,'identity_scale':dm*di,
            'M':[[int(x) for x in row] for row in m.tolist()],
            'R':[[int(x) for x in row] for row in inv.tolist()],
            'A':[[int(x) for x in row] for row in a.tolist()],
            'B':[[int(x) for x in row] for row in b.tolist()],
            'identities':['A M = M B','M R = k I','R M = k I'],
            'nonzero_M_entries':sum(x!=0 for x in m),
            'max_abs_M':int(max(abs(x) for x in m)),
            'max_abs_R':int(max(abs(x) for x in inv))}
    (ROOT/'results/frontier-c3-n4-similarity.json').write_text(json.dumps(report,indent=2)+'\n')
    print({k:v for k,v in report.items() if k not in ['M','R','A','B']})

if __name__=='__main__':main()

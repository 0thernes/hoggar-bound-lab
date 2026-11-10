"""Bound every arithmetic value in the Eshkol C3 certificate using Python ints.

Matches the ordered dot-product/trace accumulations of frontier_c3_demo.py,
and checks the scalar operations in its block-Jordan cube formula. This
rules out signed-64-bit overflow in those exact-integer calculations.
"""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]

def integer_bounds(data):
    limits={}
    def record(name,value):
        if type(value) is not int:
            raise TypeError('Certificate arithmetic must use Python integers')
        limits[name]=max(limits.get(name,0),abs(value))
        return value
    for name in ['A','B','M','R']:
        if len(data[name])!=16 or any(len(row)!=16 for row in data[name]):
            raise ValueError('Expected 16x16 certificate matrices')
        for row in data[name]:
            for value in row:record('input',value)
    def multiply(name,a,b):
        n=len(a);out=[]
        for i in range(n):
            row=[]
            for j in range(n):
                acc=0
                for k in range(n):
                    product=record(name+' product',a[i][k]*b[k][j])
                    acc=record(name+' partial sum',acc+product)
                row.append(acc)
            out.append(row)
        return out
    def trace(name,a):
        acc=0
        for i in range(len(a)):acc=record(name+' trace partial',acc+a[i][i])
        return acc
    a,b,m,r=[data[k] for k in ['A','B','M','R']]
    if multiply('AM',a,m)!=multiply('MB',m,b):raise ValueError('Intertwining failed')
    identity=[[46656 if i==j else 0 for j in range(16)] for i in range(16)]
    if multiply('MR',m,r)!=identity or multiply('RM',r,m)!=identity:
        raise ValueError('Scaled inverse failed')
    cubes=[]
    for label,a in [('A',a),('B',b)]:
        p=[row[:8] for row in a[:8]];m=[row[8:] for row in a[8:]]
        p2=multiply(label+' p2',p,p);m2=multiply(label+' m2',m,m)
        p3=multiply(label+' p3',p,p2);m3=multiply(label+' m3',m,m2)
        tp=trace(label+' p',p);tm=trace(label+' m',m)
        tp2=trace(label+' p2',p2);tm2=trace(label+' m2',m2)
        tp3=trace(label+' p3',p3);tm3=trace(label+' m3',m3)
        s1=record(label+' trace cube sum',tp3+tm3)
        s2=record(label+' 8 cube sum',8*s1)
        c1=record(label+' square trace product1',tp2*tm)
        c2=record(label+' square trace product2',tp*tm2)
        c3=record(label+' cross sum',c1+c2)
        c4=record(label+' 3 cross sum',3*c3)
        numerator=record(label+' numerator',s2+c4)
        if numerator%8:raise ValueError('Nonintegral completion cube')
        cubes.append(numerator//8)
    if cubes!=[14976,15360]:raise ValueError('Wrong completion moments')
    # Index arithmetic: n<=16, flattened vector length<=256, and i*n+j<=255.
    limits['index arithmetic']=256
    limits['scaled identity comparison']=46656
    maximum=max(limits.values())
    if maximum>2**63-1:raise OverflowError('Signed 64-bit bound exceeded')
    return {'status':'pass','maximum_absolute_intermediate':maximum,
            'signed_64_bit_maximum':2**63-1,'bounds':limits,
            'completion_cubes':cubes,
            'scope':'Every product and ordered accumulation in the generated Eshkol certificate; arithmetic safety, not compiler correctness'}

def main():
    path=ROOT/'results/frontier-c3-n4-similarity.json'
    report=integer_bounds(json.loads(path.read_text()))
    report['certificate_sha256']=hashlib.sha256(path.read_bytes()).hexdigest()
    (ROOT/'results/frontier-c3-integer-bounds.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()

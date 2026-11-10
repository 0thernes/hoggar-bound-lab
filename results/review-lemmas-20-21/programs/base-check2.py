import numpy as np
from functools import reduce
X=np.array([[0,1],[1,0]],dtype=complex); Z=np.diag([1,-1]).astype(complex); I2=np.eye(2,dtype=complex)
Y=np.array([[0,-1j],[1j,0]])
def XZ(a,c,m):  # bit j -> qubit j, qubit 0 rightmost
    fs=[]
    for j in reversed(range(m)):
        f=I2
        if (a>>j)&1: f=X
        if (c>>j)&1: f=f@Z
        fs.append(f)
    return reduce(np.kron,fs)
def dot(a,c): return bin(a&c).count('1')
def eps(a,c,u,t):
    if a==0: return (-1)**dot(c,t)
    if dot(a,c)%2==0: return (-1)**dot(c,u[a])*(-1)**(dot(a,c)//2)
    return (-1)**dot(c,u[a])*(-1)**((dot(a,c)-1)//2)
def P(a,c,m): return (1j)**dot(a,c)*XZ(a,c,m)
def blocks(case,m,u,t,moved):
    # returns C,D for sigma and tau on block of size 2^(m) (C1) or 2^(m+1) (C5)
    out=[]
    for mv in (set(),moved):
        if case=='C1':
            k=2**m; C=np.eye(k,dtype=complex); D=-np.eye(k,dtype=complex)
            for a in range(2**m):
                for c in range(2**m):
                    if a==0 and c==0: continue
                    e=eps(a,c,u,t); M=e*P(a,c,m)
                    if a in mv: D+=2*M
                    else: C+=2*M
        else:  # C5: graph on m qubits, quaternion qubit 0 rightmost
            k=2**(m+1); C=np.eye(k,dtype=complex); D=-np.eye(k,dtype=complex)
            for a in range(2**m):
                for c in range(2**m):
                    if a==0 and c==0: continue
                    e=eps(a,c,u,t); Pp=P(a,c,m)
                    sig=[I2] if dot(a,c)%2==0 else [X,Y,Z]
                    for s in sig:
                        M=e*np.kron(Pp,s)
                        if a in mv: D+=2*M
                        else: C+=2*M
        out.append((C,D))
    return out,k
def tr(M,j): return np.trace(np.linalg.matrix_power(M,j)).real
def e8(C,D,k,kap): return kap/8*(k*tr(C,3)+3*tr(C,2)*tr(D,1)+3*tr(C,1)*tr(D,2)+k*tr(D,3))
def report(name,case,m,u,t,moved,kap):
    ((Cs,Ds),(Ct,Dt)),k=blocks(case,m,u,t,moved)
    for M in (Cs,Ds,Ct,Dt): assert np.allclose(M,M.conj().T)
    ss=np.sort(np.concatenate([np.linalg.eigvalsh(Cs),np.linalg.eigvalsh(Ds)]))
    st=np.sort(np.concatenate([np.linalg.eigvalsh(Ct),np.linalg.eigvalsh(Dt)]))
    r=int(round((np.count_nonzero(np.abs(Dt+np.eye(k))>1e-9))))
    print(name,'cospectral',np.allclose(ss,st),'diff',round(e8(Cs,Ds,k,kap)-e8(Ct,Dt,k,kap)),'k',k)
    return Cs
# C1 N=3 triangle
u={1:0,2:1,3:0}; Cs=report('C1 N=3','C1',2,u,2,{1,2,3},2)
# formula check C1: C=-I+2k|t><t|+k sum(E_a+iJ_a)
k=4; t=2; F=-np.eye(k)+2*k*np.outer(np.eye(k)[t],np.eye(k)[t]).astype(complex)
for a,ua in u.items():
    e=np.zeros((k,k),dtype=complex); e[ua^a,ua]=1; e[ua,ua^a]=1
    j=np.zeros((k,k),dtype=complex); j[ua^a,ua]=1; j[ua,ua^a]=-1
    F+=k*(e+1j*j)
print('C1 formula', np.allclose(Cs,F))
u4={1:0,2:4,3:4,4:2,5:2,6:2,7:2}
report('C1 N=4','C1',3,u4,2,{1},2)
report('C5 N=4','C5',2,u,2,{1,2,3},1)
report('C5 N=5','C5',3,u4,2,{1},1)
report('C3-like check N=4 via C1 code skipped','C1',3,u4,2,{1},2)

import numpy as np, itertools, random
I2=np.eye(2,dtype=complex); X=np.array([[0,1],[1,0]],dtype=complex)
Y=np.array([[0,-1j],[1j,0]]); Z=np.diag([1,-1]).astype(complex)
PA={'I':I2,'X':X,'Y':Y,'Z':Z}
def mat(w):  # w string, leftmost = qubit N-1
    m=np.array([[1]],dtype=complex)
    for ch in w: m=np.kron(m,PA[ch])
    return m
def ny(w): return w.count('Y')%2
def symp(u,v): return sum(1 for a,b in zip(u,v) if a!='I' and b!='I' and a!=b)%2
def run(N,case,seed=1):
    k=2**(N-1)
    words=[''.join(t) for t in itertools.product('IXYZ',repeat=N) if set(t)!={'I'}]
    if case=='C1': cw=None; Xs=words
    elif case=='C3': cw='I'*N; Xs=[w for w in words if ny(w)==0]
    else: cw='I'*(N-1)+'Y'; Xs=[w for w in words if (ny(w)+symp(cw,w))%2==0]
    d='Z'+'I'*(N-1)
    assert d in Xs
    H=[w for w in Xs if symp(w,d)==0]; O=[w for w in Xs if symp(w,d)==1]
    Ms=[mat(w)[:k,k:] for w in O]
    # check off-diagonal
    for w in O:
        m=mat(w); assert np.allclose(m[:k,:k],0) and np.allclose(m[k:,k:],0)
    R=np.array([np.concatenate([M.real.ravel(),M.imag.ravel()]) for M in Ms])
    rank=np.linalg.matrix_rank(R)
    res={'|O|':len(O),'k^2':k*k,'realrank':rank}
    if cw is not None:
        J=mat(cw)[:k,:k]; res['JJbar']=complex(np.round((J@J.conj())[0,0],9))
        assert np.allclose(J@J.conj(),res['JJbar']*np.eye(k))
        res['allfixed']=all(np.allclose(J@M.conj()@J,M) for M in Ms)
        # fixed-point space dimension: solve real-linear system M - J conj(M) J = 0
        basis=[]
        for i in range(k*k*2):
            E=np.zeros(2*k*k); E[i]=1
            M=(E[:k*k]+1j*E[k*k:]).reshape(k,k)
            F=M-J@M.conj()@J
            basis.append(np.concatenate([F.real.ravel(),F.imag.ravel()]))
        res['fixdim']=2*k*k-np.linalg.matrix_rank(np.array(basis).T)
        # span(M) == fixed space: rank of fixed-space-condition applied to Ms is 0 and rank == fixdim
    # random sign carrier: compare Lambda spectrum with Phi spectrum eigen (E8 formula)
    rng=random.Random(seed)
    sig={w:rng.choice([1,-1]) for w in H}
    A=sum(sig[w]*mat(w) for w in H)
    C=A[:k,:k]; D=A[k:,k:]
    idx={w:i for i,w in enumerate(O)}
    L=np.zeros((len(O),len(O)))
    for s in H:
        Ps=mat(s)
        for p in O:
            if symp(s,p)==0:
                q=''.join(  # product word
                    {('I','I'):'I'}.get((a,b), None) or (a if b=='I' else b if a=='I' else 'I' if a==b else ({'X','Y','Z'}-{a,b}).pop())
                    for a,b in zip(s,p))
                Pp=mat(p);Pq=mat(q)
                sL=np.trace(Ps@Pp@Pq)/2**N
                assert abs(abs(sL)-1)<1e-9 and abs(sL.imag)<1e-9
                L[idx[q],idx[p]]=sL.real*sig[s]
    assert np.allclose(L,L.T)
    kap=2 if case=='C1' else 1
    g=np.linalg.eigvalsh(C); dl=np.linalg.eigvalsh(D)
    pred=np.sort(np.repeat([(a+b)/2 for a in g for b in dl],kap))
    res['specmatch']=np.allclose(np.sort(np.linalg.eigvalsh(L)),pred,atol=1e-7)
    tC=lambda M,j: np.trace(np.linalg.matrix_power(M,j)).real
    e8=kap/8*(k*tC(C,3)+3*tC(C,2)*tC(D,1)+3*tC(C,1)*tC(D,2)+k*tC(D,3))
    res['E8']=(round(np.trace(L@L@L)),round(e8))
    return res
for N in (3,4):
    for case in ('C1','C3','C5'):
        print(N,case,run(N,case))

"""Independent check of Lemma 21 (a), (b) and of (E8), (E9) on random Hermitian matrices."""
import numpy as np
import sympy as sp
from fractions import Fraction

rng = np.random.default_rng(12345)

def rand_herm(k):
    A = rng.normal(size=(k, k)) + 1j * rng.normal(size=(k, k))
    return (A + A.conj().T) / 2

def real_matrix_of(op, basis):
    """matrix of a real-linear op on the real span of basis (list of complex matrices)."""
    B = np.array([np.concatenate([b.real.ravel(), b.imag.ravel()]) for b in basis]).T
    imgs = np.array([np.concatenate([op(b).real.ravel(), op(b).imag.ravel()]) for b in basis]).T
    X, res, rk, _ = np.linalg.lstsq(B, imgs, rcond=None)
    assert rk == len(basis)
    assert np.allclose(B @ X, imgs), "not invariant"
    return X

def check_a(k):
    C, D = rand_herm(k), rand_herm(k)
    g, dl = np.linalg.eigvalsh(C), np.linalg.eigvalsh(D)
    Phi = lambda M: (C @ M + M @ D) / 2
    basis = []
    for i in range(k):
        for j in range(k):
            E = np.zeros((k, k), complex); E[i, j] = 1
            basis += [E, 1j * E]
    R = real_matrix_of(Phi, basis)
    ev = np.sort(np.linalg.eigvals(R).real)
    exp = np.sort(np.repeat([(a + b) / 2 for a in g for b in dl], 2))
    assert np.allclose(ev, exp)
    # (E8) with kappa=2
    t3 = np.trace(np.linalg.matrix_power(R, 3))
    tr = lambda A, j: np.trace(np.linalg.matrix_power(A, j)).real
    e8 = 2 / 8 * (k * tr(C, 3) + 3 * tr(C, 2) * tr(D, 1) + 3 * tr(C, 1) * tr(D, 2) + k * tr(D, 3))
    assert np.isclose(t3, e8), (t3, e8)
    # invariant real form U = fixed points of M -> J conj(M) J with J = Y (x) I, J conj(J) = -I,
    # need C, D commuting with the antiunitary: J conj(C) J^{-1} = C
    if k % 2 == 0:
        Y = np.array([[0, -1j], [1j, 0]])
        J = np.kron(Y, np.eye(k // 2))
        Jinv = np.linalg.inv(J)
        C2 = (C + J @ C.conj() @ Jinv) / 2
        D2 = (D + J @ D.conj() @ Jinv) / 2
        Phi2 = lambda M: (C2 @ M + M @ D2) / 2
        inv = lambda M: J @ M.conj() @ J
        U = [(b + inv(b)) / 2 for b in basis]
        # pick a real basis of U
        V = np.array([np.concatenate([u.real.ravel(), u.imag.ravel()]) for u in U]).T
        Uq, s, _ = np.linalg.svd(V, full_matrices=False)
        r = int((s > 1e-9).sum())
        assert r == k * k, r
        Ub = [ (Uq[:k*k, i] + 1j * Uq[k*k:, i]).reshape(k, k) for i in range(r)]
        RU = real_matrix_of(Phi2, Ub)
        g2, d2 = np.linalg.eigvalsh(C2), np.linalg.eigvalsh(D2)
        evU = np.sort(np.linalg.eigvals(RU).real)
        expU = np.sort([(a + b) / 2 for a in g2 for b in d2])
        assert np.allclose(evU, expU)
        t3U = np.trace(np.linalg.matrix_power(RU, 3))
        e8U = 1 / 8 * (k * tr(C2, 3) + 3 * tr(C2, 2) * tr(D2, 1) + 3 * tr(C2, 1) * tr(D2, 2) + k * tr(D2, 3))
        assert np.isclose(t3U, e8U)

def check_b(k, eps):
    C = rand_herm(k)
    mu = np.linalg.eigvalsh(C)
    Phi = lambda M: (C @ M + M @ C.conj()) / 2
    basis = []
    for i in range(k):
        for j in range(i if eps == 1 else i + 1, k):
            E = np.zeros((k, k), complex); E[i, j] += 1; E[j, i] += eps
            basis += [E, 1j * E]
    R = real_matrix_of(Phi, basis)
    ev = np.sort(np.linalg.eigvals(R).real)
    pairs = [(mu[i] + mu[j]) / 2 for i in range(k) for j in range(k) if (i <= j if eps == 1 else i < j)]
    assert np.allclose(ev, np.sort(np.repeat(pairs, 2)))
    t3 = np.trace(np.linalg.matrix_power(R, 3))
    p = [np.trace(np.linalg.matrix_power(C, j)).real for j in range(4)]
    e9 = 0.25 * ((k + 4 * eps) * p[3] + 3 * p[1] * p[2])
    assert np.isclose(t3, e9), (k, eps, t3, e9)

for k in range(1, 7):
    check_a(k)
    for eps in (1, -1):
        if k > 1 or eps == 1:
            check_b(k, eps)
print("numeric Lemma 21 (a),(b), (E8), (E9) OK")

# symbolic (E9) identity for k = 1..6
for k in range(1, 7):
    m = sp.symbols(f"m0:{k}")
    p = [sum(x**j for x in m) for j in range(4)]
    for eps in (1, -1):
        S = sum(2 * ((m[i] + m[j]) / 2) ** 3 for i in range(k) for j in range(k) if (i <= j if eps == 1 else i < j))
        assert sp.expand(S - sp.Rational(1, 4) * ((k + 4 * eps) * p[3] + 3 * p[1] * p[2])) == 0
    m2 = sp.symbols(f"n0:{k}")
    q = [sum(x**j for x in m2) for j in range(4)]
    S8 = sum(((m[i] + m2[j]) / 2) ** 3 for i in range(k) for j in range(k))
    assert sp.expand(S8 - sp.Rational(1, 8) * (k * p[3] + 3 * p[2] * q[1] + 3 * p[1] * q[2] + k * q[3])) == 0
print("symbolic (E8)/(E9) identities OK")

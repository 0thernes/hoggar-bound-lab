# Quantitative stability candidate

2026-11-09. Status: the scalar spectral-distance theorem below is checked in the isolated `lean/HoggarBound/Stability.lean`. The matrix/Pauli interpretations in this note are mathematical derivations, not yet additional Lean theorems. Work was redirected to the stronger four-qubit C3 finite-certificate target. No historical novelty is claimed for the scalar inequality.

Let a traceless Hermitian matrix A have dimension n >= 2 and tr(A^2)=n*m, with m>0. Write c=n-1, a=sqrt(c*m), t=lambda_max(A), and

    delta = n*m*(n-2)*a/c - tr(A^3).

The original third-moment theorem says delta >= 0. The residual identity is

    sum_i (a-lambda_i)(c*lambda_i+a)^2 = c^2*delta.

Also sum_i (c*lambda_i+a)^2 = n^2*a^2. Since lambda_i <= t, termwise comparison gives

    n^2*a^2*(a-t) <= c^2*delta.

Choose a normalized top eigenvector psi and P=|psi><psi|. The corresponding equality-orbit matrix is

    B = (n*a/c)*P - (a/c)*I.

It has spectrum (a,-a/c,...,-a/c). Direct trace expansion gives

    ||A-B||_F^2 = 2*n*a*(a-t)/c <= 2*c*delta/(n*a).

The top-eigenvector choice minimizes this Frobenius distance over the rank-one equality orbit. This is quantitative proximity to some extremal matrix, not identification with a particular Hoggar orbit or Clifford-equivalence class.

For a nonempty Pauli support S, let m=|S|, A=sum_(v in S) f_v P_v with f_v in {+1,-1}, and define a vector over ALL nonidentity Paulis by q_v=(c/a)f_v on S and zero outside. Let p_v=<psi|P_v|psi>. Pauli Parseval and purity give

    ||p-q||_2^2 = (c^2/(n*a^2))*||A-B||_F^2
                = 2*c*(1-t/a)
               <= 2*c^3*delta/(n^2*a^3).

If L is the number of contexts contained in S and v the violated count, put

    v_star = (L - (n-2)*m^(3/2)/(6*sqrt(c)))/2.

This is the REAL spectral floor, not its rounded integer version and not an assumed unknown optimum. Since delta=12*n*(v-v_star), the number h of support coordinates with f_v*p_v <= 0 satisfies

    h <= (m/c)*||p-q||_2^2
      <= (24/n)*sqrt(c/m)*(v-v_star).

The first inequality counts zeros as disagreements: at each such coordinate the squared error is at least c/m. It is consequently an upper bound even if a numerical sign convention chooses an arbitrary sign at zero.

Two concrete specializations:

- Full three-qubit space: ||p-f/3||^2 <= (v-63)/9, and h <= v-63.
- Real four-qubit quadric: ||p-q||^2 <= (v-315)/18, and h <= (v-315)/2, with q=f/3 on the 135-point support and zero on the remaining nonidentity coordinates.

The certificate is operational: compute the assignment operator, select a top eigenvector, compute its complete Pauli expectation vector, and check the exact distance identity and inequality. Controlled flips of a saturating witness and random sparse supports provide falsification tests. Small deficit certifies closeness to a flat pure-state Pauli vector, but does not by itself solve nearest-Hoggar recovery or classify all equality cases.

## Checked Lean scope

`Stability.lean` currently checks the following without adding project axioms:

- `moment_entry_le`: the bound lambda_i <= a under the two moment constraints;
- `shifted_square_sum`: the exact shifted-square identity;
- `cubic_residual_identity`: the exact residual identity, with the scaled deficit Delta=c*delta;
- `cubic_deficit_controls_top`: the upper-eigenvalue stability inequality;
- `spectrum_distance_identity`: the exact Euclidean distance to a chosen one-outlier spectrum;
- `exists_near_extremal_spectrum`: a largest entry i satisfies n*a*distance_squared <= 2*Delta.

The final theorem is nontrivial stability information beyond merely Delta>=0. Its proof does not formally construct the eigenprojector, prove the Pauli Parseval step, or formalize the sign-error counting corollary yet. Those distinctions must be retained in any paper.

Primary-source inspection by the literature audit found exact equality/flat-state results in the inspected Jonah sources and recent Pauli-flat-state work. No identical quantitative statement was located in that bounded inspection. This does not establish priority; the scalar estimate is an elementary refinement of the same residual-polynomial argument, and any possible contribution would primarily be the certified contextuality/rounding application.


## Explicit axiom audit

`lean/StabilityVerification.lean` imports the checked module and prints dependencies for `moment_entry_le`, `shifted_square_sum`, `cubic_residual_identity`, `cubic_deficit_controls_top`, `spectrum_distance_identity`, and `exists_near_extremal_spectrum`. A direct source check with the pinned Lean 4.35.0 toolchain exited 0 on 2026-11-09. All six declarations use only `propext`, `Classical.choice`, and `Quot.sound`; the output is `results/stability-lean-axioms.log`.

Reproduce from `lean/`:

```sh
lake build HoggarBound.Stability
lake env lean StabilityVerification.lean
```

This audit concerns the scalar spectral theorem. The matrix and Pauli-coordinate translations in this note remain ordinary mathematical derivations rather than additional Lean statements.

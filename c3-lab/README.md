# Exact four-qubit C3 certificate

This browser demonstration reconstructs two assignments on the 71-point section
of the real four-qubit Pauli quadric commuting with `ZIII`. Each assignment is +1
except at four explicitly listed observables. The carriers have the same exact
characteristic polynomial, while the completion cubic traces are 14976 and 15360.

Run from the repository root:

```sh
python -m http.server 8769 --bind 127.0.0.1
```

Open `http://127.0.0.1:8769/c3-lab/`. No package installation or remote script is
needed for the browser demonstration. A modern browser with `BigInt` support is
required. Verification runs automatically and can be repeated after editing signs.

`model.js` builds real Pauli matrices from their bit action, enumerates all 1120
outside contexts, and obtains their signs by multiplying actual matrix entries.
It uses the exact Faddeev–LeVerrier recurrence with `BigInt` to compute the carrier
characteristic polynomials, and sums integer products to compute completion cubic
traces. Approximate eigenvalues are not used to accept a certificate.

The `Flip ZIII in B` control changes one input and destroys the matching carrier
polynomial. `Restore witness` returns to the passing pair. The editor permits any
of the 71 signs in assignment B to be changed. `Download certificate` exports the
current exact results, including failed checks.

```sh
node tests/frontier_c3_browser_test.cjs
```

The test compares the browser implementation with the independent Python matrix
artifact and checks a sign perturbation, an identical-pair negative control, and
invalid inputs. The paper and Lean sources state their verification scope.

The result establishes the four-qubit C3 instance of Conjecture E in Jonah's
*The reach of the section-square law*, v0.5, DOI 10.5281/zenodo.23524332. It does
not establish all dimensions, universal historical priority, or physical hardware
performance. This is a mathematical demonstration of a finite spectral mismatch.

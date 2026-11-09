/*
 * qgt_hoggar.c - the quantum geometric tensor of the Hoggar state in the Pauli frame, computed
 * with the verified diffgeo_* kernels of Tsotchke's quantum_geometric_tensor library
 * (third_party/qgtl; only these kernels are used - see third_party/qgtl/PROVENANCE.md).
 *
 * For a state psi and the 4^N - 1 one-parameter flows exp(-i t P_v / 2), the tangent vectors are
 * d_v psi = -(i/2) P_v psi and
 *
 *     Q_uv = <d_u psi|d_v psi> - <d_u psi|psi><psi|d_v psi> = ( <P_u P_v> - <P_u><P_v> ) / 4 .
 *
 * Prediction for the Hoggar fiducial (all <P_v> = f_v / 3, f_v = +-1):
 *     g_vv = Re Q_vv = 2/9                                  for every v,
 *     |g_uv| = 1/36                                         if P_u, P_v anticommute,
 *     |g_uv| = 1/18                                         if they commute and the context {u,v,u+v}
 *                                                           is SATISFIED by the sign assignment f,
 *     |g_uv| = 1/9                                          if they commute and the context is VIOLATED,
 *     |F_uv| = |-2 Im Q_uv| = 1/6 on anticommuting pairs, 0 on commuting pairs
 *     (for the real 16-dimensional state of the second run, F vanishes identically).
 * So the 63 violated contexts (the split Cayley hexagon) are exactly the 189 pairs of largest
 * off-diagonal quantum metric.
 *
 * Build: gcc -std=gnu11 -O1 -Ithird_party/qgtl/include -Ithird_party/qgtl/stub
 *            third_party/qgtl/src/quantum_geometric/distributed/differential_geometry.c src/qgt_hoggar.c -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
#include "quantum_geometric/distributed/differential_geometry.h"
#include "witness_io.h"

static int pc(uint32_t x) { return __builtin_popcount(x); }

/* out = P(a,c) psi, with P = i^{|a&c|} X^a Z^c:  (P psi)[x] = i^k (-1)^{c.(x^a)} psi[x^a] */
static void apply_pauli(int N, uint32_t a, uint32_t c, const ComplexDouble *psi, ComplexDouble *out) {
    uint32_t D = 1u << N;
    int k = pc(a & c) & 3;
    for (uint32_t x = 0; x < D; x++) {
        uint32_t y = x ^ a;
        double s = (pc(c & y) & 1) ? -1.0 : 1.0;
        double re = s * psi[y].real, im = s * psi[y].imag, t;
        for (int j = 0; j < k; j++) { t = re; re = -im; im = t; }   /* multiply by i */
        out[x].real = re; out[x].imag = im;
    }
}

static int run(int N, const ComplexDouble *psi_in, int only_real, double F_anti, const char *witness, const char *label) {
    uint32_t D = 1u << N, n = 1u << (2 * N);
    ComplexDouble *psi = malloc(sizeof(ComplexDouble) * D), *tmp = malloc(sizeof(ComplexDouble) * D);
    double nrm = 0;
    for (uint32_t x = 0; x < D; x++) nrm += psi_in[x].real * psi_in[x].real + psi_in[x].imag * psi_in[x].imag;
    nrm = sqrt(nrm);
    for (uint32_t x = 0; x < D; x++) { psi[x].real = psi_in[x].real / nrm; psi[x].imag = psi_in[x].imag / nrm; }

    /* directions: all non-identity Paulis, or only the real (even number of Y) ones */
    uint32_t *dir = malloc(sizeof(uint32_t) * n), P = 0;
    for (uint32_t v = 1; v < n; v++) {
        uint32_t a = v & (D - 1), c = v >> N;
        if (only_real && (pc(a & c) & 1)) continue;
        dir[P++] = v;
    }
    ComplexDouble *deriv = malloc(sizeof(ComplexDouble) * (size_t)P * D);
    for (uint32_t i = 0; i < P; i++) {
        uint32_t a = dir[i] & (D - 1), c = dir[i] >> N;
        apply_pauli(N, a, c, psi, tmp);
        for (uint32_t x = 0; x < D; x++) {      /* multiply by -i/2 */
            deriv[(size_t)i * D + x].real = 0.5 * tmp[x].imag;
            deriv[(size_t)i * D + x].imag = -0.5 * tmp[x].real;
        }
    }
    double *g = malloc(sizeof(double) * (size_t)P * P), *F = malloc(sizeof(double) * (size_t)P * P);
    diffgeo_engine_t *eng = diffgeo_engine_create();
    if (!eng) { fprintf(stderr, "engine create failed\n"); return 2; }
    if (!diffgeo_compute_fubini_study(eng, psi, D, deriv, P, g)) { fprintf(stderr, "fubini_study failed\n"); return 2; }
    if (!diffgeo_compute_berry_curvature(eng, psi, D, deriv, P, F)) { fprintf(stderr, "berry_curvature failed\n"); return 2; }

    /* assignment from the witness file (bit v set <=> f(v) = -1) */
    int8_t *f = malloc(n);
    if (!f || !witness_read(witness, N, only_real ? 'h' : 'f', f)) {
        diffgeo_engine_destroy(eng);
        free(f); free(g); free(F); free(deriv); free(dir); free(psi); free(tmp);
        return 2;
    }

    /* classify */
    double dev_diag = 0, dev_anti = 0, dev_sat = 0, dev_viol = 0, dev_F_anti = 0, dev_F_comm = 0;
    long n_anti = 0, n_sat = 0, n_viol = 0, mismatches = 0;
    for (uint32_t i = 0; i < P; i++) {
        dev_diag = fmax(dev_diag, fabs(g[(size_t)i * P + i] - 2.0 / 9.0));
        for (uint32_t j = i + 1; j < P; j++) {
            uint32_t u = dir[i], v = dir[j];
            uint32_t au = u & (D - 1), cu = u >> N, av = v & (D - 1), cv = v >> N;
            int anti = (pc(au & cv) + pc(cu & av)) & 1;
            double gij = g[(size_t)i * P + j], Fij = F[(size_t)i * P + j];
            if (anti) {
                n_anti++;
                dev_anti = fmax(dev_anti, fabs(fabs(gij) - 1.0 / 36.0));
                dev_F_anti = fmax(dev_F_anti, fabs(fabs(Fij) - F_anti));
            } else {
                unsigned t = (unsigned)pc(au & cu) + (unsigned)pc(av & cv) + 2u * (unsigned)pc(cu & av)
                           + 3u * (unsigned)pc((au ^ av) & (cu ^ cv));
                int s = (t & 3u) == 0 ? 1 : -1;
                int violated = (f[u] * f[v] * f[u ^ v] != s);
                int large = fabs(gij) > 1.0 / 12.0;         /* midway between 1/18 and 1/9 */
                if (violated != large) mismatches++;
                if (violated) { n_viol++; dev_viol = fmax(dev_viol, fabs(fabs(gij) - 1.0 / 9.0)); }
                else { n_sat++; dev_sat = fmax(dev_sat, fabs(fabs(gij) - 1.0 / 18.0)); }
                dev_F_comm = fmax(dev_F_comm, fabs(Fij));
            }
        }
    }
    printf("%s: N=%d, %u Pauli directions, state dimension %u\n", label, N, P, D);
    printf("  diagonal metric g_vv = 2/9                      max deviation %.2e\n", dev_diag);
    printf("  anticommuting pairs  : %6ld  |g| = 1/36         max deviation %.2e ; |F| = %s max deviation %.2e\n", n_anti, dev_anti, F_anti == 0.0 ? "0" : "1/6", dev_F_anti);
    printf("  commuting, satisfied : %6ld  |g| = 1/18         max deviation %.2e\n", n_sat, dev_sat);
    printf("  commuting, violated  : %6ld  |g| = 1/9          max deviation %.2e\n", n_viol, dev_viol);
    printf("  Berry curvature on commuting pairs = 0          max |F| %.2e\n", dev_F_comm);
    printf("  pairs where (|g| > 1/12) disagrees with (context violated): %ld\n", mismatches);
    printf("  violated contexts recovered from the metric: %ld (each context = 3 pairs)\n", n_viol / 3);
    int ok = dev_diag < 1e-12 && dev_anti < 1e-12 && dev_sat < 1e-12 && dev_viol < 1e-12 && dev_F_anti < 1e-12
          && dev_F_comm < 1e-12 && mismatches == 0;
    printf("  %s\n", ok ? "PASS" : "FAIL");
    diffgeo_engine_destroy(eng);
    free(f); free(g); free(F); free(deriv); free(dir); free(psi); free(tmp);
    return ok ? 0 : 1;
}

int main(int argc, char **argv) {
    if (argc > 3) { fprintf(stderr, "usage: qgt_hoggar [three-qubit-witness [four-qubit-witness]]\n"); return 2; }
    const char *w3 = argc > 1 ? argv[1] : "data/witness/n3_f_hoggar_moonlab.txt";
    const char *w4 = argc > 2 ? argv[2] : "data/witness/n4_h_hoggar_moonlab.txt";
    ComplexDouble h3[8] = {{-1, 2}, {1, 0}, {1, 0}, {1, 0}, {1, 0}, {1, 0}, {1, 0}, {1, 0}};
    ComplexDouble h4[16] = {{-1, 0}, {1, 0}, {1, 0}, {1, 0}, {1, 0}, {1, 0}, {1, 0}, {1, 0},
                            {2, 0},  {0, 0}, {0, 0}, {0, 0}, {0, 0}, {0, 0}, {0, 0}, {0, 0}};
    int r1 = run(3, h3, 0, 1.0 / 6.0, w3, "Hoggar fiducial (C^8), all 63 Pauli flows");
    int r2 = run(4, h4, 1, 0.0, w4, "Realified Hoggar (R^16), the 135 real Pauli flows (real state: Berry curvature vanishes)");
    return r1 | r2;
}

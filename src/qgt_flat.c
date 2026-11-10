/*
 * qgt_flat.c - the quantum geometric tensor of eight Pauli-flat states along the Pauli flows of their
 * supports, computed with the diffgeo_* kernels of Tsotchke's quantum_geometric_tensor library
 * (third_party/qgtl; only these two kernels are used - see third_party/qgtl/PROVENANCE.md).
 *
 * Let psi be flat on S: <P_v> = f_v mu for v in S (f_v = +-1) and <P_v> = 0 for the other non-identity
 * Pauli observables.  With tangent vectors d_v psi = -(i/2) P_v psi,
 *
 *     Q_uv = ( <P_u P_v> - <P_u><P_v> ) / 4 ,   g = Re Q ,   F = -2 Im Q .
 *
 * Prediction, for u, v in S:
 *     g_vv   = (1 - mu^2)/4
 *     |g_uv| = (mu + mu^2)/4   u, v commute, u+v in S, and the context {u, v, u+v} is VIOLATED by f
 *     |g_uv| = (mu - mu^2)/4   u, v commute, u+v in S, and the context is satisfied
 *     |g_uv| = mu^2/4          u, v commute and u+v is outside S, or u, v anticommute
 *     |F_uv| = mu/2            u, v anticommute and u+v in S;  F_uv = 0 otherwise
 * So the violated contexts are exactly the pairs with |g_uv| > mu/4: the optimal noncontextual
 * assignment is read off the quantum metric of the state.
 *
 * The supports and signs are read from data/flat/ (written by scripts/flat_states.py and
 * scripts/phase_states.py).  The seven-qubit state has 8128 directions: its two 8128 x 8128 matrices take
 * about 1.1 GB; run with --no-seven to skip it.
 *
 * Build: gcc -std=gnu11 -O1 -Ithird_party/qgtl/include -Ithird_party/qgtl/stub
 *            third_party/qgtl/src/quantum_geometric/distributed/differential_geometry.c src/qgt_flat.c -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
#include "quantum_geometric/distributed/differential_geometry.h"

#define MAXN 7
#define MAXPTS (1u << (2 * MAXN))
#define HEXMAX (MAXPTS / 4)

static int pc(uint32_t x) { return __builtin_popcount(x); }

/* reads one line of at most HEXMAX hexadecimal digits into bits[0 .. npts-1]; returns 1 on success */
static int read_mask(FILE *fp, uint32_t npts, uint8_t *bits) {
    char line[HEXMAX + 8];
    if (!fgets(line, sizeof line, fp)) return 0;
    size_t len = strcspn(line, "\r\n");
    if (len == 0 || len > npts / 4) return 0;
    memset(bits, 0, npts);
    for (size_t k = 0; k < len; k++) {
        char ch = line[len - 1 - k];
        int d = (ch >= '0' && ch <= '9') ? ch - '0' : (ch >= 'a' && ch <= 'f') ? ch - 'a' + 10 : -1;
        if (d < 0) return 0;
        for (int b = 0; b < 4; b++) bits[4 * k + b] = (uint8_t)((d >> b) & 1);
    }
    return 1;
}

/* out = P(a,c) psi, with P = i^{|a&c|} X^a Z^c */
static void apply_pauli(int N, uint32_t a, uint32_t c, const ComplexDouble *psi, ComplexDouble *out) {
    uint32_t D = 1u << N;
    int k = pc(a & c) & 3;
    for (uint32_t x = 0; x < D; x++) {
        uint32_t y = x ^ a;
        double s = (pc(c & y) & 1) ? -1.0 : 1.0;
        double re = s * psi[y].real, im = s * psi[y].imag, t;
        for (int j = 0; j < k; j++) { t = re; re = -im; im = t; }
        out[x].real = re; out[x].imag = im;
    }
}

static int run(const char *name, int N, const ComplexDouble *psi_in) {
    uint32_t D = 1u << N, n = 1u << (2 * N);
    char path[128];
    snprintf(path, sizeof path, "data/flat/n%d_%s.txt", N, name);
    FILE *fp = fopen(path, "r");
    if (!fp) { fprintf(stderr, "cannot open %s (run scripts/flat_states.py first)\n", path); return 2; }
    int fN = 0; unsigned long points = 0, contexts = 0, degree = 0;
    char head[96];
    static uint8_t inS[MAXPTS], isNeg[MAXPTS];
    if (!fgets(head, sizeof head, fp) || sscanf(head, "%d %lu %lu %lu", &fN, &points, &contexts, &degree) != 4 || fN != N
        || !read_mask(fp, n, inS) || !read_mask(fp, n, isNeg)) {
        fprintf(stderr, "malformed %s\n", path); fclose(fp); return 2;
    }
    fclose(fp);

    ComplexDouble *psi = malloc(sizeof(ComplexDouble) * D), *tmp = malloc(sizeof(ComplexDouble) * D);
    uint32_t *dir = malloc(sizeof(uint32_t) * n), P = 0;
    if (!psi || !tmp || !dir) return 2;
    double nrm = 0;
    for (uint32_t x = 0; x < D; x++) nrm += psi_in[x].real * psi_in[x].real + psi_in[x].imag * psi_in[x].imag;
    nrm = sqrt(nrm);
    for (uint32_t x = 0; x < D; x++) { psi[x].real = psi_in[x].real / nrm; psi[x].imag = psi_in[x].imag / nrm; }
    for (uint32_t v = 1; v < n; v++) if (inS[v]) dir[P++] = v;
    if (P != points) { fprintf(stderr, "%s: mask has %u points, header says %lu\n", name, P, points); return 2; }

    ComplexDouble *deriv = malloc(sizeof(ComplexDouble) * (size_t)P * D);
    double *g = malloc(sizeof(double) * (size_t)P * P), *F = malloc(sizeof(double) * (size_t)P * P);
    if (!deriv || !g || !F) return 2;
    for (uint32_t i = 0; i < P; i++) {
        apply_pauli(N, dir[i] & (D - 1), dir[i] >> N, psi, tmp);
        for (uint32_t x = 0; x < D; x++) {                 /* multiply by -i/2 */
            deriv[(size_t)i * D + x].real = 0.5 * tmp[x].imag;
            deriv[(size_t)i * D + x].imag = -0.5 * tmp[x].real;
        }
    }
    diffgeo_engine_t *eng = diffgeo_engine_create();
    if (!eng) { fprintf(stderr, "engine create failed\n"); return 2; }
    if (!diffgeo_compute_fubini_study(eng, psi, D, deriv, P, g)) { fprintf(stderr, "fubini_study failed\n"); return 2; }
    if (!diffgeo_compute_berry_curvature(eng, psi, D, deriv, P, F)) { fprintf(stderr, "berry_curvature failed\n"); return 2; }

    double mu = sqrt((double)(D - 1) / (double)P);
    double dev_diag = 0, dev_viol = 0, dev_sat = 0, dev_small = 0, dev_F = 0;
    long n_viol = 0, n_sat = 0, n_out = 0, n_anti = 0, mismatches = 0;
    for (uint32_t i = 0; i < P; i++) {
        dev_diag = fmax(dev_diag, fabs(g[(size_t)i * P + i] - (1.0 - mu * mu) / 4.0));
        for (uint32_t j = i + 1; j < P; j++) {
            uint32_t u = dir[i], v = dir[j], w = u ^ v;
            uint32_t au = u & (D - 1), cu = u >> N, av = v & (D - 1), cv = v >> N;
            int anti = (pc(au & cv) + pc(cu & av)) & 1;
            double gij = fabs(g[(size_t)i * P + j]), Fij = fabs(F[(size_t)i * P + j]);
            int large = gij > mu / 4.0, violated = 0;
            if (anti) {
                n_anti++;
                dev_small = fmax(dev_small, fabs(gij - mu * mu / 4.0));
                dev_F = fmax(dev_F, fabs(Fij - (inS[w] ? mu / 2.0 : 0.0)));
            } else if (!inS[w]) {
                n_out++;
                dev_small = fmax(dev_small, fabs(gij - mu * mu / 4.0));
                dev_F = fmax(dev_F, Fij);
            } else {
                unsigned t = (unsigned)pc(au & cu) + (unsigned)pc(av & cv) + 2u * (unsigned)pc(cu & av)
                           + 3u * (unsigned)pc((au ^ av) & (cu ^ cv));
                int s = (t & 3u) == 0 ? 1 : -1;
                int fu = isNeg[u] ? -1 : 1, fv = isNeg[v] ? -1 : 1, fw = isNeg[w] ? -1 : 1;
                violated = (fu * fv * fw != s);
                if (violated) { n_viol++; dev_viol = fmax(dev_viol, fabs(gij - (mu + mu * mu) / 4.0)); }
                else { n_sat++; dev_sat = fmax(dev_sat, fabs(gij - (mu - mu * mu) / 4.0)); }
                dev_F = fmax(dev_F, Fij);
            }
            if (violated != large) mismatches++;
        }
    }
    printf("%s: N=%d, %u Pauli directions (the support), mu = %.6f\n", name, N, P, mu);
    printf("  g_vv = (1-mu^2)/4                                       max deviation %.2e\n", dev_diag);
    printf("  pairs on violated contexts   : %7ld  |g| = (mu+mu^2)/4  max deviation %.2e\n", n_viol, dev_viol);
    printf("  pairs on satisfied contexts  : %7ld  |g| = (mu-mu^2)/4  max deviation %.2e\n", n_sat, dev_sat);
    printf("  other pairs (anticommuting %ld, product outside %ld): |g| = mu^2/4  max deviation %.2e\n", n_anti, n_out, dev_small);
    printf("  Berry curvature (mu/2 on anticommuting pairs with product in the support, else 0)  max deviation %.2e\n", dev_F);
    printf("  pairs where (|g| > mu/4) disagrees with (context violated): %ld\n", mismatches);
    printf("  contexts recovered from the metric: %ld violated of %ld (file: %lu of %lu)\n",
           n_viol / 3, (n_viol + n_sat) / 3, degree, contexts);
    int ok = dev_diag < 1e-12 && dev_viol < 1e-12 && dev_sat < 1e-12 && dev_small < 1e-12 && dev_F < 1e-12 && mismatches == 0
          && (unsigned long)(n_viol / 3) == degree && (unsigned long)((n_viol + n_sat) / 3) == contexts;
    printf("  %s\n", ok ? "PASS" : "FAIL");
    diffgeo_engine_destroy(eng);
    free(g); free(F); free(deriv); free(dir); free(psi); free(tmp);
    return ok ? 0 : 1;
}

/* amplitudes i^q, q = sum over CS pairs of x_j x_k + 2 sum over CCZ triples of x_j x_k x_l (mod 4) */
static void phase_state(int N, int ncs, const int cs[][2], int nccz, const int ccz[][3], ComplexDouble *psi) {
    for (uint32_t x = 0; x < (1u << N); x++) {
        int q = 0;
        for (int i = 0; i < ncs; i++) q += (int)((x >> cs[i][0]) & (x >> cs[i][1]) & 1);
        for (int i = 0; i < nccz; i++) q += 2 * (int)((x >> ccz[i][0]) & (x >> ccz[i][1]) & (x >> ccz[i][2]) & 1);
        q &= 3;
        psi[x].real = (q == 0) - (q == 2);
        psi[x].imag = (q == 1) - (q == 3);
    }
}

int main(int argc, char **argv) {
    int seven = !(argc > 1 && strcmp(argv[1], "--no-seven") == 0);
    ComplexDouble lly[4] = {{0, 1}, {0, 1}, {0, 1}, {1, 0}};
    ComplexDouble ccz[8], hog[8], quad[16], piv[16], c5[32];
    for (int x = 0; x < 8; x++) { ccz[x].real = (x == 7) ? -1 : 1; ccz[x].imag = 0; hog[x].real = 1; hog[x].imag = 0; }
    hog[0].real = -1; hog[0].imag = 2;
    for (int x = 0; x < 16; x++) { quad[x].real = (x == 0) ? -3 : 1; quad[x].imag = 0; piv[x].real = 0; piv[x].imag = 0; }
    int bent[6] = {3, 7, 11, 12, 13, 14};
    for (int k = 0; k < 6; k++) piv[bent[k]].real = 1;
    piv[14].real = 0; piv[14].imag = 1;
    /* Cieslinski, arXiv:2610.07172, eq. (18); a1 = -1-2i, a2 = 2-i, a3 = 5, a4 = -3+4i */
    const double A[4][2] = {{-1, -2}, {2, -1}, {5, 0}, {-3, 4}};
    /* entries: index of alpha (1..4), sign, and a factor i (1) or not (0) */
    const int E[32][3] = {{1,1,0},{2,-1,0},{1,1,0},{2,-1,0},{1,-1,0},{2,-1,0},{1,-1,0},{2,1,0},{3,1,1},{1,1,0},{2,1,0},{3,1,0},
        {2,1,0},{4,1,0},{2,-1,0},{3,1,0},{2,1,0},{3,1,0},{2,-1,0},{1,-1,0},{2,1,0},{4,-1,0},{2,-1,0},{1,-1,0},{1,1,0},
        {3,-1,1},{1,-1,0},{2,1,0},{3,-1,0},{2,1,0},{1,-1,0},{2,-1,0}};
    for (int x = 0; x < 32; x++) {
        double re = E[x][1] * A[E[x][0] - 1][0], im = E[x][1] * A[E[x][0] - 1][1];
        if (E[x][2]) { double t = re; re = -im; im = t; }
        c5[x].real = re; c5[x].imag = im;
    }
    int r = 0;
    r |= run("lly", 2, lly);
    r |= run("ccz", 3, ccz);
    r |= run("hoggar", 3, hog);
    r |= run("quadric", 4, quad);
    r |= run("pivot", 4, piv);
    r |= run("cieslinski5", 5, c5);
    /* the phase states of Section 5.3: gates applied to |+...+> */
    static ComplexDouble p5[32], p7[128];
    const int cs5[3][2] = {{0, 1}, {1, 3}, {2, 4}}, ccz5[2][3] = {{0, 1, 4}, {0, 2, 3}};
    const int cs7[3][2] = {{0, 1}, {2, 3}, {4, 5}};
    const int ccz7[8][3] = {{0, 1, 2}, {0, 3, 5}, {1, 2, 4}, {0, 4, 6}, {0, 5, 6}, {1, 3, 6}, {2, 3, 6}, {2, 5, 6}};
    phase_state(5, 3, cs5, 2, ccz5, p5);
    r |= run("phase5", 5, p5);
    if (seven) {
        phase_state(7, 3, cs7, 8, ccz7, p7);
        r |= run("phase7", 7, p7);
    }
    printf("%s\n", r == 0 ? "QGT-FLAT-PASS" : "QGT-FLAT-FAIL");
    return r;
}

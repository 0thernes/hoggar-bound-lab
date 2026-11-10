/* family7.c - seven qubits: every third-level form T with B = T(x,x,.) alternating of rank 6.
 *
 * In a suitable basis (e6 spanning the radical of B, and e0..e5 a symplectic basis of a complement) such
 * a form is the third difference of
 *
 *   p(x) = 2 (x0 x1 + x2 x3 + x4 x5) + 4 w(x0..x5) + 4 x6 s(x0..x5)          (mod 8)
 *
 * with w any of the 2^20 sets of CCZ gates on qubits 0..5 and s any of the 2^15 graphs on qubits 0..5
 * (CCZ gates {6,j,k}).  The state is flat (one non-zero modulus, 1/8, on 8128 observables) exactly when
 * T(v,.,.) has rank 6 for every v != 0.  T(e6,.,.) is the graph s, so only the 13888 nondegenerate graphs
 * are tried; for each, all 2^20 sets w.
 *
 * Result of the full run (about 8 core-hours; scripts/run_family7.sh):
 *     13 271 040 solutions, with 2880 distinct graphs s; one orbit of the group that preserves the normal
 *     form (order 92 897 280 = 64 |Sp(6,2)|), stabiliser of order 7 (src/orbits7.c).
 *
 * usage: family7 s_first s_count outfile     (uint64 codes  s | (w << 15)  are appended to outfile)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define N 7

static inline int rank_rows(uint32_t *r) {
    int rank = 0;
    for (int col = 0; col < N && rank < N; col++) {
        int piv = -1;
        for (int i = rank; i < N; i++) if ((r[i] >> col) & 1) { piv = i; break; }
        if (piv < 0) continue;
        uint32_t t = r[piv]; r[piv] = r[rank]; r[rank] = t;
        for (int i = rank + 1; i < N; i++) if ((r[i] >> col) & 1) r[i] ^= r[rank];
        rank++;
    }
    return rank;
}
static void add_ccz(uint32_t M[N][N], int j, int k, int l) {
    M[j][k] ^= 1u << l; M[j][l] ^= 1u << k;
    M[k][j] ^= 1u << l; M[k][l] ^= 1u << j;
    M[l][j] ^= 1u << k; M[l][k] ^= 1u << j;
}

int main(int argc, char **argv) {
    uint32_t s_first = argc > 1 ? (uint32_t)strtoul(argv[1], NULL, 0) : 0;
    uint32_t s_count = argc > 2 ? (uint32_t)strtoul(argv[2], NULL, 0) : (1u << 15);
    FILE *out = argc > 3 ? fopen(argv[3], "wb") : NULL;
    int ej[15], ek[15], ne = 0, tj[20], tk[20], tl[20], nt = 0;
    for (int j = 0; j < 6; j++) for (int k = j + 1; k < 6; k++) { ej[ne] = j; ek[ne] = k; ne++; }
    for (int j = 0; j < 6; j++) for (int k = j + 1; k < 6; k++) for (int l = k + 1; l < 6; l++) { tj[nt] = j; tk[nt] = k; tl[nt] = l; nt++; }
    uint32_t base[N][N];
    for (int j = 0; j < N; j++) for (int k = 0; k < N; k++) base[j][k] = 0;
    for (int i = 0; i < 3; i++) {                       /* CS gates on (0,1), (2,3), (4,5) */
        int j = 2 * i, k = 2 * i + 1;
        base[j][j] ^= 1u << k; base[j][k] ^= 1u << j; base[j][k] ^= 1u << k;
        base[k][k] ^= 1u << j; base[k][j] ^= 1u << k; base[k][j] ^= 1u << j;
    }
    static uint32_t dW[20][N][N];
    for (int i = 0; i < nt; i++) {
        for (int j = 0; j < N; j++) for (int k = 0; k < N; k++) dW[i][j][k] = 0;
        add_ccz(dW[i], tj[i], tk[i], tl[i]);
    }
    uint64_t found = 0, tried = 0, with_solutions = 0;
    for (uint32_t s = s_first; s < s_first + s_count && s < (1u << 15); s++) {
        uint32_t M[N][N];
        for (int j = 0; j < N; j++) for (int k = 0; k < N; k++) M[j][k] = base[j][k];
        for (int i = 0; i < ne; i++) if ((s >> i) & 1) add_ccz(M, 6, ej[i], ek[i]);
        { uint32_t rows[N]; for (int k = 0; k < N; k++) rows[k] = M[6][k]; if (rank_rows(rows) != 6) continue; }
        tried++;
        uint64_t before = found;
        uint32_t w = 0;
        for (uint32_t g = 0; g < (1u << 20); g++) {      /* Gray-code walk over w */
            if (g) {
                int bit = __builtin_ctz(g);
                w ^= 1u << bit;
                for (int j = 0; j < 6; j++) for (int k = 0; k < 6; k++) M[j][k] ^= dW[bit][j][k];
            }
            int ok = 1;
            for (uint32_t v = 1; v < (1u << N) && ok; v++) {
                uint32_t rows[N] = {0, 0, 0, 0, 0, 0, 0};
                for (int j = 0; j < N; j++) if ((v >> j) & 1) for (int k = 0; k < N; k++) rows[k] ^= M[j][k];
                if (rank_rows(rows) != 6) ok = 0;
            }
            if (ok) {
                found++;
                if (out) { uint64_t code = (uint64_t)s | ((uint64_t)w << 15); fwrite(&code, 8, 1, out); }
            }
        }
        if (found > before) with_solutions++;
    }
    if (out) fclose(out);
    printf("slice s=[0x%x,+0x%x): nondegenerate graphs %llu, with solutions %llu, solutions %llu\n", s_first, s_count,
           (unsigned long long)tried, (unsigned long long)with_solutions, (unsigned long long)found);
    return 0;
}

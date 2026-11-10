/* third_level.c - exhaustive census of flat third-level phase states on N <= 5 qubits.
 *
 * A diagonal gate of the third level of the Clifford hierarchy multiplies |x> by exp(i pi p(x)/4) with
 *
 *     p(x) = sum_j a_j x_j + 2 sum_{j<k} b_jk x_j x_k + 4 sum_{j<k<l} c_jkl x_j x_k x_l     (mod 8)
 *
 * (T, CS and CCZ gates).  The third difference of p is a symmetric trilinear form T over F_2 with
 * t_jjj = a_j, t_jjk = t_jkk = b_jk, t_jkl = c_jkl.  In the state U|+...+> the observables X^a Z^c with a
 * given a != 0 have expectation value 0 or of modulus 2^(-r_a/2), where r_a is the rank of the symmetric
 * matrix T(a,.,.) (paper, Proposition 11).  The state has a single non-zero modulus - and then attains the
 * spectral floor on its Pauli support - exactly when r_a is the same for every a != 0.
 *
 * This program enumerates all 2^(N + C(N,2) + C(N,3)) forms for N = 1..5 (33 554 432 for N = 5), keeps those
 * of constant rank, and splits them into orbits of GL(N,2) (changes of basis x -> g x: CNOT circuits).
 *
 * Expected, and checked:   N=1  1 form  (rank 1)            N=2  1 form  (rank 2)
 *                          N=3  8 forms (rank 2), 2 orbits   N=4  none
 *                          N=5  166656 forms (rank 4), one orbit, stabiliser of order 60
 *
 * usage: third_level            (prints THIRD-LEVEL-PASS and exits 0 when every count is as expected)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define MAXN 5
static int N, nb, nc;
static int bj[10], bk[10], cj[10], ck[10], cl[10];
static int bidx[MAXN][MAXN], cidx[MAXN][MAXN][MAXN];

static int rank_rows(uint32_t *r, int n) {
    int rank = 0;
    for (int col = 0; col < n; col++) {
        int piv = -1;
        for (int i = rank; i < n; i++) if ((r[i] >> col) & 1) { piv = i; break; }
        if (piv < 0) continue;
        uint32_t t = r[piv]; r[piv] = r[rank]; r[rank] = t;
        for (int i = rank + 1; i < n; i++) if ((r[i] >> col) & 1) r[i] ^= r[rank];
        rank++;
    }
    return rank;
}

/* M[j][k] = bit mask over l of T(e_j, e_k, e_l) */
static void build(uint32_t code, uint8_t M[MAXN][MAXN]) {
    uint32_t A = code & ((1u << N) - 1), B = (code >> N) & ((1u << nb) - 1), C = code >> (N + nb);
    for (int j = 0; j < N; j++) for (int k = 0; k < N; k++) {
        uint32_t row = 0;
        for (int l = 0; l < N; l++) {
            int bit;
            if (j == k && k == l) bit = (A >> j) & 1;
            else if (j == k) bit = (B >> bidx[j][l]) & 1;
            else if (j == l || k == l) bit = (B >> bidx[j][k]) & 1;
            else bit = (C >> cidx[j][k][l]) & 1;
            row |= (uint32_t)bit << l;
        }
        M[j][k] = (uint8_t)row;
    }
}
static uint32_t extract(uint8_t M[MAXN][MAXN]) {
    uint32_t code = 0;
    for (int j = 0; j < N; j++) code |= (uint32_t)((M[j][j] >> j) & 1) << j;
    for (int i = 0; i < nb; i++) code |= (uint32_t)((M[bj[i]][bj[i]] >> bk[i]) & 1) << (N + i);
    for (int i = 0; i < nc; i++) code |= (uint32_t)((M[cj[i]][ck[i]] >> cl[i]) & 1) << (N + nb + i);
    return code;
}
/* constant rank of T(v,.,.) over v != 0, or -1 */
static int constant_rank(uint8_t M[MAXN][MAXN]) {
    int r0 = -1;
    for (uint32_t v = 1; v < (1u << N); v++) {
        uint32_t rows[MAXN] = {0, 0, 0, 0, 0};
        for (int j = 0; j < N; j++) if ((v >> j) & 1) for (int k = 0; k < N; k++) rows[k] ^= M[j][k];
        int r = rank_rows(rows, N);
        if (r0 < 0) r0 = r; else if (r != r0) return -1;
    }
    return r0;
}
/* T'(x,y,z) = T(gx,gy,gz) for the transvection g = I + u phi^T */
static void act(uint8_t T[MAXN][MAXN], uint32_t u, uint32_t phi) {
    uint8_t U[MAXN];
    for (int k = 0; k < N; k++) { U[k] = 0; for (int i = 0; i < N; i++) if ((u >> i) & 1) U[k] ^= T[i][k]; }
    for (int j = 0; j < N; j++) if ((phi >> j) & 1) for (int k = 0; k < N; k++) T[j][k] ^= U[k];
    for (int j = 0; j < N; j++) { U[j] = 0; for (int i = 0; i < N; i++) if ((u >> i) & 1) U[j] ^= T[j][i]; }
    for (int k = 0; k < N; k++) if ((phi >> k) & 1) for (int j = 0; j < N; j++) T[j][k] ^= U[j];
    for (int j = 0; j < N; j++) for (int k = 0; k < N; k++)
        if (__builtin_parity(T[j][k] & u)) T[j][k] ^= (uint8_t)phi;
}
static int cmp_u32(const void *a, const void *b) {
    uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b;
    return x < y ? -1 : x > y;
}
static uint32_t *parent;
static uint32_t find(uint32_t x) {
    while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; }
    return x;
}
static void describe(uint32_t code) {
    printf("T on {");
    for (int j = 0; j < N; j++) if ((code >> j) & 1) printf(" %d", j);
    printf(" } CS on {");
    for (int i = 0; i < nb; i++) if ((code >> (N + i)) & 1) printf(" (%d,%d)", bj[i], bk[i]);
    printf(" } CCZ on {");
    for (int i = 0; i < nc; i++) if ((code >> (N + nb + i)) & 1) printf(" (%d,%d,%d)", cj[i], ck[i], cl[i]);
    printf(" }");
}

int main(void) {
    static const uint64_t want_forms[6] = {0, 1, 1, 8, 0, 166656};
    static const int want_rank[6] = {0, 1, 2, 2, 0, 4};
    static const int want_orbits[6] = {0, 1, 1, 2, 0, 1};
    int all_ok = 1;
    for (N = 1; N <= MAXN; N++) {
        nb = nc = 0;
        for (int j = 0; j < N; j++) for (int k = j + 1; k < N; k++) { bj[nb] = j; bk[nb] = k; bidx[j][k] = bidx[k][j] = nb++; }
        for (int j = 0; j < N; j++) for (int k = j + 1; k < N; k++) for (int l = k + 1; l < N; l++) {
            cj[nc] = j; ck[nc] = k; cl[nc] = l;
            cidx[j][k][l] = cidx[j][l][k] = cidx[k][j][l] = cidx[k][l][j] = cidx[l][j][k] = cidx[l][k][j] = nc++;
        }
        uint32_t total = 1u << (N + nb + nc);
        size_t cap = 1 << 18, n = 0;
        uint32_t *sol = malloc(cap * 4);
        int rank_seen = -1, mixed = 0;
        for (uint32_t code = 1; code < total; code++) {
            uint8_t M[MAXN][MAXN];
            build(code, M);
            int r = constant_rank(M);
            if (r < 0) continue;
            if (rank_seen >= 0 && r != rank_seen) mixed = 1;
            rank_seen = r;
            if (n == cap) { cap *= 2; sol = realloc(sol, cap * 4); }
            sol[n++] = code;
        }
        /* orbits under the transvections x -> x + x_k e_j, which generate GL(N,2) */
        parent = malloc((n + 1) * 4);
        for (size_t i = 0; i < n; i++) parent[i] = (uint32_t)i;
        size_t escaped = 0;
        for (size_t i = 0; i < n; i++) for (int j = 0; j < N; j++) for (int k = 0; k < N; k++) if (j != k) {
            uint8_t M[MAXN][MAXN];
            build(sol[i], M);
            act(M, 1u << j, 1u << k);
            uint32_t c2 = extract(M);
            uint32_t *p = bsearch(&c2, sol, n, 4, cmp_u32);
            if (!p) { escaped++; continue; }
            uint32_t a = find((uint32_t)i), b = find((uint32_t)(p - sol));
            if (a != b) parent[a] = b;
        }
        double gl = 1;
        for (int i = 0; i < N; i++) gl *= (double)((1u << N) - (1u << i));
        uint32_t *size = calloc(n + 1, 4), *best = malloc((n + 1) * 4);
        for (size_t i = 0; i < n; i++) {
            uint32_t r = find((uint32_t)i);
            if (!size[r] || __builtin_popcount(sol[i]) < __builtin_popcount(best[r])) best[r] = sol[i];
            size[r]++;
        }
        int norb = 0;
        printf("N=%d: %u forms, %llu of constant rank", N, total - 1, (unsigned long long)n);
        if (n) printf(" (rank %d: modulus 2^-%d/2 on %u observables)", rank_seen, rank_seen, ((1u << N) - 1) << rank_seen);
        printf("\n");
        for (size_t i = 0; i < n; i++) if (size[i]) {
            norb++;
            printf("   orbit of %u forms, stabiliser of order %.0f in GL(%d,2); fewest gates: ", size[i], gl / size[i], N);
            describe(best[i]);
            printf("\n");
        }
        int ok = (n == want_forms[N]) && !mixed && !escaped && (n == 0 || rank_seen == want_rank[N]) && norb == want_orbits[N];
        if (N == 5 && n) ok = ok && size[find(0)] == 166656;
        printf("%s  N=%d census as expected\n", ok ? "PASS" : "FAIL", N);
        all_ok &= ok;
        free(sol); free(parent); free(size); free(best);
    }
    printf(all_ok ? "THIRD-LEVEL-PASS\n" : "THIRD-LEVEL-FAIL\n");
    return all_ok ? 0 : 1;
}

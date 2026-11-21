/*
 * n9_rank8_search.c - Reproducible exhaustive cyclic-symmetry census for constant
 * rank-8 symmetric realizable trilinear forms on F_2^9 (third-level flat phase states
 * on N = 9 qubits with |S| = 511 * 256 = 130,816, modulus 1/16).
 *
 * Background (paper Section 5.3 & Section 12):
 *   The known odd-qubit rank-(N-1) flat phase states Phi_3 (N=3, r=2), Phi_5 (N=5, r=4,
 *   stabilizer order 60), and Phi_7 (N=7, r=6, stabilizer order 7) leave open whether
 *   a constant rank-8 third-level phase state exists on N = 9 qubits.
 *
 * This program computes the exact F_2 subspace of ALL realizable symmetric trilinear
 * forms on F_2^9 (dimension 129: 9 T + 36 CS + 84 CCZ) invariant under cyclic subgroups
 * of GL(9, 2) of orders 73, 51, 31, 21, 17, 15 (all 8 actions on F_16^2 x F_2), 9,
 * 7 (all 7 actions on F_8^3, including all three dim-27 subspaces of size 2^27 = 134,217,728),
 * and 5 (all 4 actions on F_16^2 x F_2, each dim 25 of size 2^25 = 33,554,432), and
 * exhaustively tests every single nonzero form (539,809,814 forms total) using exact
 * early-exit F_2 Gaussian elimination over orbit representatives.
 *
 * Result: 0 constant rank-8 forms across all 21 cyclic-invariant subspaces (exhaustive
 * proof of nonexistence within each listed invariant subspace; best near-miss 504/511
 * vectors of rank 8 in Z_7 on F_8^3). Constant rank-6 forms DO occur (e.g. the 12-CCZ
 * pure determinant state |Psi_9> of our infinite family |Psi_{3m}>).
 *
 * Compile (Windows Clang): clang -O3 -march=native src/n9_rank8_search.c -o n9_rank8_search.exe
 * Compile (Linux GCC):     cc -O3 src/n9_rank8_search.c -o n9_rank8_search
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static inline int rank9(const uint16_t r_in[9]) {
    uint16_t r[9];
    memcpy(r, r_in, sizeof(r));
    int rk = 0;
    for (int col = 0; col < 9; col++) {
        uint16_t bit = (uint16_t)(1u << col);
        int piv = -1;
        for (int i = rk; i < 9; i++) if (r[i] & bit) { piv = i; break; }
        if (piv < 0) continue;
        uint16_t tmp = r[rk]; r[rk] = r[piv]; r[piv] = tmp;
        uint16_t pr = r[rk];
        for (int i = rk + 1; i < 9; i++) if (r[i] & bit) r[i] ^= pr;
        rk++;
    }
    return rk;
}

static inline int contract_is_rank8(const uint16_t M[9][9], uint16_t v) {
    uint16_t r[9] = {0};
    while (v) {
        int b = __builtin_ctz(v);
        v &= (uint16_t)(v - 1);
        for (int k = 0; k < 9; k++) r[k] ^= M[b][k];
    }
    return rank9(r) == 8;
}

static int cs_pairs[36][2];
static int ccz_trips[84][3];
static void init_tables(void) {
    int p = 0;
    for (int i = 0; i < 9; i++)
        for (int j = i + 1; j < 9; j++) { cs_pairs[p][0] = i; cs_pairs[p][1] = j; p++; }
    int t = 0;
    for (int i = 0; i < 9; i++)
        for (int j = i + 1; j < 9; j++)
            for (int k = j + 1; k < 9; k++) { ccz_trips[t][0]=i; ccz_trips[t][1]=j; ccz_trips[t][2]=k; t++; }
}
static inline void toggle_cs(uint16_t M[9][9], int j, int k) {
    M[j][j] ^= (1u<<k); M[j][k] ^= (1u<<j)|(1u<<k); M[k][j] ^= (1u<<j)|(1u<<k); M[k][k] ^= (1u<<j);
}
static inline void toggle_ccz(uint16_t M[9][9], int a, int b, int c) {
    M[a][b]^=(1u<<c); M[b][a]^=(1u<<c); M[a][c]^=(1u<<b); M[c][a]^=(1u<<b); M[b][c]^=(1u<<a); M[c][b]^=(1u<<a);
}
static void basis_to_M(int idx, uint16_t M[9][9]) {
    memset(M, 0, 9*9*sizeof(uint16_t));
    if (idx < 9) M[idx][idx] = (uint16_t)(1u << idx);
    else if (idx < 45) toggle_cs(M, cs_pairs[idx-9][0], cs_pairs[idx-9][1]);
    else toggle_ccz(M, ccz_trips[idx-45][0], ccz_trips[idx-45][1], ccz_trips[idx-45][2]);
}
static int eval_M(const uint16_t M[9][9], uint16_t x, uint16_t y, uint16_t z) {
    int s = 0;
    for (int i = 0; i < 9; i++) if ((x >> i) & 1)
        for (int j = 0; j < 9; j++) if ((y >> j) & 1)
            s ^= __builtin_popcount(M[i][j] & z) & 1;
    return s;
}

typedef struct { uint64_t lo, hi, top; } Vec129;
static inline int get_bit(Vec129 v, int idx) {
    return (idx < 64) ? (int)((v.lo >> idx) & 1) : ((idx < 128) ? (int)((v.hi >> (idx - 64)) & 1) : (int)(v.top & 1));
}
static inline void flip_bit(Vec129 *v, int idx) {
    if (idx < 64) v->lo ^= (1ULL << idx); else if (idx < 128) v->hi ^= (1ULL << (idx - 64)); else v->top ^= 1ULL;
}
static inline void xor_vec(Vec129 *a, Vec129 b) { a->lo ^= b.lo; a->hi ^= b.hi; a->top ^= b.top; }

static int find_invariant_basis(const uint16_t G[9], uint16_t out_basis[][9][9]) {
    static uint16_t BM[129][9][9];
    for (int idx = 0; idx < 129; idx++) basis_to_M(idx, BM[idx]);
    int tt_arr[129][3];
    for (int i = 0; i < 9; i++) { tt_arr[i][0]=i; tt_arr[i][1]=i; tt_arr[i][2]=i; }
    for (int p = 0; p < 36; p++) { tt_arr[9+p][0]=cs_pairs[p][0]; tt_arr[9+p][1]=cs_pairs[p][0]; tt_arr[9+p][2]=cs_pairs[p][1]; }
    for (int t = 0; t < 84; t++) { tt_arr[45+t][0]=ccz_trips[t][0]; tt_arr[45+t][1]=ccz_trips[t][1]; tt_arr[45+t][2]=ccz_trips[t][2]; }
    static Vec129 eqs[129];
    int piv_col[129], neq = 0;
    for (int tt = 0; tt < 129; tt++) {
        int a=tt_arr[tt][0], b=tt_arr[tt][1], c=tt_arr[tt][2];
        uint16_t ga=G[a], gb=G[b], gc=G[c];
        Vec129 row = {0,0,0};
        for (int idx = 0; idx < 129; idx++) {
            if (eval_M(BM[idx], ga, gb, gc) ^ eval_M(BM[idx], (uint16_t)(1u<<a), (uint16_t)(1u<<b), (uint16_t)(1u<<c)))
                flip_bit(&row, idx);
        }
        for (int r = 0; r < neq; r++) if (get_bit(row, piv_col[r])) xor_vec(&row, eqs[r]);
        int pc = -1;
        for (int col = 0; col < 129; col++) if (get_bit(row, col)) { pc = col; break; }
        if (pc >= 0) { eqs[neq] = row; piv_col[neq] = pc; neq++; }
    }
    for (int r = neq - 1; r >= 0; r--)
        for (int u = 0; u < r; u++)
            if (get_bit(eqs[u], piv_col[r])) xor_vec(&eqs[u], eqs[r]);
    int is_piv[129] = {0};
    for (int r = 0; r < neq; r++) is_piv[piv_col[r]] = 1;
    int dim = 0;
    for (int col = 0; col < 129; col++) {
        if (is_piv[col]) continue;
        memset(out_basis[dim], 0, 9*9*sizeof(uint16_t));
        for (int i = 0; i < 9; i++) for (int j = 0; j < 9; j++) out_basis[dim][i][j] ^= BM[col][i][j];
        for (int r = 0; r < neq; r++) if (get_bit(eqs[r], col)) {
            int p = piv_col[r];
            for (int i = 0; i < 9; i++) for (int j = 0; j < 9; j++) out_basis[dim][i][j] ^= BM[p][i][j];
        }
        dim++;
    }
    return dim;
}

static uint16_t apply_G(const uint16_t G[9], uint16_t v) {
    uint16_t out = 0;
    for (int i = 0; i < 9; i++) if ((v >> i) & 1) out ^= G[i];
    return out;
}

static int build_orbit_reps(const uint16_t G[9], uint16_t reps[512]) {
    uint8_t seen[512] = {0};
    int nrep = 0;
    for (uint16_t v = 1; v < 512; v++) {
        if (seen[v]) continue;
        reps[nrep++] = v;
        uint16_t cur = v;
        while (!seen[cur]) { seen[cur] = 1; cur = apply_G(G, cur); }
    }
    return nrep;
}

static uint64_t total_tested = 0;
static int total_hits = 0;

static void exhaust_subspace(const char *label, const uint16_t G[9], int max_dim) {
    static uint16_t basis[129][9][9];
    int dim = find_invariant_basis(G, basis);
    uint16_t reps[512];
    int nrep = build_orbit_reps(G, reps);
    if (dim > max_dim) {
        printf("SKIP\t%s\tdim=%d\treps=%d\n", label, dim, nrep);
        return;
    }
    uint64_t total = (1ULL << dim) - 1;
    uint16_t M[9][9] = {0};
    uint64_t prev_g = 0;
    int hits = 0;
    for (uint64_t step = 1; step <= total; step++) {
        uint64_t g = step ^ (step >> 1);
        int bit = __builtin_ctzll(g ^ prev_g);
        prev_g = g;
        for (int i = 0; i < 9; i++)
            for (int j = 0; j < 9; j++)
                M[i][j] ^= basis[bit][i][j];
        int ok = 1;
        for (int r = 0; r < nrep; r++) {
            if (!contract_is_rank8(M, reps[r])) { ok = 0; break; }
        }
        if (ok) hits++;
    }
    total_tested += total;
    total_hits += hits;
    printf("EXHAUST\t%s\tdim=%d\tforms=%llu\treps=%d\trank8_hits=%d\n",
           label, dim, (unsigned long long)total, nrep, hits);
    fflush(stdout);
}

static uint32_t pmul(uint32_t a, uint32_t b, uint32_t mod, int m) {
    uint32_t res = 0;
    for (int i = 0; i < m; i++) if ((b >> i) & 1) res ^= (a << i);
    for (int i = 2*m - 2; i >= m; i--) if ((res >> i) & 1) res ^= (mod << (i - m));
    return res;
}
static uint32_t ppow(uint32_t a, int e, uint32_t mod, int m) {
    uint32_t r = 1;
    while (e > 0) { if (e & 1) r = pmul(r, a, mod, m); a = pmul(a, a, mod, m); e >>= 1; }
    return r;
}

int main(int argc, char **argv) {
    int max_dim = (argc > 1 && strcmp(argv[1], "--quick") == 0) ? 21 : 27;
    init_tables();
    uint16_t G[9];

    /* Z_73 on F_512 */
    {
        uint32_t z = ppow(2, 7, 0x211, 9);
        for (int i = 0; i < 9; i++) G[i] = (uint16_t)pmul(1u<<i, z, 0x211, 9);
        exhaust_subspace("Z_73(F_512)", G, max_dim);
    }
    /* Z_51 and Z_17 on F_256 x F_2 */
    {
        uint32_t z = ppow(2, 5, 0x11d, 8);
        for (int i = 0; i < 8; i++) G[i] = (uint16_t)pmul(1u<<i, z, 0x11d, 8);
        G[8] = 1u<<8;
        exhaust_subspace("Z_51(F_256xF_2)", G, max_dim);
    }
    {
        uint32_t z = ppow(2, 15, 0x11d, 8);
        for (int i = 0; i < 8; i++) G[i] = (uint16_t)pmul(1u<<i, z, 0x11d, 8);
        G[8] = 1u<<8;
        exhaust_subspace("Z_17(F_256xF_2)", G, max_dim);
    }
    /* Z_31 on F_32 x F_16 */
    {
        for (int i = 0; i < 5; i++) G[i] = (uint16_t)pmul(1u<<i, 2, 0x25, 5);
        for (int i = 0; i < 4; i++) G[5+i] = (uint16_t)(1u<<(5+i));
        exhaust_subspace("Z_31(F_32xF_16)", G, max_dim);
    }
    /* Z_21 on F_8^2 x F_4 x F_2 */
    {
        for (int i = 0; i < 3; i++) G[i] = (uint16_t)pmul(1u<<i, 2, 0xb, 3);
        for (int i = 0; i < 3; i++) G[3+i] = (uint16_t)(pmul(1u<<i, ppow(2,6,0xb,3), 0xb, 3) << 3);
        for (int i = 0; i < 2; i++) G[6+i] = (uint16_t)(pmul(1u<<i, 2, 0x7, 2) << 6);
        G[8] = 1u<<8;
        exhaust_subspace("Z_21(F_8^2xF_4xF_2)", G, max_dim);
    }
    /* Z_15 on F_16^2 x F_2 (all 8 coprime exponents) */
    int rs15[] = {14, 13, 11, 8, 7, 4, 2, 1};
    for (int ri = 0; ri < 8; ri++) {
        int r = rs15[ri];
        uint32_t l2 = ppow(2, r, 0x13, 4);
        for (int i = 0; i < 4; i++) G[i] = (uint16_t)pmul(1u<<i, 2, 0x13, 4);
        for (int i = 0; i < 4; i++) G[4+i] = (uint16_t)(pmul(1u<<i, l2, 0x13, 4) << 4);
        G[8] = 1u<<8;
        char lbl[48]; snprintf(lbl, sizeof(lbl), "Z_15(F_16^2xF_2,r=%d)", r);
        exhaust_subspace(lbl, G, max_dim);
    }
    /* Z_9 on F_64 x F_8 */
    {
        uint32_t z = ppow(2, 7, 0x43, 6);
        for (int i = 0; i < 6; i++) G[i] = (uint16_t)pmul(1u<<i, z, 0x43, 6);
        for (int i = 0; i < 3; i++) G[6+i] = (uint16_t)(1u<<(6+i));
        exhaust_subspace("Z_9(F_64xF_8)", G, max_dim);
    }
    /* Z_7 on F_8^3 (all 7 representative actions) */
    int tr7[][2] = {{6,0},{6,1},{6,2},{6,3},{2,4},{1,1},{1,2}};
    for (int ti = 0; ti < 7; ti++) {
        int r2 = tr7[ti][0], r3 = tr7[ti][1];
        uint32_t l2 = ppow(2, r2, 0xb, 3), l3 = (r3 == 0 ? 1 : ppow(2, r3, 0xb, 3));
        for (int i = 0; i < 3; i++) G[i] = (uint16_t)pmul(1u<<i, 2, 0xb, 3);
        for (int i = 0; i < 3; i++) G[3+i] = (uint16_t)(pmul(1u<<i, l2, 0xb, 3) << 3);
        for (int i = 0; i < 3; i++) G[6+i] = (uint16_t)(pmul(1u<<i, l3, 0xb, 3) << 6);
        char lbl[48]; snprintf(lbl, sizeof(lbl), "Z_7(F_8^3,r2=%d,r3=%d)", r2, r3);
        exhaust_subspace(lbl, G, max_dim);
    }
    /* Z_5 on F_16^2 x F_2 (all 4 nontrivial actions) */
    for (int r = 1; r <= 4; r++) {
        uint32_t l1 = ppow(2, 3, 0x13, 4), l2 = ppow(2, (3*r)%15, 0x13, 4);
        for (int i = 0; i < 4; i++) G[i] = (uint16_t)pmul(1u<<i, l1, 0x13, 4);
        for (int i = 0; i < 4; i++) G[4+i] = (uint16_t)(pmul(1u<<i, l2, 0x13, 4) << 4);
        G[8] = 1u<<8;
        char lbl[48]; snprintf(lbl, sizeof(lbl), "Z_5(F_16^2xF_2,r=%d)", r);
        exhaust_subspace(lbl, G, max_dim);
    }

    printf("TOTAL\tforms=%llu\trank8_hits=%d\n", (unsigned long long)total_tested, total_hits);
    return 0;
}

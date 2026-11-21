/*
 * w52_census_verify.c - Clean, independent, multithreaded exact census of all
 * W(5,2) noncontextual assignment classes with n <= 92 violated contexts.
 *
 * Mathematical basis (cf. Jonah [J1], Section 3, Lemmas L1-L4):
 *   1. On W(5,2) (63 nonzero 3-qubit Paulis, 315 contexts), the F_2 line-incidence
 *      kernel has dimension 7: the 6 Pauli gauge functionals <g, .> together with
 *      the transpose-parity quadratic form q_0(v) = (#Y(v) mod 2), which satisfies
 *      q_0(u ^ v) = q_0(u) ^ q_0(v) on every commuting triple.
 *   2. Every line of W(5,2) lies in 15 of the 63 hyperplanes u^perp, and
 *      15 * 92 = 1380 < 1386 = 63 * 22, so every assignment with n <= 92 has at
 *      least one hyperplane H = u^perp with n_H <= 21.
 *   3. Fixing u_0 = Z_0 (label 8), the kernel restricts to a 6-dim space on H (31
 *      points, 75 lines), giving 2^25 canonical classes on H and 2^31 completions on
 *      O = W(5,2) \ H (total 2^56 canonical classes on W(5,2)).
 *   4. Enumerates ALL 2^25 classes on H (no pruning), collapses those with n_H <= 21
 *      under the u_0-stabilizer in Sp(6,2) (order 23,040), enumerates ALL 2^31
 *      completions on O for each stabilizer orbit representative (no pruning),
 *      and closes the resulting set C_0 under the 63 Clifford transvections
 *      generating Sp(6,2) (order 1,451,520) via BFS.
 *
 * Author: Alexander S. Donahue (0thernes LLC) / Hoggar Bound Lab (v1.8.0).
 * Compile (Windows MSVC/Clang): clang -O3 -march=native src/w52_census_verify.c -o w52_census_verify.exe
 * Compile (Linux GCC/Clang):    cc -O3 -pthread src/w52_census_verify.c -o w52_census_verify
 */
#ifndef _CRT_SECURE_NO_WARNINGS
#define _CRT_SECURE_NO_WARNINGS
#endif

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#else
#include <pthread.h>
#include <unistd.h>
#endif

static inline int popcnt32(uint32_t x) { return __builtin_popcount(x); }
static inline int popcnt64(uint64_t x) { return __builtin_popcountll(x); }
static inline int ctz32(uint32_t x) { return __builtin_ctz(x); }

/* 3-qubit Pauli label v = a + 8*c in 1..63 (a = X-bits, c = Z-bits). */
static int symp(int u, int v) {
    return (popcnt32((u & 7) & (v >> 3)) ^ popcnt32((u >> 3) & (v & 7))) & 1;
}
static int q0(int v) {
    return popcnt32((v & 7) & (v >> 3)) & 1;
}
/* P_u P_v = i^{pow} P_{u^v}; returns pow mod 4. */
static int pauli_mul_ipow(int u, int v) {
    int au = u & 7, cu = u >> 3, av = v & 7, cv = v >> 3;
    return (popcnt32(au & cu) + popcnt32(av & cv)
            + 2 * popcnt32(cu & av) + 3 * popcnt32((au ^ av) & (cu ^ cv))) & 3;
}
/* For commuting u, v: returns 0 if P_u P_v = +P_{u^v}, 1 if -P_{u^v}. */
static int line_sign_bit(int u, int v) {
    int k = pauli_mul_ipow(u, v);
    if (k != 0 && k != 2) { fprintf(stderr, "FATAL: non-commuting line_sign_bit\n"); exit(2); }
    return (k == 2) ? 1 : 0;
}

/* Transvection U_r = (I + i P_r)/sqrt(2):
 * For symp(r, v) == 0: U_r P_v U_r^dag = P_v.
 * For symp(r, v) == 1: U_r P_v U_r^dag = i P_r P_v = (-1)^{eta_r(v)} P_{v^r}. */
static int transv_img[64][64];
static uint64_t transv_flip[64]; /* bit (v-1) set iff eta_r(v) = 1 */

static void init_transvections(void) {
    for (int r = 1; r < 64; r++) {
        uint64_t fl = 0;
        for (int v = 1; v < 64; v++) {
            if (symp(r, v) == 0) {
                transv_img[r][v] = v;
            } else {
                transv_img[r][v] = v ^ r;
                int ip = (1 + pauli_mul_ipow(r, v)) & 3; /* i * i^{pow} = +-1 */
                if (ip != 0 && ip != 2) { fprintf(stderr, "FATAL: transv ip=%d\n", ip); exit(2); }
                if (ip == 2) fl |= (1ULL << (v - 1));
            }
        }
        transv_flip[r] = fl;
    }
}

/* 7-dimensional line-incidence kernel on W(5,2) (63 bits: bit (v-1) for v=1..63).
 * Pivot points (guaranteed invertible 7x7 over F_2):
 *   Inside H = Z_0^perp (v & 1 == 0): 2, 4, 8, 16, 32, 18 (note q0(18) = 1, q0(2,4,8,16,32) = 0).
 *   Inside O (v & 1 == 1): 1. */
static const int PIVOTS[7] = {2, 4, 8, 16, 32, 18, 1};
static uint64_t canon_masks[7]; /* canon_masks[p] is in the 7-dim kernel and has bit (PIVOTS[q]-1) == delta_{p,q} */

static void init_canonicalizer(void) {
    uint64_t raw[7] = {0};
    for (int g = 0; g < 6; g++) {
        int gv = 1 << g;
        for (int v = 1; v < 64; v++)
            if (symp(gv, v)) raw[g] |= (1ULL << (v - 1));
    }
    for (int v = 1; v < 64; v++)
        if (q0(v)) raw[6] |= (1ULL << (v - 1));

    /* Gaussian elimination to make raw[p] dual to PIVOTS[0..6] */
    uint64_t M[7];
    memcpy(M, raw, sizeof(M));
    for (int col = 0; col < 7; col++) {
        uint64_t pbit = 1ULL << (PIVOTS[col] - 1);
        int piv = -1;
        for (int r = col; r < 7; r++) if (M[r] & pbit) { piv = r; break; }
        if (piv < 0) { fprintf(stderr, "FATAL: pivot matrix singular at col %d\n", col); exit(2); }
        uint64_t tmp = M[col]; M[col] = M[piv]; M[piv] = tmp;
        for (int r = 0; r < 7; r++) if (r != col && (M[r] & pbit)) M[r] ^= M[col];
    }
    memcpy(canon_masks, M, sizeof(M));
}

static inline uint64_t canonicalize(uint64_t y) {
    for (int p = 0; p < 7; p++) {
        if ((y >> (PIVOTS[p] - 1)) & 1ULL) y ^= canon_masks[p];
    }
    return y;
}

/* Apply transvection t_r to assignment y (bit (v-1) = sign bit of P_v):
 * (t_r . y)(v) = eta_r(v) ^ y(t_r(v)), then canonicalize. */
static inline uint64_t apply_transv(int r, uint64_t y) {
    uint64_t out = transv_flip[r];
    /* Note: for symp(r,v)==0, img is v; for symp(r,v)==1, img is v^r. */
    for (int v = 1; v < 64; v++) {
        int src = transv_img[r][v];
        if ((y >> (src - 1)) & 1ULL) out ^= (1ULL << (v - 1));
    }
    return canonicalize(out);
}

/* Geometry tables for W(5,2), H = Z_0^perp (31 pts, 75 lines), O (32 pts, 240 outside lines). */
static int H_pts[31], O_pts[32];
static int H_free[25], O_free[31]; /* non-pivot points of H and O */
static int lines_all[315][4]; /* (u, v, w, s_bit) */
static int lines_H[75][4];
static int lines_O[240][4];

static int count_viol_all(uint64_t y) {
    int c = 0;
    for (int i = 0; i < 315; i++) {
        int a = (int)((y >> (lines_all[i][0] - 1)) & 1ULL);
        int b = (int)((y >> (lines_all[i][1] - 1)) & 1ULL);
        int d = (int)((y >> (lines_all[i][2] - 1)) & 1ULL);
        c += (a ^ b ^ d ^ lines_all[i][3]);
    }
    return c;
}

static int count_viol_H(uint64_t y) {
    int c = 0;
    for (int i = 0; i < 75; i++) {
        int a = (int)((y >> (lines_H[i][0] - 1)) & 1ULL);
        int b = (int)((y >> (lines_H[i][1] - 1)) & 1ULL);
        int d = (int)((y >> (lines_H[i][2] - 1)) & 1ULL);
        c += (a ^ b ^ d ^ lines_H[i][3]);
    }
    return c;
}

static int is_pivot(int v) {
    for (int p = 0; p < 7; p++) if (PIVOTS[p] == v) return 1;
    return 0;
}

static void init_geometry(void) {
    int nh = 0, no = 0, nhf = 0, nof = 0;
    for (int v = 1; v < 64; v++) {
        if ((v & 1) == 0) {
            H_pts[nh++] = v;
            if (!is_pivot(v)) H_free[nhf++] = v;
        } else {
            O_pts[no++] = v;
            if (!is_pivot(v)) O_free[nof++] = v;
        }
    }
    if (nh != 31 || no != 32 || nhf != 25 || nof != 31) {
        fprintf(stderr, "FATAL: geom sizes %d %d %d %d\n", nh, no, nhf, nof);
        exit(2);
    }
    int na = 0, nlh = 0, nlo = 0;
    for (int u = 1; u < 64; u++)
        for (int v = u + 1; v < 64; v++)
            if (symp(u, v) == 0) {
                int w = u ^ v;
                if (w > v) {
                    int s = line_sign_bit(u, v);
                    lines_all[na][0] = u; lines_all[na][1] = v; lines_all[na][2] = w; lines_all[na][3] = s;
                    na++;
                    if ((u & 1) == 0 && (v & 1) == 0) {
                        lines_H[nlh][0] = u; lines_H[nlh][1] = v; lines_H[nlh][2] = w; lines_H[nlh][3] = s;
                        nlh++;
                    } else {
                        /* Ensure lines_O[nlo][0] is the unique point in H, and [1],[2] are in O! */
                        int hpt, o1, o2;
                        if ((u & 1) == 0) { hpt = u; o1 = v; o2 = w; }
                        else if ((v & 1) == 0) { hpt = v; o1 = u; o2 = w; }
                        else { hpt = w; o1 = u; o2 = v; }
                        lines_O[nlo][0] = hpt; lines_O[nlo][1] = o1; lines_O[nlo][2] = o2; lines_O[nlo][3] = s;
                        nlo++;
                    }
                }
            }
    if (na != 315 || nlh != 75 || nlo != 240) {
        fprintf(stderr, "FATAL: line counts %d %d %d\n", na, nlh, nlo);
        exit(2);
    }
}

/* Open-addressing hash set for uint64_t keys (0 is invalid? No, 0 CAN be a valid canonical key!
 * Store key + 1 so 0 means empty slot!). */
typedef struct {
    uint64_t *tab;
    size_t cap; /* power of 2 */
    size_t mask;
    size_t count;
} HashSet;

static inline uint64_t hash64(uint64_t x) {
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27; x *= 0x94d049bb133111ebULL;
    x ^= x >> 31;
    return x;
}

static void hs_init(HashSet *hs, size_t cap_pow2) {
    hs->cap = cap_pow2;
    hs->mask = cap_pow2 - 1;
    hs->count = 0;
    hs->tab = (uint64_t *)calloc(cap_pow2, sizeof(uint64_t));
    if (!hs->tab) { fprintf(stderr, "FATAL: OOM allocating hash set (%zu entries)\n", cap_pow2); exit(2); }
}
static void hs_free(HashSet *hs) { free(hs->tab); hs->tab = NULL; }

static inline int hs_insert(HashSet *hs, uint64_t key) {
    uint64_t val = key + 1;
    size_t idx = (size_t)hash64(key) & hs->mask;
    while (1) {
        uint64_t cur = hs->tab[idx];
        if (cur == 0) {
            hs->tab[idx] = val;
            hs->count++;
            return 1;
        }
        if (cur == val) return 0;
        idx = (idx + 1) & hs->mask;
    }
}

static inline int hs_contains(const HashSet *hs, uint64_t key) {
    uint64_t val = key + 1;
    size_t idx = (size_t)hash64(key) & hs->mask;
    while (1) {
        uint64_t cur = hs->tab[idx];
        if (cur == 0) return 0;
        if (cur == val) return 1;
        idx = (idx + 1) & hs->mask;
    }
}

/* Canonicalize restriction to H (only bits in H_pts matter, zero out O bits and apply first 6 canon_masks). */
static uint64_t H_mask_bits = 0;
static void init_H_mask(void) {
    for (int i = 0; i < 31; i++) H_mask_bits |= (1ULL << (H_pts[i] - 1));
}
static inline uint64_t canon_H(uint64_t yH) {
    yH &= H_mask_bits;
    for (int p = 0; p < 6; p++) {
        if ((yH >> (PIVOTS[p] - 1)) & 1ULL) yH ^= (canon_masks[p] & H_mask_bits);
    }
    return yH;
}
/* Stabilizer of u0 = 8 in Sp(6,2) is generated by transvections t_r with r in H (31 of them)! */
static inline uint64_t apply_stab_H(int r, uint64_t yH) {
    uint64_t out = transv_flip[r] & H_mask_bits;
    for (int i = 0; i < 31; i++) {
        int v = H_pts[i];
        int src = transv_img[r][v];
        if ((yH >> (src - 1)) & 1ULL) out ^= (1ULL << (v - 1));
    }
    return canon_H(out);
}

/* Worker thread for exhaustive 2^31 completion enumeration of one H-orbit representative! */
typedef struct {
    int orb_id;
    uint64_t yH;
    int nH;
    int orb_size_H;
    uint64_t *hits;
    size_t nhits;
    size_t cap;
} ExtJob;

static uint64_t O_inc_0[31], O_inc_1[31], O_inc_2[31], O_inc_3[31]; /* 240 outside lines = 4 x 60 bits */

static void init_O_inc(void) {
    memset(O_inc_0, 0, sizeof(O_inc_0));
    memset(O_inc_1, 0, sizeof(O_inc_1));
    memset(O_inc_2, 0, sizeof(O_inc_2));
    memset(O_inc_3, 0, sizeof(O_inc_3));
    int pos_in_Ofree[64];
    for (int i = 0; i < 64; i++) pos_in_Ofree[i] = -1;
    for (int i = 0; i < 31; i++) pos_in_Ofree[O_free[i]] = i;
    for (int l = 0; l < 240; l++) {
        int p1 = pos_in_Ofree[lines_O[l][1]];
        int p2 = pos_in_Ofree[lines_O[l][2]];
        int blk = l / 60, sh = l % 60;
        uint64_t bit = 1ULL << sh;
        int pts2[2] = {p1, p2};
        for (int t = 0; t < 2; t++) {
            int p = pts2[t];
            if (p < 0) continue; /* pivot point 1 is fixed to 0 */
            if (blk == 0) O_inc_0[p] |= bit;
            else if (blk == 1) O_inc_1[p] |= bit;
            else if (blk == 2) O_inc_2[p] |= bit;
            else O_inc_3[p] |= bit;
        }
    }
}

/* Split a single 2^31 job into 4 sub-ranges (by fixing top 2 bits) or run one thread per H-orbit! */
static void run_ext_job(ExtJob *job) {
    int max_nO = 92 - job->nH;
    uint64_t s0 = 0, s1 = 0, s2 = 0, s3 = 0;
    for (int l = 0; l < 240; l++) {
        int hbit = (int)((job->yH >> (lines_O[l][0] - 1)) & 1ULL);
        int v = hbit ^ lines_O[l][3];
        if (v) {
            int blk = l / 60, sh = l % 60;
            uint64_t bit = 1ULL << sh;
            if (blk == 0) s0 |= bit;
            else if (blk == 1) s1 |= bit;
            else if (blk == 2) s2 |= bit;
            else s3 |= bit;
        }
    }

    job->cap = 1024;
    job->nhits = 0;
    job->hits = (uint64_t *)malloc(job->cap * sizeof(uint64_t));

    /* Precompute bit-mask of O_free[b] in full 63-bit y representation */
    uint64_t y_bit[31];
    for (int b = 0; b < 31; b++) y_bit[b] = 1ULL << (O_free[b] - 1);

    uint64_t cur_y = job->yH;
    int nO = popcnt64(s0) + popcnt64(s1) + popcnt64(s2) + popcnt64(s3);
    if (nO <= max_nO) {
        job->hits[job->nhits++] = cur_y;
    }

    /* Full unpruned Gray-code sweep over all 2^31 completions! */
    uint32_t prev_g = 0;
    for (uint32_t step = 1; step < (1u << 31); step++) {
        uint32_t g = step ^ (step >> 1);
        int b = ctz32(g ^ prev_g);
        prev_g = g;
        cur_y ^= y_bit[b];
        s0 ^= O_inc_0[b];
        s1 ^= O_inc_1[b];
        s2 ^= O_inc_2[b];
        s3 ^= O_inc_3[b];
        nO = popcnt64(s0) + popcnt64(s1) + popcnt64(s2) + popcnt64(s3);
        if (nO <= max_nO) {
            if (job->nhits == job->cap) {
                job->cap *= 2;
                job->hits = (uint64_t *)realloc(job->hits, job->cap * sizeof(uint64_t));
            }
            job->hits[job->nhits++] = cur_y;
        }
    }
}

#ifdef _WIN32
static DWORD WINAPI win_thread_fn(LPVOID arg) {
    run_ext_job((ExtJob *)arg);
    return 0;
}
#else
static void *posix_thread_fn(void *arg) {
    run_ext_job((ExtJob *)arg);
    return NULL;
}
#endif

int main(int argc, char **argv) {
    const char *out_tsv = (argc > 1) ? argv[1] : NULL;
    clock_t t0 = clock();

    init_transvections();
    init_canonicalizer();
    init_geometry();
    init_H_mask();
    init_O_inc();

    /* Step 1: Exhaustive enumeration of all 2^25 canonical classes on H = Z_0^perp */
    uint64_t inc_lo[25] = {0}, inc_hi[25] = {0};
    int posH[64];
    for (int i = 0; i < 64; i++) posH[i] = -1;
    for (int i = 0; i < 25; i++) posH[H_free[i]] = i;
    for (int l = 0; l < 75; l++) {
        for (int t = 0; t < 3; t++) {
            int p = posH[lines_H[l][t]];
            if (p >= 0) {
                if (l < 64) inc_lo[p] |= (1ULL << l);
                else inc_hi[p] |= (1ULL << (l - 64));
            }
        }
    }
    uint64_t v_lo = 0, v_hi = 0;
    for (int l = 0; l < 75; l++) if (lines_H[l][3]) {
        if (l < 64) v_lo |= (1ULL << l); else v_hi |= (1ULL << (l - 64));
    }
    uint64_t yH_bit[25];
    for (int b = 0; b < 25; b++) yH_bit[b] = 1ULL << (H_free[b] - 1);

    uint64_t *H_low = (uint64_t *)malloc(65536 * sizeof(uint64_t));
    size_t nH_low = 0;
    uint64_t cur_yH = 0;
    if (popcnt64(v_lo) + popcnt64(v_hi) <= 21) H_low[nH_low++] = cur_yH;
    uint32_t prev_g = 0;
    for (uint32_t step = 1; step < (1u << 25); step++) {
        uint32_t g = step ^ (step >> 1);
        int b = ctz32(g ^ prev_g);
        prev_g = g;
        cur_yH ^= yH_bit[b];
        v_lo ^= inc_lo[b];
        v_hi ^= inc_hi[b];
        if (popcnt64(v_lo) + popcnt64(v_hi) <= 21) {
            H_low[nH_low++] = cur_yH;
        }
    }
    printf("Step 1 (all 2^25 classes on H): %zu classes with n_H <= 21 (expected 18752)\n", nH_low);
    fflush(stdout);

    /* Step 2: Collapse H_low into stabilizer orbits under the 31 transvections r in H */
    HashSet H_vis;
    hs_init(&H_vis, 1 << 16);
    uint64_t *qH = (uint64_t *)malloc(65536 * sizeof(uint64_t));
    ExtJob jobs[64];
    int n_horbs = 0;
    for (size_t i = 0; i < nH_low; i++) {
        uint64_t y0 = H_low[i];
        if (!hs_insert(&H_vis, y0)) continue;
        size_t head = 0, tail = 0;
        qH[tail++] = y0;
        while (head < tail) {
            uint64_t cur = qH[head++];
            for (int k = 0; k < 31; k++) {
                uint64_t nxt = apply_stab_H(H_pts[k], cur);
                if (hs_insert(&H_vis, nxt)) qH[tail++] = nxt;
            }
        }
        jobs[n_horbs].orb_id = n_horbs;
        jobs[n_horbs].yH = y0;
        jobs[n_horbs].nH = count_viol_H(y0);
        jobs[n_horbs].orb_size_H = (int)tail;
        n_horbs++;
    }
    printf("Step 2 (u_0-stabilizer orbits on H): %d orbits (expected 18), total=%zu\n", n_horbs, H_vis.count);
    for (int i = 0; i < n_horbs; i++) {
        printf("  H-orbit %2d: n_H=%2d, size=%5d\n", i, jobs[i].nH, jobs[i].orb_size_H);
    }
    fflush(stdout);
    hs_free(&H_vis);
    free(qH);
    free(H_low);

    /* Step 3: Exhaustive unpruned 2^31 completions for all 18 H-orbit reps in parallel! */
    printf("Step 3: Launching %d parallel exhaustive 2^31 completion threads...\n", n_horbs);
    fflush(stdout);
#ifdef _WIN32
    HANDLE th[64];
    for (int i = 0; i < n_horbs; i++) {
        th[i] = CreateThread(NULL, 0, win_thread_fn, &jobs[i], 0, NULL);
    }
    WaitForMultipleObjects(n_horbs, th, TRUE, INFINITE);
    for (int i = 0; i < n_horbs; i++) CloseHandle(th[i]);
#else
    pthread_t th[64];
    for (int i = 0; i < n_horbs; i++) pthread_create(&th[i], NULL, posix_thread_fn, &jobs[i]);
    for (int i = 0; i < n_horbs; i++) pthread_join(th[i], NULL);
#endif

    uint64_t C0_total = 0;
    size_t raw_seeds = 0;
    for (int i = 0; i < n_horbs; i++) {
        C0_total += (uint64_t)jobs[i].orb_size_H * (uint64_t)jobs[i].nhits;
        raw_seeds += jobs[i].nhits;
        printf("  H-orbit %2d (n_H=%2d, size=%5d): %zu completions with n<=92\n",
               i, jobs[i].nH, jobs[i].orb_size_H, jobs[i].nhits);
    }
    printf("Step 3 done: |C_0| = %llu (expected 9017680), raw seeds = %zu\n",
           (unsigned long long)C0_total, raw_seeds);
    fflush(stdout);

    /* Step 4: BFS closure of all raw seeds under the 63 transvections of Sp(6,2)! */
    printf("Step 4: BFS closure under Sp(6,2) (63 transvections)...\n");
    fflush(stdout);
    HashSet visited;
    hs_init(&visited, 1ULL << 25); /* 33,554,432 slots for 17,652,160 classes (~52% load) */
    uint64_t *queue = (uint64_t *)malloc(20000000ULL * sizeof(uint64_t));
    if (!queue) { fprintf(stderr, "FATAL: OOM queue\n"); exit(2); }

    int n_orbits = 0;
    uint64_t orb_rep[128];
    int orb_n[128];
    size_t orb_size[128];
    uint64_t orb_c0[128];

    for (int ji = 0; ji < n_horbs; ji++) {
        for (size_t si = 0; si < jobs[ji].nhits; si++) {
            uint64_t seed = jobs[ji].hits[si];
            if (!hs_insert(&visited, seed)) continue;
            size_t head = 0, tail = 0;
            queue[tail++] = seed;
            uint64_t c0_cnt = 0;
            int nval = count_viol_all(seed);
            while (head < tail) {
                uint64_t cur = queue[head++];
                if (count_viol_H(cur) <= 21) c0_cnt++;
                for (int r = 1; r < 64; r++) {
                    uint64_t nxt = apply_transv(r, cur);
                    if (hs_insert(&visited, nxt)) queue[tail++] = nxt;
                }
            }
            orb_rep[n_orbits] = seed;
            orb_n[n_orbits] = nval;
            orb_size[n_orbits] = tail;
            orb_c0[n_orbits] = c0_cnt;
            n_orbits++;
        }
        free(jobs[ji].hits);
    }

    uint64_t sum_sizes = 0, sum_c0 = 0;
    for (int i = 0; i < n_orbits; i++) {
        sum_sizes += orb_size[i];
        sum_c0 += orb_c0[i];
    }

    double elapsed = (double)(clock() - t0) / CLOCKS_PER_SEC;
    printf("\n=== W(5,2) n <= 92 CENSUS COMPLETE (CPU-time %.1fs) ===\n", elapsed);
    printf("Orbits found : %d (expected 42)\n", n_orbits);
    printf("Total classes: %llu (expected 17652160)\n", (unsigned long long)sum_sizes);
    printf("Recount |C_0|: %llu (expected 9017680, step3=%llu)\n",
           (unsigned long long)sum_c0, (unsigned long long)C0_total);

    if (out_tsv) {
        FILE *fp = fopen(out_tsv, "w");
        if (!fp) { fprintf(stderr, "FATAL: cannot write %s\n", out_tsv); exit(2); }
        fprintf(fp, "orbit\tn\tsize\tc0_count\trep_hex\n");
        for (int i = 0; i < n_orbits; i++) {
            fprintf(fp, "%d\t%d\t%zu\t%llu\t%016llx\n",
                    i, orb_n[i], orb_size[i], (unsigned long long)orb_c0[i],
                    (unsigned long long)orb_rep[i]);
        }
        fclose(fp);
        printf("Wrote %s\n", out_tsv);
    }

    free(queue);
    hs_free(&visited);

    if (n_orbits != 42 || sum_sizes != 17652160ULL || sum_c0 != 9017680ULL || C0_total != 9017680ULL) {
        fprintf(stderr, "FAIL: census totals mismatch!\n");
        return 1;
    }
    printf("PASS: exact independent match (42 orbits, 17,652,160 classes, |C_0| = 9,017,680)\n");
    return 0;
}

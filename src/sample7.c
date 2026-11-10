/* sample7.c - random census of third-level forms on seven qubits by the type of B = T(x,x,.).
 *
 *   p(x) = sum_{j<k} x_j  +  2 sum_{i<m} x_{2i} x_{2i+1}  +  4 w(x)      (mod 8)
 *
 * k T gates on qubits 0..k-1 (B = identity of rank k) or m CS gates on disjoint pairs (B alternating of
 * rank 2m), plus a uniformly random set w of CCZ gates (35 bits).  Counts the forms for which the rank of
 * T(v,.,.) is the same for every v != 0, by that rank.
 *
 * usage: sample7 k m samples seed
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
static uint64_t state;
static inline uint64_t rnd(void) {
    state ^= state << 13; state ^= state >> 7; state ^= state << 17;
    return state * 0x2545F4914F6CDD1DULL;
}

int main(int argc, char **argv) {
    int k = argc > 1 ? atoi(argv[1]) : 0;
    int m = argc > 2 ? atoi(argv[2]) : 3;
    uint64_t samples = argc > 3 ? strtoull(argv[3], NULL, 0) : 1000000;
    state = argc > 4 ? strtoull(argv[4], NULL, 0) : 88172645463325252ULL;
    int tj[35], tk[35], tl[35], nt = 0;
    for (int j = 0; j < N; j++) for (int a = j + 1; a < N; a++) for (int l = a + 1; l < N; l++) { tj[nt] = j; tk[nt] = a; tl[nt] = l; nt++; }
    uint32_t base[N][N];
    for (int j = 0; j < N; j++) for (int a = 0; a < N; a++) base[j][a] = 0;
    for (int j = 0; j < k; j++) base[j][j] ^= 1u << j;
    for (int i = 0; i < m; i++) {
        int j = 2 * i, a = 2 * i + 1;
        base[j][j] ^= 1u << a; base[j][a] ^= 1u << j; base[j][a] ^= 1u << a;
        base[a][a] ^= 1u << j; base[a][j] ^= 1u << a; base[a][j] ^= 1u << j;
    }
    uint64_t hits[N + 1] = {0};
    uint64_t first[N + 1]; for (int i = 0; i <= N; i++) first[i] = ~0ULL;
    for (uint64_t it = 0; it < samples; it++) {
        uint64_t w = rnd() >> 29;                 /* 35 random bits */
        uint32_t M[N][N];
        for (int j = 0; j < N; j++) for (int a = 0; a < N; a++) M[j][a] = base[j][a];
        for (int i = 0; i < 35; i++) if ((w >> i) & 1) {
            int j = tj[i], a = tk[i], l = tl[i];
            M[j][a] ^= 1u << l; M[j][l] ^= 1u << a; M[a][j] ^= 1u << l; M[a][l] ^= 1u << j; M[l][j] ^= 1u << a; M[l][a] ^= 1u << j;
        }
        int r0 = -1, ok = 1;
        for (uint32_t v = 1; v < (1u << N) && ok; v++) {
            uint32_t rows[N] = {0, 0, 0, 0, 0, 0, 0};
            for (int j = 0; j < N; j++) if ((v >> j) & 1) for (int a = 0; a < N; a++) rows[a] ^= M[j][a];
            int r = rank_rows(rows);
            if (r0 < 0) r0 = r; else if (r != r0) ok = 0;
        }
        if (ok) { hits[r0]++; if (first[r0] == ~0ULL) first[r0] = w; }
    }
    printf("T gates %d, CS pairs %d, samples %llu:", k, m, (unsigned long long)samples);
    for (int r = 0; r <= N; r++) if (hits[r]) printf("  constant rank %d: %llu (first w=0x%llx)", r, (unsigned long long)hits[r], (unsigned long long)first[r]);
    printf("\n");
    return 0;
}

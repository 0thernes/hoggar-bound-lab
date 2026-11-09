/*
 * hoggar.c - engine for the Hoggar Bound Lab.
 *
 * Geometry of N-qubit Pauli observables (points of the symplectic polar space W(2N-1,2)),
 * their commuting triples ("lines" / contexts), the three quadric families, violation
 * counting, the third-moment bound in exact integer arithmetic, and a simulated-annealing
 * search whose randomness comes from Tsotchke's quantum_rng (a classical, "quantum-inspired"
 * mixer - NOT a hardware quantum source; see third_party/quantum_rng/PROVENANCE.md).
 *
 * Encoding: a point is an integer v in [1, 4^N).  a = v & (2^N - 1) is the X part,
 * c = v >> N is the Z part.  The Hermitian Pauli operator is P(a,c) = i^{|a&c|} X^a Z^c.
 * Bit j of a / c refers to qubit j (qubit 0 = least significant bit of the basis index).
 *
 * Build:  gcc -O2 -std=gnu11 -o hoggar src/hoggar.c third_party/quantum_rng/src/quantum_rng/quantum_rng.c
 *             -Ithird_party/quantum_rng/src/quantum_rng -lm
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include "quantum_rng.h"

typedef unsigned __int128 u128;

/* ------------------------------------------------------------------ geometry */

typedef struct {
    int N;
    uint32_t D;      /* 2^N  */
    uint32_t n;      /* 4^N  */
    char type;       /* 'f' full space, 'h' hyperbolic (real) quadric, 'e' elliptic quadric */
    uint8_t *inS;    /* membership, indexed by point */
    uint32_t *pts;   /* list of member points */
    uint32_t npts;
    uint64_t nlines, nneg;
    /* adjacency: for point index i (position in pts), partners q with q < (p^q), both in S, commuting.
       entry = q | (neg ? 0x80000000 : 0) */
    uint64_t *adj_off;
    uint32_t *adj;
    uint32_t *pos;   /* point -> position in pts (or UINT32_MAX) */
} geo_t;

static inline uint32_t Xp(const geo_t *g, uint32_t v) { return v & (g->D - 1); }
static inline uint32_t Zp(const geo_t *g, uint32_t v) { return v >> g->N; }

static inline int commute(const geo_t *g, uint32_t u, uint32_t v) {
    uint32_t au = Xp(g, u), cu = Zp(g, u), av = Xp(g, v), cv = Zp(g, v);
    return !(__builtin_parity(au & cv) ^ __builtin_parity(cu & av));
}

/* phase exponent k (mod 4) with P_u P_v = i^k P_{u^v} */
static inline int phase4(const geo_t *g, uint32_t u, uint32_t v) {
    uint32_t au = Xp(g, u), cu = Zp(g, u), av = Xp(g, v), cv = Zp(g, v);
    unsigned t = (unsigned)__builtin_popcount(au & cu) + (unsigned)__builtin_popcount(av & cv)
               + 2u * (unsigned)__builtin_popcount(cu & av)
               + 3u * (unsigned)__builtin_popcount((au ^ av) & (cu ^ cv));
    return (int)(t & 3u);
}

/* for commuting u,v: sign s with P_u P_v P_{u^v} = s * I */
static inline int line_sign(const geo_t *g, uint32_t u, uint32_t v) {
    return phase4(g, u, v) == 0 ? +1 : -1;
}

static int member(const geo_t *g, uint32_t v) {
    if (v == 0) return 0;
    uint32_t a = Xp(g, v), c = Zp(g, v);
    int ypar = __builtin_parity(a & c);          /* parity of the number of Y factors */
    switch (g->type) {
    case 'f': return 1;
    case 'h': return ypar == 0;                  /* real symmetric Paulis: Q+(2N-1,2) */
    case 'e': {                                  /* commute with the antiunitary Y_{N-1} K (theta^2 = -1): Q-(2N-1,2) */
        int top = (int)((a >> (g->N - 1)) & 1u) ^ (int)((c >> (g->N - 1)) & 1u);
        return (ypar ^ top) == 0;
    }
    default: return 0;
    }
}

static geo_t *geo_new(int N, char type, int want_adj) {
    geo_t *g = (geo_t *)calloc(1, sizeof(geo_t));
    g->N = N; g->D = 1u << N; g->n = 1u << (2 * N); g->type = type;
    g->inS = (uint8_t *)calloc(g->n, 1);
    g->pos = (uint32_t *)malloc(sizeof(uint32_t) * g->n);
    g->pts = (uint32_t *)malloc(sizeof(uint32_t) * g->n);
    for (uint32_t v = 0; v < g->n; v++) {
        g->pos[v] = UINT32_MAX;
        if (member(g, v)) { g->inS[v] = 1; g->pos[v] = g->npts; g->pts[g->npts++] = v; }
    }
    /* count lines (each once: u < v < w) and, per point, partners */
    uint64_t *cnt = (uint64_t *)calloc(g->npts + 1, sizeof(uint64_t));
    for (uint32_t i = 0; i < g->npts; i++) {
        uint32_t p = g->pts[i];
        for (uint32_t j = 0; j < g->npts; j++) {
            uint32_t q = g->pts[j];
            uint32_t r = p ^ q;
            if (q == p || r <= q || !g->inS[r] || !commute(g, p, q)) continue;
            cnt[i]++;
            if (p < q) { g->nlines++; if (line_sign(g, p, q) < 0) g->nneg++; }
        }
    }
    if (want_adj) {
        g->adj_off = (uint64_t *)malloc(sizeof(uint64_t) * (g->npts + 1));
        uint64_t tot = 0;
        for (uint32_t i = 0; i < g->npts; i++) { g->adj_off[i] = tot; tot += cnt[i]; }
        g->adj_off[g->npts] = tot;
        g->adj = (uint32_t *)malloc(sizeof(uint32_t) * (tot ? tot : 1));
        for (uint32_t i = 0; i < g->npts; i++) {
            uint32_t p = g->pts[i]; uint64_t o = g->adj_off[i];
            for (uint32_t j = 0; j < g->npts; j++) {
                uint32_t q = g->pts[j];
                uint32_t r = p ^ q;
                if (q == p || r <= q || !g->inS[r] || !commute(g, p, q)) continue;
                g->adj[o++] = q | (line_sign(g, p, q) < 0 ? 0x80000000u : 0u);
            }
        }
    }
    free(cnt);
    return g;
}

/* ------------------------------------------------------------------ the bound */

/* n_eff: number of independent spectral atoms (D, or D/2 with Kramers pairs for the elliptic quadric). */
static uint32_t n_eff(const geo_t *g) { return g->type == 'e' ? g->D / 2 : g->D; }

/* largest integer b with b = L (mod 2) and 36 (n-1) b^2 <= (n-2)^2 |S|^3   (b >= 0) */
static int64_t beta_bound_int(uint64_t npts, uint64_t L, uint32_t n, long double *real_out) {
    long double B = (long double)(n - 2) * powl((long double)npts, 1.5L) / (6.0L * sqrtl((long double)(n - 1)));
    if (real_out) *real_out = B;
    int64_t b = (int64_t)floorl(B) + 2;
    u128 rhs = (u128)(n - 2) * (n - 2) * (u128)npts * npts * npts;
    for (;; b--) {
        if (b < 0) return b;
        if (((uint64_t)b ^ L) & 1ull) continue;
        u128 lhs = (u128)36 * (n - 1) * (u128)b * (u128)b;
        if (lhs <= rhs) return b;
    }
}

/* ------------------------------------------------------------------ assignments */

typedef struct {
    const geo_t *g;
    int8_t *f;        /* +1 / -1 per point (only members matter) */
    int32_t *score;   /* per member position: (#satisfied - #violated) lines through it */
    int64_t viol;
} asg_t;

static asg_t *asg_new(const geo_t *g) {
    asg_t *a = (asg_t *)calloc(1, sizeof(asg_t));
    a->g = g;
    a->f = (int8_t *)malloc(g->n);
    memset(a->f, 1, g->n);
    a->score = (int32_t *)calloc(g->npts, sizeof(int32_t));
    return a;
}

static void asg_recount(asg_t *a) {
    const geo_t *g = a->g;
    memset(a->score, 0, sizeof(int32_t) * g->npts);
    a->viol = 0;
    for (uint32_t i = 0; i < g->npts; i++) {
        uint32_t p = g->pts[i];
        for (uint64_t o = g->adj_off[i]; o < g->adj_off[i + 1]; o++) {
            uint32_t e = g->adj[o], q = e & 0x7fffffffu, r = p ^ q;
            int s = (e >> 31) ? -1 : +1;
            int sat = (a->f[p] * a->f[q] * a->f[r] == s) ? +1 : -1;
            a->score[i] += sat;
            if (p < q && sat < 0) a->viol++;
        }
    }
}

static inline void asg_flip(asg_t *a, uint32_t i) {
    const geo_t *g = a->g;
    uint32_t p = g->pts[i];
    for (uint64_t o = g->adj_off[i]; o < g->adj_off[i + 1]; o++) {
        uint32_t e = g->adj[o], q = e & 0x7fffffffu, r = p ^ q;
        int s = (e >> 31) ? -1 : +1;
        int sat = (a->f[p] * a->f[q] * a->f[r] == s) ? +1 : -1;
        a->score[g->pos[q]] -= 2 * sat;
        a->score[g->pos[r]] -= 2 * sat;
        a->viol += sat;            /* satisfied -> violated adds one; violated -> satisfied removes one */
    }
    a->score[i] = -a->score[i];
    a->f[p] = (int8_t)-a->f[p];
}

/* independent, slow, obviously-correct recount straight from the definitions (no adjacency tables) */
static int64_t viol_from_scratch(const geo_t *g, const int8_t *f) {
    int64_t viol = 0;
    for (uint32_t i = 0; i < g->npts; i++) {
        uint32_t u = g->pts[i];
        for (uint32_t j = i + 1; j < g->npts; j++) {
            uint32_t v = g->pts[j], w = u ^ v;
            if (w <= v || !g->inS[w] || !commute(g, u, v)) continue;
            if (f[u] * f[v] * f[w] != line_sign(g, u, v)) viol++;
        }
    }
    return viol;
}

/* file format: line 1 "N type viol", line 2 hex string of 4^N bits (bit v set <=> f(v) = -1), most significant nibble first */
static void asg_write(const geo_t *g, const int8_t *f, int64_t viol, const char *path) {
    FILE *fp = fopen(path, "w");
    if (!fp) { perror(path); exit(2); }
    fprintf(fp, "%d %c %lld\n", g->N, g->type, (long long)viol);
    for (int64_t nib = (int64_t)g->n / 4 - 1; nib >= 0; nib--) {
        unsigned x = 0;
        for (int b = 0; b < 4; b++) { uint32_t v = (uint32_t)nib * 4 + b; if (g->inS[v] && f[v] < 0) x |= 1u << b; }
        fputc("0123456789abcdef"[x], fp);
    }
    fputc('\n', fp);
    fclose(fp);
}

static void asg_read(const geo_t *g, int8_t *f, const char *path) {
    FILE *fp = fopen(path, "r");
    if (!fp) { perror(path); exit(2); }
    int N; char type; long long v0;
    if (fscanf(fp, "%d %c %lld", &N, &type, &v0) != 3 || N != g->N) { fprintf(stderr, "bad header in %s\n", path); exit(2); }
    size_t len = g->n / 4;
    char *hex = (char *)malloc(len + 16);
    if (fscanf(fp, "%s", hex) != 1 || strlen(hex) != len) { fprintf(stderr, "bad hex length in %s\n", path); exit(2); }
    memset(f, 1, g->n);
    for (size_t k = 0; k < len; k++) {
        char ch = hex[k];
        unsigned x = (ch >= '0' && ch <= '9') ? (unsigned)(ch - '0') : (unsigned)(ch - 'a' + 10);
        size_t nib = len - 1 - k;
        for (int b = 0; b < 4; b++) if (x & (1u << b)) f[nib * 4 + b] = -1;
    }
    free(hex);
    fclose(fp);
}

/* ------------------------------------------------------------------ randomness: Tsotchke quantum_rng */

typedef struct { qrng_ctx *ctx; uint8_t buf[1 << 15]; size_t at; } rnd_t;

static void rnd_init(rnd_t *r, uint64_t seed) {
    uint8_t s[16];
    for (int i = 0; i < 8; i++) s[i] = (uint8_t)(seed >> (8 * i));
    memcpy(s + 8, "HOGGAR!!", 8);
    if (qrng_init(&r->ctx, s, sizeof s) != QRNG_SUCCESS) { fprintf(stderr, "qrng_init failed\n"); exit(2); }
    r->at = sizeof r->buf;
}
static inline uint32_t rnd_u32(rnd_t *r) {
    if (r->at + 4 > sizeof r->buf) { qrng_bytes(r->ctx, r->buf, sizeof r->buf); r->at = 0; }
    uint32_t x; memcpy(&x, r->buf + r->at, 4); r->at += 4; return x;
}
static inline double rnd_unit(rnd_t *r) { return (rnd_u32(r) >> 8) * (1.0 / 16777216.0); }
static inline uint32_t rnd_below(rnd_t *r, uint32_t m) { return (uint32_t)(((uint64_t)rnd_u32(r) * m) >> 32); }

/* ------------------------------------------------------------------ search */

static int64_t anneal(asg_t *a, rnd_t *r, uint64_t steps, double T0, double T1, int8_t *best_f) {
    const geo_t *g = a->g;
    int64_t best = a->viol;
    memcpy(best_f, a->f, g->n);
    double lnratio = log(T1 / T0);
    for (uint64_t s = 0; s < steps; s++) {
        double T = T0 * exp(lnratio * (double)s / (double)steps);
        uint32_t i = rnd_below(r, g->npts);
        int d = a->score[i];
        if (d <= 0 || rnd_unit(r) < exp(-(double)d / T)) {
            asg_flip(a, i);
            if (a->viol < best) { best = a->viol; memcpy(best_f, a->f, g->n); }
        }
    }
    return best;
}

/* ------------------------------------------------------------------ commands */

static void print_row(const geo_t *g) {
    long double B;
    uint32_t n = n_eff(g);
    int64_t b = beta_bound_int(g->npts, g->nlines, n, &B);
    int64_t dlow = ((int64_t)g->nlines - b) / 2;
    if (dlow < 0) dlow = 0;
    printf("%d %c %u %llu %llu %.6Lf %lld %lld %.6Lf\n", g->N, g->type, g->npts,
           (unsigned long long)g->nlines, (unsigned long long)g->nneg, (double)B, (long long)b, (long long)dlow,
           g->nlines ? (double)dlow / (double)g->nlines : 0.0);
}

static int cmd_table(int Nmax) {
    printf("# N type points lines negative_lines beta_bound_real beta_bound_int degree_lower_bound fraction\n");
    for (int N = 2; N <= Nmax; N++)
        for (const char *t = "fhe"; *t; t++) {
            geo_t *g = geo_new(N, *t, 0);
            if (g->nlines) print_row(g);
            else printf("%d %c %u 0 0 0 0 0 0\n", N, *t, g->npts);
            fflush(stdout);
        }
    return 0;
}

static int cmd_verify(int N, char type, const char *path) {
    geo_t *g = geo_new(N, type, 1);
    asg_t *a = asg_new(g);
    asg_read(g, a->f, path);
    asg_recount(a);
    int64_t v2 = viol_from_scratch(g, a->f);
    long double B; int64_t b = beta_bound_int(g->npts, g->nlines, n_eff(g), &B);
    printf("N=%d type=%c points=%u lines=%llu violated=%lld (independent recount %lld) beta=%lld bound_int=%lld bound_real=%.6Lf\n",
           N, type, g->npts, (unsigned long long)g->nlines, (long long)a->viol, (long long)v2,
           (long long)((int64_t)g->nlines - 2 * a->viol), (long long)b, (double)B);
    /* per-point number of violated lines */
    int maxdeg = 0; uint32_t *hist = (uint32_t *)calloc(g->n, sizeof(uint32_t));
    for (uint32_t i = 0; i < g->npts; i++) {
        uint32_t deg = (uint32_t)(g->adj_off[i + 1] - g->adj_off[i]);
        int vdeg = (int)(deg - (uint32_t)a->score[i]) / 2 + 0;   /* sat - viol = score, sat + viol = deg */
        vdeg = ((int)deg - a->score[i]) / 2;
        hist[vdeg]++; if (vdeg > maxdeg) maxdeg = vdeg;
    }
    printf("violated-lines-per-point histogram:");
    for (int d = 0; d <= maxdeg; d++) if (hist[d]) printf(" %d:%u", d, hist[d]);
    printf("\n");
    if (a->viol != v2) { printf("MISMATCH between incremental and from-scratch counts\n"); return 1; }
    if ((int64_t)g->nlines - 2 * a->viol > b) { printf("THEOREM FALSIFIED: beta exceeds the bound\n"); return 3; }
    return 0;
}

static int cmd_search(int N, char type, uint64_t seed, int restarts, uint64_t steps, double T0, double T1,
                      const char *start, const char *out) {
    geo_t *g = geo_new(N, type, 1);
    asg_t *a = asg_new(g);
    rnd_t r; rnd_init(&r, seed);
    int8_t *best_f = (int8_t *)malloc(g->n), *run_f = (int8_t *)malloc(g->n);
    int64_t best = INT64_MAX;
    long double B; int64_t b = beta_bound_int(g->npts, g->nlines, n_eff(g), &B);
    int64_t dlow = ((int64_t)g->nlines - b) / 2;
    fprintf(stderr, "N=%d type=%c points=%u lines=%llu neg=%llu lower-bound=%lld\n", N, type, g->npts,
            (unsigned long long)g->nlines, (unsigned long long)g->nneg, (long long)dlow);
    for (int rs = 0; rs < restarts; rs++) {
        if (start) asg_read(g, a->f, start);
        else for (uint32_t i = 0; i < g->npts; i++) a->f[g->pts[i]] = (rnd_u32(&r) & 1u) ? 1 : -1;
        asg_recount(a);
        int64_t v0 = a->viol;
        int64_t v = anneal(a, &r, steps, T0, T1, run_f);
        fprintf(stderr, "  restart %d: start %lld -> best %lld\n", rs, (long long)v0, (long long)v);
        if (v < best) { best = v; memcpy(best_f, run_f, g->n); }
        if (best < dlow) { fprintf(stderr, "THEOREM FALSIFIED\n"); break; }
    }
    int64_t check = viol_from_scratch(g, best_f);
    printf("N=%d type=%c best=%lld recount=%lld lower_bound=%lld lines=%llu\n", N, type, (long long)best,
           (long long)check, (long long)dlow, (unsigned long long)g->nlines);
    if (out) asg_write(g, best_f, best, out);
    return (check == best && best >= dlow) ? 0 : 3;
}

/* Falsification harness: many independent random starts, each greedily + thermally improved; the theorem
   predicts that no assignment ever goes below the bound.  Exit code 3 if one does. */
static int cmd_falsify(int N, char type, uint64_t seed, uint64_t trials, uint64_t steps) {
    geo_t *g = geo_new(N, type, 1);
    asg_t *a = asg_new(g);
    rnd_t r; rnd_init(&r, seed);
    int8_t *tmp = (int8_t *)malloc(g->n);
    long double B; int64_t b = beta_bound_int(g->npts, g->nlines, n_eff(g), &B);
    int64_t dlow = ((int64_t)g->nlines - b) / 2;
    int64_t minraw = INT64_MAX, minopt = INT64_MAX; double sumraw = 0;
    uint64_t below = 0;
    for (uint64_t t = 0; t < trials; t++) {
        for (uint32_t i = 0; i < g->npts; i++) a->f[g->pts[i]] = (rnd_u32(&r) & 1u) ? 1 : -1;
        asg_recount(a);
        sumraw += (double)a->viol; if (a->viol < minraw) minraw = a->viol;
        if (a->viol < dlow) below++;
        if (steps) {
            int64_t v = anneal(a, &r, steps, 0.8, 0.05, tmp);
            if (v < minopt) minopt = v;
            if (v < dlow) below++;
        }
    }
    printf("N=%d type=%c lines=%llu lower_bound=%lld trials=%llu mean_random=%.2f min_random=%lld min_optimised=%lld counterexamples=%llu\n",
           N, type, (unsigned long long)g->nlines, (long long)dlow, (unsigned long long)trials, sumraw / (double)trials,
           (long long)minraw, steps ? (long long)minopt : -1LL, (unsigned long long)below);
    return below ? 3 : 0;
}

/* exhaustive enumeration for two qubits: all 2^15 assignments of the doily, and the 2^9 of the real grid */
static int cmd_exhaust2(void) {
    for (const char *t = "fh"; *t; t++) {
        geo_t *g = geo_new(2, *t, 1);
        asg_t *a = asg_new(g);
        uint32_t hist[32] = {0};
        for (uint32_t m = 0; m < (1u << g->npts); m++) {
            for (uint32_t i = 0; i < g->npts; i++) a->f[g->pts[i]] = (m >> i) & 1u ? -1 : 1;
            hist[viol_from_scratch(g, a->f)]++;
        }
        long double B; int64_t b = beta_bound_int(g->npts, g->nlines, n_eff(g), &B);
        printf("N=2 type=%c points=%u lines=%llu bound_degree>=%lld histogram(violated:count):", *t, g->npts,
               (unsigned long long)g->nlines, (long long)(((int64_t)g->nlines - b) / 2));
        for (int d = 0; d < 32; d++) if (hist[d]) printf(" %d:%u", d, hist[d]);
        printf("\n");
    }
    return 0;
}

/* dump geometry for other tools: lines as "u v w sign" */
static int cmd_lines(int N, char type) {
    geo_t *g = geo_new(N, type, 1);
    printf("# N=%d type=%c points=%u lines=%llu\n", N, type, g->npts, (unsigned long long)g->nlines);
    for (uint32_t i = 0; i < g->npts; i++) {
        uint32_t p = g->pts[i];
        for (uint64_t o = g->adj_off[i]; o < g->adj_off[i + 1]; o++) {
            uint32_t e = g->adj[o], q = e & 0x7fffffffu, r = p ^ q;
            if (p < q) printf("%u %u %u %d\n", p, q, r, (e >> 31) ? -1 : 1);
        }
    }
    return 0;
}

static void usage(void) {
    fprintf(stderr,
        "usage:\n"
        "  hoggar table <Nmax>\n"
        "  hoggar exhaust2\n"
        "  hoggar lines <N> <f|h|e>\n"
        "  hoggar verify <N> <f|h|e> <assignment-file>\n"
        "  hoggar search <N> <f|h|e> <seed> <restarts> <steps> <T0> <T1> <start-file|-> <out-file|->\n"
        "  hoggar falsify <N> <f|h|e> <seed> <trials> <anneal-steps-per-trial>\n");
}

int main(int argc, char **argv) {
    if (argc < 2) { usage(); return 2; }
    if (!strcmp(argv[1], "table") && argc == 3) return cmd_table(atoi(argv[2]));
    if (!strcmp(argv[1], "exhaust2")) return cmd_exhaust2();
    if (!strcmp(argv[1], "lines") && argc == 4) return cmd_lines(atoi(argv[2]), argv[3][0]);
    if (!strcmp(argv[1], "verify") && argc == 5) return cmd_verify(atoi(argv[2]), argv[3][0], argv[4]);
    if (!strcmp(argv[1], "search") && argc == 11)
        return cmd_search(atoi(argv[2]), argv[3][0], strtoull(argv[4], 0, 10), atoi(argv[5]), strtoull(argv[6], 0, 10),
                          atof(argv[7]), atof(argv[8]), strcmp(argv[9], "-") ? argv[9] : NULL,
                          strcmp(argv[10], "-") ? argv[10] : NULL);
    if (!strcmp(argv[1], "falsify") && argc == 7)
        return cmd_falsify(atoi(argv[2]), argv[3][0], strtoull(argv[4], 0, 10), strtoull(argv[5], 0, 10),
                           strtoull(argv[6], 0, 10));
    usage();
    return 2;
}

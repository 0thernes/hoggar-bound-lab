/*
 * qrng_stream.c - writes a seeded byte stream from Tsotchke's quantum_rng to stdout (hex).
 * quantum_rng is a classical "quantum-inspired" mixer; this is NOT a hardware quantum source.
 * The stream depends on the libm of the build (see third_party/quantum_rng/PROVENANCE.md), so
 * every result that uses it is re-verified independently of the stream.
 *
 * usage: qrng_stream <seed> <nbytes>
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "quantum_rng.h"

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: qrng_stream <seed> <nbytes>\n"); return 2; }
    uint64_t seed = strtoull(argv[1], 0, 10);
    size_t n = (size_t)strtoull(argv[2], 0, 10);
    uint8_t s[16];
    for (int i = 0; i < 8; i++) s[i] = (uint8_t)(seed >> (8 * i));
    memcpy(s + 8, "HOGGAR!!", 8);
    qrng_ctx *ctx = NULL;
    if (qrng_init(&ctx, s, sizeof s) != QRNG_SUCCESS) { fprintf(stderr, "qrng_init failed\n"); return 2; }
    uint8_t buf[4096];
    static const char hex[] = "0123456789abcdef";
    char out[8192];
    while (n) {
        size_t k = n < sizeof buf ? n : sizeof buf;
        qrng_bytes(ctx, buf, k);
        for (size_t i = 0; i < k; i++) { out[2 * i] = hex[buf[i] >> 4]; out[2 * i + 1] = hex[buf[i] & 15]; }
        fwrite(out, 1, 2 * k, stdout);
        n -= k;
    }
    qrng_free(ctx);
    return 0;
}

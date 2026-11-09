#ifndef HOGGAR_WITNESS_IO_H
#define HOGGAR_WITNESS_IO_H

#include <ctype.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* The engine enumerates O(16^N) pairs; this lab supports N=2..7. */
#define HOGGAR_MIN_N 2
#define HOGGAR_MAX_N 7

static int witness_u64(const char *s, uint64_t *out) {
    if (!s || !*s) return 0;
    for (const unsigned char *p = (const unsigned char *)s; *p; p++)
        if (*p < '0' || *p > '9') return 0;
    errno = 0;
    char *end;
    unsigned long long value = strtoull(s, &end, 10);
    if (errno == ERANGE || *end || value > UINT64_MAX) return 0;
    *out = (uint64_t)value;
    return 1;
}

/* Consume one whitespace-separated token, rejecting overlong input. */
static int witness_token(FILE *fp, char *out, size_t capacity) {
    int ch;
    do { ch = fgetc(fp); } while (ch != EOF && isspace((unsigned char)ch));
    if (ch == EOF) return 0;
    size_t used = 0;
    do {
        if (ch == 0) return 0;
        if (used + 1 >= capacity) return 0;
        out[used++] = (char)ch;
        ch = fgetc(fp);
    } while (ch != EOF && !isspace((unsigned char)ch));
    out[used] = '\0';
    return 1;
}

/* Read an exact fixed-size assignment. A full-space assignment can be
 * restricted to h/e at the same N; a partial assignment cannot be expanded
 * or transferred to the other quadric. Header violation count is metadata:
 * callers recompute violations in their requested geometry. Bits outside that
 * geometry (including identity) are ignored by those callers.
 */
static int witness_read(const char *path, int expected_n, char expected_type,
                        int8_t *assignment) {
    if (expected_n < HOGGAR_MIN_N || expected_n > HOGGAR_MAX_N ||
        !strchr("fhe", expected_type) || !expected_type) {
        fprintf(stderr, "invalid witness target geometry\n");
        return 0;
    }
    FILE *fp = fopen(path, "r");
    if (!fp) { perror(path); return 0; }
    const char *error = "invalid header";
    char ntok[32], ttok[2], vtok[32];
    uint64_t n, declared_violations;
    if (!witness_token(fp, ntok, sizeof ntok) ||
        !witness_token(fp, ttok, sizeof ttok) ||
        !witness_token(fp, vtok, sizeof vtok) ||
        !witness_u64(ntok, &n) || n != (uint64_t)expected_n ||
        !witness_u64(vtok, &declared_violations) ||
        !strchr("fhe", ttok[0]) ||
        !(ttok[0] == expected_type || (ttok[0] == 'f' && expected_type != 'f')))
        goto invalid;
    uint32_t count = 1u << (2 * expected_n);
    /* A metadata count larger than all full-space contexts is malformed. */
    if (declared_violations > (uint64_t)(count - 1) * (count / 4 - 1) / 3)
        goto invalid;
    memset(assignment, 1, count);
    int ch;
    do { ch = fgetc(fp); } while (ch != EOF && isspace((unsigned char)ch));
    size_t length = count / 4;
    error = "expected exact-length hexadecimal assignment";
    for (size_t k = 0; k < length; k++) {
        unsigned nibble;
        if (ch >= '0' && ch <= '9') nibble = (unsigned)(ch - '0');
        else if (ch >= 'a' && ch <= 'f') nibble = (unsigned)(ch - 'a' + 10);
        else if (ch >= 'A' && ch <= 'F') nibble = (unsigned)(ch - 'A' + 10);
        else goto invalid;
        size_t base = (length - 1 - k) * 4;
        for (unsigned bit = 0; bit < 4; bit++)
            if (nibble & (1u << bit)) assignment[base + bit] = -1;
        ch = fgetc(fp);
    }
    error = "trailing data after hexadecimal assignment";
    while (ch != EOF && isspace((unsigned char)ch)) ch = fgetc(fp);
    if (ch != EOF || ferror(fp)) goto invalid;
    fclose(fp);
    return 1;
invalid:
    fprintf(stderr, "bad witness %s: %s\n", path, error);
    fclose(fp);
    return 0;
}

#endif

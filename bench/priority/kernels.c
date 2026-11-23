#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef __SSE2__
#include <emmintrin.h>
#endif

static void require(int valid) {
    if (!valid) exit(2);
}
static int64_t add(int64_t a, int64_t b) {
    int64_t result;
    require(!__builtin_add_overflow(a, b, &result));
    return result;
}
static int64_t mul(int64_t a, int64_t b) {
    int64_t result;
    require(!__builtin_mul_overflow(a, b, &result));
    return result;
}
static uint64_t now(void) {
    struct timespec t;
    require(clock_gettime(CLOCK_MONOTONIC, &t) == 0);
    return (uint64_t)t.tv_sec * UINT64_C(1000000000) + (uint64_t)t.tv_nsec;
}
static void *alloc(size_t n, size_t width) {
    require(width && n <= SIZE_MAX / width);
    void *data = malloc(n * width);
    require(data != NULL);
    return data;
}
static void observe(const void *p) {
    __asm__ volatile("" : : "r"(p) : "memory");
}
static int64_t *data(size_t length) {
    int64_t *a = alloc(length, sizeof *a);
    for (size_t i = 0; i < length; ++i)
        a[i] = (int64_t)((i * 7919 + 17) % 100003);
    return a;
}
static int cmp_i64(const void *left, const void *right) {
    const int64_t a = *(const int64_t *)left, b = *(const int64_t *)right;
    return (a > b) - (a < b);
}
static int contains(const int64_t *a, size_t n, int64_t key) {
    for (size_t i = 0; i < n; ++i) {
        if (a[i] == key) return 1;
    }
    return 0;
}
static int contains_bytes(const char *hay, size_t n, const char *needle, size_t m) {
    if (m > n) return 0;
    if (m == 0) return 1;
    size_t candidates = n - m + 1;
    while (candidates) {
        const char *hit = memchr(hay, (unsigned char)needle[0], candidates);
        if (!hit) break;
        if (memcmp(hit + 1, needle + 1, m - 1) == 0) return 1;
        candidates -= (size_t)(hit - hay) + 1;
        hay = hit + 1;
    }
    return 0;
}

static int64_t pop_sum(const int64_t *values, size_t *length, size_t count) {
    require(count <= *length);
    size_t start = *length, end = start - count;
    int64_t sum = 0;
    for (size_t i = start; i > end; --i) sum = add(sum, values[i - 1]);
    *length = end;
    return sum;
}
static int64_t bool_count(const unsigned char *values, size_t length) {
    require(length <= INT64_MAX);
    int64_t sum = 0;
    /* Each term is at most one, so the length guard proves every addition fits. */
    for (size_t i = 0; i < length; ++i) sum += values[i] != 0;
    return sum;
}
static int64_t parse_int(const char *input) {
    const char *start = input;
    int negative = *input == '-';
    if (*input == '-' || *input == '+') ++input;
    require(*input != '\0');
    int64_t acc = 0;
    for (; *input; ++input) {
        unsigned d = (unsigned char)*input - (unsigned)'0';
        require(d < 10);
        if (__builtin_mul_overflow(acc, INT64_C(10), &acc) ||
            __builtin_sub_overflow(acc, (int64_t)d, &acc)) exit(2);
    }
    (void)start;
    require(negative || acc != INT64_MIN);
    return negative ? acc : -acc;
}
static double parse_float(const char *s) {
    require(*s != '\0');
    for (const char *p = s; *p; ++p) require(strchr("0123456789.+-eE", *p) != NULL);
    char *end;
    double x = strtod(s, &end);
    require(end != s && *end == '\0');
    return x;
}
#include "extra.h"
int main(void) {
    char name[64];
    int64_t seed;
    require(scanf("%63s %" SCNd64, name, &seed) == 2 && seed >= 7 && seed < 1000);
    uint64_t start, end;
    int64_t check = 0;
    if (!strcmp(name, "array_pop")) {
        size_t n = 500000;
        int64_t *a = data(n);
        start = now();
        check = pop_sum(a, &n, 500000);
        end = now();
        check = add(check, (int64_t)n);
        free(a);
    } else if (!strcmp(name, "array_scan")) {
        size_t n = 500000;
        int64_t *a = data(n);
        start = now();
        for (size_t i = 0; i < n; ++i) check = add(check, a[i]);
        end = now();
        free(a);
    } else if (!strcmp(name, "array_index_read") || !strcmp(name, "array_index_write")) {
        size_t n = 500000;
        int64_t *a = data(n);
        int read = !strcmp(name, "array_index_read");
        start = now();
        if (read) {
            for (size_t i = 0; i < 1000000; ++i) {
                size_t index = i * 7919 % 500000;
                require(index < n);
                check = add(check, a[index]);
            }
        } else {
            for (size_t i = 0; i < n; ++i) {
                size_t index = i * 7919 % 500000;
                require(index < n);
                a[index] = add(seed, (int64_t)i);
            }
            observe(a);
        }
        end = now();
        if (!read) check = add(add(a[0], a[333333]), a[499999]);
        free(a);
    } else if (!strcmp(name, "array_sort")) {
        size_t n = 50000;
        int64_t *a = alloc(n, sizeof *a);
        int64_t x = seed;
        for (size_t i = 0; i < n; ++i) {
            x = add(mul(x, 1664525), 1013904223) % 2147483647;
            a[i] = x % 100003;
        }
        start = now();
        qsort(a, n, sizeof *a, cmp_i64);
        observe(a);
        end = now();
        for (size_t i = 1; i < n; ++i) require(a[i-1] <= a[i]);
        check = add(add(a[0], a[25000]), a[49999]);
        free(a);
    } else if (!strcmp(name, "array_contains")) {
        size_t n = 10000;
        int64_t *a = data(n);
        start = now();
        for (size_t i = 0; i < 1800; ++i) {
            if (contains(a, n, (int64_t)(i * 7919 % 100003))) ++check;
        }
        end = now();
        free(a);
    } else if (!strcmp(name, "bool_logic_scan")) {
        size_t n = 1000000;
        unsigned char *a = alloc(n, sizeof *a);
        for (size_t i = 0; i < n; ++i) a[i] = ((int64_t)i + seed) % 7 < 3;
        start = now();
        check = bool_count(a, n);
        end = now();
        free(a);
    } else if (!strcmp(name, "str_contains") || !strcmp(name, "str_prefix_suffix_eq")) {
        char a[128][64];
        size_t lengths[128];
        for (size_t i = 0; i < 128; ++i) {
            int d = (int)((i * 7 + seed) % 1000 + 1000);
            int length = snprintf(a[i], sizeof a[i], "  name%d,alpha,tag%d,é漢🙂  ", d, d * 3);
            require(length >= 22 && length < (int)sizeof a[i]);
            lengths[i] = (size_t)length;
        }
        int search = !strcmp(name, "str_contains");
        start = now();
        if (search) {
            for (size_t i = 0; i < 200000; ++i) {
                size_t key = (i * 7 + 13) % 128;
                size_t text = i % 128;
                if (contains_bytes(a[text], lengths[text], a[key] + 18, 4)) ++check;
            }
        } else {
            for (size_t i = 0; i < 500000; ++i) {
                size_t ix = i % 128, next = (i + 1) % 128, n = lengths[ix];
                if (n >= 6 && memcmp(a[ix], "  name", 6) == 0 &&
                    memcmp(a[ix] + n - 2, "  ", 2) == 0 &&
                    (lengths[next] != n || memcmp(a[ix], a[next], n) != 0)) ++check;
            }
        }
        end = now();
    } else if (!strcmp(name, "str_parse_int") || !strcmp(name, "str_parse_float")) {
        char a[128][32];
        int integer = !strcmp(name, "str_parse_int");
        for (int64_t i = 0; i < 128; ++i) {
            int length;
            if (integer) length = snprintf(a[i], sizeof a[i], "%" PRId64, i * 777777 + seed);
            else length = snprintf(a[i], sizeof a[i], "%" PRId64 ".125", i + seed);
            require(length >= 0 && length < (int)sizeof a[i]);
        }
        start = now();
        if (integer) {
            for (size_t i = 0; i < 300000; ++i) check = add(check, parse_int(a[i % 128]));
            end = now();
        } else {
            double sum = 0;
            for (size_t i = 0; i < 300000; ++i) sum += parse_float(a[i % 128]);
            end = now();
            require(sum * 8 >= -0x1p63 && sum * 8 < 0x1p63);
            check = (int64_t)(sum * 8);
        }
    } else {
        uint64_t duration;
        if (!extra(name,seed,&duration,&check)) return 2;
        start=0; end=duration;
    }
    printf("%" PRIu64 " %" PRId64 "\n", end - start, check);
    return 0;
}

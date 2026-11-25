#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "stn_runtime.h"

/* These kernels call the runtime of the baseline checkout, whose Str was a pointer to a buffer
   before strings of up to 15 bytes were stored inline, and is a 16-byte value read by address
   since. STN_STR_INLINE_MAX is defined by the second. */
#ifdef STN_STR_INLINE_MAX
#  define SREF(s) (&(s))
#  define SLEN(s) stn_str_len(s)
#  define SBYTE(s, i) ((unsigned char)stn_str_ptr(&(s))[i])
#  define SOBSERVE(s) observe(&(s))
#else
#  define SREF(s) (s)
#  define SLEN(s) ((s)->len)
#  define SBYTE(s, i) ((unsigned char)(s)->data[i])
#  define SOBSERVE(s) observe(s)
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
static int64_t pop_sum(const int64_t *values, size_t *length, size_t count) {
    require(count <= *length);
    size_t start = *length, end = start - count;
    int64_t sum = 0;
    for (size_t i = start; i > end; --i) sum = add(sum, values[i - 1]);
    *length = end;
    return sum;
}
static StnArray *copy_array(const void *data, size_t n, const StnElemOps *ops) {
    StnArray *result = stn_array_new(ops, (int64_t)n);
    memcpy(result->data, data, n * ops->size);
    result->len = (int64_t)n;
    return result;
}
static const StnElemOps integer_ops = {sizeof(int64_t), NULL, NULL};
static const StnElemOps boolean_ops = {sizeof(unsigned char), NULL, NULL};
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
            require(n >= 500000);
            size_t index = 0;
            for (size_t i = 0; i < 1000000; ++i) {
                check = add(check, a[index]);
                index = index >= 492081 ? index - 492081 : index + 7919;
            }
        } else {
            require(n >= 500000);
            size_t index = 0;
            for (size_t i = 0; i < n; ++i) {
                a[index] = add(seed, (int64_t)i);
                index = index >= 492081 ? index - 492081 : index + 7919;
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
        StnArray *sorted = copy_array(a, n, &integer_ops);
        free(a);
        start = now();
        stn_array_sort_i64(&sorted);
        a = (int64_t*)sorted->data;
        observe(a);
        end = now();
        for (size_t i = 1; i < n; ++i) require(a[i-1] <= a[i]);
        check = add(add(a[0], a[25000]), a[49999]);
        stn_drop(sorted, stn_array_release);
    } else if (!strcmp(name, "array_contains")) {
        size_t n = 10000;
        int64_t *a = data(n);
        StnArray *values = copy_array(a, n, &integer_ops);
        free(a);
        start = now();
        for (size_t i = 0; i < 1800; ++i) {
            if (stn_array_contains_i64(values, (int64_t)(i * 7919 % 100003))) ++check;
        }
        end = now();
        stn_drop(values, stn_array_release);
    } else if (!strcmp(name, "bool_logic_scan")) {
        size_t n = 1000000;
        unsigned char *a = alloc(n, sizeof *a);
        for (size_t i = 0; i < n; ++i) a[i] = ((int64_t)i + seed) % 7 < 3;
        StnArray *values = copy_array(a, n, &boolean_ops);
        free(a);
        start = now();
        check = stn_array_count_true(values);
        end = now();
        stn_drop(values, stn_array_release);
    } else if (!strcmp(name, "str_contains") || !strcmp(name, "str_prefix_suffix_eq")) {
        char a[128][64];
        size_t lengths[128];
        for (size_t i = 0; i < 128; ++i) {
            int d = (int)((i * 7 + seed) % 1000 + 1000);
            int length = snprintf(a[i], sizeof a[i], "  name%d,alpha,tag%d,é漢🙂  ", d, d * 3);
            require(length >= 22 && length < (int)sizeof a[i]);
            lengths[i] = (size_t)length;
        }
        StnStr strings[128], needles[128];
        for (size_t i = 0; i < 128; ++i) {
            strings[i] = stn_str_new(a[i], (int64_t)lengths[i]);
            needles[i] = stn_str_new(a[i] + 18, 4);
        }
        int search = !strcmp(name, "str_contains");
        start = now();
        if (search) {
            for (size_t i = 0; i < 200000; ++i) {
                size_t key = (i * 7 + 13) % 128;
                size_t text = i % 128;
                if (stn_str_contains(SREF(strings[text]), SREF(needles[key]))) ++check;
            }
        } else {
            for (size_t i = 0; i < 500000; ++i) {
                size_t ix = i % 128, next = (i + 1) % 128, n = lengths[ix];
                if (n >= 6 && memcmp(a[ix], "  name", 6) == 0 &&
                    memcmp(a[ix] + n - 2, "  ", 2) == 0 &&
                    !stn_str_eq(strings[ix], strings[next])) ++check;
            }
        }
        end = now();
        for (size_t i = 0; i < 128; ++i) {
            STN_STR_DROP(strings[i]);
            STN_STR_DROP(needles[i]);
        }
    } else if (!strcmp(name, "str_parse_int") || !strcmp(name, "str_parse_float")) {
        char a[128][32];
        int integer = !strcmp(name, "str_parse_int");
        for (int64_t i = 0; i < 128; ++i) {
            int length;
            if (integer) length = snprintf(a[i], sizeof a[i], "%" PRId64, i * 777777 + seed);
            else length = snprintf(a[i], sizeof a[i], "%" PRId64 ".125", i + seed);
            require(length >= 0 && length < (int)sizeof a[i]);
        }
        StnStr strings[128];
        for (size_t i = 0; i < 128; ++i) strings[i] = stn_str_new(a[i], (int64_t)strlen(a[i]));
        start = now();
        if (integer) {
            for (size_t i = 0; i < 300000; ++i) {
                int64_t value;
                require(stn_parse_int(SREF(strings[i % 128]), &value) == 0);
                check = add(check, value);
            }
            end = now();
        } else {
            double sum = 0;
            for (size_t i = 0; i < 300000; ++i) {
                double value;
                require(stn_parse_float(SREF(strings[i % 128]), &value) == 0);
                sum += value;
            }
            end = now();
            require(sum * 8 >= -0x1p63 && sum * 8 < 0x1p63);
            check = (int64_t)(sum * 8);
        }
        for (size_t i = 0; i < 128; ++i) STN_STR_DROP(strings[i]);
    } else {
        uint64_t duration;
        if (!extra(name,seed,&duration,&check)) return 2;
        start=0; end=duration;
    }
    printf("%" PRIu64 " %" PRId64 "\n", end - start, check);
    return 0;
}

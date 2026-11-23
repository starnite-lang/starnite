/* SPDX-License-Identifier: Apache-2.0 */
/* The Starnite runtime (section 11). */
#define _XOPEN_SOURCE 700
#include "stn_runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#if defined(__unix__) || defined(__APPLE__)
#include <signal.h>
#include <unistd.h>
#include <sys/resource.h>
#define STN_STACK_TRAP 1
#endif
#if defined(__linux__)
#include <sys/mman.h>
#endif
#include <sys/types.h>
#include <sys/stat.h>
#include <errno.h>

#if defined(__x86_64__) && defined(__SSE2__)
#include <immintrin.h>
#endif

int64_t stn_live_objects = 0;

/* ---- allocation (section 11.2) ---- */
/* Size classes step by 16 bytes up to 1 KiB, with a free list per class. Milestone 1 is
   single-threaded, so the lists are plain globals; milestone 6 makes them per thread. */
#define STN_CLASSES 64
typedef struct stn_free_node { struct stn_free_node* next; } stn_free_node;
static stn_free_node* stn_free_lists[STN_CLASSES + 1];

/* A buffer of a few megabytes is scanned across thousands of pages; asking for huge pages for the
   2 MiB spans inside it takes most of the translation misses away. Advice only: a refusal changes
   nothing, and it is not given to the debug build, whose blocks go through poison and quarantine. */
#if defined(__linux__) && defined(MADV_HUGEPAGE) && !defined(STN_DEBUG)
static void stn_advise_huge(void* p, size_t bytes) {
    const uintptr_t span = (uintptr_t)2 << 20;
    if (bytes < span) return;
    uintptr_t lo = ((uintptr_t)p + span - 1) & ~(span - 1);
    uintptr_t hi = ((uintptr_t)p + bytes) & ~(span - 1);
    if (hi > lo) (void)madvise((void*)lo, hi - lo, MADV_HUGEPAGE);
}
#else
static void stn_advise_huge(void* p, size_t bytes) { (void)p; (void)bytes; }
#endif

void* stn_alloc(size_t size) {
    stn_header* h;
    /* compare before rounding up, so a huge size cannot wrap into a small class */
    size_t cls = size <= (size_t)STN_CLASSES * 16 ? (size + 15) / 16 : STN_CLASSES + 1;
    if (cls <= STN_CLASSES) {
        if (cls == 0) cls = 1;
        stn_free_node* n = stn_free_lists[cls];
        if (n) { stn_free_lists[cls] = n->next; h = (stn_header*)n; }
        else {
            h = (stn_header*)malloc(cls * 16);
            if (!h) { fputs("trap: out of memory\n", stderr); exit(2); }
        }
        h->size_class = (uint8_t)cls;
    } else {
        h = (stn_header*)malloc(size);
        if (!h) { fputs("trap: out of memory\n", stderr); exit(2); }
        stn_advise_huge(h, size);
        h->size_class = 0;
    }
    h->rc = 1; h->tag = 0; h->flags = 0;
#ifdef STN_DEBUG
    stn_live_objects++;
#endif
    return h;
}

void stn_free(void* p) {
    stn_header* h = (stn_header*)p;
    size_t cls = h->size_class;
#ifdef STN_DEBUG
    stn_live_objects--;
    /* Freed memory is poisoned and held in a quarantine, so a later drop of the same
       object reads the poison rather than memory malloc has reused. */
    if (cls) memset(h, 0xDB, cls * 16); else memset(h, 0xDB, sizeof(stn_header));
    static void* quarantine[1 << 16];
    static size_t next = 0;
    if (quarantine[next]) free(quarantine[next]);
    quarantine[next] = h;
    next = (next + 1) % (sizeof quarantine / sizeof quarantine[0]);
    return;
#endif
    if (cls) {
        stn_free_node* n = (stn_free_node*)p;
        n->next = stn_free_lists[cls];
        stn_free_lists[cls] = n;
    } else free(p);
}

void stn_check_header(void* p) {
    stn_header* h = (stn_header*)p;
    if (h->rc == 0xDBDBDBDBu || (h->flags == 0 && h->rc == 0)) {
        fputs("debug runtime: drop of a released object\n", stderr);
        abort();
    }
}

/* ---- traps ---- */
static char stn_outbuf[1 << 16];
static size_t stn_outlen = 0;
static void stn_flush(void) { fwrite(stn_outbuf, 1, stn_outlen, stdout); stn_outlen = 0; fflush(stdout); }

_Noreturn void stn_trap(const char* kind, const char* file, int line, int col, const char* msg) {
    stn_flush();
    fprintf(stderr, "trap: %s at %s:%d:%d\n%s\n", kind, file, line, col, msg);
    exit(2);
}
_Noreturn void stn_overflow(const char* file, int line, int col) {
    stn_trap("integer overflow", file, line, col, "the result does not fit its type");
}
_Noreturn void stn_div_zero(const char* file, int line, int col) {
    stn_trap("division by zero", file, line, col, "the divisor is zero");
}
_Noreturn void stn_conv_trap(const char* to, const char* file, int line, int col) {
    char buf[64];
    snprintf(buf, sizeof buf, "the value does not fit in %s", to);
    stn_trap("integer overflow", file, line, col, buf);
}
void stn_check_char(int64_t c, const char* file, int line, int col) {
    if (c < 0 || c > 0x10FFFF || (c >= 0xD800 && c <= 0xDFFF)) {
        char buf[64];
        snprintf(buf, sizeof buf, "%lld is not a Unicode scalar value", (long long)c);
        stn_trap("invalid character", file, line, col, buf);
    }
}

/* ---- strings ---- */
void stn_str_release(void* p) { stn_free(p); }

StnStr stn_str_new(const char* data, int64_t len) {
    StnStr s = (StnStr)stn_alloc(sizeof(StnStrBuf) + (size_t)len + 1);
    s->len = len;
    if (len) memcpy(s->data, data, (size_t)len);
    s->data[len] = 0;
    return s;
}

StnStr stn_str_concat(StnStr a, StnStr b) {
    StnStr s = (StnStr)stn_alloc(sizeof(StnStrBuf) + (size_t)(a->len + b->len) + 1);
    s->len = a->len + b->len;
    memcpy(s->data, a->data, (size_t)a->len);
    memcpy(s->data + a->len, b->data, (size_t)b->len);
    s->data[s->len] = 0;
    return s;
}

StnStr stn_str_concat_n(int n, StnStr* parts) {
    int64_t total = 0;
    for (int i = 0; i < n; i++) total += parts[i]->len;
    StnStr s = (StnStr)stn_alloc(sizeof(StnStrBuf) + (size_t)total + 1);
    s->len = total;
    int64_t at = 0;
    for (int i = 0; i < n; i++) { memcpy(s->data + at, parts[i]->data, (size_t)parts[i]->len); at += parts[i]->len; }
    s->data[total] = 0;
    return s;
}

int stn_str_cmp(StnStr a, StnStr b) {
    int64_t n = a->len < b->len ? a->len : b->len;
    int c = memcmp(a->data, b->data, (size_t)n);
    if (c) return c < 0 ? -1 : 1;
    return a->len < b->len ? -1 : a->len > b->len ? 1 : 0;
}

static int stn_boundary(StnStr s, int64_t i) {
    return i == 0 || i == s->len || ((unsigned char)s->data[i] & 0xC0) != 0x80;
}

StnStr stn_str_slice(StnStr s, int64_t lo, int64_t hi, const char* file, int line, int col) {
    if (lo < 0 || hi > s->len || lo > hi) {
        char buf[96];
        snprintf(buf, sizeof buf, "slice %lld..%lld, length %lld", (long long)lo, (long long)hi, (long long)s->len);
        stn_trap("index out of range", file, line, col, buf);
    }
    if (!stn_boundary(s, lo) || !stn_boundary(s, hi))
        stn_trap("index out of range", file, line, col, "slice does not fall on character boundaries");
    return stn_str_new(s->data + lo, hi - lo);
}

StnStr stn_show_i64(int64_t v) { char b[32]; int n = snprintf(b, sizeof b, "%lld", (long long)v); return stn_str_new(b, n); }
StnStr stn_show_u64(uint64_t v) { char b[32]; int n = snprintf(b, sizeof b, "%llu", (unsigned long long)v); return stn_str_new(b, n); }

/* Float text: the shortest digits that read back as the same value, in fixed notation
   when the decimal exponent is in [-4, 16), else scientific. The reference interpreter
   uses the same rule (compiler/values.ml); the two must agree exactly. */
static StnStr stn_show_float_digits(double v, int maxp, int is_f32) {
    char b[64], out[96];
    if (isnan(v)) return stn_str_new("nan", 3);
    if (isinf(v)) return v > 0 ? stn_str_new("inf", 3) : stn_str_new("-inf", 4);
    for (int p = 1; p <= maxp; p++) {
        snprintf(b, sizeof b, "%.*e", p - 1, v);
        double back = strtod(b, NULL);
        if (p == maxp || (is_f32 ? (float)back == (float)v : back == v)) break;
    }
    const char* s = b;
    int neg = 0;
    if (*s == '-') { neg = 1; s++; }
    char digits[40]; int nd = 0;
    const char* e = strchr(s, 'e');
    for (const char* q = s; q < e; q++) if (*q != '.') digits[nd++] = *q;
    while (nd > 1 && digits[nd - 1] == '0') nd--;
    int exp = atoi(e + 1);
    int n = 0;
    if (neg) out[n++] = '-';
    if (exp >= -4 && exp < 16) {
        if (exp >= 0) {
            for (int i = 0; i <= exp; i++) out[n++] = i < nd ? digits[i] : '0';
            out[n++] = '.';
            if (nd > exp + 1) for (int i = exp + 1; i < nd; i++) out[n++] = digits[i];
            else out[n++] = '0';
        } else {
            out[n++] = '0'; out[n++] = '.';
            for (int i = 0; i < -exp - 1; i++) out[n++] = '0';
            for (int i = 0; i < nd; i++) out[n++] = digits[i];
        }
    } else {
        out[n++] = digits[0];
        if (nd > 1) { out[n++] = '.'; for (int i = 1; i < nd; i++) out[n++] = digits[i]; }
        n += snprintf(out + n, sizeof out - (size_t)n, "e%c%02d", exp < 0 ? '-' : '+', exp < 0 ? -exp : exp);
    }
    return stn_str_new(out, n);
}

StnStr stn_show_f64(double v) { return stn_show_float_digits(v, 17, 0); }
StnStr stn_show_f32(float v) { return stn_show_float_digits((double)v, 9, 1); }

StnStr stn_show_bool(uint8_t v) { return v ? stn_str_new("true", 4) : stn_str_new("false", 5); }
StnStr stn_show_unit(void) { return stn_str_new("()", 2); }
StnStr stn_show_dur(int64_t v) { char b[40]; int n = snprintf(b, sizeof b, "%lldns", (long long)v); return stn_str_new(b, n); }
StnStr stn_show_bytes(int64_t v) { char b[40]; int n = snprintf(b, sizeof b, "%lldb", (long long)v); return stn_str_new(b, n); }

static int stn_utf8_encode(char* out, uint32_t c) {
    if (c < 0x80) { out[0] = (char)c; return 1; }
    if (c < 0x800) { out[0] = (char)(0xC0 | (c >> 6)); out[1] = (char)(0x80 | (c & 0x3F)); return 2; }
    if (c < 0x10000) {
        out[0] = (char)(0xE0 | (c >> 12)); out[1] = (char)(0x80 | ((c >> 6) & 0x3F)); out[2] = (char)(0x80 | (c & 0x3F)); return 3;
    }
    out[0] = (char)(0xF0 | (c >> 18)); out[1] = (char)(0x80 | ((c >> 12) & 0x3F));
    out[2] = (char)(0x80 | ((c >> 6) & 0x3F)); out[3] = (char)(0x80 | (c & 0x3F)); return 4;
}

StnStr stn_show_char(uint32_t c) { char b[4]; int n = stn_utf8_encode(b, c); return stn_str_new(b, n); }

/* ---- arrays ---- */
void stn_array_release(void* p) {
    StnArray* a = (StnArray*)p;
    if (a->ops->drop) {
        size_t sz = a->ops->size;
        for (int64_t i = 0; i < a->len; i++) a->ops->drop(a->data + (size_t)i * sz);
    }
    stn_free(a);
}

/* Requests above STN_MAX_ALLOC (stn_runtime.h) elements or bytes trap rather than wrap
   a size computation. The reference interpreter applies the same limit
   (compiler/interp.ml), and generated code relies on it through stn_len. */

_Noreturn static void stn_too_large(const char* file, int line, int col) {
    stn_trap("allocation too large", file, line, col, "the requested size is too large");
}

StnArray* stn_array_new(const StnElemOps* ops, int64_t cap) {
    if (cap < 0 || cap > STN_MAX_ALLOC || (uint64_t)cap > (uint64_t)STN_MAX_ALLOC / (ops->size ? ops->size : 1))
        stn_too_large("<runtime>", 0, 0);
    StnArray* a = (StnArray*)stn_alloc(sizeof(StnArray) + (size_t)cap * ops->size);
    a->len = 0; a->cap = cap; a->ops = ops;
    return a;
}

/* A write needs the box unshared (section 4.5): copy it when its count is not 1.
   The copy is shallow: boxed elements gain one reference each. */
static StnArray* stn_array_copy(StnArray* a, int64_t cap) {
    StnArray* b = stn_array_new(a->ops, cap);
    size_t sz = a->ops->size;
    memcpy(b->data, a->data, (size_t)a->len * sz);
    b->len = a->len;
    if (a->ops->dup) for (int64_t i = 0; i < a->len; i++) a->ops->dup(b->data + (size_t)i * sz);
    return b;
}

void stn_array_copy_for_write(StnArray** pa) {
    StnArray* a = *pa;
    if (stn_unique(a)) return;
    StnArray* b = stn_array_copy(a, a->len > 0 ? a->len : 1);
    stn_drop(a, stn_array_release);
    *pa = b;
}

void stn_array_reserve(StnArray** pa, int64_t extra) {
    StnArray* a = *pa;
    int64_t need = a->len + extra;
    if (extra > STN_MAX_ALLOC || need > STN_MAX_ALLOC) stn_too_large("<runtime>", 0, 0);
    if (stn_unique(a)) {
        if (need <= a->cap) return;
        int64_t cap = a->cap ? a->cap * 2 : 4;
        while (cap < need) cap *= 2;
        /* capacity never passes the limit, so no push can take a length past it */
        if (cap > STN_MAX_ALLOC) cap = STN_MAX_ALLOC;
        size_t bytes = sizeof(StnArray) + (size_t)cap * a->ops->size;
#ifndef STN_DEBUG
        /* a large buffer already belongs to the system allocator, whose realloc can
           move pages instead of copying them; the debug build keeps copying so that
           every freed block goes through the poison and quarantine of stn_free */
        /* a buffer that is not yet huge-page sized is copied once into one that is, so that the whole of it
           gets the advice before its pages are touched; mremap would carry small pages along */
        if (a->h.size_class == 0 && bytes > (size_t)STN_CLASSES * 16 &&
            (bytes < ((size_t)2 << 20) || sizeof(StnArray) + (size_t)a->cap * a->ops->size >= ((size_t)2 << 20))) {
            StnArray* b = (StnArray*)realloc(a, bytes);
            if (!b) { fputs("trap: out of memory\n", stderr); exit(2); }
            stn_advise_huge(b, bytes);
            b->cap = cap;
            *pa = b;
            return;
        }
#endif
        StnArray* b = (StnArray*)stn_alloc(bytes);
        uint8_t sc = b->h.size_class;
        memcpy(b, a, sizeof(StnArray) + (size_t)a->len * a->ops->size);
        b->h.rc = 1; b->h.flags = 0; b->h.size_class = sc;
        b->cap = cap;
        /* the elements moved; free the old buffer without dropping them */
        stn_free(a);
        *pa = b;
    } else {
        int64_t cap = need > a->len * 2 ? need : a->len * 2;
        if (cap < 4) cap = 4;
        if (cap > STN_MAX_ALLOC) cap = STN_MAX_ALLOC;
        StnArray* b = stn_array_copy(a, cap);
        stn_drop(a, stn_array_release);
        *pa = b;
    }
}

void stn_array_push_slow(StnArray** pa, const void* elem) {
    StnArray* a = *pa;
    if (!stn_unique(a) || a->len == a->cap) { stn_array_reserve(pa, 1); a = *pa; }
    memcpy(a->data + (size_t)a->len * a->ops->size, elem, a->ops->size);
    a->len++;
}

StnArray* stn_array_slice(StnArray* a, int64_t lo, int64_t hi, const char* file, int line, int col) {
    if (lo < 0 || hi > a->len || lo > hi) {
        char buf[96];
        snprintf(buf, sizeof buf, "slice %lld..%lld, length %lld", (long long)lo, (long long)hi, (long long)a->len);
        stn_trap("index out of range", file, line, col, buf);
    }
    int64_t n = hi - lo;
    StnArray* b = stn_array_new(a->ops, n > 0 ? n : 1);
    size_t sz = a->ops->size;
    memcpy(b->data, a->data + (size_t)lo * sz, (size_t)n * sz);
    b->len = n;
    if (a->ops->dup) for (int64_t i = 0; i < n; i++) a->ops->dup(b->data + (size_t)i * sz);
    return b;
}

void stn_array_extend(StnArray** pa, StnArray* b) {
    int64_t n = b->len;
    stn_dup(b);   /* b may be *pa itself */
    stn_array_reserve(pa, n);
    StnArray* a = *pa;
    size_t sz = a->ops->size;
    memcpy(a->data + (size_t)a->len * sz, b->data, (size_t)n * sz);
    if (a->ops->dup) for (int64_t i = 0; i < n; i++) a->ops->dup(a->data + (size_t)(a->len + i) * sz);
    a->len += n;
    stn_drop(b, stn_array_release);
}

void stn_array_insert(StnArray** pa, int64_t i, const void* elem, const char* file, int line, int col) {
    if (i < 0 || i > (*pa)->len) {
        char buf[96];
        snprintf(buf, sizeof buf, "index %lld, length %lld", (long long)i, (long long)(*pa)->len);
        stn_trap("index out of range", file, line, col, buf);
    }
    stn_array_reserve(pa, 1);
    StnArray* a = *pa;
    size_t sz = a->ops->size;
    memmove(a->data + (size_t)(i + 1) * sz, a->data + (size_t)i * sz, (size_t)(a->len - i) * sz);
    memcpy(a->data + (size_t)i * sz, elem, sz);
    a->len++;
}

void stn_array_remove(StnArray** pa, int64_t i, void* out, const char* file, int line, int col) {
    if (i < 0 || i >= (*pa)->len) {
        char buf[96];
        snprintf(buf, sizeof buf, "index %lld, length %lld", (long long)i, (long long)(*pa)->len);
        stn_trap("index out of range", file, line, col, buf);
    }
    stn_array_make_unique(pa);
    StnArray* a = *pa;
    size_t sz = a->ops->size;
    memcpy(out, a->data + (size_t)i * sz, sz);
    memmove(a->data + (size_t)i * sz, a->data + (size_t)(i + 1) * sz, (size_t)(a->len - i - 1) * sz);
    a->len--;
}

void stn_array_clear(StnArray** pa) {
    StnArray* a = *pa;
    if (stn_unique(a)) {
        if (a->ops->drop) {
            for (int64_t i = 0; i < a->len; i++)
                a->ops->drop(a->data + (size_t)i * a->ops->size);
        }
        a->len = 0;
    } else {
        *pa = stn_array_new(a->ops, 4);
        stn_drop(a, stn_array_release);
    }
}

StnArray* stn_array_filled_i64(const StnElemOps* ops, int64_t n, int64_t value,
                              const char* file, int line, int col) {
    if (n < 0) stn_trap("index out of range", file, line, col, "negative length");
    if (n > STN_MAX_ALLOC / (int64_t)sizeof(int64_t)) stn_too_large(file, line, col);
    StnArray* a = stn_array_new(ops, n > 0 ? n : 1);
    int64_t* elements = (int64_t*)a->data;
    for (int64_t i = 0; i < n; i++) elements[i] = value;
    a->len = n;
    return a;
}

void stn_array_reverse_i64(StnArray** pa) {
    if ((*pa)->len < 2) return;
    stn_array_make_unique(pa);
    int64_t* elements = (int64_t*)(*pa)->data;
    int64_t i = 0, end = (*pa)->len;
#if defined(__SSE2__)
    for (; end - i >= 4; i += 2, end -= 2) {
        __m128i lo = _mm_loadu_si128((const __m128i_u*)(elements + i));
        __m128i hi = _mm_loadu_si128((const __m128i_u*)(elements + end - 2));
        _mm_storeu_si128((__m128i_u*)(elements + i), _mm_shuffle_epi32(hi, _MM_SHUFFLE(1, 0, 3, 2)));
        _mm_storeu_si128((__m128i_u*)(elements + end - 2), _mm_shuffle_epi32(lo, _MM_SHUFFLE(1, 0, 3, 2)));
    }
#endif
    for (; i < --end; i++) {
        int64_t tmp = elements[i];
        elements[i] = elements[end];
        elements[end] = tmp;
    }
}

#if defined(__x86_64__) && defined(__SSE2__)
__attribute__((target("avx512f")))
static int stn_contains_i64_avx512(const int64_t* elements, int64_t length, int64_t value) {
    const __m512i needle = _mm512_set1_epi64(value);
    int64_t i = 0;
    /* Align the full-width loads so none straddles a cache line. */
    for (; i < length && ((uintptr_t)(elements + i) & 63u) != 0; i++)
        if (elements[i] == value) return 1;
    for (; length - i >= 32; i += 32) {
        const __mmask8 a = _mm512_cmpeq_epi64_mask(_mm512_load_si512(elements + i), needle);
        const __mmask8 b = _mm512_cmpeq_epi64_mask(_mm512_load_si512(elements + i + 8), needle);
        const __mmask8 c = _mm512_cmpeq_epi64_mask(_mm512_load_si512(elements + i + 16), needle);
        const __mmask8 d = _mm512_cmpeq_epi64_mask(_mm512_load_si512(elements + i + 24), needle);
        if (a | b | c | d) return 1;
    }
    for (; i < length; i++)
        if (elements[i] == value) return 1;
    return 0;
}

__attribute__((target("avx2")))
static int stn_contains_i64_avx2(const int64_t* elements, int64_t length, int64_t value) {
    const __m256i needle = _mm256_set1_epi64x(value);
    int64_t i = 0;
    for (; length - i >= 16; i += 16) {
        const __m256i a = _mm256_cmpeq_epi64(_mm256_loadu_si256((const __m256i_u*)(elements + i)), needle);
        const __m256i b = _mm256_cmpeq_epi64(_mm256_loadu_si256((const __m256i_u*)(elements + i + 4)), needle);
        const __m256i c = _mm256_cmpeq_epi64(_mm256_loadu_si256((const __m256i_u*)(elements + i + 8)), needle);
        const __m256i d = _mm256_cmpeq_epi64(_mm256_loadu_si256((const __m256i_u*)(elements + i + 12)), needle);
        __m256i any = _mm256_or_si256(_mm256_or_si256(a, b), _mm256_or_si256(c, d));
        if (_mm256_movemask_epi8(any)) return 1;
    }
    for (; i < length; i++)
        if (elements[i] == value) return 1;
    return 0;
}
#endif

int stn_array_contains_i64(const StnArray* a, int64_t value) {
    const int64_t* elements = (const int64_t*)a->data;
#if defined(__x86_64__) && defined(__SSE2__)
    if (a->len >= 64 && __builtin_cpu_supports("avx512f"))
        return stn_contains_i64_avx512(elements, a->len, value);
    if (a->len >= 32 && __builtin_cpu_supports("avx2"))
        return stn_contains_i64_avx2(elements, a->len, value);
#endif
    int64_t i = 0;
    for (; a->len - i >= 32; i += 32) {
        unsigned found = 0;
        for (int64_t j = 0; j < 32; j++)
            found |= (unsigned)(elements[i + j] == value);
        if (found) return 1;
    }
    for (; i < a->len; i++)
        if (elements[i] == value) return 1;
    return 0;
    return 0;
}

int64_t stn_array_count_true(const StnArray* a) {
    const uint8_t* values = (const uint8_t*)a->data;
    int64_t i = 0, count = 0;
#if defined(__SSE2__)
    __m128i zero = _mm_setzero_si128();
    __m128i one = _mm_set1_epi8(1);
    __m128i total = zero;
    for (; a->len - i >= 16; i += 16) {
        __m128i bytes = _mm_loadu_si128((const __m128i_u*)(values + i));
        __m128i truth = _mm_andnot_si128(_mm_cmpeq_epi8(bytes, zero), one);
        total = _mm_add_epi64(total, _mm_sad_epu8(truth, zero));
    }
    uint64_t halves[2];
    memcpy(halves, &total, sizeof halves);
    count = (int64_t)(halves[0] + halves[1]);
#endif
    for (; i < a->len; i++) count += values[i] != 0;
    return count;
}

int64_t stn_array_sum_i64(const StnArray* a, int64_t sum, const char* file, int line, int col) {
    const int64_t* values = (const int64_t*)a->data;
    int64_t n = stn_len(a);
    #pragma GCC unroll 4
    for (int64_t i = 0; i < n; i++)
        sum = stn_add_i64(sum, values[i], file, line, col);
    return sum;
}

/* Entry guards prove unique ownership and 0 <= count <= len. */
int64_t stn_array_sum_popped_i64(StnArray* a, int64_t count, int64_t sum,
                                const char* file, int line, int col) {
    const int64_t* values = (const int64_t*)a->data;
    int64_t n = stn_len(a);
    int64_t end = n - count;
    #pragma GCC unroll 4
    for (int64_t i = n; i > end; i--)
        sum = stn_add_i64(sum, values[i - 1], file, line, col);
    a->len = end;
    return sum;
}

void stn_array_sort_i64(StnArray** pa) {
    size_t n = (size_t)(*pa)->len;
    if (n < 2) return;
    stn_array_make_unique(pa);
    int64_t* elements = (int64_t*)(*pa)->data;
    if (n <= 32) {
        for (size_t i = 1; i < n; i++) {
            int64_t value = elements[i];
            size_t j = i;
            while (j > 0 && elements[j - 1] > value) {
                elements[j] = elements[j - 1];
                j--;
            }
            elements[j] = value;
        }
        return;
    }

    /* Skip passes for bytes that are constant across the input. Stable digit
       passes order negative keys first by flipping the sign bit on the last pass. */
    uint64_t differing = 0, first = (uint64_t)elements[0];
    for (size_t i = 1; i < n; i++) differing |= first ^ (uint64_t)elements[i];
    if (differing == 0) return;
    int64_t* scratch = malloc(n * sizeof *scratch);
    if (!scratch) stn_trap("out of memory", "<runtime>", 0, 0, "could not allocate sort buffer");
    int64_t* src = elements;
    int64_t* dst = scratch;
    for (unsigned shift = 0; differing; shift += 8, differing >>= 8) {
        if ((differing & 255) == 0) continue;
        size_t offsets[256] = {0};
        unsigned sign = shift == 56 ? 128 : 0;
        for (size_t i = 0; i < n; i++) offsets[(((uint64_t)src[i] >> shift) & 255) ^ sign]++;
        size_t total = 0;
        for (unsigned bucket = 0; bucket < 256; bucket++) {
            size_t count = offsets[bucket];
            offsets[bucket] = total;
            total += count;
        }
        for (size_t i = 0; i < n; i++)
            dst[offsets[(((uint64_t)src[i] >> shift) & 255) ^ sign]++] = src[i];
        int64_t* tmp = src;
        src = dst;
        dst = tmp;
    }
    if (src != elements) memcpy(elements, src, n * sizeof *elements);
    free(scratch);
}

StnArray* stn_array_filled(const StnElemOps* ops, int64_t n, const void* elem, const char* file, int line, int col) {
    if (n < 0) stn_trap("index out of range", file, line, col, "negative length");
    if (n > STN_MAX_ALLOC || (uint64_t)n > (uint64_t)STN_MAX_ALLOC / (ops->size ? ops->size : 1)) stn_too_large(file, line, col);
    StnArray* a = stn_array_new(ops, n > 0 ? n : 1);
    for (int64_t i = 0; i < n; i++) {
        memcpy(a->data + (size_t)i * ops->size, elem, ops->size);
        if (ops->dup) ops->dup(a->data + (size_t)i * ops->size);
    }
    a->len = n;
    return a;
}

_Noreturn void stn_index_trap(int64_t i, int64_t len, const char* file, int line, int col) {
    char buf[96];
    snprintf(buf, sizeof buf, "index %lld, length %lld", (long long)i, (long long)len);
    stn_trap("index out of range", file, line, col, buf);
}

/* ---- console ---- */
void stn_print(StnStr s) {
    if (stn_outlen + (size_t)s->len + 1 > sizeof stn_outbuf) stn_flush();
    if ((size_t)s->len + 1 > sizeof stn_outbuf) { fwrite(s->data, 1, (size_t)s->len, stdout); fputc('\n', stdout); return; }
    memcpy(stn_outbuf + stn_outlen, s->data, (size_t)s->len);
    stn_outlen += (size_t)s->len;
    stn_outbuf[stn_outlen++] = '\n';
}

/* A Str is always valid UTF-8 (section 3.1): each byte that does not start a well-formed
   sequence (no overlong forms, no surrogates, nothing above U+10FFFF) becomes U+FFFD.
   The reference interpreter applies the same rule (Interp.sanitize_utf8). */
/* Returns the width of a valid non-ASCII sequence, or zero. The caller has
   already established that at least one byte is present. */
static size_t stn_utf8_width(const unsigned char* p, size_t remaining) {
    unsigned lead = p[0];
    if (remaining < 2 || lead < 0xC2 || lead > 0xF4) return 0;
    unsigned second = p[1];
    if ((second & 0xC0) != 0x80) return 0;
    if (lead < 0xE0) return 2;
    if (remaining < 3 || (p[2] & 0xC0) != 0x80) return 0;
    if (lead < 0xF0) {
        if ((lead == 0xE0 && second < 0xA0) || (lead == 0xED && second >= 0xA0)) return 0;
        return 3;
    }
    if (remaining < 4 || (p[3] & 0xC0) != 0x80) return 0;
    if ((lead == 0xF0 && second < 0x90) || (lead == 0xF4 && second >= 0x90)) return 0;
    return 4;
}

static int stn_utf8_valid(const char* data, size_t n) {
    const unsigned char* p = (const unsigned char*)data;
    while (n > 0) {
        while (n >= sizeof(uint64_t)) {
            uint64_t block;
            memcpy(&block, p, sizeof block);
            if (block & UINT64_C(0x8080808080808080)) break;
            p += sizeof block;
            n -= sizeof block;
        }
        while (n > 0 && *p < 0x80) {
            p++;
            n--;
        }
        if (n == 0) return 1;
        size_t width = stn_utf8_width(p, n);
        if (width == 0) return 0;
        p += width;
        n -= width;
    }
    return 1;
}

static StnStr stn_str_replace_invalid_utf8(const char* data, size_t n) {
    const unsigned char* bytes = (const unsigned char*)data;
    if (n > (SIZE_MAX - sizeof(StnStrBuf) - 1) / 3 ||
        n > INT64_MAX / 3)
        stn_too_large("<runtime>", 0, 0);
    char* repaired = malloc(n * 3 + 1);
    if (!repaired) stn_trap("out of memory", "<runtime>", 0, 0, "could not repair input");
    size_t written = 0;
    for (size_t i = 0; i < n;) {
        if (bytes[i] < 0x80) {
            repaired[written++] = (char)bytes[i++];
            continue;
        }
        size_t width = stn_utf8_width(bytes + i, n - i);
        if (width > 0) {
            memcpy(repaired + written, bytes + i, width);
            written += width;
            i += width;
        } else {
            memcpy(repaired + written, "\xEF\xBF\xBD", 3);
            written += 3;
            i++;
        }
    }
    StnStr result = stn_str_new(repaired, (int64_t)written);
    free(repaired);
    return result;
}

StnStr stn_str_from_bytes(const char* data, int64_t n) {
    if (stn_utf8_valid(data, (size_t)n)) return stn_str_new(data, n);
    return stn_str_replace_invalid_utf8(data, (size_t)n);
}

int stn_read_line(StnStr* out) {
    stn_flush();
    char* buf = NULL;
    size_t cap = 0;
    errno = 0;
    ssize_t n = getline(&buf, &cap, stdin);
    if (n < 0) {
        if (errno == ENOMEM) stn_trap("out of memory", "<runtime>", 0, 0, "could not allocate input buffer");
        free(buf);
        return 0;
    }
    if (n > 0 && buf[n - 1] == '\n') n--;
    *out = stn_str_from_bytes(buf, (int64_t)n);
    free(buf);
    return 1;
}

StnStr stn_read_all(const char* file, int line, int col) {
    stn_flush();
    size_t cap = 65536;
    struct stat info;
    if (fstat(fileno(stdin), &info) == 0 && S_ISREG(info.st_mode) &&
        info.st_size > 0 && info.st_size < 32 * 1024 * 1024) {
        off_t offset = ftello(stdin);
        if (offset >= 0 && info.st_size - offset >= (off_t)cap)
            cap = (size_t)(info.st_size - offset) + 1;
    }

    StnStr s = (StnStr)stn_alloc(sizeof(StnStrBuf) + cap + 1);
    size_t len = 0;
    for (;;) {
        len += fread(s->data + len, 1, cap - len, stdin);
        if (feof(stdin)) break;
        if (ferror(stdin)) stn_trap("input error", file, line, col, "could not read stdin");
        if (len == cap) {
            if (cap > (SIZE_MAX - sizeof(StnStrBuf) - 1) / 2 ||
                (uint64_t)cap > (uint64_t)STN_MAX_ALLOC / 2)
                stn_too_large(file, line, col);
            cap *= 2;
            StnStr grown = realloc(s, sizeof(StnStrBuf) + cap + 1);
            if (!grown) stn_trap("out of memory", file, line, col, "could not grow input buffer");
            s = grown;
        }
    }
    if (!stn_utf8_valid(s->data, len)) {
        StnStr text = stn_str_replace_invalid_utf8(s->data, len);
        STN_STR_DROP(s);
        return text;
    }
    s->len = (int64_t)len;
    s->data[len] = 0;
    return s;
}

int64_t stn_clock_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

/* ---- string built-ins ---- */
StnArray* stn_str_chars(StnStr s, const StnElemOps* ops) {
    StnArray* a = stn_array_new(ops, s->len > 0 ? s->len : 1);
    const unsigned char* p = (const unsigned char*)s->data;
    int64_t i = 0;
    while (i < s->len) {
        uint32_t c = p[i];
        int len = 1;
        /* strings are valid UTF-8; the bound keeps a decode inside the buffer regardless */
        if ((c >= 0xF0 && i + 4 > s->len) || (c >= 0xE0 && i + 3 > s->len) || (c >= 0xC0 && i + 2 > s->len)) c = 0xFFFD, len = 0;
        if (len == 0) len = 1;
        else if (c >= 0xF0) { c = ((c & 7) << 18) | ((p[i+1] & 0x3F) << 12) | ((p[i+2] & 0x3F) << 6) | (p[i+3] & 0x3F); len = 4; }
        else if (c >= 0xE0) { c = ((c & 15) << 12) | ((p[i+1] & 0x3F) << 6) | (p[i+2] & 0x3F); len = 3; }
        else if (c >= 0xC0) { c = ((c & 31) << 6) | (p[i+1] & 0x3F); len = 2; }
        ((uint32_t*)a->data)[a->len++] = c;
        i += len;
    }
    return a;
}

/* Search counted bytes, including embedded NULs. Empty needles are handled by callers. */
static const char* stn_find_bytes(const char* haystack, size_t n, const char* needle, size_t m) {
    if (m > n) return NULL;
#if defined(__SSE2__)
    if (m <= 16 && m > 1) {
        const size_t candidates = n - m + 1;
        const __m128i first = _mm_set1_epi8(needle[0]);
        const __m128i last = _mm_set1_epi8(needle[m - 1]);
        size_t i = 0;
        for (; candidates - i >= 16; i += 16) {
            const __m128i starts = _mm_loadu_si128((const __m128i_u*)(haystack + i));
            const __m128i ends = _mm_loadu_si128((const __m128i_u*)(haystack + i + m - 1));
            unsigned hits = (unsigned)_mm_movemask_epi8(_mm_and_si128(
                _mm_cmpeq_epi8(starts, first), _mm_cmpeq_epi8(ends, last)));
            while (hits) {
                unsigned offset = (unsigned)__builtin_ctz(hits);
                if (m == 2 || memcmp(haystack + i + offset + 1, needle + 1, m - 2) == 0)
                    return haystack + i + offset;
                hits &= hits - 1;
            }
        }
        haystack += i;
        n -= i;
    }
#endif
    if (m == 1) return memchr(haystack, (unsigned char)*needle, n);
    const char* end = haystack + (n - m) + 1;
    while (haystack < end) {
        const char* hit = memchr(haystack, (unsigned char)*needle, (size_t)(end - haystack));
        if (!hit || memcmp(hit + 1, needle + 1, m - 1) == 0) return hit;
        haystack = hit + 1;
    }
    return NULL;
}

StnArray* stn_str_split(StnStr s, StnStr sep, const StnElemOps* ops, const char* file, int line, int col) {
    if (sep->len == 0) stn_trap("invalid argument", file, line, col, "split with an empty separator");
    StnArray* a = stn_array_new(ops, 4);
    const char* field = s->data;
    const char* end = s->data + s->len;
    const char* hit;
    while ((hit = stn_find_bytes(field, (size_t)(end - field), sep->data, (size_t)sep->len))) {
        StnStr part = stn_str_new(field, (int64_t)(hit - field));
        STN_PUSH(&a, StnStr, part);
        field = hit + sep->len;
    }
    StnStr last = stn_str_new(field, (int64_t)(end - field));
    STN_PUSH(&a, StnStr, last);
    return a;
}

StnStr stn_str_join_parts(const StnStr* parts, int64_t n, StnStr sep) {
    size_t total = 0;
    size_t limit = SIZE_MAX - sizeof(StnStrBuf) - 1;
    if (limit > INT64_MAX) limit = INT64_MAX;
    for (int64_t i = 0; i < n; i++) {
        if ((uint64_t)parts[i]->len > limit - total ||
            (i && (uint64_t)sep->len > limit - total - (size_t)parts[i]->len))
            stn_too_large("<runtime>", 0, 0);
        total += (size_t)parts[i]->len + (i ? (size_t)sep->len : 0);
    }
    StnStr s = (StnStr)stn_alloc(sizeof(StnStrBuf) + total + 1);
    s->len = (int64_t)total;
    size_t at = 0;
    for (int64_t i = 0; i < n; i++) {
        if (i) {
            memcpy(s->data + at, sep->data, (size_t)sep->len);
            at += (size_t)sep->len;
        }
        memcpy(s->data + at, parts[i]->data, (size_t)parts[i]->len);
        at += (size_t)parts[i]->len;
    }
    s->data[total] = 0;
    return s;
}

StnStr stn_str_join(StnArray* xs, StnStr sep) {
    return stn_str_join_parts((const StnStr*)xs->data, xs->len, sep);
}

static int stn_space(char c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c == '\v'; }

StnStr stn_str_trim(StnStr s) {
    int64_t lo = 0, hi = s->len;
    while (lo < hi && stn_space(s->data[lo])) lo++;
    while (hi > lo && stn_space(s->data[hi - 1])) hi--;
    return stn_str_new(s->data + lo, hi - lo);
}

uint8_t stn_str_contains_slow(StnStr s, StnStr sub) {
    return sub->len == 0 || stn_find_bytes(s->data, (size_t)s->len, sub->data, (size_t)sub->len) != NULL;
}
StnStr stn_str_repeat(StnStr s, int64_t n, const char* file, int line, int col) {
    if (n < 0) stn_trap("invalid argument", file, line, col, "negative repeat count");
    if (n > 0 && s->len > STN_MAX_ALLOC / n) stn_too_large(file, line, col);
    StnStr r = (StnStr)stn_alloc(sizeof(StnStrBuf) + (size_t)(s->len * n) + 1);
    r->len = s->len * n;
    for (int64_t i = 0; i < n; i++) memcpy(r->data + i * s->len, s->data, (size_t)s->len);
    r->data[r->len] = 0;
    return r;
}

int stn_parse_int(StnStr s, int64_t* out) {
    int64_t i = 0, n = s->len;
    if (n == 0) return 1;
    int neg = s->data[0] == '-';
    if (s->data[0] == '-' || s->data[0] == '+') i = 1;
    if (i == n) return 1;
    int64_t acc = 0;
    if (n - i <= 18) {
        for (; n - i >= 4; i += 4) {
            unsigned a = (unsigned char)s->data[i] - (unsigned)'0';
            unsigned b = (unsigned char)s->data[i+1] - (unsigned)'0';
            unsigned c = (unsigned char)s->data[i+2] - (unsigned)'0';
            unsigned d = (unsigned char)s->data[i+3] - (unsigned)'0';
            if (a > 9 || b > 9 || c > 9 || d > 9) return 1;
            acc = acc * 10000 - (int64_t)(1000*a + 100*b + 10*c + d);
        }
        for (; i < n; i++) {
            unsigned digit = (unsigned char)s->data[i] - (unsigned)'0';
            if (digit > 9) return 1;
            acc = acc * 10 - digit;
        }
    } else {
        for (; i < n; i++) {
            unsigned digit = (unsigned char)s->data[i] - (unsigned)'0';
            if (digit > 9) return 1;
            if (acc < INT64_MIN / 10 || acc * 10 < INT64_MIN + digit) {
                /* Invalid syntax has priority over a range error. */
                for (i++; i < n; i++)
                    if (s->data[i] < '0' || s->data[i] > '9') return 1;
                return 2;
            }
            acc = acc * 10 - digit;
        }
    }
    if (!neg) { if (acc == INT64_MIN) return 2; acc = -acc; }
    *out = acc;
    return 0;
}

/* A short plain decimal can be rounded by one binary64 division: both
   operands are exact integers below 2^53. Exponents and long decimals use strtod. */
static int stn_parse_short_float(const char* data, int64_t n, double* out) {
    if (n > 15) return 0;
    int64_t i = data[0] == '-' || data[0] == '+' ? 1 : 0;
    uint64_t mantissa = 0, divisor = 1;
    int digits = 0, has_point = 0;
    for (; i < n; i++) {
        unsigned c = (unsigned char)data[i];
        if (c == '.' && !has_point) {
            has_point = 1;
            continue;
        }
        if (c - '0' > 9) return 0;
        mantissa = mantissa * 10 + (c - '0');
        if (has_point) divisor *= 10;
        digits++;
    }
    if (!digits) return 0;
    double signed_mantissa = data[0] == '-' ? -(double)mantissa : (double)mantissa;
    *out = signed_mantissa / (double)divisor;
    return 1;
}

int stn_parse_float(StnStr s, double* out) {
    if (s->len == 0) return 1;
    if (stn_parse_short_float(s->data, s->len, out)) return 0;
    for (int64_t i = 0; i < s->len; i++) {
        char c = s->data[i];
        if (!((c >= '0' && c <= '9') || c == '.' || c == '-' || c == '+' || c == 'e' || c == 'E')) return 1;
    }
    char* end;
    *out = strtod(s->data, &end);
    return end != s->data + s->len;
}

void stn_runtime_flush_for_error(void) { stn_flush(); }

/* ---- start-up ---- */
#ifdef STN_STACK_TRAP
/* A program that recurses without end runs the stack out. The fault is reported as a trap, like the other
   ways a program can be wrong, with the status of one, instead of ending in a signal. The handler runs on a
   stack of its own, and only code that is safe in a handler runs in it. A fault anywhere else is a bug, and
   ends the process as it would have. */
static uintptr_t stn_stack_high; /* an integer: the address of a local of start-up, taken while it lived */
static size_t stn_stack_size;
static void stn_on_fault(int sig, siginfo_t* si, void* ctx) {
    (void)ctx;
    /* The addresses are compared as integers, which is defined for any value of si_addr, and the range is
       written as a difference that cannot wrap: the fault is below the top of the stack, by no more than
       the stack's size and a page of slack for the frame that faulted. */
    uintptr_t a = (uintptr_t)si->si_addr;
    if (a < stn_stack_high && stn_stack_high - a <= (uintptr_t)stn_stack_size + 65536) {
        static const char msg[] = "trap: stack overflow\nthe program recursed deeper than its stack allows\n";
        ssize_t r = write(1, stn_outbuf, stn_outlen);
        r = write(2, msg, sizeof msg - 1);
        (void)r;
        _exit(2);
    }
    signal(sig, SIG_DFL);
    raise(sig);
}
void stn_runtime_init(void) {
    struct rlimit rl;
    char here;
    stn_stack_high = (uintptr_t)&here;
    stn_stack_size = (getrlimit(RLIMIT_STACK, &rl) == 0 && rl.rlim_cur != RLIM_INFINITY) ? (size_t)rl.rlim_cur : (size_t)8 << 20;
    size_t alt_size = 64 * 1024;
    void* alt = malloc(alt_size);
    if (alt == NULL) return;
    stack_t ss;
    ss.ss_sp = alt; ss.ss_size = alt_size; ss.ss_flags = 0;
    if (sigaltstack(&ss, NULL) != 0) return;
    struct sigaction sa;
    sa.sa_sigaction = stn_on_fault;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);
}
#else
void stn_runtime_init(void) {}
#endif

void stn_runtime_exit(int status) {
    stn_flush();
#ifdef STN_DEBUG
    /* an error that reaches main returns normally through every frame, so counts must
       balance then too; only a trap (exit 2) leaves objects behind */
    if ((status == 0 || status == 1) && stn_live_objects != 0 && getenv("STN_ALLOW_LEAKS") == NULL) {
        fprintf(stderr, "debug runtime: %lld object(s) still live at exit; counts do not balance\n",
                (long long)stn_live_objects);
        exit(3);
    }
#endif
    exit(status);
}

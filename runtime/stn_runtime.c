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

char* stn_str_start(StnStr* s, int64_t len) {
    if (len <= STN_STR_INLINE_MAX) {
        s->w0 = 0;
        s->w1 = (uint64_t)len << 56;
        return (char*)s;
    }
    StnStrBuf* b = (StnStrBuf*)stn_alloc(sizeof(StnStrBuf) + (size_t)len + 1);
    b->len = len;
    b->data[len] = 0;
    s->buf = b;
    s->w1 = (uint64_t)len | STN_STR_HEAP_BIT;
    return b->data;
}

_Noreturn void stn_trap_str(const char* kind, const char* file, int line, int col, StnStr msg) {
    int64_t n = stn_str_len(msg);
    char* text = malloc((size_t)n + 1);
    if (!text) stn_trap(kind, file, line, col, "");
    memcpy(text, stn_str_ptr(&msg), (size_t)n);
    text[n] = 0;
    stn_trap(kind, file, line, col, text);
}

StnStr stn_str_new_heap(const char* data, int64_t len) {
    StnStr s;
    char* d = stn_str_start(&s, len);
    memcpy(d, data, (size_t)len);
    return s;
}

#if defined(__SIZEOF_INT128__)
/* A 128-bit integer is an extension; __extension__ keeps a strict ISO build (-pedantic-errors)
   accepting it, as both GCC and Clang allow. */
__extension__ typedef unsigned __int128 stn_u128;
/* the bytes of an inline string as one number, without its length */
static inline stn_u128 stn_str_bits(const StnStr* s) {
    return (stn_u128)s->w0 | ((stn_u128)(s->w1 & ~(UINT64_C(0xFF) << 56)) << 64);
}
#endif

#if defined(__SIZEOF_INT128__)
/* Both parts are inline: shift and combine their words. Kept out of line, so the registers it
   needs are not saved on every call that builds a buffer. */
static __attribute__((noinline)) StnStr stn_str_concat_small(const StnStr* a, const StnStr* b, int64_t an, int64_t bn) {
    StnStr s;
    stn_u128 v = stn_str_bits(a) | (stn_str_bits(b) << (8 * an));
    s.w0 = (uint64_t)v;
    s.w1 = (uint64_t)(v >> 64) | ((uint64_t)(an + bn) << 56);
    return s;
}

static __attribute__((noinline)) StnStr stn_str_concat_n_small(int n, const StnStr* parts, int64_t total) {
    StnStr s;
    stn_u128 v = 0;
    int64_t at = 0;
    for (int i = 0; i < n; i++) {
        int64_t k = stn_str_len(parts[i]);
        if (k) v |= stn_str_bits(&parts[i]) << (8 * at);
        at += k;
    }
    s.w0 = (uint64_t)v;
    s.w1 = (uint64_t)(v >> 64) | ((uint64_t)total << 56);
    return s;
}
#endif

StnStr stn_str_concat(const StnStr* a, const StnStr* b) {
    int64_t an, bn;
    const char* ad = stn_str_span(a, &an);
    const char* bd = stn_str_span(b, &bn);
    StnStr s;
#if defined(__SIZEOF_INT128__)
    if (an + bn <= STN_STR_INLINE_MAX) return stn_str_concat_small(a, b, an, bn);
#endif
    char* d = stn_str_start(&s, an + bn);
    memcpy(d, ad, (size_t)an);
    memcpy(d + an, bd, (size_t)bn);
    return s;
}

StnStr stn_str_concat_n(int n, StnStr* parts) {
    int64_t total = 0;
    for (int i = 0; i < n; i++) total += stn_str_len(parts[i]);
    StnStr s;
#if defined(__SIZEOF_INT128__)
    if (total <= STN_STR_INLINE_MAX) return stn_str_concat_n_small(n, parts, total);
#endif
    char* d = stn_str_start(&s, total);
    int64_t at = 0;
    for (int i = 0; i < n; i++) {
        int64_t k;
        const char* pd = stn_str_span(&parts[i], &k);
        memcpy(d + at, pd, (size_t)k);
        at += k;
    }
    return s;
}

int stn_str_cmp(const StnStr* a, const StnStr* b) {
    int64_t an, bn;
    const char* ad = stn_str_span(a, &an);
    const char* bd = stn_str_span(b, &bn);
    int64_t n = an < bn ? an : bn;
    int c = memcmp(ad, bd, (size_t)n);
    if (c) return c < 0 ? -1 : 1;
    return an < bn ? -1 : an > bn ? 1 : 0;
}

static int stn_boundary(const char* d, int64_t n, int64_t i) {
    return i == 0 || i == n || ((unsigned char)d[i] & 0xC0) != 0x80;
}

StnStr stn_str_slice(const StnStr* s, int64_t lo, int64_t hi, const char* file, int line, int col) {
    int64_t n;
    const char* d = stn_str_span(s, &n);
    if (lo < 0 || hi > n || lo > hi) {
        char buf[96];
        snprintf(buf, sizeof buf, "slice %lld..%lld, length %lld", (long long)lo, (long long)hi, (long long)n);
        stn_trap("index out of range", file, line, col, buf);
    }
    if (!stn_boundary(d, n, lo) || !stn_boundary(d, n, hi))
        stn_trap("index out of range", file, line, col, "slice does not fall on character boundaries");
    if (lo == 0 && hi == n) return stn_str_dup(*s);
    return stn_str_new(d + lo, hi - lo);
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

/* A counted loop that pushes once per turn says how many elements are coming. Growing once to that
   size saves the copies of doubling and leaves no slack. It is only a hint: it never traps, an
   array that is shared or small is left alone, and a failed allocation leaves ordinary growth to
   report it when a push actually needs the room. */
void stn_array_reserve_hint(StnArray** pa, uint64_t extra) {
    StnArray* a = *pa;
    size_t size = a->ops->size;
    if (!stn_unique(a) || size == 0) return;
    if (extra > (uint64_t)STN_MAX_ALLOC || (uint64_t)a->len + extra > (uint64_t)STN_MAX_ALLOC) return;
    int64_t need = a->len + (int64_t)extra;
    if (need <= a->cap || (uint64_t)need > (uint64_t)STN_MAX_ALLOC / size) return;
    /* the byte count must fit size_t, which is narrower than the element limit on a 32-bit target */
    if ((uint64_t)need > (SIZE_MAX - sizeof(StnArray)) / size) return;
    size_t bytes = sizeof(StnArray) + (size_t)need * size;
    if (bytes <= (size_t)STN_CLASSES * 16) return;
#ifndef STN_DEBUG
    if (a->h.size_class == 0 && sizeof(StnArray) + (size_t)a->cap * size > (size_t)STN_CLASSES * 16) {
        StnArray* grown = (StnArray*)realloc(a, bytes);
        if (!grown) return;
        grown->cap = need;
        *pa = grown;
        return;
    }
#endif
    StnArray* b = (StnArray*)malloc(bytes);
    if (!b) return;
    memcpy(b, a, sizeof(StnArray) + (size_t)a->len * size);
    b->h.rc = 1; b->h.flags = 0; b->h.size_class = 0;
    b->cap = need;
#ifdef STN_DEBUG
    stn_live_objects++;
#endif
    /* the elements moved; free the old buffer without dropping them */
    stn_free(a);
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
        if (a->h.size_class == 0 && bytes > (size_t)STN_CLASSES * 16) {
            StnArray* b = (StnArray*)realloc(a, bytes);
            if (!b) { fputs("trap: out of memory\n", stderr); exit(2); }
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
    int64_t i = 0;
    /* written out so that each checked add is an add and a jump on overflow */
    for (; i + 4 <= n; i += 4) {
        if (__builtin_add_overflow(sum, values[i], &sum)) goto overflow;
        if (__builtin_add_overflow(sum, values[i + 1], &sum)) goto overflow;
        if (__builtin_add_overflow(sum, values[i + 2], &sum)) goto overflow;
        if (__builtin_add_overflow(sum, values[i + 3], &sum)) goto overflow;
    }
    for (; i < n; i++)
        if (__builtin_add_overflow(sum, values[i], &sum)) goto overflow;
    return sum;
overflow:
    stn_overflow(file, line, col);
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

    /* Stable digit passes over the bits that differ across the input, lowest first. The span of
       differing bits is cut into as few digits as possible, of up to eleven bits for a large input
       (a 16 KiB table of counts) and eight for a small one; a digit whose bits are all constant is
       skipped. Negative keys order first by flipping the sign bit in the digit that holds it. */
    uint64_t differing = 0, first = (uint64_t)elements[0];
    for (size_t i = 1; i < n; i++) differing |= first ^ (uint64_t)elements[i];
    if (differing == 0) return;
    int64_t* scratch = malloc(n * sizeof *scratch);
    if (!scratch) stn_trap("out of memory", "<runtime>", 0, 0, "could not allocate sort buffer");
    int64_t* src = elements;
    int64_t* dst = scratch;
    const unsigned low = (unsigned)__builtin_ctzll(differing);
    const unsigned span = 64 - (unsigned)__builtin_clzll(differing) - low;
    const unsigned widest = n >= 16384 ? 11 : 8;
    const unsigned passes = (span + widest - 1) / widest;
    const unsigned width = (span + passes - 1) / passes;
    const uint64_t mask = ((uint64_t)1 << width) - 1;
    for (unsigned shift = low; shift < low + span; shift += width) {
        if (((differing >> shift) & mask) == 0) continue;
        size_t offsets[2048];
        memset(offsets, 0, ((size_t)mask + 1) * sizeof offsets[0]);
        const uint64_t sign = shift + width > 63 ? (uint64_t)1 << (63 - shift) : 0;
        for (size_t i = 0; i < n; i++) offsets[(((uint64_t)src[i] >> shift) & mask) ^ sign]++;
        size_t total = 0;
        for (size_t bucket = 0; bucket <= mask; bucket++) {
            size_t count = offsets[bucket];
            offsets[bucket] = total;
            total += count;
        }
        for (size_t i = 0; i < n; i++)
            dst[offsets[(((uint64_t)src[i] >> shift) & mask) ^ sign]++] = src[i];
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
void stn_print(const StnStr* s) {
    int64_t len;
    const char* d = stn_str_span(s, &len);
    size_t n = (size_t)len;
    if (stn_outlen + n + 1 > sizeof stn_outbuf) stn_flush();
    if (n + 1 > sizeof stn_outbuf) { fwrite(d, 1, n, stdout); fputc('\n', stdout); return; }
    memcpy(stn_outbuf + stn_outlen, d, n);
    stn_outlen += n;
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

    StnStrBuf* s = (StnStrBuf*)stn_alloc(sizeof(StnStrBuf) + cap + 1);
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
            StnStrBuf* grown = realloc(s, sizeof(StnStrBuf) + cap + 1);
            if (!grown) stn_trap("out of memory", file, line, col, "could not grow input buffer");
            s = grown;
        }
    }
    if (!stn_utf8_valid(s->data, len)) {
        StnStr text = stn_str_replace_invalid_utf8(s->data, len);
        stn_free(s);
        return text;
    }
    if (len <= STN_STR_INLINE_MAX) {
        StnStr text = stn_str_new(s->data, (int64_t)len);
        stn_free(s);
        return text;
    }
    s->len = (int64_t)len;
    s->data[len] = 0;
    StnStr text;
    text.buf = s;
    text.w1 = (uint64_t)len | STN_STR_HEAP_BIT;
    return text;
}

int64_t stn_clock_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

/* ---- maps and sets (section 3.6) ---- */
uint64_t stn_hash_k0 = UINT64_C(0x0706050403020100), stn_hash_k1 = UINT64_C(0x0f0e0d0c0b0a0908);

/* The key of the hash is drawn once, when the program starts, so that chosen keys cannot be made to
   collide. Nothing a program can observe depends on it: iteration follows insertion. */
static void stn_hash_init(void) {
    uint64_t k[2];
    int got = 0;
    FILE* f = fopen("/dev/urandom", "rb");
    if (f) { got = fread(k, sizeof k, 1, f) == 1; fclose(f); }
    if (!got) {
        struct timespec ts;
        clock_gettime(CLOCK_REALTIME, &ts);
        k[0] = (uint64_t)ts.tv_nsec ^ ((uint64_t)ts.tv_sec << 20) ^ (uint64_t)(uintptr_t)&k;
        k[1] = (uint64_t)getpid() * UINT64_C(0x9E3779B97F4A7C15) ^ (uint64_t)(uintptr_t)&stn_hash_init;
    }
    stn_hash_k0 = k[0]; stn_hash_k1 = k[1];
}

uint64_t stn_hash_bytes(const void* p, size_t n) {
    const unsigned char* in = (const unsigned char*)p;
    uint64_t v0 = stn_hash_k0 ^ UINT64_C(0x736f6d6570736575), v1 = stn_hash_k1 ^ UINT64_C(0x646f72616e646f6d);
    uint64_t v2 = stn_hash_k0 ^ UINT64_C(0x6c7967656e657261), v3 = stn_hash_k1 ^ UINT64_C(0x7465646279746573);
    size_t i = 0;
    for (; n - i >= 8; i += 8) {
        uint64_t m;
        memcpy(&m, in + i, 8);
        v3 ^= m; STN_SIPROUND; v0 ^= m;
    }
    /* the last 0 to 7 bytes, in at most two loads that may overlap: a byte read twice lands on
       the same bits both times */
    uint64_t b = (uint64_t)n << 56;
    size_t r = n - i;
    if (r >= 4) {
        uint32_t lo, hi;
        memcpy(&lo, in + i, 4);
        memcpy(&hi, in + i + r - 4, 4);
        b |= (uint64_t)lo | ((uint64_t)hi << ((r - 4) * 8));
    } else if (r >= 2) {
        uint16_t lo;
        memcpy(&lo, in + i, 2);
        b |= (uint64_t)lo | ((uint64_t)in[i + r - 1] << ((r - 1) * 8));
    } else if (r == 1) b |= in[i];
    v3 ^= b; STN_SIPROUND; v0 ^= b;
    v2 ^= 0xff; STN_SIPROUND; STN_SIPROUND; STN_SIPROUND;
    return v0 ^ v1 ^ v2 ^ v3;
}

uint64_t stn_hash_inline(uint64_t w0, uint64_t w1) {
    uint64_t v0 = stn_hash_k0 ^ UINT64_C(0x736f6d6570736575), v1 = stn_hash_k1 ^ UINT64_C(0x646f72616e646f6d);
    uint64_t v2 = stn_hash_k0 ^ UINT64_C(0x6c7967656e657261), v3 = stn_hash_k1 ^ UINT64_C(0x7465646279746573);
    uint64_t n = w1 >> 56, b;
    if (n >= 8) {
        v3 ^= w0; STN_SIPROUND; v0 ^= w0;
        b = w1;                      /* bytes 8 to n-1, zeros, and n in the last byte */
    } else b = w0 | (n << 56);       /* w0 is zero past byte n, and w1 holds only the length */
    v3 ^= b; STN_SIPROUND; v0 ^= b;
    v2 ^= 0xff; STN_SIPROUND; STN_SIPROUND; STN_SIPROUND;
    return v0 ^ v1 ^ v2 ^ v3;
}

/* The hash word of an entry: never 0, which marks a tombstone. */
static inline uint64_t stn_map_word(uint64_t h) { return h | (uint64_t)(h == 0); }

/* The two key types that most tables have are hashed and compared in place; any other goes
   through the functions of its table. */
static inline uint64_t stn_key_word(const StnMapOps* ops, const void* key) {
    if (ops->kind == STN_KEY_I64) return stn_map_word(stn_hash_u64(*(const uint64_t*)key));
    if (ops->kind == STN_KEY_STR) return stn_map_word(stn_str_hash(*(const StnStr*)key));
    return stn_map_word(ops->hash(key));
}
static inline int stn_key_eq(const StnMapOps* ops, const void* a, const void* b) {
    if (ops->kind == STN_KEY_I64) return *(const uint64_t*)a == *(const uint64_t*)b;
    if (ops->kind == STN_KEY_STR) return stn_str_eq(*(const StnStr*)a, *(const StnStr*)b);
    return ops->eq(a, b);
}

/* The index has a power of two of slots, 16 or more. Each slot has a control byte: STN_FREE, or
   STN_DEAD for a slot whose entry was removed, or the low seven bits of the hash of the entry it
   names. The control bytes are searched a group of sixteen at a time, and only a slot whose byte
   matches has its entry looked at, so a key that is not there is mostly settled within the control
   bytes, which are small enough to stay in the cache. Beside them, each slot has the place of its
   entry in the dense array, in 1, 2, 4 or 8 bytes as the capacity needs. */
#define STN_FREE 0xFF
#define STN_DEAD 0x80
#define STN_GROUP 16

static inline unsigned stn_place_width(int64_t cap) { return cap <= 256 ? 1 : cap <= 65536 ? 2 : cap <= INT64_C(4294967296) ? 4 : 8; }
static inline uint64_t stn_place_get(const uint8_t* places, unsigned width, uint64_t i) {
    switch (width) {
        case 1: return places[i];
        case 2: { uint16_t v; memcpy(&v, places + i * 2, 2); return v; }
        case 4: { uint32_t v; memcpy(&v, places + i * 4, 4); return v; }
        default: { uint64_t v; memcpy(&v, places + i * 8, 8); return v; }
    }
}
static inline void stn_place_set(uint8_t* places, unsigned width, uint64_t i, uint64_t v) {
    switch (width) {
        case 1: places[i] = (uint8_t)v; break;
        case 2: { uint16_t x = (uint16_t)v; memcpy(places + i * 2, &x, 2); break; }
        case 4: { uint32_t x = (uint32_t)v; memcpy(places + i * 4, &x, 4); break; }
        default: memcpy(places + i * 8, &v, 8);
    }
}
/* the slots of a group whose control byte is this tag, and those that are free or dead, as bits */
static inline unsigned stn_group_match(const uint8_t* g, uint8_t tag) {
#if defined(__SSE2__)
    return (unsigned)_mm_movemask_epi8(_mm_cmpeq_epi8(_mm_loadu_si128((const __m128i_u*)g), _mm_set1_epi8((char)tag)));
#else
    unsigned bits = 0;
    for (unsigned i = 0; i < STN_GROUP; i++) bits |= (unsigned)(g[i] == tag) << i;
    return bits;
#endif
}
static inline unsigned stn_group_unused(const uint8_t* g) {
#if defined(__SSE2__)
    return (unsigned)_mm_movemask_epi8(_mm_loadu_si128((const __m128i_u*)g));
#else
    unsigned bits = 0;
    for (unsigned i = 0; i < STN_GROUP; i++) bits |= (unsigned)(g[i] >> 7) << i;
    return bits;
#endif
}
/* the first sixteen control bytes are kept again after the last, so a group that starts near the
   end reads on without wrapping */
static inline void stn_ctrl_set(uint8_t* ctrl, uint64_t mask, uint64_t i, uint8_t c) {
    ctrl[i] = c;
    if (i < STN_GROUP) ctrl[mask + 1 + i] = c;
}
/* entries the index of this size takes before it grows: seven eighths of its slots */
static inline int64_t stn_map_room(uint32_t ilog) { return (int64_t)(((uint64_t)1 << ilog) / 8 * 7); }
static inline size_t stn_index_bytes(uint32_t ilog, unsigned width) {
    size_t slots = (size_t)1 << ilog;
    return slots + STN_GROUP + slots * width;
}

StnMap* stn_map_new(const StnMapOps* ops) {
    StnMap* m = (StnMap*)stn_alloc(sizeof(StnMap));
    m->len = 0; m->used = 0; m->cap = 0; m->ilog = 0; m->ops = ops;
    m->koff = ops->kind == STN_KEY_I64 ? 0 : 8;
    m->voff = (uint32_t)(m->koff + ((ops->ksize + 7) & ~(size_t)7));
    m->stride = (uint32_t)(m->voff + ((ops->vsize + 7) & ~(size_t)7));
    m->index = NULL; m->places = NULL; m->entries = NULL; m->dead = NULL;
    return m;
}

/* the hash word of an entry, stored or worked out again from its key */
static inline uint64_t stn_entry_word(const StnMap* m, const char* e) {
    if (m->koff) return *(const uint64_t*)e;
    return stn_key_word(m->ops, e);
}

_Noreturn static void stn_map_oom(void) { fputs("trap: out of memory\n", stderr); exit(2); }

/* The slot for a new entry with this hash word: the first one free or dead on its path. */
static inline uint64_t stn_map_free_slot(const uint8_t* ctrl, uint64_t mask, uint64_t w) {
    uint64_t pos = (w >> 7) & mask, step = 0;
    for (;;) {
        unsigned unused = stn_group_unused(ctrl + pos);
        if (unused) return (pos + (unsigned)__builtin_ctz(unused)) & mask;
        step += STN_GROUP;
        pos = (pos + step) & mask;
    }
}

/* Gives the table an index of 1 << ilog slots and room for the entries that go with it. The live
   entries close up over the tombstones, in their order and in the buffer they are in, which then
   grows or shrinks in place where the allocator can; the index is made anew from their hashes. */
static void stn_map_rebuild(StnMap* m, uint32_t ilog) {
    if (ilog > 40) stn_too_large("<runtime>", 0, 0);
    uint64_t slots = (uint64_t)1 << ilog, mask = slots - 1;
    int64_t cap = stn_map_room(ilog);
    unsigned width = stn_place_width(cap);
    if (m->used != m->len) {
        int64_t n = 0;
        for (int64_t i = 0; i < m->used; i++) {
            char* e = m->entries + (size_t)i * m->stride;
            if (stn_map_dead(m, i, e)) continue;
            if (i != n) memcpy(m->entries + (size_t)n * m->stride, e, m->stride);
            n++;
        }
        m->used = n;
    }
    free(m->dead); m->dead = NULL;
    char* entries = (char*)realloc(m->entries, (size_t)cap * m->stride);
    uint8_t* index = (uint8_t*)malloc(stn_index_bytes(ilog, width));
    if (!index || !entries) stn_map_oom();
    memset(index, STN_FREE, slots + STN_GROUP);
    uint8_t* places = index + slots + STN_GROUP;
    for (int64_t i = 0; i < m->used; i++) {
        uint64_t w = m->koff ? *(const uint64_t*)(entries + (size_t)i * m->stride) : stn_key_word(m->ops, entries + (size_t)i * m->stride);
        uint64_t s = stn_map_free_slot(index, mask, w);
        stn_ctrl_set(index, mask, s, (uint8_t)(w & 0x7F));
        stn_place_set(places, width, s, (uint64_t)i);
    }
    free(m->index);
    m->index = index; m->places = places; m->entries = entries; m->ilog = ilog; m->cap = cap;
}

static uint32_t stn_map_ilog_for(int64_t n) {
    uint32_t ilog = 4;
    while (stn_map_room(ilog) < n) ilog++;
    return ilog;
}

StnMap* stn_map_with_capacity(const StnMapOps* ops, int64_t n) {
    StnMap* m = stn_map_new(ops);
    if (n > 0) {
        if (n > STN_MAX_ALLOC) stn_too_large("<runtime>", 0, 0);
        stn_map_rebuild(m, stn_map_ilog_for(n));
    }
    return m;
}

void stn_map_release(void* p) {
    StnMap* m = (StnMap*)p;
    const StnMapOps* ops = m->ops;
    if (ops->kdrop || ops->vdrop)
        for (int64_t i = 0; i < m->used; i++) {
            char* e = m->entries + (size_t)i * m->stride;
            if (stn_map_dead(m, i, e)) continue;
            if (ops->kdrop) ops->kdrop(e + m->koff);
            if (ops->vdrop) ops->vdrop(e + m->voff);
        }
    free(m->index); free(m->entries); free(m->dead);
    stn_free(m);
}

/* A write needs the box unshared (section 4.5): the copy keeps the order and shares nothing. */
static void stn_map_copy_for_write(StnMap** pm) {
    StnMap* m = *pm;
    const StnMapOps* ops = m->ops;
    StnMap* c = stn_map_new(ops);
    if (m->ilog) {
        size_t ibytes = stn_index_bytes(m->ilog, stn_place_width(m->cap)), ebytes = (size_t)m->cap * m->stride;
        c->index = (uint8_t*)malloc(ibytes);
        c->entries = (char*)malloc(ebytes);
        if (!c->index || !c->entries) stn_map_oom();
        memcpy(c->index, m->index, ibytes);
        c->places = c->index + ((size_t)1 << m->ilog) + STN_GROUP;
        memcpy(c->entries, m->entries, (size_t)m->used * m->stride);
        c->ilog = m->ilog; c->cap = m->cap; c->used = m->used; c->len = m->len;
        if (m->dead) {
            size_t dbytes = (size_t)((m->cap + 63) / 64) * 8;
            c->dead = (uint64_t*)malloc(dbytes);
            if (!c->dead) stn_map_oom();
            memcpy(c->dead, m->dead, dbytes);
        }
        if (ops->kdup || ops->vdup)
            for (int64_t i = 0; i < c->used; i++) {
                char* e = c->entries + (size_t)i * c->stride;
                if (stn_map_dead(c, i, e)) continue;
                if (ops->kdup) ops->kdup(e + c->koff);
                if (ops->vdup) ops->vdup(e + c->voff);
            }
    }
    stn_drop(m, stn_map_release);
    *pm = c;
}
static inline void stn_map_make_unique(StnMap** pm) {
    if (__builtin_expect(!stn_unique(*pm), 0)) stn_map_copy_for_write(pm);
}
void stn_map_make_unique_for_write(StnMap** pm) { stn_map_make_unique(pm); }

/* The entry of the key, or NULL. When it is there and slot is given, *slot is the slot of the
   index that names it. */
static inline char* stn_map_lookup(const StnMap* m, const void* key, uint64_t w, uint64_t* slot) {
    if (__builtin_expect(!m->ilog, 0)) return NULL;
    const StnMapOps* ops = m->ops;
    const uint8_t* ctrl = m->index;
    unsigned width = stn_place_width(m->cap);
    uint64_t mask = ((uint64_t)1 << m->ilog) - 1, pos = (w >> 7) & mask, step = 0;
    uint8_t tag = (uint8_t)(w & 0x7F);
    for (;;) {
        const uint8_t* g = ctrl + pos;
        for (unsigned hits = stn_group_match(g, tag); hits; hits &= hits - 1) {
            uint64_t s = (pos + (unsigned)__builtin_ctz(hits)) & mask;
            char* e = m->entries + (size_t)stn_place_get(m->places, width, s) * m->stride;
            if ((!m->koff || *(const uint64_t*)e == w) && stn_key_eq(ops, e + m->koff, key)) { if (slot) *slot = s; return e; }
        }
        /* a free slot in the group ends the path: the key would have been put there or before */
#if defined(__SSE2__)
        if (_mm_movemask_epi8(_mm_cmpeq_epi8(_mm_loadu_si128((const __m128i_u*)g), _mm_set1_epi8((char)STN_FREE)))) return NULL;
#else
        if (stn_group_match(g, STN_FREE)) return NULL;
#endif
        step += STN_GROUP;
        pos = (pos + step) & mask;
    }
}

void* stn_map_find(const StnMap* m, const void* key) {
    char* e = stn_map_lookup(m, key, stn_key_word(m->ops, key), NULL);
    return e ? e + m->voff : NULL;
}

/* Appends an entry for a key that is known to be absent, and returns it. */
static inline char* stn_map_append(StnMap* m, uint64_t w, const void* key) {
    if (__builtin_expect(m->used == m->cap, 0)) {
        if (m->len >= STN_MAX_ALLOC) stn_too_large("<runtime>", 0, 0);
        /* mostly tombstones: the same index, emptied of them; otherwise twice the index */
        uint32_t ilog = !m->ilog ? 4 : (m->len * 2 <= m->cap ? m->ilog : m->ilog + 1);
        stn_map_rebuild(m, ilog);
    }
    uint64_t mask = ((uint64_t)1 << m->ilog) - 1;
    uint64_t s = stn_map_free_slot(m->index, mask, w);
    char* e = m->entries + (size_t)m->used * m->stride;
    if (m->koff) *(uint64_t*)e = w;
    if (m->ops->ksize == 8) memcpy(e + m->koff, key, 8); else memcpy(e + m->koff, key, m->ops->ksize);
    stn_ctrl_set(m->index, mask, s, (uint8_t)(w & 0x7F));
    stn_place_set(m->places, stn_place_width(m->cap), s, (uint64_t)m->used++);
    m->len++;
    return e;
}

void* stn_map_slot(StnMap** pm, const void* key, int* fresh) {
    stn_map_make_unique(pm);
    StnMap* m = *pm;
    const StnMapOps* ops = m->ops;
    uint64_t w = stn_key_word(ops, key);
    char* e = stn_map_lookup(m, key, w, NULL);
    if (e) {
        /* the key that is there stays; the one given is let go */
        if (ops->kdrop) ops->kdrop((void*)key);
        *fresh = 0;
        return e + m->voff;
    }
    *fresh = 1;
    return stn_map_append(m, w, key) + m->voff;
}

void* stn_map_slot_ref(StnMap** pm, const void* key, int* fresh) {
    stn_map_make_unique(pm);
    StnMap* m = *pm;
    const StnMapOps* ops = m->ops;
    uint64_t w = stn_key_word(ops, key);
    char* e = stn_map_lookup(m, key, w, NULL);
    if (e) { *fresh = 0; return e + m->voff; }
    *fresh = 1;
    e = stn_map_append(m, w, key);
    if (ops->kdup) ops->kdup(e + m->koff);
    return e + m->voff;
}

void stn_map_put(StnMap** pm, const void* key, const void* value) {
    int fresh;
    void* v = stn_map_slot(pm, key, &fresh);
    const StnMapOps* ops = (*pm)->ops;
    if (!ops->vsize) return;
    if (!fresh && ops->vdrop) ops->vdrop(v);
    if (ops->vsize == 8) memcpy(v, value, 8); else memcpy(v, value, ops->vsize);
}

int stn_map_remove(StnMap** pm, const void* key, void* out) {
    StnMap* m = *pm;
    const StnMapOps* ops = m->ops;
    uint64_t w = stn_key_word(ops, key), s = 0;
    char* e = stn_map_lookup(m, key, w, &s);
    if (!e) return 0;
    if (!stn_unique(m)) {
        stn_map_copy_for_write(pm);
        m = *pm;
        e = stn_map_lookup(m, key, w, &s);
    }
    if (ops->kdrop) ops->kdrop(e + m->koff);
    if (out) { if (ops->vsize) memcpy(out, e + m->voff, ops->vsize); }
    else if (ops->vdrop) ops->vdrop(e + m->voff);
    uint64_t mask = ((uint64_t)1 << m->ilog) - 1;
    if (m->koff) *(uint64_t*)e = 0;
    else {
        if (!m->dead) {
            m->dead = (uint64_t*)calloc((size_t)((m->cap + 63) / 64), 8);
            if (!m->dead) stn_map_oom();
        }
        int64_t i = (e - m->entries) / m->stride;
        m->dead[i >> 6] |= (uint64_t)1 << (i & 63);
    }
    m->len--;
    if (m->len == 0) {
        memset(m->index, STN_FREE, (size_t)mask + 1 + STN_GROUP);
        m->used = 0;
        free(m->dead); m->dead = NULL;
    } else {
        /* the slot stays taken for the paths that pass it, until the index is made anew. Tombstones
           are closed up when the table next runs out of room, which costs nothing extra since it
           rebuilds then anyway, or here when they are three quarters of the entries, so that a
           table that shrinks gives its memory back and a walk over it stays short. */
        stn_ctrl_set(m->index, mask, s, STN_DEAD);
        if ((m->used - m->len) * 4 > m->used * 3 && m->used >= 16) {
            uint32_t ilog = stn_map_ilog_for(m->len);
            stn_map_rebuild(m, ilog > m->ilog ? m->ilog : ilog);
        }
    }
    return 1;
}

void stn_map_clear(StnMap** pm) {
    StnMap* m = *pm;
    if (m->len == 0 && m->used == 0) return;
    StnMap* fresh = stn_map_new(m->ops);
    stn_drop(m, stn_map_release);
    *pm = fresh;
}

/* Equal as collections: the same keys, with equal values, in whatever order each was built. */
int stn_map_eq(const StnMap* a, const StnMap* b) {
    /* a table is not taken to equal itself: a NaN key or value is unequal to itself, and the
       answer must not depend on whether two Maps share storage */
    if (a->len != b->len) return 0;
    const StnMapOps* ops = a->ops;
    int64_t pos = 0;
    for (const char* e; (e = stn_map_next(a, &pos)); ) {
        const char* f = stn_map_lookup(b, e + a->koff, stn_entry_word(a, e), NULL);
        if (!f) return 0;
        if (ops->vsize && !ops->veq(e + a->voff, f + b->voff)) return 0;
    }
    return 1;
}

/* Adds the key of an entry of another set, which brings its hash with it. r is not shared. */
static inline void stn_set_take(StnMap* r, const char* e) {
    const StnMapOps* ops = r->ops;
    uint64_t w = stn_entry_word(r, e);
    if (stn_map_lookup(r, e + r->koff, w, NULL)) return;
    char* n = stn_map_append(r, w, e + r->koff);
    if (ops->kdup) ops->kdup(n + r->koff);
}

StnMap* stn_set_union(const StnMap* a, const StnMap* b) {
    StnMap* r = stn_map_with_capacity(a->ops, a->len > b->len ? a->len : b->len);
    int64_t pos = 0;
    for (const char* e; (e = stn_map_next(a, &pos)); ) stn_set_take(r, e);
    pos = 0;
    for (const char* e; (e = stn_map_next(b, &pos)); ) stn_set_take(r, e);
    return r;
}

StnMap* stn_set_intersection(const StnMap* a, const StnMap* b) {
    StnMap* r = stn_map_new(a->ops);
    int64_t pos = 0;
    for (const char* e; (e = stn_map_next(a, &pos)); )
        if (stn_map_lookup(b, e + a->koff, stn_entry_word(a, e), NULL)) stn_set_take(r, e);
    return r;
}

StnMap* stn_set_difference(const StnMap* a, const StnMap* b) {
    StnMap* r = stn_map_new(a->ops);
    int64_t pos = 0;
    for (const char* e; (e = stn_map_next(a, &pos)); )
        if (!stn_map_lookup(b, e + a->koff, stn_entry_word(a, e), NULL)) stn_set_take(r, e);
    return r;
}

/* ---- string built-ins ---- */
StnArray* stn_str_chars(const StnStr* s, const StnElemOps* ops) {
    int64_t n;
    const unsigned char* p = (const unsigned char*)stn_str_span(s, &n);
    StnArray* a = stn_array_new(ops, n > 0 ? n : 1);
    int64_t i = 0;
    while (i < n) {
        uint32_t c = p[i];
        int len = 1;
#if defined(__SSE2__)
        /* a run of ASCII widens sixteen bytes at a time; the block is all inside the string, and
           the array has room for one Char per byte */
        if (c < 0x80 && i + 16 <= n) {
            const __m128i block = _mm_loadu_si128((const __m128i_u*)(p + i));
            if (_mm_movemask_epi8(block) == 0) {
                const __m128i zero = _mm_setzero_si128();
                const __m128i lo = _mm_unpacklo_epi8(block, zero), hi = _mm_unpackhi_epi8(block, zero);
                uint32_t* out = (uint32_t*)a->data + a->len;
                _mm_storeu_si128((__m128i_u*)(out), _mm_unpacklo_epi16(lo, zero));
                _mm_storeu_si128((__m128i_u*)(out + 4), _mm_unpackhi_epi16(lo, zero));
                _mm_storeu_si128((__m128i_u*)(out + 8), _mm_unpacklo_epi16(hi, zero));
                _mm_storeu_si128((__m128i_u*)(out + 12), _mm_unpackhi_epi16(hi, zero));
                a->len += 16;
                i += 16;
                continue;
            }
        }
#endif
        /* strings are valid UTF-8; the bound keeps a decode inside the buffer regardless */
        if ((c >= 0xF0 && i + 4 > n) || (c >= 0xE0 && i + 3 > n) || (c >= 0xC0 && i + 2 > n)) c = 0xFFFD, len = 0;
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

StnArray* stn_str_split(const StnStr* s, const StnStr* sep, const StnElemOps* ops, const char* file, int line, int col) {
    int64_t sep_len, s_len;
    const char* sep_data = stn_str_span(sep, &sep_len);
    if (sep_len == 0) stn_trap("invalid argument", file, line, col, "split with an empty separator");
    StnArray* a = stn_array_new(ops, 4);
    const char* field = stn_str_span(s, &s_len);
    const char* end = field + s_len;
    const char* hit;
    while ((hit = stn_find_bytes(field, (size_t)(end - field), sep_data, (size_t)sep_len))) {
        StnStr part = stn_str_new(field, (int64_t)(hit - field));
        STN_PUSH(&a, StnStr, part);
        field = hit + sep_len;
    }
    StnStr last = stn_str_new(field, (int64_t)(end - field));
    STN_PUSH(&a, StnStr, last);
    return a;
}

StnStr stn_str_join_parts(const StnStr* parts, int64_t n, StnStr sep) {
    /* The total is kept in 64 bits and checked once per part against a limit that is both the
       largest allocation and what a size_t of this target can hold beside the buffer's header, so
       it cannot wrap and the narrowing below loses nothing. */
    int64_t sep_n;
    const char* sep_data = stn_str_span(&sep, &sep_n);
    size_t sep_len = (size_t)sep_n;
    uint64_t limit = (uint64_t)STN_MAX_ALLOC, room = (uint64_t)SIZE_MAX - sizeof(StnStrBuf) - 1;
    if (limit > room) limit = room;
    uint64_t sum = 0;
    for (int64_t i = 0; i < n; i++) {
        /* each term is the length of a string that exists, so the two cannot wrap 64 bits */
        uint64_t k = (uint64_t)stn_str_len(parts[i]) + (i ? (uint64_t)sep_n : 0);
        if (k > limit - sum) stn_too_large("<runtime>", 0, 0);
        sum += k;
    }
    size_t total = (size_t)sum;
    StnStr s;
    char* d = stn_str_start(&s, (int64_t)total);
    for (int64_t i = 0; i < n; i++) {
        if (i) {
            memcpy(d, sep_data, sep_len);
            d += sep_len;
        }
        int64_t k;
        const char* pd = stn_str_span(&parts[i], &k);
        memcpy(d, pd, (size_t)k);
        d += k;
    }
    return s;
}

StnStr stn_str_join(StnArray* xs, StnStr sep) {
    return stn_str_join_parts((const StnStr*)xs->data, xs->len, sep);
}

static int stn_space(char c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c == '\v'; }

StnStr stn_str_trim(const StnStr* s) {
    int64_t n;
    const char* d = stn_str_span(s, &n);
    int64_t lo = 0, hi = n;
    while (lo < hi && stn_space(d[lo])) lo++;
    while (hi > lo && stn_space(d[hi - 1])) hi--;
    if (lo == 0 && hi == n) return stn_str_dup(*s);
    return stn_str_new(d + lo, hi - lo);
}

uint8_t stn_str_contains_slow(const StnStr* s, const StnStr* sub) {
    int64_t m, n;
    const char* sub_data = stn_str_span(sub, &m);
    const char* data = stn_str_span(s, &n);
    return m == 0 || stn_find_bytes(data, (size_t)n, sub_data, (size_t)m) != NULL;
}
StnStr stn_str_repeat(const StnStr* s, int64_t n, const char* file, int line, int col) {
    if (n < 0) stn_trap("invalid argument", file, line, col, "negative repeat count");
    int64_t k;
    const char* src = stn_str_span(s, &k);
    if (n > 0 && k > STN_MAX_ALLOC / n) stn_too_large(file, line, col);
    StnStr r;
    char* d = stn_str_start(&r, k * n);
    for (int64_t i = 0; i < n; i++) memcpy(d + i * k, src, (size_t)k);
    return r;
}

int stn_parse_int(const StnStr* s, int64_t* out) {
    int64_t i = 0, n;
    const char* text = stn_str_span(s, &n);
    if (n == 0) return 1;
    int neg = text[0] == '-';
    if (text[0] == '-' || text[0] == '+') i = 1;
    if (i == n) return 1;
    int64_t acc = 0;
    if (n - i <= 18) {
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
        /* eight digits at a time: one test says all eight bytes are digits, three multiplies
           combine them; at most eighteen digits in all, so nothing here can overflow */
        for (; n - i >= 8; i += 8) {
            uint64_t v;
            memcpy(&v, text + i, 8);
            if (((v & UINT64_C(0xF0F0F0F0F0F0F0F0)) |
                 (((v + UINT64_C(0x0606060606060606)) & UINT64_C(0xF0F0F0F0F0F0F0F0)) >> 4)) !=
                UINT64_C(0x3333333333333333)) return 1;
            v = ((v & UINT64_C(0x0F0F0F0F0F0F0F0F)) * 2561) >> 8;
            v = ((v & UINT64_C(0x00FF00FF00FF00FF)) * 6553601) >> 16;
            v = ((v & UINT64_C(0x0000FFFF0000FFFF)) * UINT64_C(42949672960001)) >> 32;
            acc = acc * 100000000 - (int64_t)v;
        }
#endif
        for (; n - i >= 4; i += 4) {
            unsigned a = (unsigned char)text[i] - (unsigned)'0';
            unsigned b = (unsigned char)text[i+1] - (unsigned)'0';
            unsigned c = (unsigned char)text[i+2] - (unsigned)'0';
            unsigned d = (unsigned char)text[i+3] - (unsigned)'0';
            if (a > 9 || b > 9 || c > 9 || d > 9) return 1;
            acc = acc * 10000 - (int64_t)(1000*a + 100*b + 10*c + d);
        }
        for (; i < n; i++) {
            unsigned digit = (unsigned char)text[i] - (unsigned)'0';
            if (digit > 9) return 1;
            acc = acc * 10 - digit;
        }
    } else {
        for (; i < n; i++) {
            unsigned digit = (unsigned char)text[i] - (unsigned)'0';
            if (digit > 9) return 1;
            if (acc < INT64_MIN / 10 || acc * 10 < INT64_MIN + digit) {
                /* Invalid syntax has priority over a range error. */
                for (i++; i < n; i++)
                    if (text[i] < '0' || text[i] > '9') return 1;
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
    int64_t first = i, digits;
    /* the digits before the point, then the digits after it: two plain loops */
    for (; i < n; i++) {
        unsigned d = (unsigned char)data[i] - (unsigned)'0';
        if (d > 9) break;
        mantissa = mantissa * 10 + d;
    }
    digits = i - first;
    if (i < n) {
        if (data[i] != '.') return 0;
        first = ++i;
        for (; i < n; i++) {
            unsigned d = (unsigned char)data[i] - (unsigned)'0';
            if (d > 9) return 0;
            mantissa = mantissa * 10 + d;
            divisor *= 10;
        }
        digits += i - first;
    }
    if (!digits) return 0;
    double signed_mantissa = data[0] == '-' ? -(double)mantissa : (double)mantissa;
    *out = signed_mantissa / (double)divisor;
    return 1;
}

int stn_parse_float(const StnStr* s, double* out) {
    int64_t n;
    const char* d = stn_str_span(s, &n);
    if (n == 0) return 1;
    if (stn_parse_short_float(d, n, out)) return 0;
    for (int64_t i = 0; i < n; i++) {
        char c = d[i];
        if (!((c >= '0' && c <= '9') || c == '.' || c == '-' || c == '+' || c == 'e' || c == 'E')) return 1;
    }
    /* strtod needs a terminator: a heap buffer has one, inline bytes are copied out */
    char text[STN_STR_INLINE_MAX + 1];
    if (!stn_str_heap(*s)) { memcpy(text, d, (size_t)n); text[n] = 0; d = text; }
    char* end;
    *out = strtod(d, &end);
    return end != d + n;
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
    stn_hash_init();
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
void stn_runtime_init(void) { stn_hash_init(); }
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

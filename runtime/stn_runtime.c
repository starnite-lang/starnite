/* SPDX-License-Identifier: Apache-2.0 */
/* The Starnite runtime (section 11). */
#define _POSIX_C_SOURCE 200809L
#include "stn_runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

int64_t stn_live_objects = 0;

/* ---- allocation (section 11.2) ---- */
/* Size classes step by 16 bytes up to 1 KiB, with a free list per class. Milestone 1 is
   single-threaded, so the lists are plain globals; milestone 6 makes them per thread. */
#define STN_CLASSES 64
typedef struct stn_free_node { struct stn_free_node* next; } stn_free_node;
static stn_free_node* stn_free_lists[STN_CLASSES + 1];

void* stn_alloc(size_t size) {
    size_t cls = (size + 15) / 16;
    stn_header* h;
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
    /* freed memory is poisoned; the header is marked so a later drop is caught */
    if (cls) memset(h, 0xDB, cls * 16); else memset(h, 0xDB, sizeof(stn_header));
    free(h);
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

int stn_str_eq(StnStr a, StnStr b) {
    return a == b || (a->len == b->len && memcmp(a->data, b->data, (size_t)a->len) == 0);
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

StnArray* stn_array_new(const StnElemOps* ops, int64_t cap) {
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
    if (stn_unique(a)) {
        if (need <= a->cap) return;
        int64_t cap = a->cap ? a->cap * 2 : 4;
        while (cap < need) cap *= 2;
        size_t bytes = sizeof(StnArray) + (size_t)cap * a->ops->size;
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

int stn_array_pop(StnArray** pa, void* out) {
    if ((*pa)->len == 0) return 0;
    stn_array_make_unique(pa);
    StnArray* a = *pa;
    a->len--;
    memcpy(out, a->data + (size_t)a->len * a->ops->size, a->ops->size);
    return 1;
}

void stn_array_clear(StnArray** pa) {
    StnArray* a = *pa;
    StnArray* b = stn_array_new(a->ops, 4);
    stn_drop(a, stn_array_release);
    *pa = b;
}

StnArray* stn_array_filled(const StnElemOps* ops, int64_t n, const void* elem, const char* file, int line, int col) {
    if (n < 0) stn_trap("index out of range", file, line, col, "negative length");
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

int stn_read_line(StnStr* out) {
    stn_flush();
    size_t cap = 128, n = 0;
    char* buf = (char*)malloc(cap);
    int c;
    while ((c = getchar()) != EOF && c != '\n') {
        if (n + 1 >= cap) { cap *= 2; buf = (char*)realloc(buf, cap); }
        buf[n++] = (char)c;
    }
    if (c == EOF && n == 0) { free(buf); return 0; }
    *out = stn_str_new(buf, (int64_t)n);
    free(buf);
    return 1;
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
        if (c >= 0xF0) { c = ((c & 7) << 18) | ((p[i+1] & 0x3F) << 12) | ((p[i+2] & 0x3F) << 6) | (p[i+3] & 0x3F); len = 4; }
        else if (c >= 0xE0) { c = ((c & 15) << 12) | ((p[i+1] & 0x3F) << 6) | (p[i+2] & 0x3F); len = 3; }
        else if (c >= 0xC0) { c = ((c & 31) << 6) | (p[i+1] & 0x3F); len = 2; }
        ((uint32_t*)a->data)[a->len++] = c;
        i += len;
    }
    return a;
}

StnArray* stn_str_split(StnStr s, StnStr sep, const StnElemOps* ops, const char* file, int line, int col) {
    if (sep->len == 0) stn_trap("invalid argument", file, line, col, "split with an empty separator");
    StnArray* a = stn_array_new(ops, 4);
    int64_t st = 0, i = 0;
    while (i <= s->len - sep->len) {
        if (memcmp(s->data + i, sep->data, (size_t)sep->len) == 0) {
            StnStr part = stn_str_new(s->data + st, i - st);
            stn_array_push(&a, &part);
            i += sep->len; st = i;
        } else i++;
    }
    StnStr last = stn_str_new(s->data + st, s->len - st);
    stn_array_push(&a, &last);
    return a;
}

StnStr stn_str_join(StnArray* xs, StnStr sep) {
    int64_t total = 0;
    StnStr* parts = (StnStr*)xs->data;
    for (int64_t i = 0; i < xs->len; i++) total += parts[i]->len + (i ? sep->len : 0);
    StnStr s = (StnStr)stn_alloc(sizeof(StnStrBuf) + (size_t)total + 1);
    s->len = total;
    int64_t at = 0;
    for (int64_t i = 0; i < xs->len; i++) {
        if (i) { memcpy(s->data + at, sep->data, (size_t)sep->len); at += sep->len; }
        memcpy(s->data + at, parts[i]->data, (size_t)parts[i]->len); at += parts[i]->len;
    }
    s->data[total] = 0;
    return s;
}

static int stn_space(char c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c == '\v'; }

StnStr stn_str_trim(StnStr s) {
    int64_t lo = 0, hi = s->len;
    while (lo < hi && stn_space(s->data[lo])) lo++;
    while (hi > lo && stn_space(s->data[hi - 1])) hi--;
    return stn_str_new(s->data + lo, hi - lo);
}

uint8_t stn_str_contains(StnStr s, StnStr sub) {
    if (sub->len == 0) return 1;
    for (int64_t i = 0; i + sub->len <= s->len; i++)
        if (memcmp(s->data + i, sub->data, (size_t)sub->len) == 0) return 1;
    return 0;
}
uint8_t stn_str_starts_with(StnStr s, StnStr p) {
    return p->len <= s->len && memcmp(s->data, p->data, (size_t)p->len) == 0;
}
uint8_t stn_str_ends_with(StnStr s, StnStr p) {
    return p->len <= s->len && memcmp(s->data + s->len - p->len, p->data, (size_t)p->len) == 0;
}
StnStr stn_str_repeat(StnStr s, int64_t n, const char* file, int line, int col) {
    if (n < 0) stn_trap("invalid argument", file, line, col, "negative repeat count");
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
    for (int64_t j = i; j < n; j++) if (s->data[j] < '0' || s->data[j] > '9') return 1;
    int64_t acc = 0;   /* accumulated negatively, to reach INT64_MIN */
    for (; i < n; i++) {
        int d = s->data[i] - '0';
        if (acc < INT64_MIN / 10 || acc * 10 < INT64_MIN + d) return 2;
        acc = acc * 10 - d;
    }
    if (!neg) { if (acc == INT64_MIN) return 2; acc = -acc; }
    *out = acc;
    return 0;
}

int stn_parse_float(StnStr s, double* out) {
    if (s->len == 0) return 1;
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
void stn_runtime_init(void) {}

void stn_runtime_exit(int status) {
    stn_flush();
#ifdef STN_DEBUG
    if (status == 0 && stn_live_objects != 0 && getenv("STN_ALLOW_LEAKS") == NULL) {
        fprintf(stderr, "debug runtime: %lld object(s) still live at exit; counts do not balance\n",
                (long long)stn_live_objects);
        exit(3);
    }
#endif
    exit(status);
}

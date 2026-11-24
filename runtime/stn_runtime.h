/* SPDX-License-Identifier: Apache-2.0 */
/* The Starnite runtime (section 11). Programs compiled with Starnite link it. */
#ifndef STN_RUNTIME_H
#define STN_RUNTIME_H

#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdatomic.h>
#if defined(__SSE2__)
#include <emmintrin.h>
#endif

/* ---- object header (section 11.1) ---- */
typedef struct stn_header {
    uint32_t rc;          /* reference count */
    uint16_t tag;         /* variant index; 0 for other objects */
    uint8_t  flags;       /* STN_NOCOUNT | STN_ATOMIC */
    uint8_t  size_class;  /* allocator class, for reuse and free */
} stn_header;

#define STN_NOCOUNT 1
#define STN_ATOMIC  2

typedef uint8_t StnUnit;

void* stn_alloc(size_t size);
void  stn_free(void* p);

static inline void stn_dup(void* p) {
    if ((uintptr_t)p & 1) return;                 /* field-less variant */
    stn_header* h = (stn_header*)p;
    if (h->flags == 0) {
        if (__builtin_expect(++h->rc == UINT32_MAX, 0)) h->flags |= STN_NOCOUNT;
        return;
    }
    if (h->flags & STN_NOCOUNT) return;
    atomic_fetch_add_explicit((_Atomic uint32_t*)&h->rc, 1, memory_order_relaxed);
}

void stn_check_header(void* p);

static inline void stn_drop(void* p, void (*release)(void*)) {
    if ((uintptr_t)p & 1) return;
    stn_header* h = (stn_header*)p;
#ifdef STN_DEBUG
    stn_check_header(p);
#endif
    if (h->flags == 0) { if (--h->rc == 0) release(p); return; }
    if (h->flags & STN_NOCOUNT) return;
    if (atomic_fetch_sub_explicit((_Atomic uint32_t*)&h->rc, 1, memory_order_acq_rel) == 1)
        release(p);
}

static inline int stn_unique(void* p) {
    return ((stn_header*)p)->flags == 0 && ((stn_header*)p)->rc == 1;
}

/* ---- traps (section 11.5) ---- */
typedef struct { const char* file; int32_t line, col; } StnLoc;
_Noreturn void stn_trap(const char* kind, const char* file, int line, int col, const char* msg);
_Noreturn void stn_overflow(const char* file, int line, int col);
_Noreturn void stn_div_zero(const char* file, int line, int col);

/* ---- strings (section 3.6) ---- */
/* Milestone 1 stores every string in a counted buffer; the 15-byte inline form arrives
   with the layout work of milestone 2. */
typedef struct StnStrBuf { stn_header h; int64_t len; char data[]; } StnStrBuf;
typedef StnStrBuf* StnStr;

void   stn_str_release(void* p);
StnStr stn_str_new(const char* data, int64_t len);
StnStr stn_str_from_bytes(const char* data, int64_t len);   /* makes the bytes valid UTF-8 */
StnStr stn_str_concat(StnStr a, StnStr b);
StnStr stn_str_concat_n(int n, StnStr* parts);   /* borrows parts */
/* Fixed-size comparisons may start at unaligned byte offsets. */
static inline uint16_t stn_load_u16(const char* p) {
    uint16_t value;
    memcpy(&value, p, sizeof value);
    return value;
}

static inline uint32_t stn_load_u32(const char* p) {
    uint32_t value;
    memcpy(&value, p, sizeof value);
    return value;
}

static inline uint64_t stn_load_u64(const char* p) {
    uint64_t value;
    memcpy(&value, p, sizeof value);
    return value;
}

static inline __attribute__((always_inline)) int stn_str_eq(StnStr a, StnStr b) {
    if (a == b) return 1;
    if (a->len != b->len) return 0;
    size_t n = (size_t)a->len;
#if defined(__SSE2__)
    if (n >= 16 && n <= 48) {
        __m128i first = _mm_cmpeq_epi8(
            _mm_loadu_si128((const __m128i_u*)a->data),
            _mm_loadu_si128((const __m128i_u*)b->data));
        if ((unsigned)_mm_movemask_epi8(first) != 0xffffu) return 0;
        __m128i last = _mm_cmpeq_epi8(
            _mm_loadu_si128((const __m128i_u*)(a->data + n - 16)),
            _mm_loadu_si128((const __m128i_u*)(b->data + n - 16)));
        if (n > 32) {
            __m128i middle = _mm_cmpeq_epi8(
                _mm_loadu_si128((const __m128i_u*)(a->data + 16)),
                _mm_loadu_si128((const __m128i_u*)(b->data + 16)));
            last = _mm_and_si128(last, middle);
        }
        return (unsigned)_mm_movemask_epi8(last) == 0xffffu;
    }
#endif
    return memcmp(a->data, b->data, n) == 0;
}
int    stn_str_cmp(StnStr a, StnStr b);
StnStr stn_str_slice(StnStr s, int64_t lo, int64_t hi, const char* file, int line, int col);
static inline int64_t stn_str_byte_at_or_end(StnStr s, int64_t i) {
    return (uint64_t)i < (uint64_t)s->len ? (unsigned char)s->data[i] : -1;
}
#define STN_STR_DUP(s) (stn_dup(s), (s))
#define STN_STR_DROP(s) stn_drop((s), stn_str_release)

StnStr stn_show_i64(int64_t v);
StnStr stn_show_u64(uint64_t v);
StnStr stn_show_f64(double v);
StnStr stn_show_f32(float v);
StnStr stn_show_bool(uint8_t v);
StnStr stn_show_char(uint32_t c);
StnStr stn_show_unit(void);
StnStr stn_show_dur(int64_t v);
StnStr stn_show_bytes(int64_t v);

/* ---- arrays (section 3.1) ---- */
typedef struct StnElemOps {
    size_t size;
    void (*dup)(void* elem);     /* NULL for Copy kind */
    void (*drop)(void* elem);
} StnElemOps;

typedef struct StnArray {
    stn_header h;
    int64_t len, cap;
    const StnElemOps* ops;
    _Alignas(16) char data[];
} StnArray;

void      stn_array_release(void* p);
StnArray* stn_array_new(const StnElemOps* ops, int64_t cap);
void      stn_array_copy_for_write(StnArray** a);
/* A write needs the box unshared (section 4.5). */
static inline void stn_array_make_unique(StnArray** a) {
    if (__builtin_expect(!stn_unique(*a), 0)) stn_array_copy_for_write(a);
}
void      stn_array_push_slow(StnArray** a, const void* elem);
/* A push with the element type known, so the store is a typed assignment rather
   than a memcpy of a size read at run time. Evaluates v once. */
#define STN_PUSH(pa, T, v) do {                                                       \
        StnArray* stn_pa_ = *(pa);                                                    \
        if (__builtin_expect(stn_unique(stn_pa_) && stn_pa_->len < stn_pa_->cap, 1)) \
            ((T*)stn_pa_->data)[stn_pa_->len++] = (v);                                \
        else { T stn_pv_ = (v); stn_array_push_slow((pa), &stn_pv_); }               \
    } while (0)

/* Used only while the compiler's loop guard proves exclusive ownership. */
#define STN_PUSH_UNIQUE(pa, T, v) do {                                            \
        StnArray** stn_slot_ = (pa);                                              \
        StnArray* stn_array_ = *stn_slot_;                                        \
        if (__builtin_expect(stn_array_->len < stn_array_->cap, 1))                \
            ((T*)stn_array_->data)[stn_array_->len++] = (v);                        \
        else { T stn_value_ = (v); stn_array_push_slow(stn_slot_, &stn_value_); }   \
    } while (0)

/* takes the element; constant time on average, since capacity doubles */
static inline void stn_array_push(StnArray** pa, const void* elem) {
    StnArray* a = *pa;
    if (__builtin_expect(stn_unique(a) && a->len < a->cap, 1)) {
        memcpy(a->data + (size_t)a->len * a->ops->size, elem, a->ops->size);
        a->len++;
    } else stn_array_push_slow(pa, elem);
}
void      stn_array_reserve(StnArray** a, int64_t extra);
void      stn_array_reserve_hint(StnArray** a, uint64_t extra);
StnArray* stn_array_slice(StnArray* a, int64_t lo, int64_t hi, const char* file, int line, int col);
void      stn_array_extend(StnArray** a, StnArray* b);
void      stn_array_insert(StnArray** a, int64_t i, const void* elem, const char* file, int line, int col);
void      stn_array_remove(StnArray** a, int64_t i, void* out, const char* file, int line, int col);
#define STN_POP(pa, T, out, ok) do {                           \
        StnArray** stn_slot_ = (pa);                           \
        (ok) = (*stn_slot_)->len != 0;                        \
        if (ok) {                                            \
            stn_array_make_unique(stn_slot_);                \
            StnArray* stn_pop_ = *stn_slot_;                   \
            (out) = ((T*)stn_pop_->data)[--stn_pop_->len];     \
        }                                                    \
    } while (0)
void      stn_array_clear(StnArray** a);
void      stn_array_sort_i64(StnArray** a);
void      stn_array_reverse_i64(StnArray** a);
int       stn_array_contains_i64(const StnArray* a, int64_t value);
int64_t   stn_array_count_true(const StnArray* a);
int64_t   stn_array_sum_popped_i64(StnArray* a, int64_t count, int64_t sum,
                                  const char* file, int line, int col);
int64_t   stn_array_sum_i64(const StnArray* a, int64_t initial, const char* file, int line, int col);
StnArray* stn_array_filled_i64(const StnElemOps* ops, int64_t n, int64_t value, const char* file, int line, int col);
StnArray* stn_array_filled(const StnElemOps* ops, int64_t n, const void* elem, const char* file, int line, int col);

_Noreturn void stn_index_trap(int64_t i, int64_t len, const char* file, int line, int col);
/* No array holds more than STN_MAX_ALLOC elements: every path that creates or grows one
   traps beyond it (stn_array_new, stn_array_reserve, stn_array_filled). Saying so
   when a length is read lets the C compiler bound loop counters and index arithmetic
   derived from it, and drop the overflow and sign checks it can then prove redundant. */
#define STN_MAX_ALLOC ((int64_t)1 << 40)
static inline int64_t stn_len(const StnArray* a) {
    int64_t n = a->len;
    if (n < 0 || n > STN_MAX_ALLOC) __builtin_unreachable();
    return n;
}

static inline int64_t stn_index(int64_t i, int64_t len, const char* file, int line, int col) {
    if (__builtin_expect((uint64_t)i >= (uint64_t)len, 0)) stn_index_trap(i, len, file, line, col);
    return i;
}

/* ---- closures (section 13) ---- */
typedef struct StnClosure {
    stn_header h;
    void* code;                           /* first parameter is the closure itself */
    void (*release)(void* self);          /* releases the captures and the object */
} StnClosure;

static inline void stn_closure_drop(StnClosure* c) { stn_drop(c, c->release); }

/* ---- trait values (section 3.4) ---- */
/* The counted box behind `any Trait`: the value follows the header, and [release] drops
   it and frees the box. The method table travels beside the box, in the value. */
typedef struct StnAnyBox {
    stn_header h;
    void (*release)(void* self);
    _Alignas(16) char data[];
} StnAnyBox;
static inline void stn_any_drop(StnAnyBox* b) { stn_drop(b, b->release); }

/* ---- errors (section 5.4) ---- */
typedef struct StnErrBox { stn_header h; void (*release)(void* self); } StnErrBox;
typedef struct StnError { uint32_t type_id; StnErrBox* box; } StnError;
static inline void stn_error_drop(StnError e) { if (e.box) stn_drop(e.box, e.box->release); }
static inline StnError stn_error_dup(StnError e) { if (e.box) stn_dup(e.box); return e; }

/* ---- console and the rest of the built-ins ---- */
void    stn_print(StnStr s);
int     stn_read_line(StnStr* out);
StnStr  stn_read_all(const char* file, int line, int col);
int64_t stn_clock_ns(void);
StnArray* stn_str_chars(StnStr s, const StnElemOps* char_ops);
StnArray* stn_str_split(StnStr s, StnStr sep, const StnElemOps* str_ops, const char* file, int line, int col);
StnStr  stn_str_join_parts(const StnStr* parts, int64_t n, StnStr sep);
StnStr  stn_str_join(StnArray* xs, StnStr sep);
StnStr  stn_str_trim(StnStr s);
uint8_t stn_str_contains_slow(StnStr s, StnStr sub);
static inline uint8_t stn_str_contains(StnStr s, StnStr sub) {
#if defined(__SSE2__)
    /* A four-byte needle can be verified without a memcmp call. Scan a
       final overlapping vector so both loads stay inside the string. */
    if (sub->len == 4 && s->len >= 19 && s->len <= 64) {
        uint32_t needle;
        memcpy(&needle, sub->data, sizeof needle);
        __m128i first = _mm_set1_epi8(sub->data[0]);
        __m128i last = _mm_set1_epi8(sub->data[3]);
        size_t limit = (size_t)s->len - 19;
        size_t i = 0;
        for (;;) {
            const char* start = s->data + i;
            __m128i lo = _mm_loadu_si128((const __m128i_u*)start);
            __m128i hi = _mm_loadu_si128((const __m128i_u*)(start + 3));
            unsigned mask = (unsigned)_mm_movemask_epi8(
                _mm_and_si128(_mm_cmpeq_epi8(lo, first), _mm_cmpeq_epi8(hi, last)));
            while (mask != 0) {
                unsigned offset = (unsigned)__builtin_ctz(mask);
                uint32_t candidate;
                memcpy(&candidate, start + offset, sizeof candidate);
                if (candidate == needle) return 1;
                mask &= mask - 1;
            }
            if (i == limit) return 0;
            i = i + 16 < limit ? i + 16 : limit;
        }
    }
#endif
    return stn_str_contains_slow(s, sub);
}
static inline uint8_t stn_str_starts_with(StnStr s, StnStr p) {
    return p->len <= s->len && memcmp(s->data, p->data, (size_t)p->len) == 0;
}
static inline uint8_t stn_str_ends_with(StnStr s, StnStr p) {
    return p->len <= s->len && memcmp(s->data + (s->len - p->len), p->data, (size_t)p->len) == 0;
}
StnStr  stn_str_repeat(StnStr s, int64_t n, const char* file, int line, int col);
int     stn_parse_int(StnStr s, int64_t* out);   /* 0 ok, 1 invalid, 2 out of range */
int     stn_parse_float(StnStr s, double* out);  /* 0 ok, 1 invalid */
void    stn_check_char(int64_t c, const char* file, int line, int col);

/* ---- maps and sets (section 3.6) ---- */
/* One table serves both: a set is a map whose values take no room. Entries sit in a dense array in
   insertion order; a sparse index of control bytes and of 1-, 2-, 4- or 8-byte places finds them
   by hash. */
typedef struct StnMapOps {
    size_t ksize, vsize;                     /* vsize 0 for a set */
    uint64_t (*hash)(const void* key);
    int (*eq)(const void* a, const void* b); /* keys */
    void (*kdup)(void* key);                 /* NULL for Copy kind */
    void (*kdrop)(void* key);
    void (*vdup)(void* value);
    void (*vdrop)(void* value);
    int (*veq)(const void* a, const void* b);/* values, for ==; NULL when V has no Eq */
    int kind;                                /* STN_KEY_I64 or STN_KEY_STR where the key is one, else 0 */
} StnMapOps;
#define STN_KEY_I64 1
#define STN_KEY_STR 2

typedef struct StnMap {
    stn_header h;
    int64_t len;          /* live entries */
    int64_t used;         /* entries written, tombstones included */
    int64_t cap;          /* entries there is room for */
    uint32_t ilog;        /* the index has 1 << ilog slots; 0 while nothing is allocated */
    uint32_t stride;      /* bytes per entry: 8 of hash word, the key, the value */
    uint32_t voff;        /* offset of the value in an entry */
    const StnMapOps* ops;
    uint8_t* index;       /* the control bytes of the slots, then the places they name */
    uint8_t* places;
    char* entries;
} StnMap;

void     stn_map_release(void* p);
StnMap*  stn_map_new(const StnMapOps* ops);
StnMap*  stn_map_with_capacity(const StnMapOps* ops, int64_t n);
/* the value of the key (for a set, any address that is not NULL), or NULL */
void*    stn_map_find(const StnMap* m, const void* key);
/* takes the key and the value; an equal key keeps its place and its own key, and gets the new value */
void     stn_map_put(StnMap** pm, const void* key, const void* value);
/* the value of the key, which is put if it is missing: *fresh says so, and the value is then the
   caller's to write. Takes the key as put does. */
void*    stn_map_slot(StnMap** pm, const void* key, int* fresh);
/* takes the key out; its value moves to out when out is not NULL, and is dropped otherwise */
int      stn_map_remove(StnMap** pm, const void* key, void* out);
void     stn_map_clear(StnMap** pm);
/* entries in insertion order: start with *pos = 0; NULL at the end. The key is at entry + 8. */
static inline char* stn_map_next(const StnMap* m, int64_t* pos) {
    while (*pos < m->used) {
        char* e = m->entries + (size_t)(*pos)++ * m->stride;
        if (*(const uint64_t*)e) return e;
    }
    return NULL;
}
int      stn_map_eq(const StnMap* a, const StnMap* b);
StnMap*  stn_set_union(const StnMap* a, const StnMap* b);
StnMap*  stn_set_intersection(const StnMap* a, const StnMap* b);
StnMap*  stn_set_difference(const StnMap* a, const StnMap* b);
/* SipHash-1-3 under a key drawn once per process */
extern uint64_t stn_hash_k0, stn_hash_k1;
#define STN_ROTL(x, b) (((x) << (b)) | ((x) >> (64 - (b))))
#define STN_SIPROUND do { \
        v0 += v1; v1 = STN_ROTL(v1, 13); v1 ^= v0; v0 = STN_ROTL(v0, 32); \
        v2 += v3; v3 = STN_ROTL(v3, 16); v3 ^= v2; \
        v0 += v3; v3 = STN_ROTL(v3, 21); v3 ^= v0; \
        v2 += v1; v1 = STN_ROTL(v1, 17); v1 ^= v2; v2 = STN_ROTL(v2, 32); } while (0)
/* SipHash-1-3 of one 64-bit word: inline, since an integer key is hashed on every lookup */
static inline uint64_t stn_hash_u64(uint64_t x) {
    uint64_t v0 = stn_hash_k0 ^ UINT64_C(0x736f6d6570736575), v1 = stn_hash_k1 ^ UINT64_C(0x646f72616e646f6d);
    uint64_t v2 = stn_hash_k0 ^ UINT64_C(0x6c7967656e657261), v3 = stn_hash_k1 ^ UINT64_C(0x7465646279746573);
    v3 ^= x; STN_SIPROUND; v0 ^= x;
    const uint64_t b = (uint64_t)8 << 56;
    v3 ^= b; STN_SIPROUND; v0 ^= b;
    v2 ^= 0xff; STN_SIPROUND; STN_SIPROUND; STN_SIPROUND;
    return v0 ^ v1 ^ v2 ^ v3;
}
uint64_t stn_hash_bytes(const void* p, size_t n);
/* equal floats hash alike: -0.0 is 0.0 */
static inline uint64_t stn_hash_f64(double x) { uint64_t b; if (x == 0) x = 0; memcpy(&b, &x, 8); return stn_hash_u64(b); }
static inline uint64_t stn_hash_combine(uint64_t h, uint64_t x) { return stn_hash_u64(h ^ (x + UINT64_C(0x9E3779B97F4A7C15) + (h << 6) + (h >> 2))); }

/* stn_map_find for a table whose keys are 64-bit integers (STN_KEY_I64), inline: the layout of
   the index is the one stn_runtime.c describes. */
static inline void* stn_map_find_i64(const StnMap* m, uint64_t key) {
    if (__builtin_expect(!m->ilog, 0)) return NULL;
    uint64_t h = stn_hash_u64(key);
    uint64_t w = h | (uint64_t)(h == 0);
    uint64_t mask = ((uint64_t)1 << m->ilog) - 1, pos = (w >> 7) & mask, step = 0;
    int64_t cap = m->cap;
    unsigned width = cap <= 256 ? 1 : cap <= 65536 ? 2 : cap <= INT64_C(4294967296) ? 4 : 8;
    const uint8_t* ctrl = m->index;
    for (;;) {
        const uint8_t* g = ctrl + pos;
        unsigned hits, unused_free;
#if defined(__SSE2__)
        __m128i grp = _mm_loadu_si128((const __m128i_u*)g);
        hits = (unsigned)_mm_movemask_epi8(_mm_cmpeq_epi8(grp, _mm_set1_epi8((char)(w & 0x7F))));
        unused_free = (unsigned)_mm_movemask_epi8(_mm_cmpeq_epi8(grp, _mm_set1_epi8((char)0xFF)));
#else
        hits = 0; unused_free = 0;
        for (unsigned i = 0; i < 16; i++) { hits |= (unsigned)(g[i] == (uint8_t)(w & 0x7F)) << i; unused_free |= (unsigned)(g[i] == 0xFF) << i; }
#endif
        for (; hits; hits &= hits - 1) {
            uint64_t s = (pos + (unsigned)__builtin_ctz(hits)) & mask;
            uint64_t place;
            switch (width) {
                case 1: place = m->places[s]; break;
                case 2: { uint16_t v; memcpy(&v, m->places + s * 2, 2); place = v; break; }
                case 4: { uint32_t v; memcpy(&v, m->places + s * 4, 4); place = v; break; }
                default: memcpy(&place, m->places + s * 8, 8);
            }
            char* e = m->entries + (size_t)place * m->stride;
            uint64_t k;
            memcpy(&k, e + 8, 8);
            if (*(const uint64_t*)e == w && k == key) return e + m->voff;
        }
        if (unused_free) return NULL;
        step += 16;
        pos = (pos + step) & mask;
    }
}

/* Generated functions are compiled for speed wherever they end up being inlined. Only an optimized
   release build asks for it: Clang honours the attribute even at -O0, which makes a debug build
   several times slower to compile. */
#if (defined(__GNUC__) || defined(__clang__)) && defined(__OPTIMIZE__) && !defined(STN_DEBUG)
#  define STN_HOT __attribute__((hot))
#else
#  define STN_HOT
#endif

/* ---- integer arithmetic that traps (section 17.1) ---- */
#define STN_ARITH(T, N)                                                                      \
    static inline T stn_add_##N(T a, T b, const char* f, int l, int c) {                     \
        T r; if (__builtin_expect(__builtin_add_overflow(a, b, &r), 0)) stn_overflow(f, l, c); return r; } \
    static inline T stn_sub_##N(T a, T b, const char* f, int l, int c) {                     \
        T r; if (__builtin_expect(__builtin_sub_overflow(a, b, &r), 0)) stn_overflow(f, l, c); return r; } \
    static inline T stn_mul_##N(T a, T b, const char* f, int l, int c) {                     \
        T r; if (__builtin_expect(__builtin_mul_overflow(a, b, &r), 0)) stn_overflow(f, l, c); return r; }
STN_ARITH(int64_t, i64)
STN_ARITH(int32_t, i32)
STN_ARITH(int16_t, i16)
STN_ARITH(int8_t, i8)
STN_ARITH(uint64_t, u64)
STN_ARITH(uint32_t, u32)
STN_ARITH(uint16_t, u16)
STN_ARITH(uint8_t, u8)

#define STN_DIV_S(T, N, MIN)                                                                 \
    static inline T stn_div_##N(T a, T b, const char* f, int l, int c) {                     \
        if (__builtin_expect(b == 0, 0)) { stn_div_zero(f, l, c); }                          \
        if (__builtin_expect(b == -1 && a == MIN, 0)) { stn_overflow(f, l, c); } return a / b; } \
    static inline T stn_rem_##N(T a, T b, const char* f, int l, int c) {                     \
        if (__builtin_expect(b == 0, 0)) { stn_div_zero(f, l, c); }                          \
        return b == -1 ? 0 : a % b; }
#define STN_DIV_U(T, N)                                                                      \
    static inline T stn_div_##N(T a, T b, const char* f, int l, int c) {                     \
        if (__builtin_expect(b == 0, 0)) { stn_div_zero(f, l, c); } return a / b; }              \
    static inline T stn_rem_##N(T a, T b, const char* f, int l, int c) {                     \
        if (__builtin_expect(b == 0, 0)) { stn_div_zero(f, l, c); } return a % b; }
STN_DIV_S(int64_t, i64, INT64_MIN)
STN_DIV_S(int32_t, i32, INT32_MIN)
STN_DIV_S(int16_t, i16, INT16_MIN)
STN_DIV_S(int8_t, i8, INT8_MIN)
STN_DIV_U(uint64_t, u64)
STN_DIV_U(uint32_t, u32)
STN_DIV_U(uint16_t, u16)
STN_DIV_U(uint8_t, u8)

/* conversions that trap when the value does not fit */
_Noreturn void stn_conv_trap(const char* to, const char* file, int line, int col);

/* ---- start-up and debug accounting (section 11.6) ---- */
void stn_runtime_init(void);
void stn_runtime_exit(int status);
void stn_runtime_flush_for_error(void);
extern int64_t stn_live_objects;

#endif

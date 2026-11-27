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

/* ---- heap block header (section 11.1) ---- */
/* A heap block, in full a heap allocation block, is one piece of counted memory that backs a
   value: the buffer of an array or of a long string, the table of a map or set, one cell of a
   boxed data type, a closure. The language has only values; these are how the runtime stores
   them, and no program sees one. */
typedef struct stn_header {
    uint32_t rc;          /* reference count */
    uint16_t tag;         /* variant index; 0 for other heap blocks */
    uint8_t  flags;       /* STN_NOCOUNT | STN_ATOMIC */
    uint8_t  size_class;  /* allocator class, for reuse and free */
} stn_header;

#define STN_NOCOUNT 1
#define STN_ATOMIC  2

typedef uint8_t StnUnit;

void* stn_alloc(size_t size);
void  stn_free(void* p);

/* ---- counters of bench blocks (section 20.3) ---- */
/* What a `measure` block did, in numbers that are the same on every machine: allocations and
   their bytes, copies of shared values (section 9.8), and counts raised or lowered. Compiled in
   only for the counting build of a bench (STN_COUNTERS); otherwise these are nothing. */
#ifdef STN_COUNTERS
extern uint64_t stn_count_allocs, stn_count_bytes, stn_count_copies, stn_count_ops;
#define STN_COUNT_OP() ((void)(stn_count_ops++))
#define STN_COUNT_COPY() ((void)(stn_count_copies++))
#else
#define STN_COUNT_OP() ((void)0)
#define STN_COUNT_COPY() ((void)0)
#endif

/* ---- counters of --profile-copies (section 9.8) ---- */
/* Generated code names the statement it is in before anything that can copy or raise a count;
   the runtime reports what then happens there. Compiled in only for a profiled build. */
#ifdef STN_PROFILE_COPIES
enum { STN_PROFILE_ARRAY, STN_PROFILE_MAP, STN_PROFILE_VIEW, STN_PROFILE_DUP };
void stn_profile_at(const char* file, int line);
void stn_profile_event(int kind);
#endif

static inline void stn_dup(void* p) {
    if ((uintptr_t)p & 1) return;                 /* field-less variant */
    STN_COUNT_OP();
    stn_header* h = (stn_header*)p;
#ifdef STN_PROFILE_COPIES
    /* only where a count does change: not for a field-less variant, nor a value never counted */
    if (!(h->flags & STN_NOCOUNT)) stn_profile_event(STN_PROFILE_DUP);
#endif
    if (h->flags == 0) {
        if (__builtin_expect(++h->rc == UINT32_MAX, 0)) h->flags |= STN_NOCOUNT;
        return;
    }
    if (h->flags & STN_NOCOUNT) return;
    atomic_fetch_add_explicit((_Atomic uint32_t*)&h->rc, 1, memory_order_relaxed);
}

void stn_check_header(void* p);
#ifdef STN_DEBUG
#  define STN_CHECK_HEADER(p) stn_check_header(p)
#else
#  define STN_CHECK_HEADER(p) ((void)0)
#endif

/* ---- releasing large structures (section 9.7) ---- */
/* A release function that drops what its heap block holds can start other releases. Each such
   function goes in through stn_release_enter, which lets them nest only STN_RELEASE_DEPTH deep:
   past that, and once STN_FREE_BUDGET heap blocks have been released in one go, the heap block is put on
   a list instead, and released when the nesting has unwound, or at a later allocation when it was
   the budget that stopped it. The stack a release needs is therefore bounded whatever the shape
   of the structure. A release that drops nothing, a string's or an array of numbers', does not
   take part and costs what it did. */
#define STN_RELEASE_DEPTH 256
extern int32_t stn_release_depth;      /* releases now running, one inside another */
extern int64_t stn_release_left;       /* heap blocks that may still be released before a pause */
extern int64_t stn_release_budget;     /* STN_FREE_BUDGET, or INT64_MAX without one */
extern size_t  stn_release_pending;    /* heap blocks on the list */
void stn_release_defer(void* p, void (*release)(void*));
void stn_release_drain(int fresh);

/* at the start of release, for p: 1 when p was put on the list instead, and release must return */
static inline int stn_release_enter(void* p, void (*release)(void*)) {
    if (__builtin_expect(stn_release_depth >= STN_RELEASE_DEPTH || --stn_release_left < 0, 0)) {
        stn_release_defer(p, release);
        return 1;
    }
    stn_release_depth++;
    return 0;
}
/* at the end of a release that went in */
static inline void stn_release_leave(void) {
    if (--stn_release_depth == 0) {
        /* what nesting put off is released now; what the budget put off waits for an allocation */
        if (__builtin_expect(stn_release_pending != 0, 0)) stn_release_drain(0);
        else stn_release_left = stn_release_budget;
    }
}

static inline void stn_drop(void* p, void (*release)(void*)) {
    if ((uintptr_t)p & 1) return;
    STN_COUNT_OP();
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
/* Where the compiler knows a value has no other holder it leaves out the test (section 6.2). A
   debug build, or one with STN_CHECK_UNIQUE, makes the test all the same, and stops if it fails: that is a fault
   of the compiler, not of the program. */
#if defined(STN_CHECK_UNIQUE) || defined(STN_DEBUG)
#define STN_ASSUME_UNIQUE(p) stn_assume_unique((void*)(p), __FILE__, __LINE__)
#else
#define STN_ASSUME_UNIQUE(p) ((void)0)
#endif
typedef struct { const char* file; int32_t line, col; } StnLoc;
_Noreturn void stn_trap(const char* kind, const char* file, int line, int col, const char* msg);
static inline void stn_assume_unique(void* p, const char* file, int line) {
    if (((uintptr_t)p & 1) || stn_unique(p)) return;
    stn_trap("compiler fault", file, line, 0, "a value the compiler took to have no other holder is shared");
}
_Noreturn void stn_overflow(const char* file, int line, int col);
_Noreturn void stn_div_zero(const char* file, int line, int col);

/* ---- strings (section 3.6) ---- */
/* A Str is 16 bytes. A string of up to 15 bytes is stored inline: its bytes, zero padding, and its
   length in the last byte. A longer one points to a counted buffer and holds its length, with the
   top bit of the second word set. The form follows from the length alone, so two equal strings
   have the same form, and two inline strings are equal exactly when their words are. */
/* len is how many bytes data has room for, before its terminator: at least the length of the
   string, which the Str itself holds, and more after an append has grown the buffer. */
typedef struct StnStrBuf { stn_header h; int64_t len; char data[]; } StnStrBuf;
/* The first word of a string in a buffer is the address of its bytes: of the data of a buffer it
   counts, or, for a view, of bytes inside another string. Only a string that counts its buffer
   has one to find, with stn_str_buf. */
/* The length of an inline string, and the bits that mark the other forms, are in the top byte of
   w1, and the inline bytes are the other fifteen bytes of the value, in order. On a little-endian
   target that byte is the last of the value, so w0 comes first and the bytes start at the value's
   address. On a big-endian one it is the first byte of w1, so w1 comes first and the bytes start
   one byte in. */
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
typedef struct StnStr { union { const char* ptr; uint64_t w0; }; uint64_t w1; } StnStr;
#  define STN_STR_INLINE_AT 0
#  define STN_STR_SHORT(le_w0, le_w1, be_w1, be_w0) ((StnStr){ .w0 = (le_w0), .w1 = (le_w1) })
/* Paths that read or build an inline string as two little-endian words. STN_STR_PORTABLE turns
   them off, leaving the byte-wise paths every other target uses, so that those can be tested here. */
#  ifndef STN_STR_PORTABLE
#    define STN_STR_WORDS 1
#  endif
#elif defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
typedef struct StnStr { uint64_t w1; union { const char* ptr; uint64_t w0; }; } StnStr;
#  define STN_STR_INLINE_AT 1
#  define STN_STR_SHORT(le_w0, le_w1, be_w1, be_w0) ((StnStr){ .w1 = (be_w1), .w0 = (be_w0) })
#else
#  error "the Str layout needs to know the byte order of the target"
#endif
#define STN_STR_INLINE_MAX 15
_Static_assert(sizeof(StnStr) == 16, "a Str is sixteen bytes");
_Static_assert(offsetof(StnStr, w1) == (STN_STR_INLINE_AT ? 0 : 8), "the byte that holds an inline length is at the far end from the inline bytes");
#define STN_STR_HEAP_BIT (UINT64_C(1) << 63)
/* A view: a string in a buffer it does not count, the bytes of a string that outlives it (a slice
   of a binding that cannot change, section 3.6). Its ptr is its first byte, wherever in the other
   string that is. Dropping a view does nothing, and duplicating one copies its
   bytes into a buffer of its own, so a view that is stored or returned stops being one. */
#define STN_STR_VIEW_BIT (UINT64_C(1) << 62)
#define STN_STR_LEN_MASK (~(STN_STR_HEAP_BIT | STN_STR_VIEW_BIT))

static inline __attribute__((always_inline)) int stn_str_heap(StnStr s) { return (int)(s.w1 >> 63); }
/* The buffer of a string that counts one: not of an inline string, and not of a view. */
static inline __attribute__((always_inline)) StnStrBuf* stn_str_buf(StnStr s) {
    return (StnStrBuf*)(void*)((char*)(uintptr_t)s.ptr - offsetof(StnStrBuf, data));
}
static inline __attribute__((always_inline)) int64_t stn_str_len(StnStr s) {
    return stn_str_heap(s) ? (int64_t)(s.w1 & STN_STR_LEN_MASK) : (int64_t)(s.w1 >> 56);
}
/* The bytes of a string; for an inline one they live in the value itself, so the pointer is good
   only while *s is. */
static inline __attribute__((always_inline)) const char* stn_str_ptr(const StnStr* s) {
    return stn_str_heap(*s) ? s->ptr : (const char*)s + STN_STR_INLINE_AT;
}
/* The bytes and the length of a string together, its form checked once. */
static inline __attribute__((always_inline)) const char* stn_str_span(const StnStr* s, int64_t* n) {
    uint64_t w1 = s->w1;
    if (w1 >> 63) { *n = (int64_t)(w1 & STN_STR_LEN_MASK); return s->ptr; }
    *n = (int64_t)(w1 >> 56);
    return (const char*)s + STN_STR_INLINE_AT;
}
void   stn_str_release(void* p);
StnStr stn_str_new_heap(const char* data, int64_t len);
static inline __attribute__((always_inline)) StnStr stn_str_dup(StnStr s) {
    if (stn_str_heap(s)) {
        if (__builtin_expect((s.w1 & STN_STR_VIEW_BIT) != 0, 0)) {
#ifdef STN_PROFILE_COPIES
            stn_profile_event(STN_PROFILE_VIEW);
#endif
            STN_COUNT_COPY();
            return stn_str_new_heap(s.ptr, (int64_t)(s.w1 & STN_STR_LEN_MASK));
        }
        stn_dup(stn_str_buf(s));
    }
    return s;
}
/* s as a view of itself, for a binding that will not outlive it */
static inline __attribute__((always_inline)) StnStr stn_str_as_view(StnStr s) {
    s.w1 |= (s.w1 >> 1) & STN_STR_VIEW_BIT;   /* the view bit, where the buffer bit is set */
    return s;
}
static inline __attribute__((always_inline)) void stn_str_drop(StnStr s) {
    if ((s.w1 >> 62) != 2) return;   /* inline, or a view */
#ifndef STN_DEBUG
    /* the common case, an unshared buffer counted by one thread, without a call */
    stn_header* h = (stn_header*)stn_str_buf(s);
    if (__builtin_expect(h->flags == 0, 1)) { STN_COUNT_OP(); if (--h->rc == 0) stn_str_release(h); return; }
#endif
    stn_drop(stn_str_buf(s), stn_str_release);
}
#define STN_MAX_ALLOC ((int64_t)1 << 40)
/* The most bytes a string may have where a size_t holds up to size_max: the largest allocation,
   or what a size_t can count beside the buffer's header and terminator, whichever is less. Sizes
   are worked out in 64 bits against this before they are narrowed to a size_t; the functions take
   the bound as an argument so that a narrow target's arithmetic can be checked on a wide one
   (tests/str_limits.c). */
static inline uint64_t stn_str_limit_for(uint64_t size_max) {
    uint64_t room = size_max - sizeof(StnStrBuf) - 1;
    return (uint64_t)STN_MAX_ALLOC < room ? (uint64_t)STN_MAX_ALLOC : room;
}
#define STN_STR_LIMIT stn_str_limit_for((uint64_t)SIZE_MAX)
/* The capacity for a buffer of capacity cap that must hold need bytes: half as much again as it
   has, so that a run of appends copies each byte a bounded number of times, but never less than
   need nor more than limit. 0 when need itself is over the limit. */
static inline uint64_t stn_str_grown(uint64_t cap, uint64_t need, uint64_t limit) {
    if (need > limit) return 0;
    if (cap > limit) cap = limit;
    uint64_t room = cap + cap / 2;
    if (room > limit) room = limit;
    return room < need ? need : room;
}
/* Starts a string of len bytes in *s and returns where its bytes go. The caller writes all len. */
char*  stn_str_start(StnStr* s, int64_t len);
/* An inline string of len <= 15 bytes, assembled in registers by loads that stay inside the
   source: writing the bytes to memory and reading the words back would stall the processor. */
static inline __attribute__((always_inline)) StnStr stn_str_small(const char* d, int64_t len) {
    StnStr s;
#ifndef STN_STR_WORDS
    s.w0 = 0;
    s.w1 = (uint64_t)len << 56;
    if (len) memcpy((char*)&s + STN_STR_INLINE_AT, d, (size_t)len);
    return s;
#else
    uint64_t w0 = 0, w1 = 0;
    if (len >= 8) {
        memcpy(&w0, d, 8);
        if (len > 8) { memcpy(&w1, d + len - 8, 8); w1 >>= 8 * (16 - len); }
    } else if (len >= 4) {
        uint32_t lo, hi;
        memcpy(&lo, d, 4);
        memcpy(&hi, d + len - 4, 4);
        w0 = (uint64_t)lo | ((uint64_t)hi << (8 * (len - 4)));
    } else if (len >= 2) {
        uint16_t lo;
        memcpy(&lo, d, 2);
        w0 = (uint64_t)lo | ((uint64_t)(unsigned char)d[len - 1] << (8 * (len - 1)));
    } else if (len == 1) w0 = (unsigned char)d[0];
    s.w0 = w0;
    s.w1 = w1 | ((uint64_t)len << 56);
    return s;
#endif
}
static inline StnStr stn_str_new(const char* data, int64_t len) {
    return len <= STN_STR_INLINE_MAX ? stn_str_small(data, len) : stn_str_new_heap(data, len);
}
_Noreturn void stn_trap_str(const char* kind, const char* file, int line, int col, StnStr msg);
StnStr stn_str_from_bytes(const char* data, int64_t len);   /* makes the bytes valid UTF-8 */
StnStr stn_str_concat(const StnStr* a, const StnStr* b);
/* a + b for an a that the caller owns and gives up: appended in place when nothing else holds
   its buffer (section 9.3), which makes growing a string by assignment linear */
StnStr stn_str_append(StnStr a, const StnStr* b);
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
    if (a.w0 == b.w0 && a.w1 == b.w1) return 1;           /* the same inline bytes, or the same buffer */
    if (((a.w1 ^ b.w1) & ~STN_STR_VIEW_BIT) || !stn_str_heap(a)) return 0;   /* lengths differ, or inline and unequal */
    size_t n = (size_t)(a.w1 & STN_STR_LEN_MASK);
    const char* ad = a.ptr;
    const char* bd = b.ptr;
#if defined(__SSE2__)
    if (n <= 48) {
        __m128i first = _mm_cmpeq_epi8(
            _mm_loadu_si128((const __m128i_u*)ad),
            _mm_loadu_si128((const __m128i_u*)bd));
        if ((unsigned)_mm_movemask_epi8(first) != 0xffffu) return 0;
        __m128i last = _mm_cmpeq_epi8(
            _mm_loadu_si128((const __m128i_u*)(ad + n - 16)),
            _mm_loadu_si128((const __m128i_u*)(bd + n - 16)));
        if (n > 32) {
            __m128i middle = _mm_cmpeq_epi8(
                _mm_loadu_si128((const __m128i_u*)(ad + 16)),
                _mm_loadu_si128((const __m128i_u*)(bd + 16)));
            last = _mm_and_si128(last, middle);
        }
        return (unsigned)_mm_movemask_epi8(last) == 0xffffu;
    }
#endif
    return memcmp(ad, bd, n) == 0;
}
int    stn_str_cmp(const StnStr* a, const StnStr* b);
_Noreturn void stn_slice_trap(int64_t n, int64_t lo, int64_t hi, const char* file, int line, int col);
/* s[lo..hi] for a string that outlives the result: no bytes are copied when it is long. Inline, so
   that a view which is stored at once costs the one call that copies it. */
static inline __attribute__((always_inline)) StnStr stn_str_view(const StnStr* s, int64_t lo, int64_t hi, const char* file, int line, int col) {
    int64_t n;
    const char* d = stn_str_span(s, &n);
    /* in range, and on character boundaries: neither end is a continuation byte */
    if (__builtin_expect(lo < 0 || hi > n || lo > hi
                         || (lo != 0 && lo != n && ((unsigned char)d[lo] & 0xC0) == 0x80)
                         || (hi != 0 && hi != n && ((unsigned char)d[hi] & 0xC0) == 0x80), 0))
        stn_slice_trap(n, lo, hi, file, line, col);
    if (hi - lo <= STN_STR_INLINE_MAX) return stn_str_small(d + lo, hi - lo);
    StnStr v;
    v.ptr = d + lo;
    v.w1 = (uint64_t)(hi - lo) | STN_STR_HEAP_BIT | STN_STR_VIEW_BIT;
    return v;
}
void   stn_str_slice_self(StnStr* s, int64_t lo, int64_t hi, const char* file, int line, int col);
StnStr stn_str_slice(const StnStr* s, int64_t lo, int64_t hi, const char* file, int line, int col);
static inline int64_t stn_str_byte_at_or_end(const StnStr* s, int64_t i) {
    return (uint64_t)i < (uint64_t)stn_str_len(*s) ? (unsigned char)stn_str_ptr(s)[i] : -1;
}
#define STN_STR_DUP(s) stn_str_dup(s)
#define STN_STR_DROP(s) stn_str_drop(s)

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
/* a new array with the same elements, each counted once more */
StnArray* stn_array_clone(StnArray* a);
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
    void (*release)(void* self);          /* releases the captures and the heap block */
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
void    stn_print(const StnStr* s);
int     stn_read_line(StnStr* out);
StnStr  stn_read_all(const char* file, int line, int col);
int64_t stn_clock_ns(void);
/* A `measure` block (section 20.3) is `stn_bench_begin(...)` and then `while (stn_bench_running())`.
   stn_bench_begin is given the bench and its budgets ("allocs<= copies==", their limits in a to
   d), and starts the counters or the clock. stn_bench_running says whether the block should run:
   in the counting build it runs once, and the counters are then printed and held to the budgets;
   otherwise it runs for STN_BENCH_MS milliseconds and the time is printed. */
void stn_bench_begin(const StnStr* name, const StnStr* label, int64_t n, const StnStr* spec,
                     int64_t a, int64_t b, int64_t c, int64_t d);
uint8_t stn_bench_running(void);
/* after a bench has run: one whose measure block was never reached has kept no budget, and fails */
void stn_bench_end(const StnStr* name);
StnArray* stn_str_chars(const StnStr* s, const StnElemOps* char_ops);
StnArray* stn_str_split(const StnStr* s, const StnStr* sep, const StnElemOps* str_ops, const char* file, int line, int col);
StnStr  stn_str_join_parts(const StnStr* parts, int64_t n, StnStr sep);
StnStr  stn_str_join(StnArray* xs, StnStr sep);
StnStr  stn_str_trim(const StnStr* s);
uint8_t stn_str_contains_slow(const StnStr* s, const StnStr* sub);
/* the offset of the first sub in s at or after from; -1 for none, or for a from outside s */
int64_t stn_str_find(const StnStr* s, const StnStr* sub, int64_t from);
static inline uint8_t stn_str_contains(const StnStr* s, const StnStr* sub) {
#if defined(__SSE2__) && defined(STN_STR_WORDS)
    /* A four-byte needle can be verified without a memcmp call. Scan a final overlapping vector
       so both loads stay inside the string. The lengths settle the forms: the needle is inline,
       its bytes in its first word, and the string is in a buffer, so each is one comparison. */
    if (sub->w1 == (UINT64_C(4) << 56) && (s->w1 & ~STN_STR_VIEW_BIT) >= (STN_STR_HEAP_BIT | 19) && (s->w1 & ~STN_STR_VIEW_BIT) <= (STN_STR_HEAP_BIT | 64)) {
        uint32_t needle = (uint32_t)sub->w0;
        const char* s_data = s->ptr;
        __m128i first = _mm_set1_epi8((char)(needle & 0xFF));
        __m128i last = _mm_set1_epi8((char)(needle >> 24));
        size_t limit = (size_t)(s->w1 & STN_STR_LEN_MASK) - 19;
        size_t i = 0;
        for (;;) {
            const char* start = s_data + i;
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
#ifdef STN_STR_WORDS
/* The first eight bytes of a string as a little-endian word, zero past its end; a string in a
   buffer has at least sixteen. Read from the words of an inline string, not through its address. */
static inline __attribute__((always_inline)) uint64_t stn_str_head8(const StnStr* s) {
    return stn_str_heap(*s) ? stn_load_u64(s->ptr) : s->w0;
}
/* The last eight bytes of a string of at least one byte, its last byte in the top position; the
   bytes before a shorter string are zero. */
static inline __attribute__((always_inline)) uint64_t stn_str_tail8(const StnStr* s) {
    if (stn_str_heap(*s)) return stn_load_u64(s->ptr + (s->w1 & STN_STR_LEN_MASK) - 8);
    uint64_t n = s->w1 >> 56, hi = s->w1 & ~(UINT64_C(0xFF) << 56);
    if (n > 8) return (s->w0 >> (8 * (n - 8))) | (hi << (8 * (16 - n)));
    return n == 8 ? s->w0 : s->w0 << (8 * (8 - n));
}
/* s starts or ends with the n bytes (1 to 8) of a literal, given as a word: a string in a buffer
   has at least sixteen bytes, so only an inline one needs its length checked. */
static inline __attribute__((always_inline)) uint8_t stn_str_starts8(const StnStr* s, unsigned n, uint64_t mask, uint64_t lit) {
    if (stn_str_heap(*s)) return (stn_load_u64(s->ptr) & mask) == lit;
    return (s->w1 >> 56) >= n && (s->w0 & mask) == lit;
}
static inline __attribute__((always_inline)) uint8_t stn_str_ends8(const StnStr* s, unsigned n, uint64_t lit) {
    if (stn_str_heap(*s))
        return (stn_load_u64(s->ptr + (s->w1 & STN_STR_LEN_MASK) - 8) >> (64 - 8 * n)) == lit;
    return (s->w1 >> 56) >= n && (stn_str_tail8(s) >> (64 - 8 * n)) == lit;
}
#else
/* The same two tests a byte at a time: the literal's bytes are in its word from the low end up. */
static inline uint8_t stn_str_lit_at(const char* d, unsigned n, uint64_t lit) {
    for (unsigned i = 0; i < n; i++)
        if ((unsigned char)d[i] != (unsigned char)(lit >> (8 * i))) return 0;
    return 1;
}
static inline uint8_t stn_str_starts8(const StnStr* s, unsigned n, uint64_t mask, uint64_t lit) {
    (void)mask;
    int64_t len;
    const char* d = stn_str_span(s, &len);
    return (uint64_t)len >= n && stn_str_lit_at(d, n, lit);
}
static inline uint8_t stn_str_ends8(const StnStr* s, unsigned n, uint64_t lit) {
    int64_t len;
    const char* d = stn_str_span(s, &len);
    return (uint64_t)len >= n && stn_str_lit_at(d + len - n, n, lit);
}
#endif
static inline uint8_t stn_str_starts_with(const StnStr* s, const StnStr* p) {
    int64_t n = stn_str_len(*p);
    return n <= stn_str_len(*s) && memcmp(stn_str_ptr(s), stn_str_ptr(p), (size_t)n) == 0;
}
static inline uint8_t stn_str_ends_with(const StnStr* s, const StnStr* p) {
    int64_t n = stn_str_len(*p), m = stn_str_len(*s);
    return n <= m && memcmp(stn_str_ptr(s) + (m - n), stn_str_ptr(p), (size_t)n) == 0;
}
StnStr  stn_str_repeat(const StnStr* s, int64_t n, const char* file, int line, int col);
int     stn_parse_int(const StnStr* s, int64_t* out);   /* 0 ok, 1 invalid, 2 out of range */
int     stn_parse_float(const StnStr* s, double* out);  /* 0 ok, 1 invalid */
void    stn_check_char(int64_t c, const char* file, int line, int col);
/* The character that starts at byte *i of the n bytes at p, with *i moved past it: what
   stn_str_chars puts in its array, one at a time, for a loop that needs no array. */
static inline uint32_t stn_str_next_char(const unsigned char* p, int64_t n, int64_t* i) {
    int64_t at = *i;
    uint32_t c = p[at];
    if (__builtin_expect(c < 0x80, 1)) { *i = at + 1; return c; }
    /* strings are valid UTF-8; the bound keeps a decode inside the buffer regardless */
    if ((c >= 0xF0 && at + 4 > n) || (c >= 0xE0 && at + 3 > n) || (c >= 0xC0 && at + 2 > n)) { *i = at + 1; return 0xFFFD; }
    if (c >= 0xF0) { *i = at + 4; return ((c & 7) << 18) | ((uint32_t)(p[at+1] & 0x3F) << 12) | ((uint32_t)(p[at+2] & 0x3F) << 6) | (p[at+3] & 0x3F); }
    if (c >= 0xE0) { *i = at + 3; return ((c & 15) << 12) | ((uint32_t)(p[at+1] & 0x3F) << 6) | (p[at+2] & 0x3F); }
    if (c >= 0xC0) { *i = at + 2; return ((c & 31) << 6) | (p[at+1] & 0x3F); }
    *i = at + 1;
    return c;
}

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

/* a table of this many entries or fewer has no index and hashes nothing: see stn_runtime.c */
#define STN_MAP_SMALL 8

typedef struct StnMap {
    stn_header h;
    int64_t len;          /* live entries */
    int64_t used;         /* entries written, tombstones included */
    int64_t cap;          /* entries there is room for */
    uint32_t ilog;        /* the index has 1 << ilog slots; 0 while nothing is allocated */
    uint32_t stride;      /* bytes per entry: 8 of hash word, the key, the value */
    uint32_t koff;        /* offset of the key in an entry: 8 after the hash word, or 0 for 64-bit integer keys,
                             whose hash is worked out again when it is needed */
    uint32_t voff;        /* offset of the value in an entry */
    const StnMapOps* ops;
    uint8_t* index;       /* the control bytes of the slots, then the places they name */
    uint8_t* places;
    char* entries;
    uint64_t* dead;       /* with no hash word: a bit for each removed entry, or NULL when there is none */
    int64_t eroom;        /* entries the buffer has room for now: it grows to cap by doubling, so a small map stays small */
} StnMap;

void     stn_map_release(void* p);
/* a write to an entry in place needs the table unshared (section 4.5) */
void     stn_map_make_unique_for_write(StnMap** pm);
/* a new table with the same entries, each key and value counted once more */
StnMap*  stn_map_clone(StnMap* m);
StnMap*  stn_map_new(const StnMapOps* ops);
StnMap*  stn_map_with_capacity(const StnMapOps* ops, int64_t n);
/* the value of the key (for a set, any address that is not NULL), or NULL */
void*    stn_map_find(const StnMap* m, const void* key);
/* takes the key and the value; an equal key keeps its place and its own key, and gets the new value */
void     stn_map_put(StnMap** pm, const void* key, const void* value);
/* the value of the key, which is put if it is missing: *fresh says so, and the value is then the
   caller's to write. Takes the key as put does. */
void*    stn_map_slot(StnMap** pm, const void* key, int* fresh);
/* the same with the key borrowed: a copy of it is counted and kept only when it is put */
void*    stn_map_slot_ref(StnMap** pm, const void* key, int* fresh);
/* takes the key out; its value moves to out when out is not NULL, and is dropped otherwise */
int      stn_map_remove(StnMap** pm, const void* key, void* out);
void     stn_map_clear(StnMap** pm);
/* whether the entry at place i has been removed */
static inline int stn_map_dead(const StnMap* m, int64_t i, const char* e) {
    if (m->koff) return *(const uint64_t*)e == 0;
    return m->dead && ((m->dead[i >> 6] >> (i & 63)) & 1);
}
/* entries in insertion order: start with *pos = 0; NULL at the end. The key is at entry + koff. */
static inline char* stn_map_next(const StnMap* m, int64_t* pos) {
    while (*pos < m->used) {
        int64_t i = (*pos)++;
        char* e = m->entries + (size_t)i * m->stride;
        if (!stn_map_dead(m, i, e)) return e;
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
/* SipHash of the bytes of an inline string, taken from its words: the bytes past its length are
   zero and its last byte is its length, which are what the last block of SipHash holds */
uint64_t stn_hash_inline(uint64_t w0, uint64_t w1);
static inline uint64_t stn_str_hash(StnStr s) {
#ifdef STN_STR_WORDS
    return stn_str_heap(s) ? stn_hash_bytes(s.ptr, (size_t)(s.w1 & STN_STR_LEN_MASK)) : stn_hash_inline(s.w0, s.w1);
#else
    int64_t n;
    const char* d = stn_str_span(&s, &n);
    return stn_hash_bytes(d, (size_t)n);
#endif
}
/* equal floats hash alike: -0.0 is 0.0 */
static inline uint64_t stn_hash_f64(double x) { uint64_t b; if (x == 0) x = 0; memcpy(&b, &x, 8); return stn_hash_u64(b); }
/* SipHash-1-3 over a stream of 64-bit words, for keys made of several parts (a tuple, a struct,
   a data type, an array): one hash for the whole key, as if its parts were laid out in a row */
typedef struct { uint64_t v0, v1, v2, v3, n; } StnSip;
static inline void stn_sip_init(StnSip* s) {
    s->v0 = stn_hash_k0 ^ UINT64_C(0x736f6d6570736575); s->v1 = stn_hash_k1 ^ UINT64_C(0x646f72616e646f6d);
    s->v2 = stn_hash_k0 ^ UINT64_C(0x6c7967656e657261); s->v3 = stn_hash_k1 ^ UINT64_C(0x7465646279746573);
    s->n = 0;
}
static inline void stn_sip_word(StnSip* s, uint64_t m) {
    uint64_t v0 = s->v0, v1 = s->v1, v2 = s->v2, v3 = s->v3;
    v3 ^= m; STN_SIPROUND; v0 ^= m;
    s->v0 = v0; s->v1 = v1; s->v2 = v2; s->v3 = v3; s->n += 8;
}
static inline uint64_t stn_sip_finish(StnSip* s) {
    uint64_t v0 = s->v0, v1 = s->v1, v2 = s->v2, v3 = s->v3;
    uint64_t b = s->n << 56;
    v3 ^= b; STN_SIPROUND; v0 ^= b;
    v2 ^= 0xff; STN_SIPROUND; STN_SIPROUND; STN_SIPROUND;
    return v0 ^ v1 ^ v2 ^ v3;
}
static inline uint64_t stn_hash_combine(uint64_t h, uint64_t x) { return stn_hash_u64(h ^ (x + UINT64_C(0x9E3779B97F4A7C15) + (h << 6) + (h >> 2))); }

/* stn_map_find for a table whose keys are 64-bit integers (STN_KEY_I64), inline: the layout of
   the index is the one stn_runtime.c describes. */
static inline void* stn_map_find_i64(const StnMap* m, uint64_t key) {
    if (!m->ilog) {
        /* small: the few entries there are, in order */
        char* e = m->entries;
        for (int64_t i = 0; i < m->used; i++, e += m->stride) { uint64_t k; memcpy(&k, e, 8); if (k == key) return e + m->voff; }
        return NULL;
    }
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
            memcpy(&k, e, 8);
            /* a removed entry keeps its key, but its control byte no longer matches */
            if (k == key) return e + m->voff;
        }
        if (unused_free) return NULL;
        step += 16;
        pos = (pos + step) & mask;
    }
}

/* stn_map_find for a table whose keys are Str (STN_KEY_STR), inline. An inline key, or the very
   string the table holds, is compared as two words. */
static inline void* stn_map_find_str(const StnMap* m, StnStr key) {
    if (!m->ilog) {
        /* small: the few entries there are, in order */
        char* e = m->entries;
        for (int64_t i = 0; i < m->used; i++, e += m->stride) if (stn_str_eq(*(const StnStr*)(e + 8), key)) return e + m->voff;
        return NULL;
    }
    uint64_t h = stn_str_hash(key);
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
            if (*(const uint64_t*)e == w && stn_str_eq(*(const StnStr*)(e + 8), key)) return e + m->voff;
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
/* An entry through which main calls a function that loops: never inlined into main, which is not
   compiled hot, so the loop is compiled as hot code where the function is inlined into the entry. */
#if defined(__GNUC__) || defined(__clang__)
#  define STN_NOINLINE __attribute__((noinline))
#else
#  define STN_NOINLINE
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

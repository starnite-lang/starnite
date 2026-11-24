/* SPDX-License-Identifier: GPL-3.0-or-later */
/* The C control for bench/maps: the open-addressing hash table a C programmer writes for the job,
   with linear probing, a byte of state per slot, tombstones, and growth at three quarters full.
   Integer keys and their values sit together in the slots; string keys point at their bytes.
   By default keys are hashed with SipHash-1-3 under a random key, as Starnite's and Rust's are;
   built with -DFAST_HASH they use a multiply-and-shift mixer, which is faster and which chosen
   keys can make collide. Arithmetic is not checked for overflow. */
#define _GNU_SOURCE
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static void require(int ok) { if (!ok) { fputs("maps.c: requirement failed\n", stderr); exit(1); } }
static uint64_t now(void) {
    struct timespec t;
    require(clock_gettime(CLOCK_MONOTONIC, &t) == 0);
    return (uint64_t)t.tv_sec * UINT64_C(1000000000) + (uint64_t)t.tv_nsec;
}

/* ---- hashing ---- */
static uint64_t k0, k1;
#define ROTL(x, b) (((x) << (b)) | ((x) >> (64 - (b))))
#define SIPROUND do { v0 += v1; v1 = ROTL(v1, 13); v1 ^= v0; v0 = ROTL(v0, 32); v2 += v3; v3 = ROTL(v3, 16); v3 ^= v2; \
        v0 += v3; v3 = ROTL(v3, 21); v3 ^= v0; v2 += v1; v1 = ROTL(v1, 17); v1 ^= v2; v2 = ROTL(v2, 32); } while (0)
__attribute__((unused)) static uint64_t sip_bytes(const unsigned char* in, size_t n) {
    uint64_t v0 = k0 ^ 0x736f6d6570736575ULL, v1 = k1 ^ 0x646f72616e646f6dULL, v2 = k0 ^ 0x6c7967656e657261ULL, v3 = k1 ^ 0x7465646279746573ULL;
    size_t i = 0;
    for (; n - i >= 8; i += 8) { uint64_t m; memcpy(&m, in + i, 8); v3 ^= m; SIPROUND; v0 ^= m; }
    uint64_t b = (uint64_t)n << 56;
    for (size_t j = 0; i + j < n; j++) b |= (uint64_t)in[i + j] << (8 * j);
    v3 ^= b; SIPROUND; v0 ^= b;
    v2 ^= 0xff; SIPROUND; SIPROUND; SIPROUND;
    return v0 ^ v1 ^ v2 ^ v3;
}
static inline uint64_t hash_int(uint64_t x) {
#ifdef FAST_HASH
    x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33;
    return x;
#else
    uint64_t v0 = k0 ^ 0x736f6d6570736575ULL, v1 = k1 ^ 0x646f72616e646f6dULL, v2 = k0 ^ 0x6c7967656e657261ULL, v3 = k1 ^ 0x7465646279746573ULL;
    v3 ^= x; SIPROUND; v0 ^= x;
    uint64_t b = (uint64_t)8 << 56;
    v3 ^= b; SIPROUND; v0 ^= b;
    v2 ^= 0xff; SIPROUND; SIPROUND; SIPROUND;
    return v0 ^ v1 ^ v2 ^ v3;
#endif
}
static inline uint64_t hash_str(const char* s, size_t n) {
#ifdef FAST_HASH
    uint64_t h = 0xcbf29ce484222325ULL;              /* FNV-1a */
    for (size_t i = 0; i < n; i++) { h ^= (unsigned char)s[i]; h *= 0x100000001b3ULL; }
    return h;
#else
    return sip_bytes((const unsigned char*)s, n);
#endif
}

/* ---- a table of 64-bit integer keys, with or without values ---- */
enum { EMPTY = 0, FULL = 1, DEAD = 2 };
typedef struct { int64_t key, value; } Slot;
typedef struct { uint8_t* state; Slot* slots; size_t cap, len, used; } IntMap;

static void im_init(IntMap* m, size_t cap) {
    m->cap = cap; m->len = m->used = 0;
    m->state = calloc(cap, 1); m->slots = malloc(cap * sizeof(Slot));
    require(m->state && m->slots);
}
static void im_free(IntMap* m) { free(m->state); free(m->slots); }
static void im_grow(IntMap* m) {
    IntMap n;
    im_init(&n, m->len * 2 >= m->cap / 2 ? m->cap * 2 : m->cap);
    for (size_t i = 0; i < m->cap; i++)
        if (m->state[i] == FULL) {
            size_t s = hash_int((uint64_t)m->slots[i].key) & (n.cap - 1);
            while (n.state[s]) s = (s + 1) & (n.cap - 1);
            n.state[s] = FULL; n.slots[s] = m->slots[i]; n.len++; n.used++;
        }
    im_free(m); *m = n;
}
/* the slot of the key, or the free slot it would take */
static inline size_t im_find(const IntMap* m, int64_t key, int* found) {
    size_t mask = m->cap - 1, s = hash_int((uint64_t)key) & mask, first_dead = SIZE_MAX;
    for (;;) {
        uint8_t st = m->state[s];
        if (st == EMPTY) { *found = 0; return first_dead != SIZE_MAX ? first_dead : s; }
        if (st == FULL && m->slots[s].key == key) { *found = 1; return s; }
        if (st == DEAD && first_dead == SIZE_MAX) first_dead = s;
        s = (s + 1) & mask;
    }
}
static inline int64_t* im_slot(IntMap* m, int64_t key, int* fresh) {
    if ((m->used + 1) * 4 > m->cap * 3) im_grow(m);
    int found;
    size_t s = im_find(m, key, &found);
    *fresh = !found;
    if (!found) {
        if (m->state[s] == EMPTY) m->used++;
        m->state[s] = FULL; m->slots[s].key = key; m->len++;
    }
    return &m->slots[s].value;
}
static inline int64_t* im_get(const IntMap* m, int64_t key) {
    int found;
    size_t s = im_find(m, key, &found);
    return found ? &((IntMap*)m)->slots[s].value : NULL;
}
static inline int im_remove(IntMap* m, int64_t key, int64_t* out) {
    int found;
    size_t s = im_find(m, key, &found);
    if (!found) return 0;
    *out = m->slots[s].value; m->state[s] = DEAD; m->len--;
    return 1;
}

/* ---- a table of string keys to integers; the table keeps its own copies ---- */
typedef struct { char* key; size_t n; uint64_t hash; int64_t value; } SSlot;
typedef struct { SSlot* slots; size_t cap, len; } StrMap;
static void sm_init(StrMap* m, size_t cap) { m->cap = cap; m->len = 0; m->slots = calloc(cap, sizeof(SSlot)); require(m->slots != NULL); }
static void sm_free(StrMap* m) { for (size_t i = 0; i < m->cap; i++) free(m->slots[i].key); free(m->slots); }
static void sm_grow(StrMap* m) {
    StrMap n;
    sm_init(&n, m->cap * 2);
    for (size_t i = 0; i < m->cap; i++)
        if (m->slots[i].key) {
            size_t s = m->slots[i].hash & (n.cap - 1);
            while (n.slots[s].key) s = (s + 1) & (n.cap - 1);
            n.slots[s] = m->slots[i]; n.len++;
        }
    free(m->slots); *m = n;
}
static inline int64_t* sm_slot(StrMap* m, const char* key, size_t n) {
    if ((m->len + 1) * 4 > m->cap * 3) sm_grow(m);
    uint64_t h = hash_str(key, n);
    size_t mask = m->cap - 1, s = h & mask;
    while (m->slots[s].key) {
        if (m->slots[s].hash == h && m->slots[s].n == n && memcmp(m->slots[s].key, key, n) == 0) return &m->slots[s].value;
        s = (s + 1) & mask;
    }
    char* copy = malloc(n + 1);
    require(copy != NULL);
    memcpy(copy, key, n + 1);
    m->slots[s] = (SSlot){ copy, n, h, 0 };
    m->len++;
    return &m->slots[s].value;
}
static inline int64_t sm_get(const StrMap* m, const char* key, size_t n) {
    uint64_t h = hash_str(key, n);
    size_t mask = m->cap - 1, s = h & mask;
    while (m->slots[s].key) {
        if (m->slots[s].hash == h && m->slots[s].n == n && memcmp(m->slots[s].key, key, n) == 0) return m->slots[s].value;
        s = (s + 1) & mask;
    }
    require(0);
    return 0;
}

static int64_t key(int64_t i, int64_t seed) { return (i * 7919 + seed) % 1000003; }
static void filled(IntMap* m, int64_t n, int64_t seed) {
    im_init(m, 16);
    for (int64_t i = 0; i < n; i++) { int fresh; *im_slot(m, key(i, seed), &fresh) = i; }
}

int main(void) {
    char name[64];
    int64_t seed;
    require(scanf("%63s %" SCNd64, name, &seed) == 2);
    FILE* r = fopen("/dev/urandom", "rb");
    require(r && fread(&k0, 8, 1, r) == 1 && fread(&k1, 8, 1, r) == 1);
    fclose(r);
    uint64_t start = 0, end = 0;
    int64_t check = 0;
    if (!strcmp(name, "map_insert_int")) {
        IntMap m;
        start = now();
        filled(&m, 200000, seed);
        end = now();
        check = (int64_t)m.len + *im_get(&m, key(7, seed)) + *im_get(&m, key(199999, seed));
        im_free(&m);
    } else if (!strcmp(name, "map_lookup_int")) {
        IntMap m;
        filled(&m, 100000, seed);
        start = now();
        for (int64_t i = 0; i < 1000000; i++) { int64_t* v = im_get(&m, key(i % 200000, seed)); check += v ? *v : 1; }
        end = now();
        im_free(&m);
    } else if (!strcmp(name, "map_update_int")) {
        IntMap m;
        im_init(&m, 16);
        start = now();
        for (int64_t i = 0; i < 1000000; i++) { int fresh; int64_t* v = im_slot(&m, (i * 31 + seed) % 50021, &fresh); if (fresh) *v = 0; *v += 1; }
        end = now();
        check = (int64_t)m.len * 1000 + *im_get(&m, seed % 50021);
        im_free(&m);
    } else if (!strcmp(name, "map_iter_int")) {
        IntMap m;
        filled(&m, 200000, seed);
        start = now();
        for (int r = 0; r < 5; r++)
            for (size_t i = 0; i < m.cap; i++) if (m.state[i] == FULL) check += m.slots[i].key - m.slots[i].value;
        end = now();
        im_free(&m);
    } else if (!strcmp(name, "map_remove_int")) {
        IntMap m;
        filled(&m, 200000, seed);
        int64_t found = 0;
        start = now();
        for (int64_t i = 0; i < 200000; i += 2) { int64_t v; if (im_remove(&m, key(i, seed), &v)) found += v; }
        end = now();
        check = (int64_t)m.len + found;
        im_free(&m);
    } else if (!strcmp(name, "map_count_str")) {
        char keys[512][32];
        size_t lens[512];
        for (int64_t i = 0; i < 512; i++) { int n = snprintf(keys[i], 32, "name%" PRId64 "/item", (i * 37 + seed) % 100000); require(n > 0 && n < 32); lens[i] = (size_t)n; }
        StrMap m;
        sm_init(&m, 16);
        start = now();
        for (int64_t i = 0; i < 300000; i++) { size_t j = (size_t)((i * 7) % 512); *sm_slot(&m, keys[j], lens[j]) += 1; }
        end = now();
        check = (int64_t)m.len * 1000000 + sm_get(&m, keys[3], lens[3]);
        sm_free(&m);
    } else if (!strcmp(name, "set_int")) {
        IntMap s;
        im_init(&s, 16);
        int64_t hits = 0;
        start = now();
        for (int64_t i = 0; i < 200000; i++) { int fresh; im_slot(&s, key(i, seed), &fresh); }
        for (int64_t i = 0; i < 1000000; i++) if (im_get(&s, key(i % 400000, seed))) hits++;
        end = now();
        check = (int64_t)s.len + hits;
        im_free(&s);
    } else if (!strcmp(name, "set_union")) {
        IntMap a, b, u, n, d;
        im_init(&a, 16); im_init(&b, 16);
        for (int64_t i = 0; i < 100000; i++) { int f; im_slot(&a, key(i, seed), &f); im_slot(&b, key(i + 50000, seed), &f); }
        start = now();
        im_init(&u, 16); im_init(&n, 16); im_init(&d, 16);
        for (size_t i = 0; i < a.cap; i++) if (a.state[i] == FULL) {
            int f; int64_t k = a.slots[i].key;
            im_slot(&u, k, &f);
            if (im_get(&b, k)) im_slot(&n, k, &f); else im_slot(&d, k, &f);
        }
        for (size_t i = 0; i < b.cap; i++) if (b.state[i] == FULL) { int f; im_slot(&u, b.slots[i].key, &f); }
        end = now();
        check = (int64_t)u.len * 3 + (int64_t)n.len * 5 + (int64_t)d.len * 7;
        im_free(&a); im_free(&b); im_free(&u); im_free(&n); im_free(&d);
    } else {
        fputs("maps.c: unknown benchmark\n", stderr);
        return 1;
    }
    printf("%" PRIu64 " %" PRId64 "\n", end - start, check);
    return 0;
}

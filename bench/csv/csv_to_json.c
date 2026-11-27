// SPDX-License-Identifier: GPL-3.0-or-later
// The CSV to JSON benchmark in C, written the way csv_to_json.stn is: every row becomes a tree,
// and the whole tree is rendered to one string. An object keeps its fields in the order they
// were put. Strings are counted byte strings of their own; nothing is shared.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void* must(void* p) { if (!p) { fputs("out of memory\n", stderr); exit(3); } return p; }

typedef struct { char* p; size_t len, cap; } Str;
static void str_reserve(Str* s, size_t extra) {
    if (s->len + extra + 1 > s->cap) {
        size_t cap = s->cap ? s->cap * 2 : 16;
        while (cap < s->len + extra + 1) cap *= 2;
        s->p = must(realloc(s->p, cap)); s->cap = cap;
    }
}
static void str_add(Str* s, const char* p, size_t n) { str_reserve(s, n); memcpy(s->p + s->len, p, n); s->len += n; s->p[s->len] = 0; }
static void str_addc(Str* s, char c) { str_reserve(s, 1); s->p[s->len++] = c; s->p[s->len] = 0; }
static Str str_of(const char* p, size_t n) { Str s = { 0, 0, 0 }; str_add(&s, p, n); return s; }

typedef struct { Str* v; size_t n, cap; } Strs;
static void strs_push(Strs* a, Str s) {
    if (a->n == a->cap) { a->cap = a->cap ? a->cap * 2 : 8; a->v = must(realloc(a->v, a->cap * sizeof(Str))); }
    a->v[a->n++] = s;
}
static void strs_free(Strs* a) { for (size_t i = 0; i < a->n; i++) free(a->v[i].p); free(a->v); }

typedef enum { JNULL, JBOOL, JINT, JNUM, JTEXT, JLIST, JOBJECT } Kind;
typedef struct Json Json;
struct Json {
    Kind kind;
    union {
        int b; int64_t i; double x; Str s;
        struct { Json* v; size_t n, cap; } list;
        struct { Str* keys; Json* v; size_t n, cap; } obj;
    } u;
};

static Strs split_on(const char* p, size_t n, char sep) {
    Strs out = { 0, 0, 0 };
    size_t start = 0;
    for (size_t i = 0; i <= n; i++)
        if (i == n || p[i] == sep) { strs_push(&out, str_of(p + start, i - start)); start = i + 1; }
    return out;
}

static Strs fields_of(const char* line, size_t n) {
    if (!memchr(line, '"', n)) return split_on(line, n, ',');
    Strs out = { 0, 0, 0 };
    Str cur = str_of("", 0);
    int quoted = 0;
    for (size_t i = 0; i < n; i++) {
        char c = line[i];
        if (quoted) {
            if (c != '"') str_addc(&cur, c);
            else if (i + 1 < n && line[i + 1] == '"') { str_addc(&cur, c); i++; }
            else quoted = 0;
        } else if (c == '"') quoted = 1;
        else if (c == ',') { strs_push(&out, cur); cur = str_of("", 0); }
        else str_addc(&cur, c);
    }
    strs_push(&out, cur);
    return out;
}

static void trim(const char** p, size_t* n) {
    while (*n && ((*p)[0] == ' ' || (*p)[0] == '\t' || (*p)[0] == '\r' || (*p)[0] == '\n')) { (*p)++; (*n)--; }
    while (*n && ((*p)[*n - 1] == ' ' || (*p)[*n - 1] == '\t' || (*p)[*n - 1] == '\r' || (*p)[*n - 1] == '\n')) (*n)--;
}

static Json value_of(const char* p, size_t n) {
    Json j;
    trim(&p, &n);
    if (n == 0) { j.kind = JNULL; return j; }
    if ((n == 4 && !memcmp(p, "true", 4)) || (n == 5 && !memcmp(p, "false", 5))) { j.kind = JBOOL; j.u.b = n == 4; return j; }
    char buf[64];
    if (n < sizeof buf) {
        memcpy(buf, p, n); buf[n] = 0;
        char* end;
        long long i = strtoll(buf, &end, 10);
        if (*end == 0 && (buf[0] == '-' || (buf[0] >= '0' && buf[0] <= '9'))) { j.kind = JINT; j.u.i = i; return j; }
        double x = strtod(buf, &end);
        if (*end == 0) { j.kind = JNUM; j.u.x = x; return j; }
    }
    j.kind = JTEXT; j.u.s = str_of(p, n);
    return j;
}

typedef struct { Strs path; int is_list; } Column;

static Column column_of(const char* p, size_t n) {
    Column c;
    trim(&p, &n);
    c.is_list = n >= 2 && p[n - 2] == '[' && p[n - 1] == ']';
    if (c.is_list) n -= 2;
    c.path = split_on(p, n, '.');
    return c;
}

static Json placed(Json node, const Strs* path, size_t at, Json value) {
    if (at == path->n) return value;
    if (node.kind != JOBJECT) { node.kind = JOBJECT; node.u.obj.keys = NULL; node.u.obj.v = NULL; node.u.obj.n = node.u.obj.cap = 0; }
    const Str* key = &path->v[at];
    for (size_t i = 0; i < node.u.obj.n; i++)
        if (node.u.obj.keys[i].len == key->len && !memcmp(node.u.obj.keys[i].p, key->p, key->len)) {
            node.u.obj.v[i] = placed(node.u.obj.v[i], path, at + 1, value);
            return node;
        }
    if (node.u.obj.n == node.u.obj.cap) {
        node.u.obj.cap = node.u.obj.cap ? node.u.obj.cap * 2 : 4;
        node.u.obj.keys = must(realloc(node.u.obj.keys, node.u.obj.cap * sizeof(Str)));
        node.u.obj.v = must(realloc(node.u.obj.v, node.u.obj.cap * sizeof(Json)));
    }
    Json none; none.kind = JNULL;
    node.u.obj.keys[node.u.obj.n] = str_of(key->p, key->len);
    node.u.obj.v[node.u.obj.n] = placed(none, path, at + 1, value);
    node.u.obj.n++;
    return node;
}

static void list_push(Json* l, Json v) {
    if (l->u.list.n == l->u.list.cap) { l->u.list.cap = l->u.list.cap ? l->u.list.cap * 2 : 4; l->u.list.v = must(realloc(l->u.list.v, l->u.list.cap * sizeof(Json))); }
    l->u.list.v[l->u.list.n++] = v;
}

static Json record_of(const Column* columns, size_t ncol, const Strs* cells) {
    Json record; record.kind = JOBJECT; record.u.obj.keys = NULL; record.u.obj.v = NULL; record.u.obj.n = record.u.obj.cap = 0;
    for (size_t i = 0; i < ncol; i++) {
        Json value;
        if (columns[i].is_list) {
            Str joined = str_of(cells->v[i].p, cells->v[i].len);
            for (size_t k = 0; k < joined.len; k++) if (joined.p[k] == ';') joined.p[k] = ',';
            Strs parts = fields_of(joined.p, joined.len);
            value.kind = JLIST; value.u.list.v = NULL; value.u.list.n = value.u.list.cap = 0;
            for (size_t k = 0; k < parts.n; k++) {
                const char* p = parts.v[k].p; size_t n = parts.v[k].len;
                trim(&p, &n);
                if (n) list_push(&value, value_of(p, n));
            }
            strs_free(&parts); free(joined.p);
        } else value = value_of(cells->v[i].p, cells->v[i].len);
        record = placed(record, &columns[i].path, 0, value);
    }
    return record;
}

static void quoted(Str* out, const char* p, size_t n) {
    str_addc(out, '"');
    for (size_t i = 0; i < n; i++) {
        if (p[i] == '"') str_add(out, "\\\"", 2);
        else if (p[i] == '\\') str_add(out, "\\\\", 2);
        else str_addc(out, p[i]);
    }
    str_addc(out, '"');
}

static void pad(Str* out, int depth) { for (int i = 0; i < depth; i++) str_add(out, "  ", 2); }

static void render(Str* out, const Json* j, int depth) {
    char buf[64];
    switch (j->kind) {
    case JNULL: str_add(out, "null", 4); break;
    case JBOOL: if (j->u.b) str_add(out, "true", 4); else str_add(out, "false", 5); break;
    case JINT: str_add(out, buf, (size_t)snprintf(buf, sizeof buf, "%lld", (long long)j->u.i)); break;
    case JNUM: {
        /* the shortest text that reads back as the same number */
        int n = 0;
        for (int prec = 1; prec <= 17; prec++) { n = snprintf(buf, sizeof buf, "%.*g", prec, j->u.x); if (strtod(buf, NULL) == j->u.x) break; }
        str_add(out, buf, (size_t)n);
        break;
    }
    case JTEXT: quoted(out, j->u.s.p, j->u.s.len); break;
    case JLIST:
        if (j->u.list.n == 0) { str_add(out, "[]", 2); break; }
        str_add(out, "[\n", 2);
        for (size_t i = 0; i < j->u.list.n; i++) {
            pad(out, depth + 1); render(out, &j->u.list.v[i], depth + 1);
            if (i + 1 < j->u.list.n) str_addc(out, ',');
            str_addc(out, '\n');
        }
        pad(out, depth); str_addc(out, ']');
        break;
    case JOBJECT:
        if (j->u.obj.n == 0) { str_add(out, "{}", 2); break; }
        str_add(out, "{\n", 2);
        for (size_t i = 0; i < j->u.obj.n; i++) {
            pad(out, depth + 1); quoted(out, j->u.obj.keys[i].p, j->u.obj.keys[i].len); str_add(out, ": ", 2);
            render(out, &j->u.obj.v[i], depth + 1);
            if (i + 1 < j->u.obj.n) str_addc(out, ',');
            str_addc(out, '\n');
        }
        pad(out, depth); str_addc(out, '}');
        break;
    }
}

int main(void) {
    Str input = { 0, 0, 0 };
    char chunk[65536];
    size_t got;
    while ((got = fread(chunk, 1, sizeof chunk, stdin)) > 0) str_add(&input, chunk, got);
    Column* columns = NULL; size_t ncol = 0;
    Json all; all.kind = JLIST; all.u.list.v = NULL; all.u.list.n = all.u.list.cap = 0;
    size_t start = 0, number = 0;
    while (start < input.len) {
        const char* nl = memchr(input.p + start, '\n', input.len - start);
        size_t stop = nl ? (size_t)(nl - input.p) : input.len;
        size_t n = stop - start;
        if (n && input.p[start + n - 1] == '\r') n--;
        number++;
        if (number == 1) {
            Strs names = fields_of(input.p + start, n);
            ncol = names.n; columns = must(malloc((ncol ? ncol : 1) * sizeof(Column)));
            for (size_t i = 0; i < ncol; i++) columns[i] = column_of(names.v[i].p, names.v[i].len);
            strs_free(&names);
        } else {
            const char* p = input.p + start; size_t tn = n;
            trim(&p, &tn);
            if (tn) {
                Strs cells = fields_of(input.p + start, n);
                if (cells.n != ncol) { printf("line %zu: %zu fields, the header has %zu\n", number, cells.n, ncol); return 0; }
                list_push(&all, record_of(columns, ncol, &cells));
                strs_free(&cells);
            }
        }
        start = stop + 1;
    }
    if (number == 0) { puts("no header line"); return 0; }
    Str out = { 0, 0, 0 };
    render(&out, &all, 0);
    str_addc(&out, '\n');
    fwrite(out.p, 1, out.len, stdout);
    return 0;
}

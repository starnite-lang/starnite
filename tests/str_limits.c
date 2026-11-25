/* SPDX-License-Identifier: GPL-3.0-or-later */
/* The size arithmetic of strings, checked for a target whose size_t is 32 bits without building
   for one or allocating anything: the runtime works sizes out in 64 bits against a limit that is
   an argument here (runtime/stn_runtime.h). Run by tests/portable.sh. */
#include <stdio.h>
#include "stn_runtime.h"

static int failed = 0;
static void expect(const char* what, uint64_t got, uint64_t want) {
    if (got != want) {
        printf("FAIL %s: got %llu, want %llu\n", what, (unsigned long long)got, (unsigned long long)want);
        failed = 1;
    }
}

int main(void) {
    const uint64_t max32 = UINT32_MAX, gib = UINT64_C(1) << 30;
    const uint64_t limit32 = stn_str_limit_for(max32);
    const uint64_t limit64 = stn_str_limit_for(UINT64_MAX);
    /* a 32-bit size_t leaves room for the header and the terminator; a 64-bit one is bounded by
       the largest allocation */
    expect("32-bit limit", limit32, max32 - sizeof(StnStrBuf) - 1);
    expect("64-bit limit", limit64, (uint64_t)STN_MAX_ALLOC);
    /* a 3 GiB buffer and one more byte: half as much again does not fit, so the capacity is the
       limit, and never less than what is needed */
    expect("grow 3 GiB by one", stn_str_grown(3 * gib, 3 * gib + 1, limit32), limit32);
    expect("grow at the limit", stn_str_grown(limit32 - 1, limit32, limit32), limit32);
    expect("grow past the limit", stn_str_grown(limit32, limit32 + 1, limit32), 0);
    expect("grow far past the limit", stn_str_grown(3 * gib, 5 * gib, limit32), 0);
    /* small buffers grow by half, or to what is needed when that is more */
    expect("grow by half", stn_str_grown(100, 101, limit32), 150);
    expect("grow to the need", stn_str_grown(100, 400, limit32), 400);
    expect("grow from nothing", stn_str_grown(0, 16, limit32), 16);
    /* every capacity handed out fits a 32-bit size_t beside the header and terminator */
    for (uint64_t cap = 1; cap < 8 * gib; cap = cap * 3 + 1) {
        uint64_t room = stn_str_grown(cap, cap + 1, limit32);
        if (room != 0 && (room < cap + 1 || room + sizeof(StnStrBuf) + 1 > max32)) {
            printf("FAIL capacity %llu for a buffer of %llu\n", (unsigned long long)room, (unsigned long long)cap);
            failed = 1;
        }
    }
    /* on the wide target the same call is bounded by the largest allocation */
    expect("64-bit grow", stn_str_grown(3 * gib, 3 * gib + 1, limit64), 3 * gib + 3 * gib / 2);
    expect("64-bit past the limit", stn_str_grown(1, (uint64_t)STN_MAX_ALLOC + 1, limit64), 0);
    if (!failed) printf("string size limits ok\n");
    return failed;
}

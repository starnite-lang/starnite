/* SPDX-License-Identifier: GPL-3.0-or-later */
/* Releases that a budget put off (section 9.7) are taken up at the next allocation, a budget's
   worth at a time, whether it asks for a cell of a size class or for more than any class holds.
   Run by tests/portable.sh. */
#include "stn_runtime.h"
#include <stdio.h>

static int released;
/* a release function that drops something, which is what goes in through the guard */
static void release(void* p) {
    if (stn_release_enter(p, release)) return;
    released++;
    stn_free(p);
    stn_release_leave();
}

int main(void) {
    void* a = stn_alloc(32);
    void* b = stn_alloc(32);
    /* as STN_FREE_BUDGET=1 leaves things: one object for each go, and two waiting */
    stn_release_budget = 1;
    stn_release_left = 0;
    stn_release_defer(a, release);
    stn_release_defer(b, release);
    void* large = stn_alloc(2048);   /* more than the largest size class */
    if (released != 1) { printf("after a large allocation %d objects were released, not 1\n", released); return 1; }
    void* small = stn_alloc(64);
    if (released != 2) { printf("after a small allocation %d objects were released, not 2\n", released); return 1; }
    stn_free(large);
    stn_free(small);
    puts("ok");
    return 0;
}

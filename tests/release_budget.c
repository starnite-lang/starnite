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

static void drop_array(void* elem) { stn_drop(*(StnArray**)elem, stn_array_release); }

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

    /* Wide, not deep: an array of four arrays of numbers. The four hold nothing counted, so
       their release starts none, but each is an object of the budget: with a budget of one,
       dropping the outer array releases it alone, and each allocation after that one more. */
    static const StnElemOps numbers = { sizeof(int64_t), NULL, NULL };
    static const StnElemOps arrays = { sizeof(StnArray*), NULL, drop_array };
    StnArray* outer = stn_array_new(&arrays, 4);
    for (int i = 0; i < 4; i++) ((StnArray**)outer->data)[i] = stn_array_new(&numbers, 8);
    outer->len = 4;
    stn_release_left = 1;
    stn_drop(outer, stn_array_release);
    if (stn_release_pending != 4) { printf("after the outer array %zu objects were waiting, not 4\n", stn_release_pending); return 1; }
    for (int i = 3; i >= 0; i--) {
        stn_free(stn_alloc(16));
        if (stn_release_pending != (size_t)i) { printf("after an allocation %zu objects were waiting, not %d\n", stn_release_pending, i); return 1; }
    }
    puts("ok");
    return 0;
}

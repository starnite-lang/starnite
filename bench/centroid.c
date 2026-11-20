#include <stdio.h>
#include <stdlib.h>
typedef struct { double x, y, z; } Vec3;
static Vec3 centroid(const Vec3* p, long n) {
    Vec3 acc = {0, 0, 0};
    for (long i = 0; i < n; i++) { acc.x += p[i].x; acc.y += p[i].y; acc.z += p[i].z; }
    double d = (double)n;
    return (Vec3){acc.x / d, acc.y / d, acc.z / d};
}
int main(void) {
    long n = 1000000, cap = 4, len = 0;
    Vec3* pts = malloc(cap * sizeof(Vec3));
    for (long i = 0; i < n; i++) {
        if (len == cap) { cap *= 2; pts = realloc(pts, cap * sizeof(Vec3)); }
        double f = (double)i;
        pts[len++] = (Vec3){f, f * 0.5, f * 0.25};
    }
    Vec3 c = {0, 0, 0};
    for (int k = 0; k < 20; k++) c = centroid(pts, len);
    printf("%.17g %.17g %.17g\n", c.x, c.y, c.z);
    free(pts);
    return 0;
}

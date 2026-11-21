#include <stdio.h>
int main(void) {
    long size = 2000, inside = 0;
    for (long y = 0; y < size; y++) {
        double ci = 2.0 * (double)y / (double)size - 1.0;
        for (long x = 0; x < size; x++) {
            double cr = 2.0 * (double)x / (double)size - 1.5;
            double zr = 0, zi = 0;
            long i = 0; int escaped = 0;
            while (i < 50 && !escaped) {
                double tr = zr * zr - zi * zi + cr;
                zi = 2.0 * zr * zi + ci;
                zr = tr;
                if (zr * zr + zi * zi > 4.0) escaped = 1;
                i += 1;
            }
            if (!escaped) inside += 1;
        }
    }
    printf("%ld\n", inside);
    return 0;
}

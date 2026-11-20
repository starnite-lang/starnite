#include <math.h>
#include <stdio.h>
#include <stdlib.h>
static double A(long i, long j) { return 1.0 / (double)((i + j) * (i + j + 1) / 2 + i + 1); }
static void mul_av(const double* v, double* out, long n) {
    for (long i = 0; i < n; i++) { double s = 0; for (long j = 0; j < n; j++) s += A(i, j) * v[j]; out[i] = s; }
}
static void mul_atv(const double* v, double* out, long n) {
    for (long i = 0; i < n; i++) { double s = 0; for (long j = 0; j < n; j++) s += A(j, i) * v[j]; out[i] = s; }
}
static void mul_atav(const double* v, double* out, double* tmp, long n) { mul_av(v, tmp, n); mul_atv(tmp, out, n); }
int main(void) {
    long n = 2000;
    double *u = malloc(n * sizeof(double)), *v = malloc(n * sizeof(double)), *tmp = malloc(n * sizeof(double));
    for (long i = 0; i < n; i++) { u[i] = 1; v[i] = 0; tmp[i] = 0; }
    for (int k = 0; k < 10; k++) { mul_atav(u, v, tmp, n); mul_atav(v, u, tmp, n); }
    double vbv = 0, vv = 0;
    for (long i = 0; i < n; i++) { vbv += u[i] * v[i]; vv += v[i] * v[i]; }
    printf("%.17g\n", sqrt(vbv / vv));
    free(u); free(v); free(tmp);
    return 0;
}

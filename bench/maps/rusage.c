/* SPDX-License-Identifier: GPL-3.0-or-later */
/* Runs a command with its standard input passed through, and prints what it printed (one line)
   followed by the CPU time it used, user and system together, in nanoseconds, and its peak
   resident memory in KiB. The status is the command's. */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/resource.h>
#include <sys/wait.h>

int main(int argc, char** argv) {
    if (argc < 2) { fputs("usage: rusage COMMAND [ARGUMENT...]\n", stderr); return 2; }
    int out[2];
    if (pipe(out) != 0) { perror("pipe"); return 2; }
    pid_t pid = fork();
    if (pid < 0) { perror("fork"); return 2; }
    if (pid == 0) {
        dup2(out[1], 1);
        close(out[0]); close(out[1]);
        execvp(argv[1], argv + 1);
        perror(argv[1]);
        _exit(127);
    }
    close(out[1]);
    char text[4096];
    size_t n = 0;
    for (;;) {
        ssize_t got = read(out[0], text + n, sizeof text - 1 - n);
        if (got <= 0) break;
        n += (size_t)got;
        if (n == sizeof text - 1) break;
    }
    text[n] = 0;
    int status;
    struct rusage ru;
    if (wait4(pid, &status, 0, &ru) < 0) { perror("wait4"); return 2; }
    while (n > 0 && (text[n - 1] == '\n' || text[n - 1] == '\r')) text[--n] = 0;
    long long cpu = (long long)ru.ru_utime.tv_sec * 1000000000LL + (long long)ru.ru_utime.tv_usec * 1000LL
                  + (long long)ru.ru_stime.tv_sec * 1000000000LL + (long long)ru.ru_stime.tv_usec * 1000LL;
    printf("%s %lld %ld\n", text, cpu, ru.ru_maxrss);
    if (WIFSIGNALED(status)) return 128 + WTERMSIG(status);
    return WEXITSTATUS(status);
}

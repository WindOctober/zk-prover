// This file is part of the SV-Benchmarks-style collection of verification tasks.
//
// SPDX-License-Identifier: GPL-3.0-or-later

extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "abs_zero_bug.c", 2, "reach_error"); }

extern int __VERIFIER_nondet_int();

int main() {
    int a = __VERIFIER_nondet_int();
    int b = __VERIFIER_nondet_int();

    if (a < -20 || a > 20 || b < -20 || b > 20)
        return 0;

    int x = a > 0 ? a : -a;
    int y = b > 0 ? b : -b;

    if (x == 0 && y == 0)
        reach_error();

    return 0;
}

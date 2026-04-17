// This file is part of the SV-Benchmarks-style collection of verification tasks.
//
// SPDX-License-Identifier: GPL-3.0-or-later

extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "nested_guard_bug.c", 2, "reach_error"); }

extern int __VERIFIER_nondet_int();

int main() {
    int a = __VERIFIER_nondet_int();
    int b = __VERIFIER_nondet_int();
    int c = __VERIFIER_nondet_int();

    int d = __VERIFIER_nondet_int();

    if (a < 0 || a > 10 || b < 0 || b > 10 || c < 0 || c > 10 || d < 0 || d > 10)
        return 0;

    int left = a + b;
    int right = c + d;

    if (left >= right) {
        if (left < right)
            reach_error();
    } else {
        if (left >= right)
            reach_error();
    }

    if (a == b && c == d) {
        int twice = a + b;
        if (twice < a)
            reach_error();
    }

    return 0;
}

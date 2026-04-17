// This file is part of the SV-Benchmarks-style collection of verification tasks.
//
// SPDX-License-Identifier: GPL-3.0-or-later

extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "range_arith_safe.c", 2, "reach_error"); }

extern int __VERIFIER_nondet_int();

int main() {
    int a = __VERIFIER_nondet_int();
    int b = __VERIFIER_nondet_int();
    int c = __VERIFIER_nondet_int();

    if (a < 0 || a > 20 || b < 0 || b > 20 || c < 0 || c > 20)
        return 0;

    if (a > b) {
        int sum = a + b;
        if (c <= sum)
            reach_error();
    }

    return 0;
}

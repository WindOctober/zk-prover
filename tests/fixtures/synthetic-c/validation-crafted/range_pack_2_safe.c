// This file is part of the SV-Benchmarks-style collection of verification tasks.
//
// SPDX-License-Identifier: GPL-3.0-or-later

extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "range_pack_2_safe.c", 2, "reach_error"); }

extern int __VERIFIER_nondet_int();

int main() {
    int a0 = __VERIFIER_nondet_int();
    int b0 = __VERIFIER_nondet_int();
    int c0 = __VERIFIER_nondet_int();
    int a1 = __VERIFIER_nondet_int();
    int b1 = __VERIFIER_nondet_int();
    int c1 = __VERIFIER_nondet_int();

    if (a0 < 0 || a0 > 20 || b0 < 0 || b0 > 20 || c0 < 0 || c0 > 20)
        return 0;
    if (a1 < 0 || a1 > 20 || b1 < 0 || b1 > 20 || c1 < 0 || c1 > 20)
        return 0;

    if (a0 > b0) {
        int sum0 = a0 + b0;
        if (c0 <= sum0)
            reach_error();
    }

    if (a1 > b1) {
        int sum1 = a1 + b1;
        if (c1 <= sum1)
            reach_error();
    }

    return 0;
}

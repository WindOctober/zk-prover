// This file is part of the SV-Benchmarks-style collection of verification tasks.
//
// SPDX-License-Identifier: GPL-3.0-or-later

extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "range_pack_8_safe.c", 2, "reach_error"); }

extern int __VERIFIER_nondet_int();

int main() {
    int a0 = __VERIFIER_nondet_int();
    int b0 = __VERIFIER_nondet_int();
    int c0 = __VERIFIER_nondet_int();
    int a1 = __VERIFIER_nondet_int();
    int b1 = __VERIFIER_nondet_int();
    int c1 = __VERIFIER_nondet_int();
    int a2 = __VERIFIER_nondet_int();
    int b2 = __VERIFIER_nondet_int();
    int c2 = __VERIFIER_nondet_int();
    int a3 = __VERIFIER_nondet_int();
    int b3 = __VERIFIER_nondet_int();
    int c3 = __VERIFIER_nondet_int();
    int a4 = __VERIFIER_nondet_int();
    int b4 = __VERIFIER_nondet_int();
    int c4 = __VERIFIER_nondet_int();
    int a5 = __VERIFIER_nondet_int();
    int b5 = __VERIFIER_nondet_int();
    int c5 = __VERIFIER_nondet_int();
    int a6 = __VERIFIER_nondet_int();
    int b6 = __VERIFIER_nondet_int();
    int c6 = __VERIFIER_nondet_int();
    int a7 = __VERIFIER_nondet_int();
    int b7 = __VERIFIER_nondet_int();
    int c7 = __VERIFIER_nondet_int();

    if (a0 < 0 || a0 > 20 || b0 < 0 || b0 > 20 || c0 < 0 || c0 > 20)
        return 0;
    if (a1 < 0 || a1 > 20 || b1 < 0 || b1 > 20 || c1 < 0 || c1 > 20)
        return 0;
    if (a2 < 0 || a2 > 20 || b2 < 0 || b2 > 20 || c2 < 0 || c2 > 20)
        return 0;
    if (a3 < 0 || a3 > 20 || b3 < 0 || b3 > 20 || c3 < 0 || c3 > 20)
        return 0;
    if (a4 < 0 || a4 > 20 || b4 < 0 || b4 > 20 || c4 < 0 || c4 > 20)
        return 0;
    if (a5 < 0 || a5 > 20 || b5 < 0 || b5 > 20 || c5 < 0 || c5 > 20)
        return 0;
    if (a6 < 0 || a6 > 20 || b6 < 0 || b6 > 20 || c6 < 0 || c6 > 20)
        return 0;
    if (a7 < 0 || a7 > 20 || b7 < 0 || b7 > 20 || c7 < 0 || c7 > 20)
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

    if (a2 > b2) {
        int sum2 = a2 + b2;
        if (c2 <= sum2)
            reach_error();
    }

    if (a3 > b3) {
        int sum3 = a3 + b3;
        if (c3 <= sum3)
            reach_error();
    }

    if (a4 > b4) {
        int sum4 = a4 + b4;
        if (c4 <= sum4)
            reach_error();
    }

    if (a5 > b5) {
        int sum5 = a5 + b5;
        if (c5 <= sum5)
            reach_error();
    }

    if (a6 > b6) {
        int sum6 = a6 + b6;
        if (c6 <= sum6)
            reach_error();
    }

    if (a7 > b7) {
        int sum7 = a7 + b7;
        if (c7 <= sum7)
            reach_error();
    }

    return 0;
}

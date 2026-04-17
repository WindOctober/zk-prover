// This file is part of the SV-Benchmarks-style collection of verification tasks.
//
// SPDX-License-Identifier: GPL-3.0-or-later

extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "equality_chain_bug.c", 2, "reach_error"); }

extern int __VERIFIER_nondet_int();

int main() {
    int a = __VERIFIER_nondet_int();
    int b = __VERIFIER_nondet_int();
    int c = __VERIFIER_nondet_int();

    if (a < -5 || a > 5 || b < -5 || b > 5 || c < -5 || c > 5)
        return 0;

    if (a == b) {
        if (b == c)
            reach_error();
    }

    return 0;
}

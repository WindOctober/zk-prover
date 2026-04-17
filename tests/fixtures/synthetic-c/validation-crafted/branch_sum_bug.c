// This file is part of the SV-Benchmarks-style collection of verification tasks.
//
// SPDX-License-Identifier: GPL-3.0-or-later

extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "branch_sum_bug.c", 2, "reach_error"); }

extern int __VERIFIER_nondet_int();

int main() {
    int a = __VERIFIER_nondet_int();
    int b = __VERIFIER_nondet_int();
    int c = __VERIFIER_nondet_int();

    if (a < 0 || a > 30 || b < 0 || b > 30 || c < 0 || c > 30)
        return 0;

    if (a >= 0) {
        if (a >= b) {
            int diff = a - b;
            if (c > diff) {
                if (a < b)
                    reach_error();
            } else {
                if (c > diff)
                    reach_error();
            }
        } else {
            int total = a + c;
            if (a >= b)
                reach_error();
            if (c == 0 && total != a)
                reach_error();
        }
    } else {
        if (a >= 0)
            reach_error();
    }

    return 0;
}

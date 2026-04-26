// Source: SV-COMP c/loop-lit/bhmr2007.c.
// We restrict the nondeterministic loop bound to 0..3, unroll the loop, and
// use a deliberately false final invariant to retain a SAT bounded-loop case.

extern int __VERIFIER_nondet_int();
extern void reach_error();

int main() {
    int i = 0;
    int a = 0;
    int b = 0;
    int n = __VERIFIER_nondet_int();
    if (!(0 <= n && n <= 3)) {
        return 0;
    }

    if (i < n) {
        if (__VERIFIER_nondet_int()) {
            a = a + 1;
            b = b + 2;
        } else {
            a = a + 2;
            b = b + 1;
        }
        i = i + 1;
    }
    if (i < n) {
        if (__VERIFIER_nondet_int()) {
            a = a + 1;
            b = b + 2;
        } else {
            a = a + 2;
            b = b + 1;
        }
        i = i + 1;
    }
    if (i < n) {
        if (__VERIFIER_nondet_int()) {
            a = a + 1;
            b = b + 2;
        } else {
            a = a + 2;
            b = b + 1;
        }
        i = i + 1;
    }
    if (i < n) { reach_error(); }

    if (!(a + b + 1 == n + n + n)) {
        reach_error();
    }

    return 0;
}

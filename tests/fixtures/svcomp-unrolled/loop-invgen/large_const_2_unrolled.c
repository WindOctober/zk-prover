// Source: SV-COMP c/loop-invgen/large_const.c.
// We keep the small-bound branch of the original benchmark and unroll it twice.

extern int __VERIFIER_nondet_int();
extern void reach_error();

int main() {
    int c1 = 4000;
    int c2 = 2000;
    int c3 = 10000;
    int n = __VERIFIER_nondet_int();
    if (!(0 <= n && n < 2)) {
        return 0;
    }

    int k = 0;
    int i = 0;
    int v = 0;

    if (i < n) {
        i = i + 1;
        v = __VERIFIER_nondet_int();
        if (!(0 <= v && v <= 2)) {
            return 0;
        }
        if (v == 0) {
            k = k + c1;
        } else {
            if (v == 1) {
                k = k + c2;
            } else {
                k = k + c3;
            }
        }
    }
    if (i < n) {
        i = i + 1;
        v = __VERIFIER_nondet_int();
        if (!(0 <= v && v <= 2)) {
            return 0;
        }
        if (v == 0) {
            k = k + c1;
        } else {
            if (v == 1) {
                k = k + c2;
            } else {
                k = k + c3;
            }
        }
    }
    if (i < n) { reach_error(); }

    int j = 0;
    if (j < n) {
        if (!(k > 0)) { reach_error(); }
        j = j + 1;
        k = k - 1;
    }
    if (j < n) {
        if (!(k > 0)) { reach_error(); }
        j = j + 1;
        k = k - 1;
    }
    if (j < n) { reach_error(); }

    return 0;
}

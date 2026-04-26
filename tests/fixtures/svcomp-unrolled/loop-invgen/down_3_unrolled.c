// Source: SV-COMP c/loop-invgen/down.c.
// We restrict the nondeterministic loop bound to 0..3 and unroll both loops.

extern int __VERIFIER_nondet_int();
extern void reach_error();

int main() {
    int n = __VERIFIER_nondet_int();
    if (!(0 <= n && n <= 3)) {
        return 0;
    }

    int k = 0;
    int i = 0;

    if (i < n) { i = i + 1; k = k + 1; }
    if (i < n) { i = i + 1; k = k + 1; }
    if (i < n) { i = i + 1; k = k + 1; }
    if (i < n) { reach_error(); }

    int j = n;
    if (j > 0) {
        if (!(k > 0)) { reach_error(); }
        j = j - 1;
        k = k - 1;
    }
    if (j > 0) {
        if (!(k > 0)) { reach_error(); }
        j = j - 1;
        k = k - 1;
    }
    if (j > 0) {
        if (!(k > 0)) { reach_error(); }
        j = j - 1;
        k = k - 1;
    }
    if (j > 0) { reach_error(); }

    return 0;
}

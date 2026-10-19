from sage.all import ZZ, Zmod, PolynomialRing

load('coppersmith.sage')

# 1. Basic API: a linear congruence (fast path).
R = PolynomialRing(Zmod(10001), 'x')
x = R.gen()
roots = small_roots(x - 7, (32,), m=2, d=2)
assert (ZZ(7),) in roots, ('linear root missing', roots)
print('[PASS] Linear congruence')

# 2. Force the lattice path instead of the linear shortcut.
stats = {}
roots = small_roots(x - 7, (32,), m=2, d=2,
                    precheck=False, stats=stats)
assert (ZZ(7),) in roots, ('lattice root missing', roots)
assert stats['lattice_shape'][0] > 0, stats
print('[PASS] Lattice-based recovery')

# 3. Nonlinear Coppersmith-style example from the v7 regression corpus.
f = x**3 + 10*x**2 + 5000*x - 222
roots = small_roots(f, (8,), m=3, d=3)
assert (ZZ(4),) in roots, ('cubic root missing', roots)
assert f(4) == 0
print('[PASS] Cubic polynomial')

# 4. One regression check for invalid bounds.
try:
    small_roots(x - 7, (0,))
    raise AssertionError('invalid bounds were accepted')
except ValueError:
    pass
print('[PASS] Input validation')
print('All smoke tests passed.')

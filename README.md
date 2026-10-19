## Usage

Download [`coppersmith.sage`](coppersmith.sage) and put it next to your Sage script:

```sage
load('coppersmith.sage')

R = PolynomialRing(Zmod(10001), 'x')
x = R.gen()

f = x**3 + 10*x**2 + 5000*x - 222
print(small_roots(f, (8,), m=3, d=3))  # includes (4,)
```


- `f`: a polynomial over `Zmod(N)`.
- `bounds`: one positive integer per *active* variable, in `f.variables()` order.
- `m`: maximum power of the input polynomial used to build shifts.
- `d`: number of monomial shifts per variable (defaults to `f.degree()`).

Returns a list of integer tuples, or `[]` if no root was recovered. Additional optional keyword arguments are documented in `coppersmith.sage`, but are **not needed** for normal use.



## Notes

- The multivariate construction is **heuristic**. It may fail even when a small root exists, and it is not guaranteed to find all roots.
- A candidate may satisfy the polynomial modulo a **proper divisor of N** rather than modulo all of N. Verify which modulus condition your application requires.
- Bounds influence lattice scaling; they are not strict output filters.

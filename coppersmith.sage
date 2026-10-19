import itertools as _cs_itertools
import time as _cs_time
from math import gcd as _cs_gcd
from sage.all import ZZ, QQ, Sequence, PolynomialRing, polygens, matrix, vector
from sage.rings.polynomial.polynomial_element import Polynomial as _CSUnivariate
from sage.rings.polynomial.multi_polynomial_sequence import PolynomialSequence as _CSPolynomialSequence


def _cs_positive_integer(value, name):
    try:
        converted = ZZ(value)
        if converted != value or converted < 1:
            raise ValueError()
    except (TypeError, ValueError, ArithmeticError):
        raise ValueError(name + ' must be a positive integer')
    return int(converted)


def _cs_prepare(f, bounds, m, d):
    # Work in a genuine multivariate ring, even if the caller passed f in R[x].
    if isinstance(f, _CSUnivariate):
        (x,) = polygens(f.base_ring(), f.variable_name(), 1)
        f = f(x)
    if not hasattr(f, 'variables') or not hasattr(f, 'change_ring'):
        raise TypeError('expected a polynomial over Zmod(N)')
    if not f or f.is_constant():
        raise ValueError('f must be nonconstant')
    R = f.base_ring()
    try:
        N = ZZ(R.cardinality())
    except (AttributeError, TypeError, ValueError, OverflowError):
        raise ValueError('coefficient ring must be Zmod(N)')
    if N <= 1:
        raise ValueError('modulus must be > 1')
    try:
        # Reject e.g. arbitrary finite extension fields, despite their finite cardinality.
        if ZZ(R.characteristic()) != N:
            raise ValueError('coefficient ring must be Zmod(N)')
    except (AttributeError, TypeError):
        raise ValueError('coefficient ring must be Zmod(N)')
    active = tuple(f.variables())
    try:
        bounds = tuple(ZZ(v) for v in bounds)
    except (TypeError, ValueError) as exc:
        raise ValueError('bounds must contain integers') from exc
    if len(bounds) != len(active) or any(v <= 0 for v in bounds):
        raise ValueError('provide one positive bound for each active variable')
    m = _cs_positive_integer(m, 'm')
    d = _cs_positive_integer(f.degree() if d is None else d, 'd')

    # Z/nZ is not necessarily a field. Polynomial division by a unit may fail
    # on composite n: multiply every coefficient by its inverse instead.
    # Prefer an existing coefficient 1 to avoid changing the integer lift.
    coeffs = tuple(f.coefficients())
    unit = next((c for c in coeffs if c == R(1)), None)
    if unit is None:
        unit = next((c for c in coeffs if _cs_gcd(int(ZZ(c)), int(N)) == 1), None)
    if unit is None:
        raise ValueError('no invertible polynomial coefficient modulo N')
    try:
        unit_inverse = unit ** -1
        f_normalized = f.map_coefficients(lambda a: a * unit_inverse)
        lifted = f_normalized.change_ring(ZZ)
    except (AttributeError, ArithmeticError, TypeError, ValueError) as exc:
        raise ValueError('cannot lift/normalize polynomial over this ring') from exc
    # Do not leave inactive parent generators in the recovery ideal: a polynomial
    # using x and z inside ZZ[x,y,z] must produce a *two*-variable ideal.
    # Compact only when needed, leaving the legacy ordering untouched otherwise.
    if lifted.parent().ngens() != len(active):
        original_gens = tuple(str(v) for v in lifted.parent().gens())
        wanted = tuple(str(v) for v in active)
        indices = tuple(original_gens.index(v) for v in wanted)
        compact = PolynomialRing(ZZ, len(wanted), names=wanted, order='degrevlex')
        compact_coeffs = {}
        for exp, coeff in lifted.dict().items():
            key = tuple(int(exp[j]) for j in indices)
            compact_coeffs[key] = compact_coeffs.get(key, ZZ(0)) + ZZ(coeff)
        lifted = compact(compact_coeffs)
    return f, lifted, active, bounds, N, m, d


def _cs_validate(original, active, values, modulus):
    """Check the *original* modular equation, incl. nontrivial divisor cases.

    A gcd > 1 establishes a congruence modulo some divisor of modulus; it does
    NOT establish a Coppersmith beta bound. It is deliberately not filtered by
    caller-provided bounds: as in defund, bounds only affect lattice scaling.
    """
    coords = {str(g): ZZ(v) for g, v in zip(active, values)}
    full = [coords.get(str(g), ZZ(0)) for g in original.parent().gens()]
    residue = ZZ(original(*full))
    divisor = ZZ(_cs_gcd(int(residue), int(modulus)))
    return divisor > 1, divisor


def _cs_integer_roots(poly, name):
    """Convert a univariate-like multivariate QQ polynomial by exponents.

    This avoids relying on Sage-specific univariate_polynomial() coercions or
    whether the ambient ring has one or several generators.
    """
    if not hasattr(poly, 'dict') or not hasattr(poly, 'parent'):
        return []
    parent = poly.parent()
    if not hasattr(parent, 'gens'):
        return []
    gs = tuple(parent.gens())
    labels = [str(g) for g in gs]
    if str(name) not in labels:
        return []
    idx = labels.index(str(name))
    coefficients = {}
    for powers, coeff in poly.dict().items():
        # Univariate Sage polynomial dictionaries use an integer exponent;
        # multivariate ones use an exponent tuple/ETuple.
        try:
            len(powers)
        except TypeError:
            powers = (int(powers),)
        if any(int(powers[j]) != 0 for j in range(len(gs)) if j != idx):
            return []
        degree = int(powers[idx])
        coefficients[degree] = QQ(coeff)
    P = PolynomialRing(QQ, str(name))
    h = P(coefficients)
    if h.is_constant():
        return []
    if h.degree() == 1:
        root = -h[0]/h[1]
        return [ZZ(root)] if root in ZZ else []
    return [ZZ(r) for r, _ in h.roots(ring=ZZ)]


def _cs_triangular_bivariate(basis, pr, record):
    """Compatibility wrapper for the two-variable helper from v5."""
    if pr.ngens() != 2:
        return False
    return _cs_triangular_integer(basis, pr, record)


def _cs_triangular_integer(basis, pr, record):
    """Enumerate finite integer fibers of a zero-dimensional lex basis.

    True means every branch was handled, including empty integer varieties.
    False requests Sage's variety fallback. Rational noninteger coordinates
    are never rounded, and every emitted point satisfies the full basis.
    """
    basis = tuple(basis)
    gens = tuple(pr.gens())

    def descend(equations, remaining, assigned):
        equations = [h for h in equations if h]
        if any(h.is_constant() for h in equations):
            return True
        if not remaining:
            point = tuple(assigned[g] for g in gens)
            if all(h(*point) == 0 for h in basis):
                record(point)
            return True
        choices = []
        for h in equations:
            variables = h.variables()
            if len(variables) == 1:
                choices.append((h, variables[0]))
        if not choices:
            return False
        h, variable = min(choices, key=lambda item: item[0].degree(item[1]))
        rest = tuple(g for g in remaining if g != variable)
        complete = True
        for value in _cs_integer_roots(h, variable):
            next_assigned = dict(assigned)
            next_assigned[variable] = value
            specialized = [h.subs({variable: value}) for h in equations]
            if not descend(specialized, rest, next_assigned):
                complete = False
        return complete

    return descend(basis, gens, {})


def _cs_resultant_pairs(rows, poly_ring, record, counters, budget=6):
    """Conservative bivariate shortcut using Sage resultants; no extra packages.

    Preserve the low-degree pair order, then try at most two degree-5/6 pairs
    within the same total budget. The extra path has a coefficient-bit guard.
    Unsupported/unsuccessful cases retain the incremental ideal fallback.
    """
    if poly_ring.ngens() != 2:
        return False
    x, y = poly_ring.gens()
    pool = [p for p in rows if p and not p.is_constant()
            and 1 < p.total_degree() <= 4][:5]
    pairs = [(f, g, False) for f, g in _cs_itertools.combinations(pool, 2)]
    higher = []
    for h in rows:
        if 4 < h.total_degree() <= 6 and all(
                max(c.numerator().nbits(), c.denominator().nbits()) <= 4096
                for c in h.coefficients()):
            higher.append(h)
            if len(higher) == 3:
                break
    extra = []
    # Prefer an existing low-degree eliminant when available, then high pairs.
    for f in pool[:2]:
        extra.extend((f, g, True) for g in higher)
    extra.extend((f, g, True) for f, g in _cs_itertools.combinations(higher, 2))
    pairs.extend(extra[:2])
    attempted = 0
    for f, g, high_degree in pairs:
        if attempted >= budget:
            break
        attempted += 1
        counters['resultant_pairs'] += 1
        if high_degree:
            counters['higher_resultant_pairs'] = counters.get('higher_resultant_pairs', 0) + 1
        try:
            res = f.resultant(g, x)
            for y0 in _cs_integer_roots(res, y):
                fx = f.subs({y: y0})
                gx = g.subs({y: y0})
                # A gcd removes noncommon roots; it also handles fx == 0.
                for x0 in _cs_integer_roots(fx.gcd(gx), x):
                    if f(x0, y0) == 0 and g(x0, y0) == 0 and record((x0, y0)):
                        return True
        except (ArithmeticError, ValueError, TypeError, NotImplementedError,
                RuntimeError, AttributeError, ZeroDivisionError):
            continue
    return False




def _cs_bivariate_linear_pairs(rows, pr, record, counters, budget=16):
    """Solve one linear + one low-degree equation by exact substitution.

    This avoids computing an ideal for common reduced-lattice outputs.
    It only returns *integer* roots, checks both equations and asks record()
    to validate the original modular relation. Failures fall back to ideals.
    """
    if pr.ngens() != 2:
        return False
    x, y = pr.gens()
    linear = [h for h in rows if h and h.total_degree() == 1][:6]
    nonlinear = [h for h in rows if h and 1 < h.total_degree() <= 6][:10]
    attempts = 0
    for h in linear:
        a = QQ(h.monomial_coefficient(x))
        b = QQ(h.monomial_coefficient(y))
        c = QQ(h.constant_coefficient())
        if not a and not b:
            continue
        for g in nonlinear:
            if attempts >= budget:
                return False
            attempts += 1
            counters['linear_pair_attempts'] += 1
            try:
                if a:
                    reduced = g.subs({x: (-b*y-c)/a})
                    for y0 in _cs_integer_roots(reduced, y):
                        x0 = (-b*QQ(y0)-c)/a
                        if x0 in ZZ and h(x0, y0) == 0 and g(x0, y0) == 0:
                            if record((ZZ(x0), ZZ(y0))):
                                return True
                else:
                    reduced = g.subs({y: (-a*x-c)/b})
                    for x0 in _cs_integer_roots(reduced, x):
                        y0 = (-a*QQ(x0)-c)/b
                        if y0 in ZZ and h(x0, y0) == 0 and g(x0, y0) == 0:
                            if record((ZZ(x0), ZZ(y0))):
                                return True
            except (ArithmeticError, TypeError, ValueError, RuntimeError,
                    NotImplementedError, ZeroDivisionError, AttributeError):
                continue
    return False

def _cs_find_roots(rows, original, active, modulus, root_method, counters,
                   max_ideal_rows=None, min_divisor_bits=None, bounds=None):
    names = tuple(str(x) for x in active)
    pr = rows[0].parent() if rows else None
    if pr is None:
        return []
    gens = tuple(pr.gens())
    # Mapping output candidates to original polynomial order is name-based.
    answer = []
    found = set()

    def record(candidate):
        try:
            # Sage ZZ rejects nonintegral rationals: no silent rounding.
            candidate = tuple(ZZ(v) for v in candidate)
            if len(candidate) != len(names):
                return False
            if candidate in found:
                return True
            counters['candidates_tested'] += 1
            valid, divisor = _cs_validate(original, active, candidate, modulus)
            if min_divisor_bits is not None and divisor.nbits() < min_divisor_bits:
                valid = False
            if valid:
                found.add(candidate)
                answer.append(candidate)
                counters['accepted_roots'] += 1
                counters['proper_divisor_roots'] += int(divisor != modulus)
                return True
        except (ArithmeticError, TypeError, ValueError):
            return False
        return False

    if root_method == 'auto' and len(names) == 1:
        # One variable: integer factorization is much cheaper than an ideal.
        for h in rows:
            for r in _cs_integer_roots(h, names[0]):
                record((r,))
        return sorted(answer)

    if root_method == 'auto':
        if len(names) == 2 and original.total_degree() > 1 and original.is_homogeneous():
            try:
                if _cs_homogeneous_gcd(rows, pr, bounds, record, counters):
                    return sorted(answer)
            except (ArithmeticError, RuntimeError, TypeError, ValueError,
                    NotImplementedError, AttributeError):
                pass
        try:
            if _cs_newton_integer(rows, pr, bounds, record, counters):
                return sorted(answer)
        except (ArithmeticError, RuntimeError, TypeError, ValueError,
                NotImplementedError, AttributeError):
            pass
        # An overdetermined linear system can be solved directly over QQ.
        eqs = []
        for h in rows:
            if h.total_degree() != 1:
                continue
            coeffs = [QQ(h.monomial_coefficient(g)) for g in gens]
            offset = -QQ(h.constant_coefficient())
            if len(eqs) < len(names):
                eqs.append((coeffs, offset))
            else:
                # Add only an independent row, or test a consistent result.
                A = matrix(QQ, [q[0] for q in eqs])
                if matrix(QQ, [q[0] for q in eqs] + [coeffs]).rank() > A.rank():
                    eqs.append((coeffs, offset))
            if len(eqs) >= len(names):
                A = matrix(QQ, [v for v, _ in eqs])
                if A.rank() == len(names):
                    try:
                        candidate = A.solve_right(vector(QQ, [v for _, v in eqs]))
                        if record(candidate):
                            return sorted(answer)
                    except (ArithmeticError, TypeError, ValueError):
                        pass

        # Restrict this shortcut to low-degree systems to prevent runaway costs.
        # The original incremental ideal route always remains the fallback.
        if len(names) == 2:
            if _cs_bivariate_linear_pairs(rows, pr, record, counters):
                return sorted(answer)
            if _cs_resultant_pairs(rows, pr, record, counters):
                return sorted(answer)

    system = _CSPolynomialSequence([], pr)
    for h in rows:
        if max_ideal_rows is not None and len(system) >= max_ideal_rows:
            break
        if not h or h.is_constant():
            continue
        system.append(h)
        if len(system) < len(names):
            continue
        counters['ideal_dimension_calls'] += 1
        try:
            I = system.ideal()
            dim = I.dimension()
            if dim < 0:
                system.pop()
                continue
            if dim == 0:
                if root_method == 'auto' and pr.ngens() >= 2:
                    counters['triangular_calls'] = counters.get('triangular_calls', 0) + 1
                    try:
                        handled = _cs_triangular_integer(I.groebner_basis(), pr, record)
                    except (ArithmeticError, RuntimeError, TypeError, ValueError,
                            NotImplementedError, AttributeError):
                        handled = False
                    if handled:
                        return sorted(answer)
                counters['variety_calls'] += 1
                for root in I.variety(ring=ZZ):
                    record(tuple(root[g] for g in gens))
                if answer:
                    return sorted(answer)
        except (ArithmeticError, RuntimeError, TypeError, ValueError, NotImplementedError):
            # May fail for some non-zero-dimensional or exceptionally large ideals.
            # A failure is not evidence that there are no small roots.
            system.pop()
    return sorted(answer)


def _cs_make_shifts(f, active, bounds, N, m, d):
    """Cache polynomial powers, N powers and monomial powers."""
    P = f.parent()
    basepowers = [P.one()]
    for _ in range(m):
        basepowers.append(basepowers[-1] * f)
    npowers = [ZZ(1)]
    for _ in range(m):
        npowers.append(npowers[-1] * N)
    gens = {str(g): g for g in P.gens()}
    monomials = []
    powtable = [[gens[str(g)] ** k for k in range(d)] for g in active]
    for indices in _cs_itertools.product(range(d), repeat=len(active)):
        term = P.one()
        for powers, exponent in zip(powtable, indices):
            term *= powers[exponent]
        monomials.append(term)
    shifts = []
    for i in range(m + 1):
        base = npowers[m-i] * basepowers[i]
        shifts.extend(base * shift for shift in monomials)
    return shifts


def _cs_make_matrix(shifts, f, active, bounds):
    seq = Sequence(shifts, f.parent())
    if hasattr(seq, 'coefficients_monomials'):
        B, monos = seq.coefficients_monomials()
    else:
        B, monos = seq.coefficient_matrix()
    allnames = [str(g) for g in f.parent().gens()]
    indices = [allnames.index(str(g)) for g in active]
    factors = []
    for mono in monos:
        exps = mono.exponents()[0]
        scale = ZZ(1)
        for j, bound in zip(indices, bounds):
            scale *= bound ** int(exps[j])
        factors.append(scale)
    for j, scale in enumerate(factors):
        B.rescale_col(j, scale)
    return B, list(monos), factors



def _cs_make_matrix_direct(f, active, bounds, N, m, d,
                           max_dimension=None, max_cells=None, selected_rows=None):
    """Build the *same* weighted lattice without materializing shift polynomials.

    Two passes: discover monomial support, then populate a sparse matrix.
    Keeps only powers of f and coefficient dictionaries in memory, rather
    than O((m+1)*d**variables) full Sage polynomial objects / row dicts.
    """
    P = f.parent()
    ngen = P.ngens()
    names = [str(g) for g in P.gens()]
    indices = [names.index(str(x)) for x in active]
    zero = (0,) * ngen
    powers = [P.one()]
    for _ in range(m):
        powers.append(powers[-1] * f)
    npowers = [ZZ(1)]
    for _ in range(m):
        npowers.append(npowers[-1] * N)
    base_terms = [
        [(tuple(map(int, exp)), ZZ(coeff) * npowers[m-i])
         for exp, coeff in powers[i].dict().items() if coeff]
        for i in range(m + 1)
    ]
    offsets = []
    for shift in _cs_itertools.product(range(d), repeat=len(active)):
        v = list(zero)
        for idx, exponent in zip(indices, shift):
            v[idx] = exponent
        offsets.append(tuple(v))

    support = set()
    for terms in base_terms:
        for offset in offsets:
            for exp, _ in terms:
                support.add(tuple(a+b for a,b in zip(exp, offset)))
            if max_dimension is not None and len(support) > max_dimension:
                raise ValueError('lattice dimensions exceed max_dimension')
            if max_cells is not None and len(support) * (m+1) * len(offsets) > max_cells:
                raise ValueError('lattice cells exceed max_cells')

    # This is the term order used by Sage Sequence.coefficients_monomials.
    mono_pairs = [(P({exp: ZZ(1)}), exp) for exp in support]
    mono_pairs.sort(key=lambda pair: pair[0], reverse=True)
    monomials = [mono for mono, _ in mono_pairs]
    exponents = [exp for _, exp in mono_pairs]
    column_index = {exp: j for j, exp in enumerate(exponents)}
    scales = {}
    for exp in exponents:
        scale = ZZ(1)
        for idx, bound in zip(indices, bounds):
            scale *= bound**exp[idx]
        scales[exp] = scale
    factors = [scales[exp] for exp in exponents]
    nrows = (m + 1) * len(offsets)
    ncols = len(monomials)
    if max_dimension is not None and max(nrows, ncols) > max_dimension:
        raise ValueError('lattice dimensions exceed max_dimension')
    if max_cells is not None and nrows * ncols > max_cells:
        raise ValueError('lattice cells exceed max_cells')
    lookup = None if selected_rows is None else {int(source): target
                for target, source in enumerate(selected_rows)}
    built_rows = nrows if lookup is None else len(selected_rows)
    B = matrix(ZZ, built_rows, ncols, sparse=True)
    nnz, source_row = 0, 0
    for terms in base_terms:
        for offset in offsets:
            row = source_row if lookup is None else lookup.get(source_row)
            source_row += 1
            if row is None:
                continue
            for exp, coeff in terms:
                key = tuple(a+b for a,b in zip(exp, offset))
                B[row, column_index[key]] = coeff * scales[key]
                nnz += 1
    return B, monomials, factors, nnz


def _cs_reconstruct(reduced, monomials, factors, parent, verify=False):
    """Unscale exactly, take primitive parts and discard duplicate equations.

    Every input column is a multiple of its scale; integral LLL row operations
    preserve that divisibility. Dividing an equation by its integer content
    preserves its rational/integer zero set, independently of norm heuristics.
    """
    powers = [tuple(map(int, mon.exponents()[0])) for mon in monomials]
    rows, seen = [], set()
    for row in reduced:
        terms, content = {}, ZZ(0)
        for j, c in enumerate(row):
            if not c:
                continue
            if verify and c % factors[j]:
                raise AssertionError('reduced column is not divisible by its scale')
            coeff = c // factors[j]
            terms[powers[j]] = coeff
            if content != 1:
                content = content.gcd(coeff)
        if not terms or not any(any(exp) for exp in terms):
            continue
        # Recovery uses lex order, so the largest exponent is the leading term.
        if terms[max(terms)] < 0:
            content = -content
        if content != 1:
            terms = {exp: coeff // content for exp, coeff in terms.items()}
        key = frozenset(terms.items())
        if key not in seen:
            seen.add(key)
            rows.append(parent(terms))
    return rows


def _cs_verify_matrix(direct, original):
    """Strict development check independent of monomial column ordering."""
    A, a_monos, a_factors, _ = direct
    B, b_monos, b_factors = original
    if A.nrows() != B.nrows() or A.ncols() != B.ncols():
        raise AssertionError('direct/reference matrix shapes differ')
    lookup = {tuple(map(int, v.exponents()[0])): i
              for i, v in enumerate(b_monos)}
    for j, mon in enumerate(a_monos):
        exps = tuple(map(int, mon.exponents()[0]))
        k = lookup[exps]
        if a_factors[j] != b_factors[k]:
            raise AssertionError('direct/reference scale mismatch')
        for i in range(A.nrows()):
            if A[i, j] != B[i, k]:
                raise AssertionError('direct/reference coefficient mismatch')
    return True


def _cs_quick_roots(original, lifted, active, bounds, N, min_divisor_bits=None):
    """Solve a one-variable linear congruence without building a lattice.

    Only when x coefficient is invertible modulo N; higher-degree cases
    deliberately fall back without invoking expensive integer factorization.
    """
    if len(active) != 1 or lifted.degree() != 1:
        return []
    x = active[0]
    exps_by_name = [str(g) for g in lifted.parent().gens()]
    index = exps_by_name.index(str(x))
    cs = {}
    for exp, coeff in lifted.dict().items():
        if any(exp[j] for j in range(len(exp)) if j != index):
            return []
        cs[int(exp[index])] = ZZ(coeff)
    a, b = cs.get(1, ZZ(0)), cs.get(0, ZZ(0))
    if _cs_gcd(int(a), int(N)) != 1:
        return []
    try:
        r = ZZ((-int(b) * pow(int(a), -1, int(N))) % int(N))
    except ValueError:
        return []
    candidates = sorted(set([r, r - N]))
    roots = []
    for v in candidates:
        if abs(v) >= bounds[0]:
            continue
        valid, divisor = _cs_validate(original, active, (v,), N)
        if valid and (min_divisor_bits is None or divisor.nbits() >= min_divisor_bits):
            roots.append((v,))
    return roots


def _cs_basis_rows(f, m, d, active=None):
    """Delete only shifts generated integrally by other shifts in this box.

    For leading term c*x^u, c = +/-1, write
    c*g[i,a] = N*g[i+1,a-u] - sum_e a_e*g[i,a-u+e].
    The coordinate test keeps every RHS shift inside the original box.
    Same-layer replacements strictly decrease in the polynomial term order.
    Top-layer rows are retained, so this proves equality of Z row modules.
    """
    if f.leading_coefficient() not in (1, -1):
        return None
    P = f.parent()
    names = tuple(map(str, P.gens()))
    active = tuple(f.variables()) if active is None else tuple(active)
    indices = [names.index(str(g)) for g in active]
    u = tuple(map(int, f.exponents()[0]))
    degrees = tuple(int(f.degree(g)) for g in P.gens())
    redundant = []
    for powers in _cs_itertools.product(range(d), repeat=len(indices)):
        a = [0] * P.ngens()
        for j, power in zip(indices, powers):
            a[j] = power
        redundant.append(all(u[j] <= a[j] <= min(d-1, d-1+u[j]-degrees[j])
                             for j in range(P.ngens())))
    count = len(redundant)
    removed = m * sum(redundant)
    if removed < max(2, ((m+1)*count)//10):
        return None
    return [i*count+j for i in range(m+1) for j in range(count)
            if i == m or not redundant[j]]


def _cs_newton_integer(rows, pr, bounds, record, counters):
    """Bounded rounded Newton proposals, accepted only after exact checks.

    QQ arithmetic avoids floating precision choices. Two starts, eight steps,
    at most n+2 equations, bounded degree/coefficients and a coordinate guard.
    Failed or singular iterations leave all symbolic recovery paths available.
    Three-variable systems use the cheaper existing triangular route.
    """
    n = pr.ngens()
    if n not in (2, 4) or bounds is None or len(bounds) != n:
        return False
    pool = list(rows[:n+2])
    if len(pool) < n or any(not h or not 1 <= h.total_degree() <= 4 for h in pool):
        return False
    if all(h.total_degree() == 1 for h in pool) or all(not h.constant_coefficient() for h in pool):
        return False
    if any(max(c.numerator().nbits(), c.denominator().nbits()) > 8192
           for h in pool for c in h.coefficients()):
        return False
    derivatives = [[h.derivative(g) for g in pr.gens()] for h in pool]
    counters['newton_attempts'] = counters.get('newton_attempts', 0) + 1
    for start in (0, 1):
        point, seen = (ZZ(start),)*n, set()
        for _ in range(8):
            if point in seen:
                break
            seen.add(point)
            values = [h(*point) for h in pool]
            if not any(values):
                if record(point):
                    return True
                break
            jac = matrix(QQ, [[h(*point) for h in row] for row in derivatives])
            independent = list(jac.transpose().pivots())
            if len(independent) != n:
                break
            update = jac.matrix_from_rows(independent).solve_right(
                vector(QQ, [values[i] for i in independent]))
            point = tuple(ZZ((v-step).round()) for v, step in zip(point, update))
            counters['newton_steps'] = counters.get('newton_steps', 0) + 1
            if any(abs(v) >= 4*bound for v, bound in zip(point, bounds)):
                break
    return False


def _cs_homogeneous_gcd(rows, pr, bounds, record, counters):
    """Recover a primitive direction from a homogeneous linear common factor.

    Such a system can have a family of solutions; this returns valid directions,
    not a claim that a hidden pair is uniquely determined.
    """
    if pr.ngens() != 2 or bounds is None:
        return False
    x, y = pr.gens()
    pool = [h for h in rows[:8] if h and 2 <= h.total_degree() <= 8
            and all(max(c.numerator().nbits(), c.denominator().nbits()) <= 4096
                    for c in h.coefficients())][:4]
    for f, g in list(_cs_itertools.combinations(pool, 2))[:3]:
        counters['gcd_pairs'] = counters.get('gcd_pairs', 0) + 1
        common = f.gcd(g)
        if common.total_degree() != 1 or common.constant_coefficient():
            continue
        a, b = QQ(common.monomial_coefficient(x)), QQ(common.monomial_coefficient(y))
        denominator = a.denominator().lcm(b.denominator())
        px, py = -ZZ(b*denominator), ZZ(a*denominator)
        content = px.gcd(py)
        if not content:
            continue
        point = (px//content, py//content)
        if any(abs(v) >= bound for v, bound in zip(point, bounds)):
            continue
        accepted = False
        for candidate in (point, tuple(-v for v in point)):
            if common(*candidate) == 0 and record(candidate):
                accepted = True
        if accepted:
            return True
    return False


def small_roots(f, bounds, m=1, d=None, *, stats=None, root_method='auto',
                max_dimension=None, matrix_builder='direct', precheck=True,
                verify_matrix=False, max_cells=None, max_ideal_rows=None,
                min_divisor_bits=None, lll_algorithm=None, lll_delta=None):
    """Find modular small roots using Sage alone; four positional args as defund.

    Default auto recovery may remove provably redundant shifts in the box.
    If recovery returns no root, retry the complete original ordered family.
    Explicit LLL settings and non-auto recovery retain the full family.
    Bounds scale the lattice, as in earlier versions; symbolic recovery can
    return valid points outside those bounds. See README for divisor semantics.
    """
    if root_method not in ('auto', 'legacy', 'ideal'):
        raise ValueError("root_method must be 'auto', 'ideal', or 'legacy'")
    if matrix_builder not in ('direct', 'sequence'):
        raise ValueError("matrix_builder must be 'direct' or 'sequence'")
    for name, value in (('max_dimension', max_dimension), ('max_cells', max_cells),
                        ('max_ideal_rows', max_ideal_rows),
                        ('min_divisor_bits', min_divisor_bits)):
        if value is not None:
            try:
                converted = ZZ(value)
                if converted != value or converted < 1:
                    raise ValueError()
            except (TypeError, ValueError, ArithmeticError):
                raise ValueError(name + ' must be a positive integer or None')
    if lll_algorithm is not None and lll_algorithm not in (
            'fpLLL:wrapper', 'fpLLL:fast', 'fpLLL:heuristic',
            'fpLLL:proved', 'NTL:LLL', 'pari'):
        raise ValueError('unsupported Sage built-in LLL algorithm')
    if lll_delta is not None and not (0.25 < float(lll_delta) < 1):
        raise ValueError('lll_delta must be between 0.25 and 1')
    clock = _cs_time.perf_counter
    start = clock()
    f, lifted, active, bounds, N, m, d = _cs_prepare(f, bounds, m, d)
    t_prepare = clock()
    if stats is not None:
        stats.clear()
    shift_count = (m+1) * d**len(active)
    if max_dimension is not None and shift_count > int(max_dimension):
        raise ValueError('shift count exceeds max_dimension')
    if max_cells is not None and shift_count * d**len(active) > max_cells:
        raise ValueError('lattice cells exceed max_cells')
    stats_count = dict(candidates_tested=0, accepted_roots=0,
                       proper_divisor_roots=0, resultant_pairs=0, higher_resultant_pairs=0,
                       linear_pair_attempts=0, ideal_dimension_calls=0, variety_calls=0,
                       triangular_calls=0, newton_attempts=0, newton_steps=0,
                       gcd_pairs=0, lll_fallbacks=0)
    if precheck and root_method == 'auto':
        quick = _cs_quick_roots(f, lifted, active, bounds, N, min_divisor_bits)
        if quick:
            if stats is not None:
                stats_count.update(candidates_tested=len(quick), accepted_roots=len(quick))
                stats.update(dict(normalize_s=t_prepare-start, matrix_s=0.0,
                                  lll_s=0.0, reconstruct_s=0.0, preprocess_s=0.0,
                                  roots_s=clock()-t_prepare, matrix_nnz=0,
                                  matrix_builder=matrix_builder, shortcut='exact_univariate',
                                  total_s=clock()-start, lattice_shape=None, lll_shape=None,
                                  removed_shifts=0, shift_count=0, **stats_count))
            return quick

    selected = (_cs_basis_rows(lifted, m, d, active)
                if root_method == 'auto' and lll_algorithm is None and lll_delta is None
                else None)
    if matrix_builder == 'direct':
        B, monos, factors, nonzeros = _cs_make_matrix_direct(
            lifted, active, bounds, N, m, d,
            max_dimension=max_dimension, max_cells=max_cells, selected_rows=selected)
        if verify_matrix:
            shifts = _cs_make_shifts(lifted, active, bounds, N, m, d)
            ref_B, ref_monos, ref_factors = _cs_make_matrix(shifts, lifted, active, bounds)
            if selected is not None:
                ref_B = ref_B.matrix_from_rows(selected)
            _cs_verify_matrix((B, monos, factors, nonzeros), (ref_B, ref_monos, ref_factors))
            del shifts, ref_B, ref_monos, ref_factors
    else:
        shifts = _cs_make_shifts(lifted, active, bounds, N, m, d)
        B, monos, factors = _cs_make_matrix(shifts, lifted, active, bounds)
        del shifts
        if verify_matrix:
            _cs_verify_matrix(_cs_make_matrix_direct(lifted, active, bounds, N, m, d),
                              (B, monos, factors))
        if selected is not None:
            B = B.matrix_from_rows(selected)
        nonzeros = len(B.dict())
    t_matrix = clock()
    shape = (shift_count, B.ncols())
    lll_shape = B.dimensions()
    removed_shifts = shift_count-B.nrows()
    if max_dimension is not None and max(shape) > int(max_dimension):
        raise ValueError('lattice dimensions exceed max_dimension')
    if max_cells is not None and shape[0]*shape[1] > max_cells:
        raise ValueError('lattice cells exceed max_cells')

    # Keep Sage's default fpLLL wrapper and delta=0.99.
    dense = B.dense_matrix()
    del B
    preprocess_s = clock()-t_matrix
    if lll_algorithm is None and lll_delta is None:
        reduced = dense.LLL()
    else:
        params = {}
        if lll_algorithm is not None:
            params['algorithm'] = lll_algorithm
        if lll_delta is not None:
            params['delta'] = lll_delta
        reduced = dense.LLL(**params)
    del dense
    t_lll = clock()
    parent = PolynomialRing(QQ, len(lifted.parent().gens()),
                            names=tuple(str(g) for g in lifted.parent().gens()), order='lex')
    rows = _cs_reconstruct(reduced, monos, factors, parent, verify=verify_matrix)
    del reduced
    t_reconstruct = clock()
    result = _cs_find_roots(rows, f, active, N, root_method, stats_count,
                            max_ideal_rows=max_ideal_rows,
                            min_divisor_bits=min_divisor_bits, bounds=bounds)
    end = clock()
    matrix_s, lll_s = t_matrix-t_prepare, t_lll-t_matrix
    reconstruct_s, roots_s = t_reconstruct-t_lll, end-t_reconstruct
    if not result and selected is not None:
        # Equal Z spans do not imply identical reduced vectors or recovery.
        # Retry the complete family in the exact original order, once.
        stats_count['lll_fallbacks'] += 1
        tick = clock()
        B, monos, factors, _ = _cs_make_matrix_direct(
            lifted, active, bounds, N, m, d,
            max_dimension=max_dimension, max_cells=max_cells)
        matrix_s += clock()-tick
        tick = clock()
        lll_shape = B.dimensions()
        dense = B.dense_matrix()
        del B
        reduced = dense.LLL()
        del dense
        lll_s += clock()-tick
        tick = clock()
        rows = _cs_reconstruct(reduced, monos, factors, parent, verify=verify_matrix)
        del reduced
        reconstruct_s += clock()-tick
        tick = clock()
        result = _cs_find_roots(rows, f, active, N, root_method, stats_count,
                                max_ideal_rows=max_ideal_rows,
                                min_divisor_bits=min_divisor_bits, bounds=bounds)
        roots_s += clock()-tick
        end = clock()
    if stats is not None:
        stats.update(dict(normalize_s=t_prepare-start, matrix_s=matrix_s,
                          lll_s=lll_s, reconstruct_s=reconstruct_s, roots_s=roots_s,
                          preprocess_s=preprocess_s, total_s=end-start,
                          lattice_shape=shape, lll_shape=lll_shape,
                          removed_shifts=removed_shifts, matrix_nnz=nonzeros,
                          shift_count=shift_count, recovery_rows=len(rows),
                          shortcut=None, matrix_builder=matrix_builder,
                          lll_algorithm=lll_algorithm or 'fpLLL:wrapper',
                          lll_delta=lll_delta if lll_delta is not None else 0.99,
                          **stats_count))
    return result

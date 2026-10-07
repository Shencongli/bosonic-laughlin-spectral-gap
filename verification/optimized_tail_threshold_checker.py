"""Exact proof checks for the spherical tail at EVERY integer flux Q >= 0.

Only Python's standard library is used. The finite low-flux range is
exhaustive; the infinite range uses a proved rational interval derivative
bound, rather than finite-Q sampling. See optimized_tail_threshold.txt.
"""
from fractions import Fraction as F
from math import comb, prod
from pathlib import Path
import json

A = F(2, 27)
C9 = 30 * F(5, 9)**9
NU = F(1, 10**10)
H = F(1, 256)
NCAP = 32


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def factors(z, n):
    """Linear factors (c,d) representing g_z,n(x)/binom(z+n,z)."""
    numerator = [(F(2), F(1)), (A, F(1))]
    denominator = [(F(3), F(-(2*z-1))), (1+A, F(1))]
    for i in range(z):
        numerator += [(F(2), F(-i))]*2
        denominator += [(1+A, F(-i)), (F(3), F(-(z-1+i)))]
    for i in range(n):
        numerator += [(F(1), F(-(z+i)))]*2
        denominator += [(1+A, F(-(z+i))), (F(3), F(-(2*z+i)))]
    return numerator, denominator


def interval_term(z, n, endpoint=H):
    numerator, denominator = factors(z, n)
    nl = [min(c, c+d*endpoint) for c,d in numerator]
    nu = [max(c, c+d*endpoint) for c,d in numerator]
    dl = [min(c, c+d*endpoint) for c,d in denominator]
    du = [max(c, c+d*endpoint) for c,d in denominator]
    require(min(nl+dl)>0, f"factor positivity failed at {(z,n)}")
    lower = comb(z+n,z)*prod(nl)/prod(du)
    upper = comb(z+n,z)*prod(nu)/prod(dl)
    log_lower = (sum(d/(c+d*endpoint) for c,d in numerator)
                 - sum(d/c for c,d in denominator))
    derivative_lower = log_lower*(lower if log_lower>=0 else upper)
    at_zero = (comb(z+n,z)*prod(c for c,d in numerator)
               /prod(c for c,d in denominator))
    return lower, upper, derivative_lower, at_zero


def finite_sum(z, q):
    """Exact sum of g_z,n(1/q), 0 <= n <= min(NCAP,q-z)."""
    mq = A*q
    term = F(2*q+1,3*q-2*z+1)*(mq+1)/(mq+q+1)
    for i in range(z):
        term *= F((2*q-i)**2,1)/((mq+q-i)*(3*q-z+1-i))
    result = term
    for n in range(min(NCAP,q-z)):
        term *= (F((q-z-n)**2*(z+n+1),1)
                 /((mq+q-z-n)*(3*q-2*z-n)*(n+1)))
        result += term
    return result


def main():
    require(F(7,50)<C9 and F(13,100)<C9 and F(1,10)<C9,
            "reference margins failed")
    coarse = 3*(1+A)*F(29,36)**27/A
    require(coarse<F(13,100), "all-Q z >= 27 bound failed")

    terms = [interval_term(9,n) for n in range(NCAP+1)]
    derivative_lower = sum(t[2] for t in terms)
    value_at_zero = sum(t[3] for t in terms)
    require(derivative_lower>73, "uniform z=9 derivative bound failed")
    require(value_at_zero >= 2/(C9+NU), "z=9 endpoint budget failed")
    require(2/value_at_zero>C9, "unexpected endpoint relation")
    # Independent closed-form check of the x=0 sum.
    zero_by_series = (2/C9)*F(20,29)**10*sum(
        F(comb(n+9,9))*F(9,29)**n for n in range(NCAP+1))
    require(value_at_zero==zero_by_series, "endpoint identity failed")

    cap=C9+NU
    strengthened=[]
    for strong_threshold, derivative_floor, reduction in [
            (2500,F(681,2),F(77,20)),
            (3000,F(345),F(391,100)),
            (5000,F(353),F(4))]:
        strong_derivative_lower=sum(interval_term(9,n,F(1,strong_threshold))[2]
                                    for n in range(NCAP+1))
        require(strong_derivative_lower>derivative_floor,
                f"strong derivative bound failed at {strong_threshold}")
        margin=cap**2*derivative_floor-reduction*(2+derivative_floor*cap/strong_threshold)
        require(margin>=0, f"minus d/Q conversion failed at {strong_threshold}")
        require(cap-reduction/strong_threshold>F(13,100),
                f"other z ranges fail strengthened budget at {strong_threshold}")
        strengthened.append({
            'uniform_flux_floor':strong_threshold,
            'coefficient':'c9 + nu - d/Q',
            'd_exact':str(reduction),
            'derivative_lower_exact':str(strong_derivative_lower),
            'derivative_floor_exact':str(derivative_floor),
            'coefficient_conversion_margin_exact':str(margin)})

    other_intervals=[]
    for z in range(11,27,2):
        lower = sum(interval_term(z,n)[0] for n in range(NCAP+1))
        require(lower>20, f"uniform lower bound failed at z={z}")
        other_intervals.append({'z':z,'D_lower_exact':str(lower),
                                'D_lower_greater_than':'20'})

    # Exhaust ALL remaining relevant integer Q and odd z, not a sample.
    finite_count=0
    maximum_coefficient=F(0)
    worst_pair=None
    for q in range(9,256):
        for z in range(9,min(q,25)+1,2):
            lower = finite_sum(z,q)
            coefficient = 2/lower
            require(coefficient<F(7,50), f"finite block failed at {(q,z)}")
            if coefficient>maximum_coefficient:
                maximum_coefficient=coefficient
                worst_pair=(q,z)
            finite_count+=1
    require(finite_count==2151, "finite block coverage count is wrong")

    result={
        'status':'EXACT_ALL_INTEGER_FLUX_NEGATIVE_TAIL_CERTIFIED',
        'scope':'T9,Q <= (c9 + nu)(S4,Q + H_Q), every integer Q >= 0',
        'coherent_exponent':'M = (2/27) Q, with no integer rounding',
        'c9_exact':str(C9),
        'nu_exact':str(NU),
        'coefficient_exact':str(C9+NU),
        'infinite_flux_range':'all Q >= 256; exact interval x in [0,1/256]',
        'truncation':'0 <= n <= 32; omitted summands are nonnegative',
        'z9_derivative_lower_exact':str(derivative_lower),
        'z9_derivative_lower_greater_than':'73',
        'z9_endpoint_D_exact':str(value_at_zero),
        'z9_endpoint_coefficient_excess_exact':str(2/value_at_zero-C9),
        'z9_endpoint_budget_margin_exact':str(C9+NU-2/value_at_zero),
        'strengthened_certificates':strengthened,
        'higher_finite_z_interval_checks':other_intervals,
        'all_Q_z_ge_27_coefficient_upper_exact':str(coarse),
        'all_Q_z_ge_27_coefficient_less_than':'13/100',
        'finite_range':'all integers 9 <= Q <= 255, odd 9 <= z <= min(Q,25)',
        'exhaustive_finite_blocks':finite_count,
        'finite_coefficient_less_than':'7/50',
        'largest_finite_coefficient_exact':str(maximum_coefficient),
        'largest_finite_coefficient_at_Q_z':list(worst_pair),
        'Q_less_than_9':'C9,Q = T9,Q = 0 exactly',
    }
    path=Path(__file__).with_name('optimized_tail_threshold_results.json')
    path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if not k.endswith('_exact')
                      and k not in ('higher_finite_z_interval_checks',
                                    'strengthened_certificates')},indent=2))
    print('Strengthened bounds: ' + ', '.join(
        f"Q >= {r['uniform_flux_floor']}: c9 + nu - ({r['d_exact']})/Q"
        for r in strengthened))
    print('All interval endpoints, derivative bounds, and finite checks use exact Fraction arithmetic.')


if __name__=='__main__':
    main()

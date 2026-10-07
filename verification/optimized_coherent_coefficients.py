"""Exact rational, general-a coherent comparison coefficients.

Keep a fixed across all z that share a kernel. theta is only a proof
parameter and may vary with z. See optimized_coherent_threshold.txt.
"""
from fractions import Fraction as F


def _rational(value):
    if not isinstance(value, (int, F)):
        raise TypeError("Use int or Fraction, not floating-point input")
    return F(value)


def choose_theta(r, q0, a=None):
    """Smallest reciprocal-integer theta certified by the global bound."""
    a = F(1, 12 if r == 3 else 16) if a is None else _rational(a)
    if r not in (3, 4) or a <= 0:
        raise ValueError("Require r=3 or 4 and a>0")
    if q0 < 4/a:
        raise ValueError("This automatic theta choice requires q0>=4/a")
    m = 2
    while 2*(m+1)*m/a <= q0:
        m += 1
    return F(1, m)


def parameters(r, z, a=None, theta=None, q0=None):
    if r not in (3, 4) or not isinstance(z, int) or z < 0:
        raise ValueError("Require r=3 or 4 and an integer z>=0")
    a = F(1, 12 if r == 3 else 16) if a is None else _rational(a)
    if theta is None:
        if q0 is None:
            raise ValueError("Supply theta or q0")
        theta = choose_theta(r, q0, a)
    theta = _rational(theta)
    if a <= 0 or not 0 < theta < 1:
        raise ValueError("Require a>0 and 0<theta<1")
    h = r - 2
    k = z + h + 1
    kappa = F(r, 2)
    Z = F(z*(z-1), 2)
    b = a*kappa**2/(2*(1-theta))
    c = 2*k+b*k*(k+1)
    if r == 3:
        t = (1+F(3, 2)*a)**(-z-1)
    else:
        t = (1+a)**(-1)*(1+2*a)**(-z-1)
    return dict(r=r, z=z, a=a, theta=theta, h=h, k=k, kappa=kappa,
                Z=Z, b=b, c=c, t=t, cinf=1/(a**h*t),
                qloc=2*(1-theta)/(a*theta**2))


def coefficient(r, z, q, a=None, theta=None):
    """Exact valid comparison coefficient at q (not an asymptotic series)."""
    p = parameters(r, z, a=a, theta=theta, q0=q)
    if not isinstance(q, int) or q < max(z, p['qloc']) or q <= max(p['Z'], p['c']):
        raise ValueError("q does not meet all proof domain conditions")
    x = F(1, q)
    denominator = ((1+x/p['a'])**p['h']*(1+x/2)
                   *(1-p['Z']*x)*(1-p['c']*x))
    return p['cinf']/denominator


def uniform_coefficient(r, z, q0, a=None, theta=None):
    """Coefficient valid for every integer q>=q0, with the chosen fixed a.

    theta is fixed at its q0 choice when proving the uniform statement.
    Log-concavity of the denominator controls both endpoints even when
    the pointwise coefficient is not decreasing at small z.
    """
    p = parameters(r, z, a=a, theta=theta, q0=q0)
    at_q0 = coefficient(r, z, q0, a=p['a'], theta=p['theta'])
    return max(at_q0, p['cinf'])


def weighted_cost(r, errors, q0, a=None, theta=None):
    """Uniform lift coefficient for nonnegative degree-indexed errors.

    errors maps z to exact rational delta_z. All z share the same a.
    The result is max_z delta_z*C_z, not a sum over z.
    """
    costs = []
    for z, error in errors.items():
        error = _rational(error)
        if error < 0:
            raise ValueError("errors must be nonnegative")
        costs.append(error*uniform_coefficient(r, z, q0, a=a, theta=theta))
    return max(costs, default=F(0))


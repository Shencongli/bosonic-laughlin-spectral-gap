"""Exact scalar checks for the uniform spherical negative-tail threshold."""
from fractions import Fraction as F


def check(name, lhs, rhs):
    if lhs > rhs:
        raise AssertionError(f"{name}: {lhs} > {rhs}")
    print(f"PASS {name}")
    print(f"  left = {lhs}")
    print(f"  right = {rhs}")
    print(f"  nonnegative exact difference = {rhs-lhs}")


def main():
    q0 = 10_000_000
    a, r, t, rho = F(2, 27), F(9, 10), F(9, 29), F(29, 36)
    c9 = 30 * F(5, 9)**9
    astar = F(2, 1)/r * (F(1, 2)/r)**9
    assert r == 2/(2+3*a)
    assert t == 1/(3*(1+a))
    assert rho == 3*(1+a)/4
    assert astar == a*c9
    assert c9 == F(19531250,129140163)
    check("relative limiting tail for every 0 <= z <= 32",
          F(20, 9)**33 * F(9, 11) * F(18, 29)**101, F(1, 1000))
    check("coarse tail for every z >= 33",
          3 * F(29, 27) * F(29, 36)**33, astar)
    check("finite Q product loss for every Q >= Q0",
          F(9900, q0), F(1, 1000))
    check("combining two relative losses",
          F(499, 500), F(999, 1000)**2)
    check("marginal correction for every Q >= Q0",
          1 + F(1, q0), F(1001, 1000))
    check("final coefficient budget", F(1001, 998)*c9, c9+F(1, 2000))
    margin = F(1, 2000) - F(3, 998)*c9
    assert margin == F(1949063779,42960627558000)
    assert q0 >= 100
    print(f"ALL EXACT CHECKS PASSED; uniform threshold Q0 = {q0}")


if __name__ == "__main__":
    main()

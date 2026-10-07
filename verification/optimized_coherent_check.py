"""Exact scalar audit for optimized_coherent_threshold.txt; no external packages."""
from fractions import Fraction as F

CASES = [
    (3, 8, F(1, 12), F(1, 14), 35, 4505),
    (3, 8, F(1, 12), F(1, 7), 36, 1254),
    (3, 8, F(1, 12), F(1, 5), 38, 544),
    (4, 16, F(1, 16), F(1, 12), 2100, 4330),
    (4, 16, F(1, 16), F(1, 8), 2200, 2107),
]

for r, degree, a, theta, target, threshold in CASES:
    h = r - 2
    k = degree + h + 1
    kappa = F(r, 2)
    Z = F(degree * (degree - 1), 2)
    b = a * kappa**2 / (2 * (1 - theta))
    c = 2 * k + b * k * (k + 1)
    t = F(8, 9)**9 if r == 3 else F(16, 17) * F(8, 9)**17
    cinf = 1 / (a**h * t)

    def coefficient(q):
        x = F(1, q)
        denominator = (1 + x/a)**h * (1 + x/2) * (1 - Z*x) * (1 - c*x)
        return cinf / denominator

    assert 0 < theta < 1
    assert threshold >= degree
    assert threshold > max(Z, c)
    assert threshold >= 2*(1-theta)/(a*theta**2)
    assert Z + c > h/a + F(1, 2)  # proves monotonicity for every larger Q
    assert coefficient(threshold) <= target
    assert coefficient(threshold - 1) > target
    print(f"PASS r={r}, cutoff={degree}, theta={theta}, target={target}, Q>={threshold}")
    print(f"  Z={Z}, c={c}; exact positive target margin={target-coefficient(threshold)}")
    print(f"  decimal diagnostic coefficient={float(coefficient(threshold)):.12f}")

print("ALL EXACT CHECKS PASSED. Original 35/2100 constants hold simultaneously for Q>=4505.")


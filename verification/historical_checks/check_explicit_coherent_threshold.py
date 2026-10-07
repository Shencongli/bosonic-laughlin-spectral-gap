"""Exact scalar checks for explicit_coherent_threshold.txt (standard library)."""
from fractions import Fraction as F

Q0 = 10**50
K = 1024
B = 4096
delta = F(1, 10**6)

# Uniform, explicit estimates proved in the companion note.
assert Q0 >= 2**24
assert K * (32 + K) < 3 * 2**19
assert 6 * B**1 * 64 + 10 * B < 2**22
assert 2**9 + K * 2**22 < 2**33
assert K + 1 < 2**11
assert F(33, 32) ** 32 > 2
block_error_bound = F(2**135, Q0) + F(66, 2**32)
assert block_error_bound < delta

# A rational upper bound on 1 + 1/Q, valid already for Q >= 10^4.
rho = F(10001, 10000)
assert 1 + F(1, Q0) <= rho
t3 = F(8, 9) ** 9
t4 = F(16, 17) * F(8, 9) ** 17
coefficient3 = 12 * rho / (t3 - delta)
coefficient4 = 256 * rho**2 / (t4 - delta)
assert coefficient3 < 35
assert coefficient4 < 2100

print("PASS: all scalar checks use exact rational arithmetic.")
print("Q0 = 10^50; descendant cutoff K = 1024.")
print("Retained-block norm error bound < 10^-6.")
print(f"Three-body upper coefficient: {float(coefficient3):.12f} < 35")
print(f"Four-body upper coefficient: {float(coefficient4):.12f} < 2100")



"""Exact arithmetic checks for explicit_head_threshold.txt.

The shifted planar certificate is replayed separately by
exact_shifted_certificate.py. This script checks row bounds, all scalar
budgets, and independently recomputes the finite planar half-gap.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
import exact_relative_blocks as E

BASE = Path(__file__).parent
rows = json.loads((BASE/'exact_shifted_certificate_rows.json').read_text())
total_rows = 0
maximum_integer = 0
for t in range(4):
    rec = rows[str(t)]
    assert rec['common_denominator'] == 10**12
    terms = rec['terms']
    expected = [None] + [[p,T-p] for T in range(t,9) for p in range(T+1)]
    assert terms == expected and len(terms) <= 46
    total_rows += len(rec['integer_scaled_rows'])
    for row in rec['integer_scaled_rows']:
        assert len(row) == len(terms)
        assert all(type(a) is int and abs(a) < 10**12 for a in row)
        maximum_integer = max(maximum_integer,*(abs(a) for a in row))
    assert E.kappa2(t) >= F(1,4)
    for term in terms[1:]:
        p,j = term
        i = p+j-t
        assert 0 <= p <= 8 and 0 <= j <= 8 and 0 <= i <= 8
        assert F(1,E.kappa2(p))*F(factorial(i),factorial(j)) < 5000**2
assert total_rows == 138
assert 2**9*factorial(8) < 5000**2

# Scalar inequalities used in the analytic estimates, all exact.
q_floor = 1024
assert F(120,q_floor) < F(1,2)
assert F(31,3*q_floor) < F(1,2)
assert F(2*q_floor+1,3*q_floor-31) < 1
assert F(66,3*(3-F(31,q_floor))) < 16
assert 120*2*3 + 240*3 + 120*3 < 2000
assert 17*6*2000 < 10**6
assert 13*10**6 < 10**8
assert 17*81 < 2000
assert 17*18*12000 < 10**8
assert 0 < 1-30*F(5,9)**9-F(1,50) < 1
assert 46*5000*6 < 2*10**6
assert 46*5000*4000 < 10**9
assert 138*(2*10**6)**2 < 10**15
assert 138*4*10**6*10**9 < 10**18
assert 1+6+4*(1+3) == 23 < 30
assert 120*2+8*11 < 512
descendant_constant = F(240*16**16)+F(512*(16**16-1),15)
assert descendant_constant < 10**22
body_norm = 3*10**16
body_difference = 3*10**19
summand_difference = 4*body_difference + 3*body_norm*10**22
average_difference = 17*summand_difference+16*17*body_norm
assert average_difference < 10**42
target_difference = 4*10**8 + 3*2000*240
head_h_difference = 4*10**6 + 3*6*240
assert target_difference < 10**9
assert head_h_difference < 5*10**6
delta = F(1,10**6)
complete_difference = average_difference + target_difference + 2*delta*head_h_difference
assert complete_difference < 10**43
flux_threshold = 10**50
assert F(10**43,flux_threshold) == F(1,10**7) < delta/2

# Independent exact replay of the finite planar half-gap.
head_checks=[]
for r,cap in [(3,8),(4,16)]:
    for z in range(cap+1):
        H=E.hamiltonian(r,z)
        U=E.relative_basis(r,z)
        defect=E.cm_lower(r,z)@H@U
        assert defect.a==E.zeros(defect.rows,defect.cols).a
        gap_form=E.rel_quadratic(H@H-H.scale(F(1,2)),r,z,z)
        gap_check=E.exact_psd(gap_form)
        assert gap_check['psd']
        head_checks.append({'body':r,'z':z,'dimension':U.cols,
                            'relative_invariance':True,**gap_check})

result={
    'status':'EXACT_HEAD_TRANSFER_SCALAR_BOUNDS_AND_PLANAR_HALF_GAP_VERIFIED',
    'scope':'Frozen finite certificate transfer only; separate planar shifted PSD verifier required',
    'analytic_proof':'explicit_head_threshold.txt',
    'uniform_integer_flux_threshold':str(flux_threshold),
    'initial_flux_floor':q_floor,
    'uniform_form_difference_bound':'10^43/Q',
    'extra_shift_margin':'1/2000000',
    'remaining_margin_at_threshold':'1/2500000',
    'total_frozen_rows':total_rows,
    'maximum_absolute_scaled_integer':maximum_integer,
    'scaled_integer_denominator':10**12,
    'descendant_constant_exact':str(descendant_constant),
    'aggregate_form_difference_constant_exact':str(complete_difference),
    'planar_head_checks':head_checks,
}
(BASE/'explicit_head_threshold_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='planar_head_checks'},indent=2))

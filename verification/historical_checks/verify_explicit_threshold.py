"""Replay finite exact inputs and scalar budgets for Q >= 10^50.

The accompanying analytic proof is essential: this driver is not a
proof-assistant verification of operator identities or norm estimates.
Uses only the Python standard library; no floating decisions.
"""
from pathlib import Path
from fractions import Fraction as F
import json, subprocess, sys

BASE=Path(__file__).resolve().parent
LOGS=BASE/'verification_logs'
LOGS.mkdir(exist_ok=True)
programs=['exact_shifted_certificate.py','exact_planar_head_gap.py',
          'verify_explicit_tail_threshold.py','check_explicit_coherent_threshold.py',
          'explicit_head_threshold_checker.py']
checks=[]
for name in programs:
    result=subprocess.run([sys.executable,'-S',str(BASE/name)],cwd=BASE,
                          capture_output=True,text=True,encoding='utf-8')
    (LOGS/(Path(name).stem+'.txt')).write_text(result.stdout+result.stderr,encoding='utf-8')
    if result.returncode:
        print(result.stdout+result.stderr)
        raise SystemExit(f'FAILED {name}: exit {result.returncode}')
    checks.append({'program':name,'exit_code':0})
    print('PASS',name,flush=True)

certificate=json.loads((BASE/'exact_shifted_certificate_results.json').read_text())
assert certificate['status']=='EXACT_SHIFTED_PSD_VERIFIED'
assert len(certificate['checks'])==26
head=json.loads((BASE/'explicit_head_threshold_results.json').read_text())
assert head['status']=='EXACT_HEAD_TRANSFER_SCALAR_BOUNDS_AND_PLANAR_HALF_GAP_VERIFIED'
assert len(head['planar_head_checks'])==26
q0=10**50; eta=F(certificate['eta']); c9=30*F(5,9)**9
mu=F(1,50); nu=F(1,2000); dq=F(2,10**6)
A=1-eta-c9-nu-dq*(35+2100)
B=mu-nu-dq*(35+4200)
assert A>F(1,3) and B>0
assert q0>=10**7 and q0==int(head['uniform_integer_flux_threshold'])
result={
 'status':'EXACT_FINITE_INPUTS_AND_EXPLICIT_THRESHOLD_BUDGETS_VERIFIED',
 'claim':'For every integer Q >= 10^50, H_Q^2 >= H_Q/3 on all bosonic particle sectors',
 'uniform_integer_flux_threshold':str(q0),
 'thresholds':{'negative_tail':'10000000','coherent_errors':str(q0),'finite_head':str(q0)},
 'scope':'Complete spherical LLL V0, unit coefficient per unordered pair projector',
 'independent_of_total_particle_number':True,
 'core_shifted_PSD_blocks':26,'additional_planar_half_gap_blocks':26,
 'analytic_proof_required':'Read the explicit-threshold appendix: coordinate identities, uniform norm bounds, geometric tail, positive lifting',
 'proof_assistant_formalization':False,'external_peer_review':False,
 'A_exact':str(A),'B_exact':str(B),'A_minus_one_third':str(A-F(1,3)),
 'checks':checks,
}
(BASE/'explicit_threshold_verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('ALL EXACT CHECKS PASSED; uniform sufficient threshold Q >= 10^50.')

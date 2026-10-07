"""Replay the complete optimized all-flux budget using the standard library.

The finite rows are frozen. This verifier uses no numerical proposal or
floating eigenvalue to decide a bound. See the accompanying mathematical
proofs for the analytic identities, kernel preservation, and positive lift.
"""
from pathlib import Path
from fractions import Fraction as F
import json, subprocess, sys, time, hashlib
from optimized_coherent_coefficients import uniform_coefficient, weighted_cost

BASE=Path(__file__).resolve().parent
WINDOWS=[
    (3088,3090,F(88473,20000000),F(70153,25000000)),
    (3090,3100,F(110519,25000000),F(56081,20000000)),
    (3100,3125,F(4409,1000000),F(1401,500000)),
    (3125,3300,F(4373,1000000),F(347,125000)),
    (3300,4000,F(4139,1000000),F(261,100000)),
    (4000,None,F(341,100000),F(21,10000)),
]

def replay(name,*args):
    logdir=BASE/'optimized_verification_logs'; logdir.mkdir(exist_ok=True)
    label=Path(name).stem+('_Q'+args[1] if args and args[0]=='--qmin' else '')
    completed=subprocess.run([sys.executable,'-S',str(BASE/name),*args],
                             cwd=BASE,text=True,capture_output=True)
    (logdir/(label+'.txt')).write_text(completed.stdout+completed.stderr,encoding='utf-8')
    if completed.returncode:
        print(completed.stdout+completed.stderr)
        raise RuntimeError('Verification failed: '+label)
    print('PASS '+label,flush=True)

def main():
    assert __debug__, 'Do not disable assertions with python -O.'
    started=time.time()
    replay('exact_shifted_certificate.py')
    core=json.loads((BASE/'exact_shifted_certificate_results.json').read_text())
    assert core['status']=='EXACT_SHIFTED_PSD_VERIFIED'
    assert len(core['checks'])==26
    assert all(c['psd'] and c['H_kernel_preserved_exactly'] and
               c['strictly_positive_on_H_image'] for c in core['checks'])
    eta=F(core['eta']); c9=30*F(5,9)**9; nu=F(1,10**10); mu=F(1,50)
    replay('optimized_tail_threshold_checker.py')
    tail=json.loads((BASE/'optimized_tail_threshold_results.json').read_text())
    assert tail['status']=='EXACT_ALL_INTEGER_FLUX_NEGATIVE_TAIL_CERTIFIED'
    assert F(tail['c9_exact'])==c9 and F(tail['nu_exact'])==nu
    assert any(t['uniform_flux_floor']==3000 and F(t['d_exact'])==F(391,100)
               for t in tail['strengthened_certificates'])
    replay('optimized_coherent_check.py')
    checks=[]
    for index,(qlo,qhi,L3,L4) in enumerate(WINDOWS):
        assert qlo>=3000
        if index: assert qlo==WINDOWS[index-1][1]
        assert qhi is None or qhi>qlo
        shiftpath=BASE/f'optimized_joint_shifts_Q{qlo}.json'
        shifts=json.loads(shiftpath.read_text())
        for r,a,L,cap in [(3,F(83,500),L3,8),(4,F(43,500),L4,16)]:
            assert set(shifts[str(r)])=={str(z) for z in range(cap+1)}
            errors={z:F(shifts[str(r)][str(z)]) for z in range(cap+1)}
            for z,error in errors.items():
                assert error==L/uniform_coefficient(r,z,qlo,a=a)
            assert weighted_cost(r,errors,qlo,a=a)==L
        resultpath=BASE/f'optimized_joint_head_Q{qlo}_results.json'
        replay('optimized_head_interval.py','--qmin',str(qlo),
               '--shifts',str(shiftpath),'--result',str(resultpath))
        head=json.loads(resultpath.read_text())
        assert head['status']=='RIGOROUS_INTERVAL_HEAD_VERIFIED'
        assert head['scope']=='all retained blocks'
        assert head['uniform_integer_Qmin']==qlo
        assert head['dyadic_precision_bits']==192 and head['taylor_order']==3
        assert {(c['body'],c['z']) for c in head['checks']}==(
            {(3,z) for z in range(9)}|{(4,z) for z in range(17)})
        for c in head['checks']:
            assert c['certified']
            if c['rank']:
                assert F(c['delta'])==F(shifts[str(c['body'])][str(c['z'])])
        gain=F(0) if qhi is None else F(391,100*qhi)
        A=1-eta-c9-nu+gain-L3-L4
        B=mu-nu+gain-L3-2*L4
        display_margins=[F(42,10**8),F(13,10**7),F(5,10**6),
                         F(66,10**8),F(193,10**6),F(454,10**6)]
        assert A-F(1,3)>display_margins[index] and B>F(1,100)
        checks.append(dict(Qmin=qlo,Qmax=qhi,L3=str(L3),L4=str(L4),
                           tail_gain=str(gain),A=str(A),B=str(B),
                           A_minus_one_third=str(A-F(1,3)),
                           A_decimal=float(A),B_decimal=float(B),
                           certified_blocks=len(head['checks'])))
    assert WINDOWS[-1][1] is None
    result={
        'status':'OPTIMIZED_UNIFORM_THRESHOLD_CERTIFIED',
        'claim':'H_Q^2 >= H_Q/3 for every integer Q >= 3088, uniformly in N',
        'uniform_flux_threshold':3088,
        'normalization':'one per unordered V0 pair projector in the complete spherical LLL',
        'eta':str(eta),'c9':str(c9),'nu':str(nu),'mu':str(mu),
        'coherent_a3':'83/500','coherent_a4':'43/500',
        'windows':checks,'certified_head_blocks':26*len(WINDOWS),
        'minimum_A_minus_one_third':str(min(F(c['A_minus_one_third']) for c in checks)),
        'rows_sha256':hashlib.sha256((BASE/'exact_shifted_certificate_rows.json').read_bytes()).hexdigest(),
        'decision_arithmetic':'integers, exact fractions, outward-rounded dyadic intervals',
        'analytic_obligations':'See proof notes: exact normal ordering, common kernel, Schur average, coherent comparison, and positive lifting.',
        'proof_assistant_formalization':False,'external_peer_review':False,
        'elapsed_seconds':time.time()-started,
    }
    (BASE/'optimized_threshold_verification.json').write_text(
        json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()

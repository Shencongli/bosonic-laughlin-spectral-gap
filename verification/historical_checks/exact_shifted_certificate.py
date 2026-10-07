"""Exact shifted-PSD verification of the saved bosonic V0 candidate.

The candidate is used only to propose rational rows. All ensuing operator
construction, normal ordering, CM averaging, and PSD decisions are rational.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, sqrt
from pathlib import Path
import json, time, argparse
import exact_relative_blocks as E

BASE=Path(__file__).parent
SOURCE=BASE/'refined_z8_t03_face_factors_basis_fixed.npz'
DEN=10**12
MAXT=8
delta=F(1,10**6)
mu=F(1,50)
c9=30*F(5,9)**9

channels={}
row_export={}
eta=F(0)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--generate',action='store_true',help='Propose new rounded rows from the NumPy candidate; requires NumPy.')
parser.add_argument('--rows',type=Path,default=BASE/'exact_shifted_certificate_rows.json',help='Frozen exact integer-row JSON (default verifier input).')
parser.add_argument('--result',type=Path,default=BASE/'exact_shifted_certificate_results.json')
args=parser.parse_args()
if args.generate:
    import numpy as np
    saved=np.load(SOURCE)
    for t in range(4):
        terms=[None]+[(p,T-p) for T in range(t,MAXT+1) for p in range(T+1)]
        rows=saved[f't{t}_original_rows']
        assert rows.shape[1]==len(terms)
        integers=[]
        for raw in rows:
            scaled=[]
            for coeff,term in zip(raw,terms):
                if term is None: scale=sqrt(float(E.kappa2(t)))
                else:
                    p,j=term; i=p+j-t
                    scale=sqrt(float(E.kappa2(p))*factorial(j)/factorial(i))
                scaled.append(int(round(float(coeff)*scale*DEN)))
            integers.append(scaled)
        row_export[t]={'terms':[None if x is None else list(x) for x in terms],
                       'common_denominator':DEN,'integer_scaled_rows':integers}
    args.rows.write_text(json.dumps(row_export,indent=2)+'\n',encoding='utf-8')
else:
    row_export=json.loads(args.rows.read_text(encoding='utf-8'))
for t in range(4):
    data=row_export[t] if t in row_export else row_export[str(t)]
    assert data['common_denominator']==DEN
    terms=[None if term is None else tuple(term) for term in data['terms']]
    expected=[None]+[(p,T-p) for T in range(t,MAXT+1) for p in range(T+1)]
    assert terms==expected
    integers=data['integer_scaled_rows']
    assert all(len(row)==len(terms) and all(type(x) is int for x in row) for row in integers)
    channels[t]=(terms,integers)
    eta+=F(sum(row[0]**2 for row in integers),DEN**2)/E.kappa2(t)

@lru_cache(None)
def integer_ops(n,D,t):
    terms=channels[t][0]
    src=E.parts(n,D); dst=E.parts(n-2,D-t); ix={A:k for k,A in enumerate(dst)}
    out=[]
    for term in terms:
        entries={}
        for col,A in enumerate(src):
            if term is None:
                for a in range(t+1):
                    B,w=E.ann(A,(a,t-a))
                    if w: entries[ix[B],col]=entries.get((ix[B],col),0)+w
            else:
                p,j=term; i=p+j-t
                for a in range(p+1):
                    B,w=E.ann(A,(a,p-a,j))
                    if w:
                        B=tuple(sorted(B+(i,)))
                        entries[ix[B],col]=entries.get((ix[B],col),0)+w
        out.append([(i,j,v) for (i,j),v in entries.items()])
    return out,len(dst),len(src)

def summed_positive_square(n,D):
    src=E.parts(n,D); dim=len(src)
    Q=[[0 for _ in range(dim)] for _ in range(dim)]
    for t,(terms,rows) in channels.items():
        operators,out_dim,_=integer_ops(n,D,t)
        g_out=[int(x) for x in E.metric(n-2,D-t)]
        for row in rows:
            fm=[[0 for _ in range(dim)] for _ in range(out_dim)]
            for c,op in zip(row,operators):
                if c:
                    for i,j,v in op: fm[i][j]+=c*v
            for w,values in zip(g_out,fm):
                nz=[(i,v) for i,v in enumerate(values) if v]
                for k,(i,a) in enumerate(nz):
                    wa=w*a
                    for j,b in nz[k:]: Q[i][j]+=wa*b
    for i in range(dim):
        for j in range(i): Q[i][j]=Q[j][i]
    metric=[int(x) for x in E.metric(n,D)]
    R=E.Mat([[F(Q[i][j],DEN**2*metric[i]) for j in range(dim)] for i in range(dim)],dim)
    E.quadratic(R,E.metric(n,D))
    return R

started=time.time()
K2={}
for t,(terms,rows) in channels.items():
    B=E.bhat(2,t,t)
    scalar=F(sum(row[0]**2 for row in rows),DEN**2)
    K2[t]=E.gram_operator(B,2,t,0,0).scale(scalar)
K3={}
for D in range(MAXT+1):
    R=summed_positive_square(3,D)
    for t,K in K2.items(): R=R-E.lift(K,2,t,3,D)
    K3[D]=R
    print('normal order 3',D,'elapsed',round(time.time()-started,2),flush=True)
K4={}
for D in range(2*MAXT+1):
    R=summed_positive_square(4,D)
    for t,K in K2.items(): R=R-E.lift(K,2,t,4,D)
    for d,K in K3.items(): R=R-E.lift(K,3,d,4,D)
    K4[D]=R
    print('normal order 4',D,'elapsed',round(time.time()-started,2),flush=True)

checks=[]
all_pass=True
for n,body in [(3,K3),(4,K4)]:
    average=E.cm_average_quadratics(body,n)
    for d,K in average.items():
        S=E.s3(d) if n==3 else E.s4(d)
        target=E.rel_quadratic(S,n,d,d)
        if n==4: target=target.scale(1-c9-mu)
        H=E.rel_quadratic(E.hamiltonian(n,d),n,d,d)
        shifted=target-K+H.scale(delta)
        result=E.exact_psd(shifted)
        H_result=E.exact_psd(H)
        H_kernel=E.nullspace(H)
        kernel_preserved=(shifted@H_kernel).a==E.zeros(shifted.rows,H_kernel.cols).a
        positive_on_H_image=(result['psd'] and H_result['psd']
                             and result.get('rank')==H_result.get('rank') and kernel_preserved)
        assert H_result['psd'] and kernel_preserved
        # The sphere transfer requires strict positivity on the H image,
        # not only semidefiniteness of the shifted comparison matrix.
        all_pass &= positive_on_H_image
        rec={'body':n,'relative_degree':d,'dimension':shifted.rows,
             'physical_H_rank':H_result['rank'],'H_kernel_preserved_exactly':kernel_preserved,
             'strictly_positive_on_H_image':positive_on_H_image,**result}
        checks.append(rec)
        print('shifted PSD',n,d,'pass',result['psd'],'rank',result.get('rank'),
              'H rank',H_result['rank'],'elapsed',round(time.time()-started,2),flush=True)

result={'status':'EXACT_SHIFTED_PSD_VERIFIED' if all_pass else 'EXACT_SHIFTED_PSD_FAILED',
        'source':args.rows.name,'row_denominator':DEN,'delta3':str(delta),'delta4':str(delta),
        'mu':str(mu),'c9':str(c9),'eta':str(eta),'eta_decimal':float(eta),
        'formal_gap_before_transfer_errors':str(1-eta-c9),
        'all_H_kernels_preserved_exactly':all(x['H_kernel_preserved_exactly'] for x in checks),
        'all_strictly_positive_on_H_image':all(x['strictly_positive_on_H_image'] for x in checks),
        'checks':checks,'elapsed_seconds':time.time()-started}
args.result.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='checks'},indent=2),flush=True)
if not all_pass:
    raise SystemExit(1)

"""Exact half-unit gap on ONLY the finite planar 3/4-body head blocks.

This establishes an input for an explicit sphere-transfer bound. It is
neither a global four-body spherical theorem nor a numerical extrapolation.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import exact_relative_blocks as E

checks=[]
for r,D in [(3,8),(4,16)]:
    for z in range(D+1):
        H=E.hamiltonian(r,z); U=E.relative_basis(r,z)
        defect=E.cm_lower(r,z)@H@U
        invariant=defect.a==E.zeros(defect.rows,defect.cols).a
        Q=E.rel_quadratic(H@H-H.scale(F(1,2)),r,z,z)
        check=E.exact_psd(Q)
        checks.append({'body':r,'z':z,'dimension':U.cols,
                       'relative_space_invariant_exactly':invariant,**check})
        if not invariant or not check['psd']:
            raise RuntimeError(f'Exact finite planar gap check failed: r={r}, z={z}')
result={'status':'EXACT_FINITE_PLANAR_HEAD_GAP_VERIFIED','gap':'1/2',
        'scope':'Only r=3,z<=8 and r=4,z<=16 planar relative blocks',
        'checks':checks}
path=Path(__file__).with_name('exact_planar_head_gap_results.json')
path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':result['status'],'blocks':len(checks),'gap':'1/2'}))

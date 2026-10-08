"""Replay the published raise_frame with exact affine scalars and export witnesses.

Lean checks each exported integer entry against its own multiset formula,
then identifies the arrays with the actual physical lowering map for Q>d.
This exporter does not certify the Python interval/Jet implementation.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import optimized_head_interval as sphere
import exact_relative_blocks as exact

REPO=Path(__file__).resolve().parents[1]


class Affine:
    def __init__(self,a=0,b=0): self.a,self.b=F(a),F(b)
    @staticmethod
    def coerce(x): return x if isinstance(x,Affine) else Affine(x)
    def __add__(self,x):
        x=self.coerce(x)
        return Affine(self.a+x.a,self.b+x.b)
    __radd__=__add__
    def __neg__(self): return Affine(-self.a,-self.b)
    def __sub__(self,x): return self+-self.coerce(x)
    def __mul__(self,x):
        x=self.coerce(x)
        assert self.b*x.b==0, 'Expected an affine result, not a truncated product.'
        return Affine(self.a*x.a,self.a*x.b+self.b*x.a)
    __rmul__=__mul__
    def scale(self,x): return self*x


def nat_matrix(name,a):
    rows,cols=len(a),len(a[0])
    out=[f'def {name} : Matrix (Fin {rows}) (Fin {cols}) ℕ := fun i j =>', '  match i.val, j.val with']
    for i,row in enumerate(a):
        for j,v in enumerate(row):
            if v: out.append(f'  | {i}, {j} => {v}')
    out.append('  | _, _ => 0')
    return '\n'.join(out)


def generate():
    sphere.JO,sphere.X,sphere.JZ=Affine(1),Affine(0,1),Affine()
    model=object.__new__(sphere.Model)
    cases=[]
    out=['import BosonicLaughlin.IndexedOccupationLowering',
         'import BosonicLaughlin.RetainedCMCoordinates', '',
         '/-! All 24 degree-raising steps used by the spherical verifier.',
         'The arrays C,S are extracted from its actual raise_frame routine.',
         'Lean checks every entry and proves R(Q)=C-S/Q for integer Q>d.',
         'No assertion about interval arithmetic is made here. -/',
         'namespace BosonicLaughlin', 'set_option maxRecDepth 100000',
         'set_option maxHeartbeats 0', '']
    for n,cap in [(3,8),(4,16)]:
        for d in range(cap):
            src,dst=exact.parts(n,d),exact.parts(n,d+1)
            arr=model.raise_frame(n,d,exact.eye(len(src)).a)
            C=[]; S=[]
            for row in arr:
                assert all(v.a.denominator==v.b.denominator==1 and v.a>=0 and v.b<=0 for v in row)
                C.append([int(v.a) for v in row]); S.append([-int(v.b) for v in row])
            # Independent source-column replay checks extraction and source multiplicities.
            c=[[0]*len(src) for _ in dst]; s=[[0]*len(src) for _ in dst]
            ix={B:i for i,B in enumerate(dst)}
            for col,A in enumerate(src):
                for j in set(A):
                    B=list(A); B.remove(j); B.append(j+1); B=tuple(sorted(B))
                    c[ix[B]][col]+=A.count(j); s[ix[B]][col]+=j*A.count(j)
            assert C==c and S==s
            cases.append({'particles':n,'degree':d,'source_parts':src,'target_parts':dst,'constant':C,'slope':S})
            pre=f'retainedRaise_{n}_{d}'
            out += [nat_matrix(pre+'C',C),'',nat_matrix(pre+'S',S),'',
                f'theorem {pre}_entries :',
                f'    (∀ (i : Fin {len(dst)}) (j : Fin {len(src)}), {pre}C i j=',
                f'      tupleLowerConstant {d} (retainedParts_{n}_{d+1}.get i) (retainedParts_{n}_{d}.get j)) ∧',
                f'    (∀ (i : Fin {len(dst)}) (j : Fin {len(src)}), {pre}S i j=',
                f'      tupleLowerSlope {d} (retainedParts_{n}_{d+1}.get i) (retainedParts_{n}_{d}.get j)) := by',
                f'  unfold {pre}C {pre}S', '  decide +kernel','',
                f'theorem {pre}_physical (Q : ℕ) (hd : {d+1}≤Q) :',
                f'    indexedVerifierRaiseMatrix hd retainedEnum_{n}_{d} retainedEnum_{n}_{d+1}=',
                f'      {pre}C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • {pre}S.map (Nat.castRingHom ℂ) := by',
                '  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd',
                '  · intro i j',
                f'    simp only [retainedEnum_{n}_{d}, retainedEnum_{n}_{d+1}]',
                f'    rw [sortedEnumerationOfTable_ofFn retainedParts_{n}_{d+1} retainedParts_{n}_{d+1}_complete i,',
                f'      sortedEnumerationOfTable_ofFn retainedParts_{n}_{d} retainedParts_{n}_{d}_complete j]',
                f'    exact {pre}_entries.1 i j',
                '  · intro i j',
                f'    simp only [retainedEnum_{n}_{d}, retainedEnum_{n}_{d+1}]',
                f'    rw [sortedEnumerationOfTable_ofFn retainedParts_{n}_{d+1} retainedParts_{n}_{d+1}_complete i,',
                f'      sortedEnumerationOfTable_ofFn retainedParts_{n}_{d} retainedParts_{n}_{d}_complete j]',
                f'    exact {pre}_entries.2 i j','']
    out += ['end BosonicLaughlin','']
    return '\n'.join(out), json.dumps({'source':'optimized_head_interval.Model.raise_frame',
        'exact_scalar_replay':'Affine scalars a+b*x; nonzero quadratic terms rejected.',
        'case_count':len(cases),'cases':cases},indent=2)+'\n'


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    lean,data=generate()
    for name,text in [('lean/BosonicLaughlin/RetainedLoweringArrays.lean',lean),
                      ('verification/lean_lowering_arrays.json',data)]:
        p=REPO/name
        if args.check:
            assert p.read_bytes()==text.encode('utf-8'),name
        else: p.write_text(text,encoding='utf-8',newline='\n')
    print('24 affine lowering arrays reproduced exactly.' if args.check else 'Exported 24 affine lowering arrays.')

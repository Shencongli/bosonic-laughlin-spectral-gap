"""Export CM index tables and Lean-checkable entry certificates.

The Python enumeration only proposes tables. Lean proves their equality to a
complete recursive enumeration and checks every integer CM matrix entry.
"""
from pathlib import Path
import argparse
import exact_relative_blocks as exact

ROOT = Path(__file__).resolve().parents[1]

def generate():
    lines = [
        'import BosonicLaughlin.EnumeratedPartitions',
        'import BosonicLaughlin.RetainedCMFrames', '',
        '/-! Complete index tables and the exact identification of the retained',
        'CM arrays with the physical occupation CM matrix for Q >= d > 0.',
        'Literal table equality and every integer entry are checked in Lean. -/',
        'namespace BosonicLaughlin', '',
        'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
    ]
    for n, maxd in [(3, 8), (4, 16)]:
        for d in range(maxd+1):
            p = f'retainedParts_{n}_{d}'
            en = f'retainedEnum_{n}_{d}'
            rows = exact.parts(n,d)
            lines += [f'def {p} : List (List ℕ) := [']
            lines += ['  ['+', '.join(map(str,a))+']'+(',' if i+1<len(rows) else '')
                      for i,a in enumerate(rows)]
            lines += [']', '',
                f'theorem {p}_complete : {p}=degreePartitions {n} {d} 0 := by',
                '  decide +kernel', '',
                f'def {en} : SortedTupleEnumeration {n} {d} {len(rows)} :=',
                f'  sortedEnumerationOfTable {p} {p}_complete', '',
            ]
            if d==0:
                continue
            pre=f'retainedCM_{n}_{d}'
            prev=f'retainedParts_{n}_{d-1}'
            ene=f'retainedEnum_{n}_{d-1}'
            nr=len(exact.parts(n,d-1))
            lines += [
                f'theorem {pre}_integer_entries : ∀ (i : Fin {nr}) (j : Fin {len(rows)}),',
                f'    sparseIntRowEval ({pre}CS i) j =',
                f'      (tupleCMCoefficient {d} ({prev}.get i) ({p}.get j) : ℤ) := by',
                '  decide +kernel', '',
                f'theorem {pre}_physical_matrix (Q : ℕ) (hd : {d}≤Q) :',
                f'    indexedOccupationCMMatrix hd {en} {ene} =',
                f'      {pre}C.map (Rat.castHom ℂ) := by',
                f'  apply indexedOccupationCMMatrix_eq_array hd (by decide)',
                '  intro i j',
                f'  change (sparseIntRowEval ({pre}CS i) j : ℚ) = _',
                f'  simp only [{en}, {ene}]',
                f'  rw [sortedEnumerationOfTable_ofFn {prev} {prev}_complete i,',
                f'    sortedEnumerationOfTable_ofFn {p} {p}_complete j]',
                f'  exact_mod_cast {pre}_integer_entries i j', '',
            ]
    lines += ['end BosonicLaughlin', '']
    return '\n'.join(lines)

def generate_physical():
    lines = [
        'import BosonicLaughlin.RetainedCMCoordinates',
        'import BosonicLaughlin.RetainedCMZeroDegree',
        'import BosonicLaughlin.KernelFramePhysical', '',
        '/-! The retained rational columns give complete (nonorthonormal)',
        'coordinates on the actual spherical physical highest-weight spaces.',
        'Positive degrees require Q >= d; the degree-zero result holds for all Q. -/',
        'namespace BosonicLaughlin', 'noncomputable section', 'open scoped Matrix', '',
    ]
    for n, maxd in [(3,8),(4,16)]:
        for d in range(maxd+1):
            pre=f'retainedCM_{n}_{d}'
            en=f'retainedEnum_{n}_{d}'
            prev=f'retainedEnum_{n}_{d-1}'
            k=exact.relative_basis(n,d).cols
            if d==0:
                lines += [
                    f'theorem {pre}_physical_finrank (Q : ℕ) :',
                    f'    Module.finrank ℂ (physicalHighestWeightSubspace Q {n} 0)=1 :=',
                    f'  physicalHighestWeight_zero_degree_finrank Q {n}', '',
                ]
                continue
            lines += [
                f'def {pre}_physicalEquiv (Q : ℕ) (hd : {d}≤Q) :',
                f'    (Fin {k} → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q {n} {d} :=',
                f'  indexedKernelFramePhysicalEquiv {pre}_frame hd {en} {prev}',
                f'    ({pre}_physical_matrix Q hd)', '',
                f'theorem {pre}_physical_apply (Q : ℕ) (hd : {d}≤Q) (c : Fin {k} → ℂ) :',
                f'    ({pre}_physicalEquiv Q hd c).val =',
                f'      (polynomialWeightCoordinates Q {n} {d}).symm',
                f'        (polynomialWeightOccupationInclude',
                f'          ((({pre}U.map (Rat.castHom ℂ)) *ᵥ c) ∘ ({en}.occupationEquiv hd).symm)) := rfl', '',
                f'theorem {pre}_columns_complete (Q : ℕ) (hd : {d}≤Q) :',
                f'    Function.Bijective ({pre}_physicalEquiv Q hd) :=',
                f'  ({pre}_physicalEquiv Q hd).bijective', '',
                f'theorem {pre}_physical_finrank (Q : ℕ) (hd : {d}≤Q) :',
                f'    Module.finrank ℂ (physicalHighestWeightSubspace Q {n} {d})={k} := by',
                f'  rw [← ({pre}_physicalEquiv Q hd).finrank_eq]',
                '  simp', '',
            ]
    lines += ['end', 'end BosonicLaughlin', '']
    return '\n'.join(lines)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check',action='store_true',help='Check byte-for-byte reproducibility without writing')
    args=p.parse_args()
    for filename, contents in [('RetainedCMCoordinates.lean',generate()),
                               ('RetainedCMPhysical.lean',generate_physical())]:
        target=ROOT/'lean/BosonicLaughlin'/filename
        data=contents.encode('utf-8')
        if args.check:
            assert target.read_bytes()==data, 'Generated source differs: '+filename
            print(filename,'matches the generator exactly.')
        else:
            target.write_bytes(data)
            print(target, len(data),'bytes')

"""Export exact planar arrays and integer witnesses for Lean kernel checking.

The historical verifier is replayed without changing its saved result. Lean
checks positivity, complete common kernels, and complementary frames of the
exported arrays. The physical interpretation of the comparison arrays and
the finite-sphere interval estimates are separate proof obligations.
"""
from pathlib import Path
from fractions import Fraction as F
from math import lcm
import argparse
import contextlib
import hashlib
import io
import json
import runpy
import sys
import uuid
import exact_relative_blocks as E
from generate_retained_cm_frames import sparse

ROOT = Path(__file__).resolve().parents[1]


def denominator(*matrices):
    return lcm(*(v.denominator for M in matrices for row in M.a for v in row))


def kernel_frame(C):
    a = [row[:] for row in C.a]
    ops = E.eye(C.rows).a
    piv, rank = [], 0
    for j in range(C.cols):
        k = next((i for i in range(rank, C.rows) if a[i][j]), None)
        if k is None:
            continue
        a[rank], a[k] = a[k], a[rank]
        ops[rank], ops[k] = ops[k], ops[rank]
        p = a[rank][j]
        a[rank] = [x/p for x in a[rank]]
        ops[rank] = [x/p for x in ops[rank]]
        for i in range(C.rows):
            if i != rank and a[i][j]:
                q = a[i][j]
                a[i] = [x-q*y for x, y in zip(a[i], a[rank])]
                ops[i] = [x-q*y for x, y in zip(ops[i], ops[rank])]
        piv.append(j)
        rank += 1
        if rank == C.rows:
            break
    free = [j for j in range(C.cols) if j not in piv]
    U, L, V = E.nullspace(C), E.zeros(len(free), C.cols), E.zeros(C.cols, C.rows)
    for k, j in enumerate(free):
        L.a[k][j] = F(1)
    for k, j in enumerate(piv):
        V.a[j] = ops[k]
    assert (C@U).a == E.zeros(C.rows, U.cols).a
    assert (L@U).a == E.eye(U.cols).a
    assert (U@L+V@C).a == E.eye(C.cols).a
    return U, L, V, piv


def gram(M):
    """Pivoted exact LDL, returned as M=R^T diag(w) R."""
    assert M.a == M.T().a
    a = [row[:] for row in M.a]
    ids, rows, weights, pivots = list(range(M.rows)), [], [], []
    while a:
        assert all(a[i][i] >= 0 for i in range(len(a)))
        k = next((i for i in range(len(a)) if a[i][i] > 0), None)
        if k is None:
            assert not any(x for row in a for x in row)
            break
        p = a[k][k]
        row = [F(0)]*M.cols
        for j, idx in enumerate(ids):
            row[idx] = a[k][j]/p
        rows.append(row)
        weights.append([p])
        pivots.append(ids[k])
        keep = [i for i in range(len(a)) if i != k]
        a = [[a[i][j]-a[i][k]*a[k][j]/p for j in keep] for i in keep]
        ids = [ids[i] for i in keep]
    R, D = E.Mat(rows, M.cols), E.Mat(weights, 1)
    diag = E.zeros(len(rows), len(rows))
    for i, w in enumerate(weights):
        diag.a[i][i] = w[0]
    assert (R.T()@diag@R).a == M.a
    return R, D, pivots


def generate(check=False):
    old = sys.argv[:]
    result = ROOT/'verification'/('.planar-export-'+uuid.uuid4().hex+'.json')
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            sys.argv = ['exact_shifted_certificate.py', '--result', str(result)]
            ns = runpy.run_path(str(ROOT/'verification/exact_shifted_certificate.py'))
    finally:
        sys.argv = old
        result.unlink(missing_ok=True)
    # run_path uses the same exact_relative_blocks module as this exporter.
    out = ['import BosonicLaughlin.KernelComplement', '', '/-!',
           'Exact exported planar comparison and Hamiltonian arrays.',
           'Their Gram decompositions, common kernels, and complement identities',
           'are checked by Lean kernel reduction. Operator-to-array identification',
           'and finite-sphere interval estimates are not asserted here.', '-/',
           'namespace BosonicLaughlin', 'open scoped Matrix ComplexOrder', '',
           'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
    cases = []
    for n in (3, 4):
        avg = E.cm_average_quadratics(ns[f'K{n}'], n)
        for d, K in avg.items():
            target = E.rel_quadratic(getattr(E, f's{n}')(d), n, d, d)
            if n == 4:
                target = target.scale(1-ns['c9']-ns['mu'])
            H = E.rel_quadratic(E.hamiltonian(n, d), n, d, d)
            A = target-K+H.scale(ns['delta'])
            pre = f'planar_{n}_{d}'
            size, data = A.rows, {}
            for tag, M in (('A', A), ('H', H)):
                name = pre+tag
                R, weights, selected = gram(M)
                dm, dr, dw = denominator(M), denominator(R), denominator(weights)
                scale = dr*dr*dw
                ints = M.scale(dm)
                rank = R.rows
                out += [f'/- N={n}, d={d}, {tag}; dimension={size}, rank={rank}. -/',
                        f'def {name}D : ℤ := {dm}', f'def {name}S : ℤ := {scale}',
                        sparse(name+'M', ints), '', sparse(name+'R', R, dr), '',
                        sparse(name+'T', R.T(), dr), '',
                        f'def {name}w : Fin {rank} → ℤ := fun i =>', '  match i.val with']
                for i, row in enumerate(weights.a):
                    q = row[0]*dw*dm
                    assert q.denominator == 1 and q > 0
                    out.append(f'  | {i} => {q.numerator}')
                out += ['  | _ => 0', '',
                        f'def {name} : Matrix (Fin {size}) (Fin {size}) ℚ := sparseRatScaledMatrix {name}D {name}M', '',
                        f'theorem {name}_gram_check : SparseGramCheck {name}S {name}M {name}R {name}T {name}w := by',
                        '  unfold SparseGramCheck', '  decide +kernel', '',
                        f'theorem {name}_posSemidef : ({name}.map (Rat.castHom ℂ)).PosSemidef :=',
                        '  sparseGramCheck_scaled_posSemidef (by decide) (by decide)',
                        f'    (by decide +kernel) {name}_gram_check', '']
                U, L, V, piv = kernel_frame(ints)
                data[tag] = (ints, U, L, V, selected)
            assert data['A'][1].a == data['H'][1].a
            assert data['A'][2].a == data['H'][2].a
            U, L, VA, VH = data['A'][1], data['A'][2], data['A'][3], data['H'][3]
            fd = denominator(U, VA, VH)
            out += [f'def {pre}KD : ℤ := {fd}', sparse(pre+'KU', U, fd), '',
                    sparse(pre+'KL', L), '', sparse(pre+'KVA', VA, fd), '', sparse(pre+'KVH', VH, fd), '',
                    f'def {pre}U : Matrix (Fin {size}) (Fin {U.cols}) ℚ := sparseRatScaledMatrix {pre}KD {pre}KU',
                    f'def {pre}L : Matrix (Fin {U.cols}) (Fin {size}) ℚ := sparseRatMatrix {pre}KL', '']
            for tag in ('A', 'H'):
                name = pre+tag
                out += [f'def {name}V : Matrix (Fin {size}) (Fin {size}) ℚ :=',
                        f'  (({name}D : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix {pre}KD {pre}KV{tag}', '',
                        f'theorem {name}_kernel_check : SparseScaledFrameCheck {pre}KD {name}M {pre}KU {pre}KL {pre}KV{tag} := by',
                        '  unfold SparseScaledFrameCheck', '  decide +kernel', '',
                        f'theorem {name}_kernel_frame : HasKernelFrame {name} {pre}U {pre}L {name}V :=',
                        f'  (sparseScaledFrameCheck_sound (by decide : {pre}KD≠0) {name}_kernel_check).scale_matrix',
                        f'    (by norm_num [{name}D])', '',
                        f'theorem {name}_kernel_finrank : Module.finrank ℂ (LinearMap.ker ({name}.map (Rat.castHom ℂ)).mulVecLin)={U.cols} :=',
                        f'  kernelFrame_finrank {name}_kernel_frame.ratCast', '']
            out += [f'theorem {pre}_same_kernel (v : Fin {size} → ℂ) :',
                    f'    ({pre}A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ ({pre}H.map (Rat.castHom ℂ)) *ᵥ v=0 :=',
                    f'  kernelFrame_same_kernel {pre}A_kernel_frame.ratCast {pre}H_kernel_frame.ratCast v', '']
            selected = data['H'][4]
            W = E.zeros(size, len(selected))
            for i, j in enumerate(selected):
                W.a[j][i] = F(1)
            proj = E.eye(size)-U@L
            R = E.Mat([proj.a[j][:] for j in selected], size)
            assert (W@R+U@L).a == E.eye(size).a
            assert (L@W).a == E.zeros(U.cols, W.cols).a
            assert (R@W).a == E.eye(W.cols).a
            rd = denominator(R)
            out += [sparse(pre+'WS', W), '', sparse(pre+'RS', R, rd), '',
                    f'def {pre}W : Matrix (Fin {size}) (Fin {W.cols}) ℚ := sparseRatMatrix {pre}WS',
                    f'def {pre}R : Matrix (Fin {W.cols}) (Fin {size}) ℚ := sparseRatScaledMatrix {rd} {pre}RS', '',
                    f'theorem {pre}_complement : HasComplement {pre}U {pre}L {pre}W {pre}R := by',
                    '  unfold HasComplement', '  decide +kernel', '']
            for tag in ('A', 'H'):
                name = pre+tag
                out += [f'theorem {name}_active_posDef :',
                        f'    (({pre}W.map (Rat.castHom ℂ))ᴴ * ({name}.map (Rat.castHom ℂ)) * ({pre}W.map (Rat.castHom ℂ))).PosDef :=',
                        f'  kernelFrame_complement_posDef {name}_kernel_frame.ratCast {name}_posSemidef _ _',
                        f'    (({pre}_complement.map (Rat.castHom ℂ)).2.1) (({pre}_complement.map (Rat.castHom ℂ)).2.2)', '']
            cases.append({'particles': n, 'degree': d, 'dimension': size, 'rank': W.cols,
                          'nullity': U.cols, 'selected': selected,
                          'comparison': [[str(v) for v in row] for row in A.a],
                          'hamiltonian': [[str(v) for v in row] for row in H.a]})
            print(n, d, 'dimension', size, 'rank', W.cols, 'nullity', U.cols, flush=True)
    out += ['end BosonicLaughlin', '']
    inputs = ['exact_relative_blocks.py', 'exact_shifted_certificate.py', 'exact_shifted_certificate_rows.json']
    record = {'scope': 'Exact exported planar arrays; physical comparison identification and finite-sphere interval bounds are not included.',
              'delta': str(ns['delta']), 'mu': str(ns['mu']), 'c9': str(ns['c9']),
              'input_sha256': {p: hashlib.sha256((ROOT/'verification'/p).read_bytes()).hexdigest() for p in inputs},
              'cases': cases}
    outputs = {
        ROOT/'lean/BosonicLaughlin/RetainedPlanarCertificates.lean': '\n'.join(out).encode('utf-8'),
        ROOT/'verification/lean_planar_matrices.json': (json.dumps(record, indent=2)+'\n').encode('utf-8')}
    for path, content in outputs.items():
        if check:
            if path.read_bytes() != content:
                raise SystemExit('Regenerated output differs: '+str(path))
        else:
            path.write_bytes(content)
    print('Exact regeneration check passed.' if check else 'Wrote Lean certificates and exact array record.')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    generate(p.parse_args().check)

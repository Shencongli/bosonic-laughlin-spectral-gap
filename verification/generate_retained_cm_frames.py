"""Export exact retained frames, checked independently by the Lean kernel.

The unchanged published verifier supplies C and U. Row operations construct
the additional witnesses L and V. A common integer denominator clears U,V;
Lean verifies sparse integer identities and derives all rational identities.
"""
from pathlib import Path
from math import lcm
import argparse
from fractions import Fraction
import exact_relative_blocks as exact

REPO = Path(__file__).resolve().parents[1]


def frame(n, d):
    C = exact.cm_lower(n, d)
    U = exact.relative_basis(n, d)
    rows = [list(r) for r in C.a]
    E = exact.eye(C.rows).a
    pivots = []
    rank = 0
    for j in range(C.cols):
        k = next((k for k in range(rank, C.rows) if rows[k][j]), None)
        if k is None:
            continue
        rows[rank], rows[k] = rows[k], rows[rank]
        E[rank], E[k] = E[k], E[rank]
        t = rows[rank][j]
        rows[rank] = [x/t for x in rows[rank]]
        E[rank] = [x/t for x in E[rank]]
        for k in range(C.rows):
            if k != rank and rows[k][j]:
                t = rows[k][j]
                rows[k] = [x-t*y for x,y in zip(rows[k],rows[rank])]
                E[k] = [x-t*y for x,y in zip(E[k],E[rank])]
        pivots.append(j)
        rank += 1
        if rank == C.rows:
            break
    free = [j for j in range(C.cols) if j not in pivots]
    L = exact.zeros(len(free), C.cols)
    for k, j in enumerate(free):
        L.a[k][j] = Fraction(1)
    V = exact.zeros(C.cols, C.rows)
    for k, j in enumerate(pivots):
        V.a[j] = E[k]
    assert (C @ U).a == exact.zeros(C.rows, U.cols).a
    assert (L @ U).a == exact.eye(U.cols).a
    assert ((U @ L) + (V @ C)).a == exact.eye(C.cols).a
    return C, U, L, V



def sparse(name, M, scale=1):
    out = [f"def {name} : SparseIntMatrix {M.rows} {M.cols} := fun i =>", "  match i.val with"]
    for i, row in enumerate(M.a):
        vals = []
        for j, q in enumerate(row):
            q *= scale
            assert q.denominator == 1
            if q:
                vals.append(f"(⟨{j}, by decide⟩, {q.numerator})")
        if vals:
            out.append(f"  | {i} => [" + ", ".join(vals) + "]")
    out.append("  | _ => []")
    return "\n".join(out)


def generate(cases, check=False):
    out = ["import BosonicLaughlin.SparseKernelFrame", "", "/-!",
           "Retained rational CM frames exported from exact_relative_blocks.py.",
           "A common denominator reduces all three exact frame identities to",
           "sparse integer row identities, verified by direct Lean kernel reduction.",
           "The data use the script's parts(n,d) order.",
           "-/", "namespace BosonicLaughlin", "open scoped Matrix", "",
           "set_option maxRecDepth 100000", "set_option maxHeartbeats 0", ""]
    for n, d in cases:
        pre = f"retainedCM_{n}_{d}"
        C, U, L, V = frame(n, d)
        D = lcm(*(q.denominator for M in (U, V) for row in M.a for q in row))
        out.append(f"/- N={n}, degree={d}; rows={C.rows}, columns={C.cols}, nullity={U.cols}. -/")
        out.append(f"def {pre}D : ℤ := {D}\n")
        for suff, M, scale in (("CS", C, 1), ("WS", U, D), ("LS", L, 1), ("ZS", V, D)):
            out += [sparse(pre+suff, M, scale), ""]
        out += [f"def {pre}C : Matrix (Fin {C.rows}) (Fin {C.cols}) ℚ := sparseRatMatrix {pre}CS",
                f"def {pre}U : Matrix (Fin {U.rows}) (Fin {U.cols}) ℚ := sparseRatScaledMatrix {pre}D {pre}WS",
                f"def {pre}L : Matrix (Fin {L.rows}) (Fin {L.cols}) ℚ := sparseRatMatrix {pre}LS",
                f"def {pre}V : Matrix (Fin {V.rows}) (Fin {V.cols}) ℚ := sparseRatScaledMatrix {pre}D {pre}ZS", "",
                f"theorem {pre}_sparse_check :",
                f"    SparseScaledFrameCheck {pre}D {pre}CS {pre}WS {pre}LS {pre}ZS := by",
                "  unfold SparseScaledFrameCheck",
                "  decide +kernel", "",
                f"theorem {pre}_frame : HasKernelFrame {pre}C {pre}U {pre}L {pre}V :=",
                f"  sparseScaledFrameCheck_sound (by decide : {pre}D≠0) {pre}_sparse_check", "",
                f"theorem {pre}_kernel_finrank :",
                f"    Module.finrank ℚ (LinearMap.ker {pre}C.mulVecLin)={U.cols} :=",
                f"  kernelFrame_finrank {pre}_frame", ""]
        print(n, d, "shapes", C.shape, U.shape, "denominator", D, flush=True)
    out += ["end BosonicLaughlin", ""]
    dest = REPO / "lean" / "BosonicLaughlin" / "RetainedCMFrames.lean"
    content = "\n".join(out).encode("utf-8")
    if check:
        if dest.read_bytes() != content:
            raise SystemExit("Generated data differ from checked-in RetainedCMFrames.lean")
        print("Exact regeneration check passed:", dest, flush=True)
    else:
        dest.write_bytes(content)
        print(dest, dest.stat().st_size, flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--check", action="store_true", help="Check exact regeneration without editing files")
    args = p.parse_args()
    generate([(3,d) for d in range(9)]+[(4,d) for d in range(17)], check=args.check)

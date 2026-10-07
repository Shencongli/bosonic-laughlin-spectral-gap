import BosonicLaughlin.SparseKernelFrame

/-!
Retained rational CM frames exported from exact_relative_blocks.py.
A common denominator reduces all three exact frame identities to
sparse integer row identities, verified by direct Lean kernel reduction.
The data use the script's parts(n,d) order.
-/
namespace BosonicLaughlin
open scoped Matrix

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- N=3, degree=0; rows=0, columns=1, nullity=1. -/
def retainedCM_3_0D : ℤ := 1

def retainedCM_3_0CS : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def retainedCM_3_0WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def retainedCM_3_0LS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def retainedCM_3_0ZS : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def retainedCM_3_0C : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix retainedCM_3_0CS
def retainedCM_3_0U : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_3_0D retainedCM_3_0WS
def retainedCM_3_0L : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix retainedCM_3_0LS
def retainedCM_3_0V : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix retainedCM_3_0D retainedCM_3_0ZS

theorem retainedCM_3_0_sparse_check :
    SparseScaledFrameCheck retainedCM_3_0D retainedCM_3_0CS retainedCM_3_0WS retainedCM_3_0LS retainedCM_3_0ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_3_0_frame : HasKernelFrame retainedCM_3_0C retainedCM_3_0U retainedCM_3_0L retainedCM_3_0V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_3_0D≠0) retainedCM_3_0_sparse_check

theorem retainedCM_3_0_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_3_0C.mulVecLin)=1 :=
  kernelFrame_finrank retainedCM_3_0_frame

/- N=3, degree=1; rows=1, columns=1, nullity=0. -/
def retainedCM_3_1D : ℤ := 1

def retainedCM_3_1CS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def retainedCM_3_1WS : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def retainedCM_3_1LS : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def retainedCM_3_1ZS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def retainedCM_3_1C : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix retainedCM_3_1CS
def retainedCM_3_1U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix retainedCM_3_1D retainedCM_3_1WS
def retainedCM_3_1L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix retainedCM_3_1LS
def retainedCM_3_1V : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_3_1D retainedCM_3_1ZS

theorem retainedCM_3_1_sparse_check :
    SparseScaledFrameCheck retainedCM_3_1D retainedCM_3_1CS retainedCM_3_1WS retainedCM_3_1LS retainedCM_3_1ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_3_1_frame : HasKernelFrame retainedCM_3_1C retainedCM_3_1U retainedCM_3_1L retainedCM_3_1V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_3_1D≠0) retainedCM_3_1_sparse_check

theorem retainedCM_3_1_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_3_1C.mulVecLin)=0 :=
  kernelFrame_finrank retainedCM_3_1_frame

/- N=3, degree=2; rows=1, columns=2, nullity=1. -/
def retainedCM_3_2D : ℤ := 2

def retainedCM_3_2CS : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 2), (⟨1, by decide⟩, 2)]
  | _ => []

def retainedCM_3_2WS : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, -2)]
  | 1 => [(⟨0, by decide⟩, 2)]
  | _ => []

def retainedCM_3_2LS : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨1, by decide⟩, 1)]
  | _ => []

def retainedCM_3_2ZS : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def retainedCM_3_2C : Matrix (Fin 1) (Fin 2) ℚ := sparseRatMatrix retainedCM_3_2CS
def retainedCM_3_2U : Matrix (Fin 2) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_3_2D retainedCM_3_2WS
def retainedCM_3_2L : Matrix (Fin 1) (Fin 2) ℚ := sparseRatMatrix retainedCM_3_2LS
def retainedCM_3_2V : Matrix (Fin 2) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_3_2D retainedCM_3_2ZS

theorem retainedCM_3_2_sparse_check :
    SparseScaledFrameCheck retainedCM_3_2D retainedCM_3_2CS retainedCM_3_2WS retainedCM_3_2LS retainedCM_3_2ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_3_2_frame : HasKernelFrame retainedCM_3_2C retainedCM_3_2U retainedCM_3_2L retainedCM_3_2V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_3_2D≠0) retainedCM_3_2_sparse_check

theorem retainedCM_3_2_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_3_2C.mulVecLin)=1 :=
  kernelFrame_finrank retainedCM_3_2_frame

/- N=3, degree=3; rows=2, columns=3, nullity=1. -/
def retainedCM_3_3D : ℤ := 6

def retainedCM_3_3CS : SparseIntMatrix 2 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 2), (⟨2, by decide⟩, 3)]
  | _ => []

def retainedCM_3_3WS : SparseIntMatrix 3 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3)]
  | 1 => [(⟨0, by decide⟩, -9)]
  | 2 => [(⟨0, by decide⟩, 6)]
  | _ => []

def retainedCM_3_3LS : SparseIntMatrix 1 3 := fun i =>
  match i.val with
  | 0 => [(⟨2, by decide⟩, 1)]
  | _ => []

def retainedCM_3_3ZS : SparseIntMatrix 3 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 2), (⟨1, by decide⟩, -1)]
  | 1 => [(⟨1, by decide⟩, 3)]
  | _ => []

def retainedCM_3_3C : Matrix (Fin 2) (Fin 3) ℚ := sparseRatMatrix retainedCM_3_3CS
def retainedCM_3_3U : Matrix (Fin 3) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_3_3D retainedCM_3_3WS
def retainedCM_3_3L : Matrix (Fin 1) (Fin 3) ℚ := sparseRatMatrix retainedCM_3_3LS
def retainedCM_3_3V : Matrix (Fin 3) (Fin 2) ℚ := sparseRatScaledMatrix retainedCM_3_3D retainedCM_3_3ZS

theorem retainedCM_3_3_sparse_check :
    SparseScaledFrameCheck retainedCM_3_3D retainedCM_3_3CS retainedCM_3_3WS retainedCM_3_3LS retainedCM_3_3ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_3_3_frame : HasKernelFrame retainedCM_3_3C retainedCM_3_3U retainedCM_3_3L retainedCM_3_3V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_3_3D≠0) retainedCM_3_3_sparse_check

theorem retainedCM_3_3_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_3_3C.mulVecLin)=1 :=
  kernelFrame_finrank retainedCM_3_3_frame

/- N=3, degree=4; rows=3, columns=4, nullity=1. -/
def retainedCM_3_4D : ℤ := 12

def retainedCM_3_4CS : SparseIntMatrix 3 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 4), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 3), (⟨2, by decide⟩, 4), (⟨3, by decide⟩, 2)]
  | 2 => [(⟨3, by decide⟩, 2)]
  | _ => []

def retainedCM_3_4WS : SparseIntMatrix 4 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 4)]
  | 1 => [(⟨0, by decide⟩, -16)]
  | 2 => [(⟨0, by decide⟩, 12)]
  | _ => []

def retainedCM_3_4LS : SparseIntMatrix 1 4 := fun i =>
  match i.val with
  | 0 => [(⟨2, by decide⟩, 1)]
  | _ => []

def retainedCM_3_4ZS : SparseIntMatrix 4 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3), (⟨1, by decide⟩, -1), (⟨2, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 4), (⟨2, by decide⟩, -4)]
  | 3 => [(⟨2, by decide⟩, 6)]
  | _ => []

def retainedCM_3_4C : Matrix (Fin 3) (Fin 4) ℚ := sparseRatMatrix retainedCM_3_4CS
def retainedCM_3_4U : Matrix (Fin 4) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_3_4D retainedCM_3_4WS
def retainedCM_3_4L : Matrix (Fin 1) (Fin 4) ℚ := sparseRatMatrix retainedCM_3_4LS
def retainedCM_3_4V : Matrix (Fin 4) (Fin 3) ℚ := sparseRatScaledMatrix retainedCM_3_4D retainedCM_3_4ZS

theorem retainedCM_3_4_sparse_check :
    SparseScaledFrameCheck retainedCM_3_4D retainedCM_3_4CS retainedCM_3_4WS retainedCM_3_4LS retainedCM_3_4ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_3_4_frame : HasKernelFrame retainedCM_3_4C retainedCM_3_4U retainedCM_3_4L retainedCM_3_4V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_3_4D≠0) retainedCM_3_4_sparse_check

theorem retainedCM_3_4_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_3_4C.mulVecLin)=1 :=
  kernelFrame_finrank retainedCM_3_4_frame

/- N=3, degree=5; rows=4, columns=5, nullity=1. -/
def retainedCM_3_5D : ℤ := 60

def retainedCM_3_5CS : SparseIntMatrix 4 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 5), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 4), (⟨2, by decide⟩, 2), (⟨3, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 3), (⟨4, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 3), (⟨4, by decide⟩, 4)]
  | _ => []

def retainedCM_3_5WS : SparseIntMatrix 5 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, -10)]
  | 1 => [(⟨0, by decide⟩, 50)]
  | 2 => [(⟨0, by decide⟩, -20)]
  | 3 => [(⟨0, by decide⟩, -80)]
  | 4 => [(⟨0, by decide⟩, 60)]
  | _ => []

def retainedCM_3_5LS : SparseIntMatrix 1 5 := fun i =>
  match i.val with
  | 0 => [(⟨4, by decide⟩, 1)]
  | _ => []

def retainedCM_3_5ZS : SparseIntMatrix 5 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 12), (⟨1, by decide⟩, -3), (⟨2, by decide⟩, 2), (⟨3, by decide⟩, 2)]
  | 1 => [(⟨1, by decide⟩, 15), (⟨2, by decide⟩, -10), (⟨3, by decide⟩, -10)]
  | 2 => [(⟨2, by decide⟩, 20)]
  | 3 => [(⟨3, by decide⟩, 20)]
  | _ => []

def retainedCM_3_5C : Matrix (Fin 4) (Fin 5) ℚ := sparseRatMatrix retainedCM_3_5CS
def retainedCM_3_5U : Matrix (Fin 5) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_3_5D retainedCM_3_5WS
def retainedCM_3_5L : Matrix (Fin 1) (Fin 5) ℚ := sparseRatMatrix retainedCM_3_5LS
def retainedCM_3_5V : Matrix (Fin 5) (Fin 4) ℚ := sparseRatScaledMatrix retainedCM_3_5D retainedCM_3_5ZS

theorem retainedCM_3_5_sparse_check :
    SparseScaledFrameCheck retainedCM_3_5D retainedCM_3_5CS retainedCM_3_5WS retainedCM_3_5LS retainedCM_3_5ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_3_5_frame : HasKernelFrame retainedCM_3_5C retainedCM_3_5U retainedCM_3_5L retainedCM_3_5V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_3_5D≠0) retainedCM_3_5_sparse_check

theorem retainedCM_3_5_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_3_5C.mulVecLin)=1 :=
  kernelFrame_finrank retainedCM_3_5_frame

/- N=3, degree=6; rows=5, columns=7, nullity=2. -/
def retainedCM_3_6D : ℤ := 60

def retainedCM_3_6CS : SparseIntMatrix 5 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 6), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 5), (⟨2, by decide⟩, 2), (⟨4, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 4), (⟨3, by decide⟩, 6), (⟨5, by decide⟩, 1)]
  | 3 => [(⟨4, by decide⟩, 4), (⟨5, by decide⟩, 2)]
  | 4 => [(⟨5, by decide⟩, 3), (⟨6, by decide⟩, 6)]
  | _ => []

def retainedCM_3_6WS : SparseIntMatrix 7 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, -6), (⟨1, by decide⟩, 6)]
  | 1 => [(⟨0, by decide⟩, 36), (⟨1, by decide⟩, -36)]
  | 2 => [(⟨0, by decide⟩, -90), (⟨1, by decide⟩, 30)]
  | 3 => [(⟨0, by decide⟩, 60)]
  | 4 => [(⟨1, by decide⟩, 60)]
  | 5 => [(⟨1, by decide⟩, -120)]
  | 6 => [(⟨1, by decide⟩, 60)]
  | _ => []

def retainedCM_3_6LS : SparseIntMatrix 2 7 := fun i =>
  match i.val with
  | 0 => [(⟨3, by decide⟩, 1)]
  | 1 => [(⟨6, by decide⟩, 1)]
  | _ => []

def retainedCM_3_6ZS : SparseIntMatrix 7 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 10), (⟨1, by decide⟩, -2), (⟨2, by decide⟩, 1), (⟨3, by decide⟩, 1), (⟨4, by decide⟩, -1)]
  | 1 => [(⟨1, by decide⟩, 12), (⟨2, by decide⟩, -6), (⟨3, by decide⟩, -6), (⟨4, by decide⟩, 6)]
  | 2 => [(⟨2, by decide⟩, 15), (⟨4, by decide⟩, -5)]
  | 4 => [(⟨3, by decide⟩, 15), (⟨4, by decide⟩, -10)]
  | 5 => [(⟨4, by decide⟩, 20)]
  | _ => []

def retainedCM_3_6C : Matrix (Fin 5) (Fin 7) ℚ := sparseRatMatrix retainedCM_3_6CS
def retainedCM_3_6U : Matrix (Fin 7) (Fin 2) ℚ := sparseRatScaledMatrix retainedCM_3_6D retainedCM_3_6WS
def retainedCM_3_6L : Matrix (Fin 2) (Fin 7) ℚ := sparseRatMatrix retainedCM_3_6LS
def retainedCM_3_6V : Matrix (Fin 7) (Fin 5) ℚ := sparseRatScaledMatrix retainedCM_3_6D retainedCM_3_6ZS

theorem retainedCM_3_6_sparse_check :
    SparseScaledFrameCheck retainedCM_3_6D retainedCM_3_6CS retainedCM_3_6WS retainedCM_3_6LS retainedCM_3_6ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_3_6_frame : HasKernelFrame retainedCM_3_6C retainedCM_3_6U retainedCM_3_6L retainedCM_3_6V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_3_6D≠0) retainedCM_3_6_sparse_check

theorem retainedCM_3_6_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_3_6C.mulVecLin)=2 :=
  kernelFrame_finrank retainedCM_3_6_frame

/- N=3, degree=7; rows=7, columns=8, nullity=1. -/
def retainedCM_3_7D : ℤ := 420

def retainedCM_3_7CS : SparseIntMatrix 7 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 7), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 6), (⟨2, by decide⟩, 2), (⟨4, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 5), (⟨3, by decide⟩, 3), (⟨5, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 4), (⟨6, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 5), (⟨5, by decide⟩, 2)]
  | 5 => [(⟨5, by decide⟩, 4), (⟨6, by decide⟩, 6), (⟨7, by decide⟩, 4)]
  | 6 => [(⟨7, by decide⟩, 3)]
  | _ => []

def retainedCM_3_7WS : SparseIntMatrix 8 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 21)]
  | 1 => [(⟨0, by decide⟩, -147)]
  | 2 => [(⟨0, by decide⟩, 189)]
  | 3 => [(⟨0, by decide⟩, -105)]
  | 4 => [(⟨0, by decide⟩, 252)]
  | 5 => [(⟨0, by decide⟩, -630)]
  | 6 => [(⟨0, by decide⟩, 420)]
  | _ => []

def retainedCM_3_7LS : SparseIntMatrix 1 8 := fun i =>
  match i.val with
  | 0 => [(⟨6, by decide⟩, 1)]
  | _ => []

def retainedCM_3_7ZS : SparseIntMatrix 8 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 60), (⟨1, by decide⟩, -10), (⟨2, by decide⟩, 4), (⟨3, by decide⟩, -3), (⟨4, by decide⟩, 4), (⟨5, by decide⟩, -3), (⟨6, by decide⟩, 4)]
  | 1 => [(⟨1, by decide⟩, 70), (⟨2, by decide⟩, -28), (⟨3, by decide⟩, 21), (⟨4, by decide⟩, -28), (⟨5, by decide⟩, 21), (⟨6, by decide⟩, -28)]
  | 2 => [(⟨2, by decide⟩, 84), (⟨3, by decide⟩, -63), (⟨5, by decide⟩, -21), (⟨6, by decide⟩, 28)]
  | 3 => [(⟨3, by decide⟩, 105)]
  | 4 => [(⟨4, by decide⟩, 84), (⟨5, by decide⟩, -42), (⟨6, by decide⟩, 56)]
  | 5 => [(⟨5, by decide⟩, 105), (⟨6, by decide⟩, -140)]
  | 7 => [(⟨6, by decide⟩, 140)]
  | _ => []

def retainedCM_3_7C : Matrix (Fin 7) (Fin 8) ℚ := sparseRatMatrix retainedCM_3_7CS
def retainedCM_3_7U : Matrix (Fin 8) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_3_7D retainedCM_3_7WS
def retainedCM_3_7L : Matrix (Fin 1) (Fin 8) ℚ := sparseRatMatrix retainedCM_3_7LS
def retainedCM_3_7V : Matrix (Fin 8) (Fin 7) ℚ := sparseRatScaledMatrix retainedCM_3_7D retainedCM_3_7ZS

theorem retainedCM_3_7_sparse_check :
    SparseScaledFrameCheck retainedCM_3_7D retainedCM_3_7CS retainedCM_3_7WS retainedCM_3_7LS retainedCM_3_7ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_3_7_frame : HasKernelFrame retainedCM_3_7C retainedCM_3_7U retainedCM_3_7L retainedCM_3_7V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_3_7D≠0) retainedCM_3_7_sparse_check

theorem retainedCM_3_7_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_3_7C.mulVecLin)=1 :=
  kernelFrame_finrank retainedCM_3_7_frame

/- N=3, degree=8; rows=8, columns=10, nullity=2. -/
def retainedCM_3_8D : ℤ := 840

def retainedCM_3_8CS : SparseIntMatrix 8 10 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 8), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 7), (⟨2, by decide⟩, 2), (⟨5, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 6), (⟨3, by decide⟩, 3), (⟨6, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 5), (⟨4, by decide⟩, 8), (⟨7, by decide⟩, 1)]
  | 4 => [(⟨5, by decide⟩, 6), (⟨6, by decide⟩, 2)]
  | 5 => [(⟨6, by decide⟩, 5), (⟨7, by decide⟩, 3), (⟨8, by decide⟩, 4)]
  | 6 => [(⟨7, by decide⟩, 4), (⟨9, by decide⟩, 2)]
  | 7 => [(⟨8, by decide⟩, 4), (⟨9, by decide⟩, 6)]
  | _ => []

def retainedCM_3_8WS : SparseIntMatrix 10 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 24), (⟨1, by decide⟩, -24)]
  | 1 => [(⟨0, by decide⟩, -192), (⟨1, by decide⟩, 192)]
  | 2 => [(⟨0, by decide⟩, 672), (⟨1, by decide⟩, -252)]
  | 3 => [(⟨0, by decide⟩, -1344), (⟨1, by decide⟩, 84)]
  | 4 => [(⟨0, by decide⟩, 840)]
  | 5 => [(⟨1, by decide⟩, -420)]
  | 6 => [(⟨1, by decide⟩, 1260)]
  | 7 => [(⟨1, by decide⟩, -420)]
  | 8 => [(⟨1, by decide⟩, -1260)]
  | 9 => [(⟨1, by decide⟩, 840)]
  | _ => []

def retainedCM_3_8LS : SparseIntMatrix 2 10 := fun i =>
  match i.val with
  | 0 => [(⟨4, by decide⟩, 1)]
  | 1 => [(⟨9, by decide⟩, 1)]
  | _ => []

def retainedCM_3_8ZS : SparseIntMatrix 10 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 105), (⟨1, by decide⟩, -15), (⟨2, by decide⟩, 5), (⟨3, by decide⟩, -3), (⟨4, by decide⟩, 5), (⟨5, by decide⟩, -3), (⟨6, by decide⟩, 3), (⟨7, by decide⟩, 3)]
  | 1 => [(⟨1, by decide⟩, 120), (⟨2, by decide⟩, -40), (⟨3, by decide⟩, 24), (⟨4, by decide⟩, -40), (⟨5, by decide⟩, 24), (⟨6, by decide⟩, -24), (⟨7, by decide⟩, -24)]
  | 2 => [(⟨2, by decide⟩, 140), (⟨3, by decide⟩, -84), (⟨5, by decide⟩, -28), (⟨6, by decide⟩, 42), (⟨7, by decide⟩, 28)]
  | 3 => [(⟨3, by decide⟩, 168), (⟨6, by decide⟩, -42)]
  | 5 => [(⟨4, by decide⟩, 140), (⟨5, by decide⟩, -56), (⟨6, by decide⟩, 42), (⟨7, by decide⟩, 56)]
  | 6 => [(⟨5, by decide⟩, 168), (⟨6, by decide⟩, -126), (⟨7, by decide⟩, -168)]
  | 7 => [(⟨6, by decide⟩, 210)]
  | 8 => [(⟨7, by decide⟩, 210)]
  | _ => []

def retainedCM_3_8C : Matrix (Fin 8) (Fin 10) ℚ := sparseRatMatrix retainedCM_3_8CS
def retainedCM_3_8U : Matrix (Fin 10) (Fin 2) ℚ := sparseRatScaledMatrix retainedCM_3_8D retainedCM_3_8WS
def retainedCM_3_8L : Matrix (Fin 2) (Fin 10) ℚ := sparseRatMatrix retainedCM_3_8LS
def retainedCM_3_8V : Matrix (Fin 10) (Fin 8) ℚ := sparseRatScaledMatrix retainedCM_3_8D retainedCM_3_8ZS

theorem retainedCM_3_8_sparse_check :
    SparseScaledFrameCheck retainedCM_3_8D retainedCM_3_8CS retainedCM_3_8WS retainedCM_3_8LS retainedCM_3_8ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_3_8_frame : HasKernelFrame retainedCM_3_8C retainedCM_3_8U retainedCM_3_8L retainedCM_3_8V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_3_8D≠0) retainedCM_3_8_sparse_check

theorem retainedCM_3_8_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_3_8C.mulVecLin)=2 :=
  kernelFrame_finrank retainedCM_3_8_frame

/- N=4, degree=0; rows=0, columns=1, nullity=1. -/
def retainedCM_4_0D : ℤ := 1

def retainedCM_4_0CS : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def retainedCM_4_0WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def retainedCM_4_0LS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def retainedCM_4_0ZS : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def retainedCM_4_0C : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix retainedCM_4_0CS
def retainedCM_4_0U : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_4_0D retainedCM_4_0WS
def retainedCM_4_0L : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix retainedCM_4_0LS
def retainedCM_4_0V : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix retainedCM_4_0D retainedCM_4_0ZS

theorem retainedCM_4_0_sparse_check :
    SparseScaledFrameCheck retainedCM_4_0D retainedCM_4_0CS retainedCM_4_0WS retainedCM_4_0LS retainedCM_4_0ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_0_frame : HasKernelFrame retainedCM_4_0C retainedCM_4_0U retainedCM_4_0L retainedCM_4_0V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_0D≠0) retainedCM_4_0_sparse_check

theorem retainedCM_4_0_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_0C.mulVecLin)=1 :=
  kernelFrame_finrank retainedCM_4_0_frame

/- N=4, degree=1; rows=1, columns=1, nullity=0. -/
def retainedCM_4_1D : ℤ := 1

def retainedCM_4_1CS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def retainedCM_4_1WS : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def retainedCM_4_1LS : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def retainedCM_4_1ZS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def retainedCM_4_1C : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix retainedCM_4_1CS
def retainedCM_4_1U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix retainedCM_4_1D retainedCM_4_1WS
def retainedCM_4_1L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix retainedCM_4_1LS
def retainedCM_4_1V : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_4_1D retainedCM_4_1ZS

theorem retainedCM_4_1_sparse_check :
    SparseScaledFrameCheck retainedCM_4_1D retainedCM_4_1CS retainedCM_4_1WS retainedCM_4_1LS retainedCM_4_1ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_1_frame : HasKernelFrame retainedCM_4_1C retainedCM_4_1U retainedCM_4_1L retainedCM_4_1V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_1D≠0) retainedCM_4_1_sparse_check

theorem retainedCM_4_1_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_1C.mulVecLin)=0 :=
  kernelFrame_finrank retainedCM_4_1_frame

/- N=4, degree=2; rows=1, columns=2, nullity=1. -/
def retainedCM_4_2D : ℤ := 2

def retainedCM_4_2CS : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 2), (⟨1, by decide⟩, 2)]
  | _ => []

def retainedCM_4_2WS : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, -2)]
  | 1 => [(⟨0, by decide⟩, 2)]
  | _ => []

def retainedCM_4_2LS : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨1, by decide⟩, 1)]
  | _ => []

def retainedCM_4_2ZS : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def retainedCM_4_2C : Matrix (Fin 1) (Fin 2) ℚ := sparseRatMatrix retainedCM_4_2CS
def retainedCM_4_2U : Matrix (Fin 2) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_4_2D retainedCM_4_2WS
def retainedCM_4_2L : Matrix (Fin 1) (Fin 2) ℚ := sparseRatMatrix retainedCM_4_2LS
def retainedCM_4_2V : Matrix (Fin 2) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_4_2D retainedCM_4_2ZS

theorem retainedCM_4_2_sparse_check :
    SparseScaledFrameCheck retainedCM_4_2D retainedCM_4_2CS retainedCM_4_2WS retainedCM_4_2LS retainedCM_4_2ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_2_frame : HasKernelFrame retainedCM_4_2C retainedCM_4_2U retainedCM_4_2L retainedCM_4_2V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_2D≠0) retainedCM_4_2_sparse_check

theorem retainedCM_4_2_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_2C.mulVecLin)=1 :=
  kernelFrame_finrank retainedCM_4_2_frame

/- N=4, degree=3; rows=2, columns=3, nullity=1. -/
def retainedCM_4_3D : ℤ := 6

def retainedCM_4_3CS : SparseIntMatrix 2 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 2), (⟨2, by decide⟩, 3)]
  | _ => []

def retainedCM_4_3WS : SparseIntMatrix 3 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3)]
  | 1 => [(⟨0, by decide⟩, -9)]
  | 2 => [(⟨0, by decide⟩, 6)]
  | _ => []

def retainedCM_4_3LS : SparseIntMatrix 1 3 := fun i =>
  match i.val with
  | 0 => [(⟨2, by decide⟩, 1)]
  | _ => []

def retainedCM_4_3ZS : SparseIntMatrix 3 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 2), (⟨1, by decide⟩, -1)]
  | 1 => [(⟨1, by decide⟩, 3)]
  | _ => []

def retainedCM_4_3C : Matrix (Fin 2) (Fin 3) ℚ := sparseRatMatrix retainedCM_4_3CS
def retainedCM_4_3U : Matrix (Fin 3) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_4_3D retainedCM_4_3WS
def retainedCM_4_3L : Matrix (Fin 1) (Fin 3) ℚ := sparseRatMatrix retainedCM_4_3LS
def retainedCM_4_3V : Matrix (Fin 3) (Fin 2) ℚ := sparseRatScaledMatrix retainedCM_4_3D retainedCM_4_3ZS

theorem retainedCM_4_3_sparse_check :
    SparseScaledFrameCheck retainedCM_4_3D retainedCM_4_3CS retainedCM_4_3WS retainedCM_4_3LS retainedCM_4_3ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_3_frame : HasKernelFrame retainedCM_4_3C retainedCM_4_3U retainedCM_4_3L retainedCM_4_3V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_3D≠0) retainedCM_4_3_sparse_check

theorem retainedCM_4_3_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_3C.mulVecLin)=1 :=
  kernelFrame_finrank retainedCM_4_3_frame

/- N=4, degree=4; rows=3, columns=5, nullity=2. -/
def retainedCM_4_4D : ℤ := 12

def retainedCM_4_4CS : SparseIntMatrix 3 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 4), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 3), (⟨2, by decide⟩, 4), (⟨3, by decide⟩, 2)]
  | 2 => [(⟨3, by decide⟩, 2), (⟨4, by decide⟩, 4)]
  | _ => []

def retainedCM_4_4WS : SparseIntMatrix 5 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 4), (⟨1, by decide⟩, -4)]
  | 1 => [(⟨0, by decide⟩, -16), (⟨1, by decide⟩, 16)]
  | 2 => [(⟨0, by decide⟩, 12)]
  | 3 => [(⟨1, by decide⟩, -24)]
  | 4 => [(⟨1, by decide⟩, 12)]
  | _ => []

def retainedCM_4_4LS : SparseIntMatrix 2 5 := fun i =>
  match i.val with
  | 0 => [(⟨2, by decide⟩, 1)]
  | 1 => [(⟨4, by decide⟩, 1)]
  | _ => []

def retainedCM_4_4ZS : SparseIntMatrix 5 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3), (⟨1, by decide⟩, -1), (⟨2, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 4), (⟨2, by decide⟩, -4)]
  | 3 => [(⟨2, by decide⟩, 6)]
  | _ => []

def retainedCM_4_4C : Matrix (Fin 3) (Fin 5) ℚ := sparseRatMatrix retainedCM_4_4CS
def retainedCM_4_4U : Matrix (Fin 5) (Fin 2) ℚ := sparseRatScaledMatrix retainedCM_4_4D retainedCM_4_4WS
def retainedCM_4_4L : Matrix (Fin 2) (Fin 5) ℚ := sparseRatMatrix retainedCM_4_4LS
def retainedCM_4_4V : Matrix (Fin 5) (Fin 3) ℚ := sparseRatScaledMatrix retainedCM_4_4D retainedCM_4_4ZS

theorem retainedCM_4_4_sparse_check :
    SparseScaledFrameCheck retainedCM_4_4D retainedCM_4_4CS retainedCM_4_4WS retainedCM_4_4LS retainedCM_4_4ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_4_frame : HasKernelFrame retainedCM_4_4C retainedCM_4_4U retainedCM_4_4L retainedCM_4_4V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_4D≠0) retainedCM_4_4_sparse_check

theorem retainedCM_4_4_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_4C.mulVecLin)=2 :=
  kernelFrame_finrank retainedCM_4_4_frame

/- N=4, degree=5; rows=5, columns=6, nullity=1. -/
def retainedCM_4_5D : ℤ := 60

def retainedCM_4_5CS : SparseIntMatrix 5 6 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 5), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 4), (⟨2, by decide⟩, 2), (⟨3, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 3), (⟨4, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 3), (⟨4, by decide⟩, 4), (⟨5, by decide⟩, 3)]
  | 4 => [(⟨5, by decide⟩, 2)]
  | _ => []

def retainedCM_4_5WS : SparseIntMatrix 6 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, -10)]
  | 1 => [(⟨0, by decide⟩, 50)]
  | 2 => [(⟨0, by decide⟩, -20)]
  | 3 => [(⟨0, by decide⟩, -80)]
  | 4 => [(⟨0, by decide⟩, 60)]
  | _ => []

def retainedCM_4_5LS : SparseIntMatrix 1 6 := fun i =>
  match i.val with
  | 0 => [(⟨4, by decide⟩, 1)]
  | _ => []

def retainedCM_4_5ZS : SparseIntMatrix 6 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 12), (⟨1, by decide⟩, -3), (⟨2, by decide⟩, 2), (⟨3, by decide⟩, 2), (⟨4, by decide⟩, -3)]
  | 1 => [(⟨1, by decide⟩, 15), (⟨2, by decide⟩, -10), (⟨3, by decide⟩, -10), (⟨4, by decide⟩, 15)]
  | 2 => [(⟨2, by decide⟩, 20)]
  | 3 => [(⟨3, by decide⟩, 20), (⟨4, by decide⟩, -30)]
  | 5 => [(⟨4, by decide⟩, 30)]
  | _ => []

def retainedCM_4_5C : Matrix (Fin 5) (Fin 6) ℚ := sparseRatMatrix retainedCM_4_5CS
def retainedCM_4_5U : Matrix (Fin 6) (Fin 1) ℚ := sparseRatScaledMatrix retainedCM_4_5D retainedCM_4_5WS
def retainedCM_4_5L : Matrix (Fin 1) (Fin 6) ℚ := sparseRatMatrix retainedCM_4_5LS
def retainedCM_4_5V : Matrix (Fin 6) (Fin 5) ℚ := sparseRatScaledMatrix retainedCM_4_5D retainedCM_4_5ZS

theorem retainedCM_4_5_sparse_check :
    SparseScaledFrameCheck retainedCM_4_5D retainedCM_4_5CS retainedCM_4_5WS retainedCM_4_5LS retainedCM_4_5ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_5_frame : HasKernelFrame retainedCM_4_5C retainedCM_4_5U retainedCM_4_5L retainedCM_4_5V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_5D≠0) retainedCM_4_5_sparse_check

theorem retainedCM_4_5_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_5C.mulVecLin)=1 :=
  kernelFrame_finrank retainedCM_4_5_frame

/- N=4, degree=6; rows=6, columns=9, nullity=3. -/
def retainedCM_4_6D : ℤ := 60

def retainedCM_4_6CS : SparseIntMatrix 6 9 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 6), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 5), (⟨2, by decide⟩, 2), (⟨4, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 4), (⟨3, by decide⟩, 6), (⟨5, by decide⟩, 1)]
  | 3 => [(⟨4, by decide⟩, 4), (⟨5, by decide⟩, 2), (⟨7, by decide⟩, 3)]
  | 4 => [(⟨5, by decide⟩, 3), (⟨6, by decide⟩, 6), (⟨8, by decide⟩, 2)]
  | 5 => [(⟨7, by decide⟩, 3), (⟨8, by decide⟩, 4)]
  | _ => []

def retainedCM_4_6WS : SparseIntMatrix 9 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, -6), (⟨1, by decide⟩, 6), (⟨2, by decide⟩, 6)]
  | 1 => [(⟨0, by decide⟩, 36), (⟨1, by decide⟩, -36), (⟨2, by decide⟩, -36)]
  | 2 => [(⟨0, by decide⟩, -90), (⟨1, by decide⟩, 30), (⟨2, by decide⟩, 10)]
  | 3 => [(⟨0, by decide⟩, 60)]
  | 4 => [(⟨1, by decide⟩, 60), (⟨2, by decide⟩, 80)]
  | 5 => [(⟨1, by decide⟩, -120), (⟨2, by decide⟩, -40)]
  | 6 => [(⟨1, by decide⟩, 60)]
  | 7 => [(⟨2, by decide⟩, -80)]
  | 8 => [(⟨2, by decide⟩, 60)]
  | _ => []

def retainedCM_4_6LS : SparseIntMatrix 3 9 := fun i =>
  match i.val with
  | 0 => [(⟨3, by decide⟩, 1)]
  | 1 => [(⟨6, by decide⟩, 1)]
  | 2 => [(⟨8, by decide⟩, 1)]
  | _ => []

def retainedCM_4_6ZS : SparseIntMatrix 9 6 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 10), (⟨1, by decide⟩, -2), (⟨2, by decide⟩, 1), (⟨3, by decide⟩, 1), (⟨4, by decide⟩, -1), (⟨5, by decide⟩, -1)]
  | 1 => [(⟨1, by decide⟩, 12), (⟨2, by decide⟩, -6), (⟨3, by decide⟩, -6), (⟨4, by decide⟩, 6), (⟨5, by decide⟩, 6)]
  | 2 => [(⟨2, by decide⟩, 15), (⟨4, by decide⟩, -5)]
  | 4 => [(⟨3, by decide⟩, 15), (⟨4, by decide⟩, -10), (⟨5, by decide⟩, -15)]
  | 5 => [(⟨4, by decide⟩, 20)]
  | 7 => [(⟨5, by decide⟩, 20)]
  | _ => []

def retainedCM_4_6C : Matrix (Fin 6) (Fin 9) ℚ := sparseRatMatrix retainedCM_4_6CS
def retainedCM_4_6U : Matrix (Fin 9) (Fin 3) ℚ := sparseRatScaledMatrix retainedCM_4_6D retainedCM_4_6WS
def retainedCM_4_6L : Matrix (Fin 3) (Fin 9) ℚ := sparseRatMatrix retainedCM_4_6LS
def retainedCM_4_6V : Matrix (Fin 9) (Fin 6) ℚ := sparseRatScaledMatrix retainedCM_4_6D retainedCM_4_6ZS

theorem retainedCM_4_6_sparse_check :
    SparseScaledFrameCheck retainedCM_4_6D retainedCM_4_6CS retainedCM_4_6WS retainedCM_4_6LS retainedCM_4_6ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_6_frame : HasKernelFrame retainedCM_4_6C retainedCM_4_6U retainedCM_4_6L retainedCM_4_6V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_6D≠0) retainedCM_4_6_sparse_check

theorem retainedCM_4_6_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_6C.mulVecLin)=3 :=
  kernelFrame_finrank retainedCM_4_6_frame

/- N=4, degree=7; rows=9, columns=11, nullity=2. -/
def retainedCM_4_7D : ℤ := 420

def retainedCM_4_7CS : SparseIntMatrix 9 11 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 7), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 6), (⟨2, by decide⟩, 2), (⟨4, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 5), (⟨3, by decide⟩, 3), (⟨5, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 4), (⟨6, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 5), (⟨5, by decide⟩, 2), (⟨8, by decide⟩, 3)]
  | 5 => [(⟨5, by decide⟩, 4), (⟨6, by decide⟩, 6), (⟨7, by decide⟩, 4), (⟨9, by decide⟩, 2)]
  | 6 => [(⟨7, by decide⟩, 3), (⟨10, by decide⟩, 1)]
  | 7 => [(⟨8, by decide⟩, 4), (⟨9, by decide⟩, 2)]
  | 8 => [(⟨9, by decide⟩, 3), (⟨10, by decide⟩, 6)]
  | _ => []

def retainedCM_4_7WS : SparseIntMatrix 11 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 21), (⟨1, by decide⟩, -28)]
  | 1 => [(⟨0, by decide⟩, -147), (⟨1, by decide⟩, 196)]
  | 2 => [(⟨0, by decide⟩, 189), (⟨1, by decide⟩, -112)]
  | 3 => [(⟨0, by decide⟩, -105)]
  | 4 => [(⟨0, by decide⟩, 252), (⟨1, by decide⟩, -476)]
  | 5 => [(⟨0, by decide⟩, -630), (⟨1, by decide⟩, 560)]
  | 6 => [(⟨0, by decide⟩, 420)]
  | 7 => [(⟨1, by decide⟩, -140)]
  | 8 => [(⟨1, by decide⟩, 420)]
  | 9 => [(⟨1, by decide⟩, -840)]
  | 10 => [(⟨1, by decide⟩, 420)]
  | _ => []

def retainedCM_4_7LS : SparseIntMatrix 2 11 := fun i =>
  match i.val with
  | 0 => [(⟨6, by decide⟩, 1)]
  | 1 => [(⟨10, by decide⟩, 1)]
  | _ => []

def retainedCM_4_7ZS : SparseIntMatrix 11 9 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 60), (⟨1, by decide⟩, -10), (⟨2, by decide⟩, 4), (⟨3, by decide⟩, -3), (⟨4, by decide⟩, 4), (⟨5, by decide⟩, -3), (⟨6, by decide⟩, 4), (⟨7, by decide⟩, -3), (⟨8, by decide⟩, 4)]
  | 1 => [(⟨1, by decide⟩, 70), (⟨2, by decide⟩, -28), (⟨3, by decide⟩, 21), (⟨4, by decide⟩, -28), (⟨5, by decide⟩, 21), (⟨6, by decide⟩, -28), (⟨7, by decide⟩, 21), (⟨8, by decide⟩, -28)]
  | 2 => [(⟨2, by decide⟩, 84), (⟨3, by decide⟩, -63), (⟨5, by decide⟩, -21), (⟨6, by decide⟩, 28), (⟨8, by decide⟩, 14)]
  | 3 => [(⟨3, by decide⟩, 105)]
  | 4 => [(⟨4, by decide⟩, 84), (⟨5, by decide⟩, -42), (⟨6, by decide⟩, 56), (⟨7, by decide⟩, -63), (⟨8, by decide⟩, 70)]
  | 5 => [(⟨5, by decide⟩, 105), (⟨6, by decide⟩, -140), (⟨8, by decide⟩, -70)]
  | 7 => [(⟨6, by decide⟩, 140)]
  | 8 => [(⟨7, by decide⟩, 105), (⟨8, by decide⟩, -70)]
  | 9 => [(⟨8, by decide⟩, 140)]
  | _ => []

def retainedCM_4_7C : Matrix (Fin 9) (Fin 11) ℚ := sparseRatMatrix retainedCM_4_7CS
def retainedCM_4_7U : Matrix (Fin 11) (Fin 2) ℚ := sparseRatScaledMatrix retainedCM_4_7D retainedCM_4_7WS
def retainedCM_4_7L : Matrix (Fin 2) (Fin 11) ℚ := sparseRatMatrix retainedCM_4_7LS
def retainedCM_4_7V : Matrix (Fin 11) (Fin 9) ℚ := sparseRatScaledMatrix retainedCM_4_7D retainedCM_4_7ZS

theorem retainedCM_4_7_sparse_check :
    SparseScaledFrameCheck retainedCM_4_7D retainedCM_4_7CS retainedCM_4_7WS retainedCM_4_7LS retainedCM_4_7ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_7_frame : HasKernelFrame retainedCM_4_7C retainedCM_4_7U retainedCM_4_7L retainedCM_4_7V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_7D≠0) retainedCM_4_7_sparse_check

theorem retainedCM_4_7_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_7C.mulVecLin)=2 :=
  kernelFrame_finrank retainedCM_4_7_frame

/- N=4, degree=8; rows=11, columns=15, nullity=4. -/
def retainedCM_4_8D : ℤ := 840

def retainedCM_4_8CS : SparseIntMatrix 11 15 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 8), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 7), (⟨2, by decide⟩, 2), (⟨5, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 6), (⟨3, by decide⟩, 3), (⟨6, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 5), (⟨4, by decide⟩, 8), (⟨7, by decide⟩, 1)]
  | 4 => [(⟨5, by decide⟩, 6), (⟨6, by decide⟩, 2), (⟨10, by decide⟩, 3)]
  | 5 => [(⟨6, by decide⟩, 5), (⟨7, by decide⟩, 3), (⟨8, by decide⟩, 4), (⟨11, by decide⟩, 2)]
  | 6 => [(⟨7, by decide⟩, 4), (⟨9, by decide⟩, 2), (⟨12, by decide⟩, 2)]
  | 7 => [(⟨8, by decide⟩, 4), (⟨9, by decide⟩, 6), (⟨13, by decide⟩, 1)]
  | 8 => [(⟨10, by decide⟩, 5), (⟨11, by decide⟩, 2)]
  | 9 => [(⟨11, by decide⟩, 4), (⟨12, by decide⟩, 6), (⟨13, by decide⟩, 4)]
  | 10 => [(⟨13, by decide⟩, 3), (⟨14, by decide⟩, 8)]
  | _ => []

def retainedCM_4_8WS : SparseIntMatrix 15 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 24), (⟨1, by decide⟩, -24), (⟨2, by decide⟩, -24), (⟨3, by decide⟩, 40)]
  | 1 => [(⟨0, by decide⟩, -192), (⟨1, by decide⟩, 192), (⟨2, by decide⟩, 192), (⟨3, by decide⟩, -320)]
  | 2 => [(⟨0, by decide⟩, 672), (⟨1, by decide⟩, -252), (⟨2, by decide⟩, -168), (⟨3, by decide⟩, 224)]
  | 3 => [(⟨0, by decide⟩, -1344), (⟨1, by decide⟩, 84), (⟨2, by decide⟩, 84)]
  | 4 => [(⟨0, by decide⟩, 840)]
  | 5 => [(⟨1, by decide⟩, -420), (⟨2, by decide⟩, -504), (⟨3, by decide⟩, 896)]
  | 6 => [(⟨1, by decide⟩, 1260), (⟨2, by decide⟩, 756), (⟨3, by decide⟩, -1344)]
  | 7 => [(⟨1, by decide⟩, -420), (⟨2, by decide⟩, -420)]
  | 8 => [(⟨1, by decide⟩, -1260), (⟨3, by decide⟩, 560)]
  | 9 => [(⟨1, by decide⟩, 840)]
  | 10 => [(⟨2, by decide⟩, 504), (⟨3, by decide⟩, -896)]
  | 11 => [(⟨2, by decide⟩, -1260), (⟨3, by decide⟩, 2240)]
  | 12 => [(⟨2, by decide⟩, 840)]
  | 13 => [(⟨3, by decide⟩, -2240)]
  | 14 => [(⟨3, by decide⟩, 840)]
  | _ => []

def retainedCM_4_8LS : SparseIntMatrix 4 15 := fun i =>
  match i.val with
  | 0 => [(⟨4, by decide⟩, 1)]
  | 1 => [(⟨9, by decide⟩, 1)]
  | 2 => [(⟨12, by decide⟩, 1)]
  | 3 => [(⟨14, by decide⟩, 1)]
  | _ => []

def retainedCM_4_8ZS : SparseIntMatrix 15 11 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 105), (⟨1, by decide⟩, -15), (⟨2, by decide⟩, 5), (⟨3, by decide⟩, -3), (⟨4, by decide⟩, 5), (⟨5, by decide⟩, -3), (⟨6, by decide⟩, 3), (⟨7, by decide⟩, 3), (⟨8, by decide⟩, -3), (⟨9, by decide⟩, 3), (⟨10, by decide⟩, -5)]
  | 1 => [(⟨1, by decide⟩, 120), (⟨2, by decide⟩, -40), (⟨3, by decide⟩, 24), (⟨4, by decide⟩, -40), (⟨5, by decide⟩, 24), (⟨6, by decide⟩, -24), (⟨7, by decide⟩, -24), (⟨8, by decide⟩, 24), (⟨9, by decide⟩, -24), (⟨10, by decide⟩, 40)]
  | 2 => [(⟨2, by decide⟩, 140), (⟨3, by decide⟩, -84), (⟨5, by decide⟩, -28), (⟨6, by decide⟩, 42), (⟨7, by decide⟩, 28), (⟨9, by decide⟩, 14), (⟨10, by decide⟩, -28)]
  | 3 => [(⟨3, by decide⟩, 168), (⟨6, by decide⟩, -42)]
  | 5 => [(⟨4, by decide⟩, 140), (⟨5, by decide⟩, -56), (⟨6, by decide⟩, 42), (⟨7, by decide⟩, 56), (⟨8, by decide⟩, -84), (⟨9, by decide⟩, 70), (⟨10, by decide⟩, -112)]
  | 6 => [(⟨5, by decide⟩, 168), (⟨6, by decide⟩, -126), (⟨7, by decide⟩, -168), (⟨9, by decide⟩, -84), (⟨10, by decide⟩, 168)]
  | 7 => [(⟨6, by decide⟩, 210)]
  | 8 => [(⟨7, by decide⟩, 210), (⟨10, by decide⟩, -70)]
  | 10 => [(⟨8, by decide⟩, 168), (⟨9, by decide⟩, -84), (⟨10, by decide⟩, 112)]
  | 11 => [(⟨9, by decide⟩, 210), (⟨10, by decide⟩, -280)]
  | 13 => [(⟨10, by decide⟩, 280)]
  | _ => []

def retainedCM_4_8C : Matrix (Fin 11) (Fin 15) ℚ := sparseRatMatrix retainedCM_4_8CS
def retainedCM_4_8U : Matrix (Fin 15) (Fin 4) ℚ := sparseRatScaledMatrix retainedCM_4_8D retainedCM_4_8WS
def retainedCM_4_8L : Matrix (Fin 4) (Fin 15) ℚ := sparseRatMatrix retainedCM_4_8LS
def retainedCM_4_8V : Matrix (Fin 15) (Fin 11) ℚ := sparseRatScaledMatrix retainedCM_4_8D retainedCM_4_8ZS

theorem retainedCM_4_8_sparse_check :
    SparseScaledFrameCheck retainedCM_4_8D retainedCM_4_8CS retainedCM_4_8WS retainedCM_4_8LS retainedCM_4_8ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_8_frame : HasKernelFrame retainedCM_4_8C retainedCM_4_8U retainedCM_4_8L retainedCM_4_8V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_8D≠0) retainedCM_4_8_sparse_check

theorem retainedCM_4_8_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_8C.mulVecLin)=4 :=
  kernelFrame_finrank retainedCM_4_8_frame

/- N=4, degree=9; rows=15, columns=18, nullity=3. -/
def retainedCM_4_9D : ℤ := 2520

def retainedCM_4_9CS : SparseIntMatrix 15 18 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 9), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 8), (⟨2, by decide⟩, 2), (⟨5, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 7), (⟨3, by decide⟩, 3), (⟨6, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 6), (⟨4, by decide⟩, 4), (⟨7, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 5), (⟨8, by decide⟩, 1)]
  | 5 => [(⟨5, by decide⟩, 7), (⟨6, by decide⟩, 2), (⟨12, by decide⟩, 3)]
  | 6 => [(⟨6, by decide⟩, 6), (⟨7, by decide⟩, 3), (⟨9, by decide⟩, 4), (⟨13, by decide⟩, 2)]
  | 7 => [(⟨7, by decide⟩, 5), (⟨8, by decide⟩, 8), (⟨10, by decide⟩, 2), (⟨14, by decide⟩, 2)]
  | 8 => [(⟨9, by decide⟩, 5), (⟨10, by decide⟩, 3), (⟨15, by decide⟩, 1)]
  | 9 => [(⟨10, by decide⟩, 4), (⟨11, by decide⟩, 9), (⟨16, by decide⟩, 1)]
  | 10 => [(⟨12, by decide⟩, 6), (⟨13, by decide⟩, 2)]
  | 11 => [(⟨13, by decide⟩, 5), (⟨14, by decide⟩, 3), (⟨15, by decide⟩, 4)]
  | 12 => [(⟨14, by decide⟩, 4), (⟨16, by decide⟩, 2)]
  | 13 => [(⟨15, by decide⟩, 4), (⟨16, by decide⟩, 6), (⟨17, by decide⟩, 6)]
  | 14 => [(⟨17, by decide⟩, 3)]
  | _ => []

def retainedCM_4_9WS : SparseIntMatrix 18 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, -36), (⟨1, by decide⟩, 45), (⟨2, by decide⟩, 45)]
  | 1 => [(⟨0, by decide⟩, 324), (⟨1, by decide⟩, -405), (⟨2, by decide⟩, -405)]
  | 2 => [(⟨0, by decide⟩, -720), (⟨1, by decide⟩, 648), (⟨2, by decide⟩, 396)]
  | 3 => [(⟨0, by decide⟩, 1008), (⟨1, by decide⟩, -378), (⟨2, by decide⟩, -126)]
  | 4 => [(⟨0, by decide⟩, -504)]
  | 5 => [(⟨0, by decide⟩, -576), (⟨1, by decide⟩, 972), (⟨2, by decide⟩, 1224)]
  | 6 => [(⟨0, by decide⟩, 2016), (⟨1, by decide⟩, -3402), (⟨2, by decide⟩, -2394)]
  | 7 => [(⟨0, by decide⟩, -4032), (⟨1, by decide⟩, 2268), (⟨2, by decide⟩, 756)]
  | 8 => [(⟨0, by decide⟩, 2520)]
  | 9 => [(⟨1, by decide⟩, 3402), (⟨2, by decide⟩, 1134)]
  | 10 => [(⟨1, by decide⟩, -5670), (⟨2, by decide⟩, -630)]
  | 11 => [(⟨1, by decide⟩, 2520)]
  | 12 => [(⟨2, by decide⟩, -1260)]
  | 13 => [(⟨2, by decide⟩, 3780)]
  | 14 => [(⟨2, by decide⟩, -1260)]
  | 15 => [(⟨2, by decide⟩, -3780)]
  | 16 => [(⟨2, by decide⟩, 2520)]
  | _ => []

def retainedCM_4_9LS : SparseIntMatrix 3 18 := fun i =>
  match i.val with
  | 0 => [(⟨8, by decide⟩, 1)]
  | 1 => [(⟨11, by decide⟩, 1)]
  | 2 => [(⟨16, by decide⟩, 1)]
  | _ => []

def retainedCM_4_9ZS : SparseIntMatrix 18 15 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 280), (⟨1, by decide⟩, -35), (⟨2, by decide⟩, 10), (⟨3, by decide⟩, -5), (⟨4, by decide⟩, 4), (⟨5, by decide⟩, 10), (⟨6, by decide⟩, -5), (⟨7, by decide⟩, 4), (⟨8, by decide⟩, 4), (⟨9, by decide⟩, -5), (⟨10, by decide⟩, -5), (⟨11, by decide⟩, 4), (⟨12, by decide⟩, -5), (⟨13, by decide⟩, -5), (⟨14, by decide⟩, 10)]
  | 1 => [(⟨1, by decide⟩, 315), (⟨2, by decide⟩, -90), (⟨3, by decide⟩, 45), (⟨4, by decide⟩, -36), (⟨5, by decide⟩, -90), (⟨6, by decide⟩, 45), (⟨7, by decide⟩, -36), (⟨8, by decide⟩, -36), (⟨9, by decide⟩, 45), (⟨10, by decide⟩, 45), (⟨11, by decide⟩, -36), (⟨12, by decide⟩, 45), (⟨13, by decide⟩, 45), (⟨14, by decide⟩, -90)]
  | 2 => [(⟨2, by decide⟩, 360), (⟨3, by decide⟩, -180), (⟨4, by decide⟩, 144), (⟨6, by decide⟩, -60), (⟨7, by decide⟩, 72), (⟨8, by decide⟩, 48), (⟨9, by decide⟩, -72), (⟨11, by decide⟩, 24), (⟨12, by decide⟩, -54), (⟨13, by decide⟩, -36), (⟨14, by decide⟩, 72)]
  | 3 => [(⟨3, by decide⟩, 420), (⟨4, by decide⟩, -336), (⟨7, by decide⟩, -84), (⟨9, by decide⟩, 42), (⟨12, by decide⟩, 42)]
  | 4 => [(⟨4, by decide⟩, 504)]
  | 5 => [(⟨5, by decide⟩, 360), (⟨6, by decide⟩, -120), (⟨7, by decide⟩, 72), (⟨8, by decide⟩, 96), (⟨9, by decide⟩, -108), (⟨10, by decide⟩, -180), (⟨11, by decide⟩, 120), (⟨12, by decide⟩, -126), (⟨13, by decide⟩, -144), (⟨14, by decide⟩, 288)]
  | 6 => [(⟨6, by decide⟩, 420), (⟨7, by decide⟩, -252), (⟨8, by decide⟩, -336), (⟨9, by decide⟩, 378), (⟨11, by decide⟩, -168), (⟨12, by decide⟩, 252), (⟨13, by decide⟩, 252), (⟨14, by decide⟩, -504)]
  | 7 => [(⟨7, by decide⟩, 504), (⟨9, by decide⟩, -252), (⟨12, by decide⟩, -252)]
  | 9 => [(⟨8, by decide⟩, 504), (⟨9, by decide⟩, -378), (⟨13, by decide⟩, -126), (⟨14, by decide⟩, 252)]
  | 10 => [(⟨9, by decide⟩, 630)]
  | 12 => [(⟨10, by decide⟩, 420), (⟨11, by decide⟩, -168), (⟨12, by decide⟩, 126), (⟨13, by decide⟩, 168), (⟨14, by decide⟩, -336)]
  | 13 => [(⟨11, by decide⟩, 504), (⟨12, by decide⟩, -378), (⟨13, by decide⟩, -504), (⟨14, by decide⟩, 1008)]
  | 14 => [(⟨12, by decide⟩, 630)]
  | 15 => [(⟨13, by decide⟩, 630), (⟨14, by decide⟩, -1260)]
  | 17 => [(⟨14, by decide⟩, 840)]
  | _ => []

def retainedCM_4_9C : Matrix (Fin 15) (Fin 18) ℚ := sparseRatMatrix retainedCM_4_9CS
def retainedCM_4_9U : Matrix (Fin 18) (Fin 3) ℚ := sparseRatScaledMatrix retainedCM_4_9D retainedCM_4_9WS
def retainedCM_4_9L : Matrix (Fin 3) (Fin 18) ℚ := sparseRatMatrix retainedCM_4_9LS
def retainedCM_4_9V : Matrix (Fin 18) (Fin 15) ℚ := sparseRatScaledMatrix retainedCM_4_9D retainedCM_4_9ZS

theorem retainedCM_4_9_sparse_check :
    SparseScaledFrameCheck retainedCM_4_9D retainedCM_4_9CS retainedCM_4_9WS retainedCM_4_9LS retainedCM_4_9ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_9_frame : HasKernelFrame retainedCM_4_9C retainedCM_4_9U retainedCM_4_9L retainedCM_4_9V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_9D≠0) retainedCM_4_9_sparse_check

theorem retainedCM_4_9_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_9C.mulVecLin)=3 :=
  kernelFrame_finrank retainedCM_4_9_frame

/- N=4, degree=10; rows=18, columns=23, nullity=5. -/
def retainedCM_4_10D : ℤ := 2520

def retainedCM_4_10CS : SparseIntMatrix 18 23 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 10), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 9), (⟨2, by decide⟩, 2), (⟨6, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 8), (⟨3, by decide⟩, 3), (⟨7, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 7), (⟨4, by decide⟩, 4), (⟨8, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 6), (⟨5, by decide⟩, 10), (⟨9, by decide⟩, 1)]
  | 5 => [(⟨6, by decide⟩, 8), (⟨7, by decide⟩, 2), (⟨14, by decide⟩, 3)]
  | 6 => [(⟨7, by decide⟩, 7), (⟨8, by decide⟩, 3), (⟨10, by decide⟩, 4), (⟨15, by decide⟩, 2)]
  | 7 => [(⟨8, by decide⟩, 6), (⟨9, by decide⟩, 4), (⟨11, by decide⟩, 2), (⟨16, by decide⟩, 2)]
  | 8 => [(⟨9, by decide⟩, 5), (⟨12, by decide⟩, 2), (⟨17, by decide⟩, 2)]
  | 9 => [(⟨10, by decide⟩, 6), (⟨11, by decide⟩, 3), (⟨18, by decide⟩, 1)]
  | 10 => [(⟨11, by decide⟩, 5), (⟨12, by decide⟩, 8), (⟨13, by decide⟩, 6), (⟨19, by decide⟩, 1)]
  | 11 => [(⟨13, by decide⟩, 4), (⟨20, by decide⟩, 1)]
  | 12 => [(⟨14, by decide⟩, 7), (⟨15, by decide⟩, 2)]
  | 13 => [(⟨15, by decide⟩, 6), (⟨16, by decide⟩, 3), (⟨18, by decide⟩, 4)]
  | 14 => [(⟨16, by decide⟩, 5), (⟨17, by decide⟩, 8), (⟨19, by decide⟩, 2)]
  | 15 => [(⟨18, by decide⟩, 5), (⟨19, by decide⟩, 3), (⟨21, by decide⟩, 6)]
  | 16 => [(⟨19, by decide⟩, 4), (⟨20, by decide⟩, 9), (⟨22, by decide⟩, 4)]
  | 17 => [(⟨21, by decide⟩, 4), (⟨22, by decide⟩, 6)]
  | _ => []

def retainedCM_4_10WS : SparseIntMatrix 23 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, -20), (⟨1, by decide⟩, 20), (⟨2, by decide⟩, 20), (⟨3, by decide⟩, -30), (⟨4, by decide⟩, -30)]
  | 1 => [(⟨0, by decide⟩, 200), (⟨1, by decide⟩, -200), (⟨2, by decide⟩, -200), (⟨3, by decide⟩, 300), (⟨4, by decide⟩, 300)]
  | 2 => [(⟨0, by decide⟩, -900), (⟨1, by decide⟩, 396), (⟨2, by decide⟩, 324), (⟨3, by decide⟩, -378), (⟨4, by decide⟩, -306)]
  | 3 => [(⟨0, by decide⟩, 2400), (⟨1, by decide⟩, -384), (⟨2, by decide⟩, -384), (⟨3, by decide⟩, 198), (⟨4, by decide⟩, 72)]
  | 4 => [(⟨0, by decide⟩, -4200), (⟨1, by decide⟩, 168), (⟨2, by decide⟩, 168)]
  | 5 => [(⟨0, by decide⟩, 2520)]
  | 6 => [(⟨1, by decide⟩, 504), (⟨2, by decide⟩, 576), (⟨3, by decide⟩, -972), (⟨4, by decide⟩, -1044)]
  | 7 => [(⟨1, by decide⟩, -2016), (⟨2, by decide⟩, -1440), (⟨3, by decide⟩, 2430), (⟨4, by decide⟩, 2232)]
  | 8 => [(⟨1, by decide⟩, 2016), (⟨2, by decide⟩, 2016), (⟨3, by decide⟩, -1386), (⟨4, by decide⟩, -504)]
  | 9 => [(⟨1, by decide⟩, -1008), (⟨2, by decide⟩, -1008)]
  | 10 => [(⟨1, by decide⟩, 2016), (⟨3, by decide⟩, -1512), (⟨4, by decide⟩, -1260)]
  | 11 => [(⟨1, by decide⟩, -4032), (⟨3, by decide⟩, 1890), (⟨4, by decide⟩, 504)]
  | 12 => [(⟨1, by decide⟩, 2520)]
  | 13 => [(⟨3, by decide⟩, -630)]
  | 14 => [(⟨2, by decide⟩, -576), (⟨3, by decide⟩, 972), (⟨4, by decide⟩, 1296)]
  | 15 => [(⟨2, by decide⟩, 2016), (⟨3, by decide⟩, -3402), (⟨4, by decide⟩, -4536)]
  | 16 => [(⟨2, by decide⟩, -4032), (⟨3, by decide⟩, 2268), (⟨4, by decide⟩, 1008)]
  | 17 => [(⟨2, by decide⟩, 2520)]
  | 18 => [(⟨3, by decide⟩, 3402), (⟨4, by decide⟩, 6048)]
  | 19 => [(⟨3, by decide⟩, -5670), (⟨4, by decide⟩, -2520)]
  | 20 => [(⟨3, by decide⟩, 2520)]
  | 21 => [(⟨4, by decide⟩, -3780)]
  | 22 => [(⟨4, by decide⟩, 2520)]
  | _ => []

def retainedCM_4_10LS : SparseIntMatrix 5 23 := fun i =>
  match i.val with
  | 0 => [(⟨5, by decide⟩, 1)]
  | 1 => [(⟨12, by decide⟩, 1)]
  | 2 => [(⟨17, by decide⟩, 1)]
  | 3 => [(⟨20, by decide⟩, 1)]
  | 4 => [(⟨22, by decide⟩, 1)]
  | _ => []

def retainedCM_4_10ZS : SparseIntMatrix 23 18 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 252), (⟨1, by decide⟩, -28), (⟨2, by decide⟩, 7), (⟨3, by decide⟩, -3), (⟨4, by decide⟩, 2), (⟨5, by decide⟩, 7), (⟨6, by decide⟩, -3), (⟨7, by decide⟩, 2), (⟨8, by decide⟩, -2), (⟨9, by decide⟩, 2), (⟨10, by decide⟩, -2), (⟨11, by decide⟩, 3), (⟨12, by decide⟩, -3), (⟨13, by decide⟩, 2), (⟨14, by decide⟩, -2), (⟨15, by decide⟩, -2), (⟨16, by decide⟩, 3), (⟨17, by decide⟩, 3)]
  | 1 => [(⟨1, by decide⟩, 280), (⟨2, by decide⟩, -70), (⟨3, by decide⟩, 30), (⟨4, by decide⟩, -20), (⟨5, by decide⟩, -70), (⟨6, by decide⟩, 30), (⟨7, by decide⟩, -20), (⟨8, by decide⟩, 20), (⟨9, by decide⟩, -20), (⟨10, by decide⟩, 20), (⟨11, by decide⟩, -30), (⟨12, by decide⟩, 30), (⟨13, by decide⟩, -20), (⟨14, by decide⟩, 20), (⟨15, by decide⟩, 20), (⟨16, by decide⟩, -30), (⟨17, by decide⟩, -30)]
  | 2 => [(⟨2, by decide⟩, 315), (⟨3, by decide⟩, -135), (⟨4, by decide⟩, 90), (⟨6, by decide⟩, -45), (⟨7, by decide⟩, 45), (⟨8, by decide⟩, -54), (⟨9, by decide⟩, 30), (⟨10, by decide⟩, -36), (⟨11, by decide⟩, 54), (⟨13, by decide⟩, 15), (⟨14, by decide⟩, -27), (⟨15, by decide⟩, -18), (⟨16, by decide⟩, 36), (⟨17, by decide⟩, 27)]
  | 3 => [(⟨3, by decide⟩, 360), (⟨4, by decide⟩, -240), (⟨7, by decide⟩, -60), (⟨8, by decide⟩, 96), (⟨10, by decide⟩, 24), (⟨11, by decide⟩, -36), (⟨14, by decide⟩, 24), (⟨16, by decide⟩, -18)]
  | 4 => [(⟨4, by decide⟩, 420), (⟨8, by decide⟩, -84)]
  | 6 => [(⟨5, by decide⟩, 315), (⟨6, by decide⟩, -90), (⟨7, by decide⟩, 45), (⟨8, by decide⟩, -36), (⟨9, by decide⟩, 60), (⟨10, by decide⟩, -54), (⟨11, by decide⟩, 81), (⟨12, by decide⟩, -135), (⟨13, by decide⟩, 75), (⟨14, by decide⟩, -63), (⟨15, by decide⟩, -72), (⟨16, by decide⟩, 99), (⟨17, by decide⟩, 108)]
  | 7 => [(⟨6, by decide⟩, 360), (⟨7, by decide⟩, -180), (⟨8, by decide⟩, 144), (⟨9, by decide⟩, -240), (⟨10, by decide⟩, 216), (⟨11, by decide⟩, -324), (⟨13, by decide⟩, -120), (⟨14, by decide⟩, 144), (⟨15, by decide⟩, 144), (⟨16, by decide⟩, -234), (⟨17, by decide⟩, -216)]
  | 8 => [(⟨7, by decide⟩, 420), (⟨8, by decide⟩, -336), (⟨10, by decide⟩, -168), (⟨11, by decide⟩, 252), (⟨14, by decide⟩, -168), (⟨16, by decide⟩, 126)]
  | 9 => [(⟨8, by decide⟩, 504)]
  | 10 => [(⟨9, by decide⟩, 420), (⟨10, by decide⟩, -252), (⟨11, by decide⟩, 378), (⟨15, by decide⟩, -84), (⟨16, by decide⟩, 126), (⟨17, by decide⟩, 126)]
  | 11 => [(⟨10, by decide⟩, 504), (⟨11, by decide⟩, -756), (⟨16, by decide⟩, -126)]
  | 13 => [(⟨11, by decide⟩, 630)]
  | 14 => [(⟨12, by decide⟩, 360), (⟨13, by decide⟩, -120), (⟨14, by decide⟩, 72), (⟨15, by decide⟩, 96), (⟨16, by decide⟩, -108), (⟨17, by decide⟩, -144)]
  | 15 => [(⟨13, by decide⟩, 420), (⟨14, by decide⟩, -252), (⟨15, by decide⟩, -336), (⟨16, by decide⟩, 378), (⟨17, by decide⟩, 504)]
  | 16 => [(⟨14, by decide⟩, 504), (⟨16, by decide⟩, -252)]
  | 18 => [(⟨15, by decide⟩, 504), (⟨16, by decide⟩, -378), (⟨17, by decide⟩, -756)]
  | 19 => [(⟨16, by decide⟩, 630)]
  | 21 => [(⟨17, by decide⟩, 630)]
  | _ => []

def retainedCM_4_10C : Matrix (Fin 18) (Fin 23) ℚ := sparseRatMatrix retainedCM_4_10CS
def retainedCM_4_10U : Matrix (Fin 23) (Fin 5) ℚ := sparseRatScaledMatrix retainedCM_4_10D retainedCM_4_10WS
def retainedCM_4_10L : Matrix (Fin 5) (Fin 23) ℚ := sparseRatMatrix retainedCM_4_10LS
def retainedCM_4_10V : Matrix (Fin 23) (Fin 18) ℚ := sparseRatScaledMatrix retainedCM_4_10D retainedCM_4_10ZS

theorem retainedCM_4_10_sparse_check :
    SparseScaledFrameCheck retainedCM_4_10D retainedCM_4_10CS retainedCM_4_10WS retainedCM_4_10LS retainedCM_4_10ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_10_frame : HasKernelFrame retainedCM_4_10C retainedCM_4_10U retainedCM_4_10L retainedCM_4_10V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_10D≠0) retainedCM_4_10_sparse_check

theorem retainedCM_4_10_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_10C.mulVecLin)=5 :=
  kernelFrame_finrank retainedCM_4_10_frame

/- N=4, degree=11; rows=23, columns=27, nullity=4. -/
def retainedCM_4_11D : ℤ := 27720

def retainedCM_4_11CS : SparseIntMatrix 23 27 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 11), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 10), (⟨2, by decide⟩, 2), (⟨6, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 9), (⟨3, by decide⟩, 3), (⟨7, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 8), (⟨4, by decide⟩, 4), (⟨8, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 7), (⟨5, by decide⟩, 5), (⟨9, by decide⟩, 1)]
  | 5 => [(⟨5, by decide⟩, 6), (⟨10, by decide⟩, 1)]
  | 6 => [(⟨6, by decide⟩, 9), (⟨7, by decide⟩, 2), (⟨16, by decide⟩, 3)]
  | 7 => [(⟨7, by decide⟩, 8), (⟨8, by decide⟩, 3), (⟨11, by decide⟩, 4), (⟨17, by decide⟩, 2)]
  | 8 => [(⟨8, by decide⟩, 7), (⟨9, by decide⟩, 4), (⟨12, by decide⟩, 2), (⟨18, by decide⟩, 2)]
  | 9 => [(⟨9, by decide⟩, 6), (⟨10, by decide⟩, 10), (⟨13, by decide⟩, 2), (⟨19, by decide⟩, 2)]
  | 10 => [(⟨11, by decide⟩, 7), (⟨12, by decide⟩, 3), (⟨20, by decide⟩, 1)]
  | 11 => [(⟨12, by decide⟩, 6), (⟨13, by decide⟩, 4), (⟨14, by decide⟩, 6), (⟨21, by decide⟩, 1)]
  | 12 => [(⟨13, by decide⟩, 5), (⟨15, by decide⟩, 3), (⟨22, by decide⟩, 1)]
  | 13 => [(⟨14, by decide⟩, 5), (⟨15, by decide⟩, 8), (⟨23, by decide⟩, 1)]
  | 14 => [(⟨16, by decide⟩, 8), (⟨17, by decide⟩, 2)]
  | 15 => [(⟨17, by decide⟩, 7), (⟨18, by decide⟩, 3), (⟨20, by decide⟩, 4)]
  | 16 => [(⟨18, by decide⟩, 6), (⟨19, by decide⟩, 4), (⟨21, by decide⟩, 2)]
  | 17 => [(⟨19, by decide⟩, 5), (⟨22, by decide⟩, 2)]
  | 18 => [(⟨20, by decide⟩, 6), (⟨21, by decide⟩, 3), (⟨24, by decide⟩, 6)]
  | 19 => [(⟨21, by decide⟩, 5), (⟨22, by decide⟩, 8), (⟨23, by decide⟩, 6), (⟨25, by decide⟩, 4)]
  | 20 => [(⟨23, by decide⟩, 4), (⟨26, by decide⟩, 2)]
  | 21 => [(⟨24, by decide⟩, 5), (⟨25, by decide⟩, 3)]
  | 22 => [(⟨25, by decide⟩, 4), (⟨26, by decide⟩, 9)]
  | _ => []

def retainedCM_4_11WS : SparseIntMatrix 27 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 110), (⟨1, by decide⟩, -132), (⟨2, by decide⟩, -132), (⟨3, by decide⟩, 231)]
  | 1 => [(⟨0, by decide⟩, -1210), (⟨1, by decide⟩, 1452), (⟨2, by decide⟩, 1452), (⟨3, by decide⟩, -2541)]
  | 2 => [(⟨0, by decide⟩, 3850), (⟨1, by decide⟩, -3036), (⟨2, by decide⟩, -2244), (⟨3, by decide⟩, 3135)]
  | 3 => [(⟨0, by decide⟩, -8250), (⟨1, by decide⟩, 2772), (⟨2, by decide⟩, 1980), (⟨3, by decide⟩, -1287)]
  | 4 => [(⟨0, by decide⟩, 9900), (⟨1, by decide⟩, -792), (⟨2, by decide⟩, -792)]
  | 5 => [(⟨0, by decide⟩, -4620)]
  | 6 => [(⟨0, by decide⟩, 2200), (⟨1, by decide⟩, -4224), (⟨2, by decide⟩, -5016), (⟨3, by decide⟩, 9570)]
  | 7 => [(⟨0, by decide⟩, -9900), (⟨1, by decide⟩, 19008), (⟨2, by decide⟩, 14256), (⟨3, by decide⟩, -24354)]
  | 8 => [(⟨0, by decide⟩, 26400), (⟨1, by decide⟩, -19008), (⟨2, by decide⟩, -12672), (⟨3, by decide⟩, 10296)]
  | 9 => [(⟨0, by decide⟩, -46200), (⟨1, by decide⟩, 5544), (⟨2, by decide⟩, 5544)]
  | 10 => [(⟨0, by decide⟩, 27720)]
  | 11 => [(⟨1, by decide⟩, -23760), (⟨2, by decide⟩, -7920), (⟨3, by decide⟩, 16038)]
  | 12 => [(⟨1, by decide⟩, 55440), (⟨2, by decide⟩, 11088), (⟨3, by decide⟩, -13860)]
  | 13 => [(⟨1, by decide⟩, -16632), (⟨2, by decide⟩, -5544)]
  | 14 => [(⟨1, by decide⟩, -44352), (⟨3, by decide⟩, 2772)]
  | 15 => [(⟨1, by decide⟩, 27720)]
  | 16 => [(⟨2, by decide⟩, 5544), (⟨3, by decide⟩, -12474)]
  | 17 => [(⟨2, by decide⟩, -22176), (⟨3, by decide⟩, 49896)]
  | 18 => [(⟨2, by decide⟩, 22176), (⟨3, by decide⟩, -22176)]
  | 19 => [(⟨2, by decide⟩, -11088)]
  | 20 => [(⟨2, by decide⟩, 22176), (⟨3, by decide⟩, -70686)]
  | 21 => [(⟨2, by decide⟩, -44352), (⟨3, by decide⟩, 66528)]
  | 22 => [(⟨2, by decide⟩, 27720)]
  | 23 => [(⟨3, by decide⟩, -13860)]
  | 24 => [(⟨3, by decide⟩, 37422)]
  | 25 => [(⟨3, by decide⟩, -62370)]
  | 26 => [(⟨3, by decide⟩, 27720)]
  | _ => []

def retainedCM_4_11LS : SparseIntMatrix 4 27 := fun i =>
  match i.val with
  | 0 => [(⟨10, by decide⟩, 1)]
  | 1 => [(⟨15, by decide⟩, 1)]
  | 2 => [(⟨22, by decide⟩, 1)]
  | 3 => [(⟨26, by decide⟩, 1)]
  | _ => []

def retainedCM_4_11ZS : SparseIntMatrix 27 23 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 2520), (⟨1, by decide⟩, -252), (⟨2, by decide⟩, 56), (⟨3, by decide⟩, -21), (⟨4, by decide⟩, 12), (⟨5, by decide⟩, -10), (⟨6, by decide⟩, 56), (⟨7, by decide⟩, -21), (⟨8, by decide⟩, 12), (⟨9, by decide⟩, -10), (⟨10, by decide⟩, 12), (⟨11, by decide⟩, -10), (⟨12, by decide⟩, 12), (⟨13, by decide⟩, 12), (⟨14, by decide⟩, -21), (⟨15, by decide⟩, 12), (⟨16, by decide⟩, -10), (⟨17, by decide⟩, 12), (⟨18, by decide⟩, -10), (⟨19, by decide⟩, 12), (⟨20, by decide⟩, -21), (⟨21, by decide⟩, 12), (⟨22, by decide⟩, -21)]
  | 1 => [(⟨1, by decide⟩, 2772), (⟨2, by decide⟩, -616), (⟨3, by decide⟩, 231), (⟨4, by decide⟩, -132), (⟨5, by decide⟩, 110), (⟨6, by decide⟩, -616), (⟨7, by decide⟩, 231), (⟨8, by decide⟩, -132), (⟨9, by decide⟩, 110), (⟨10, by decide⟩, -132), (⟨11, by decide⟩, 110), (⟨12, by decide⟩, -132), (⟨13, by decide⟩, -132), (⟨14, by decide⟩, 231), (⟨15, by decide⟩, -132), (⟨16, by decide⟩, 110), (⟨17, by decide⟩, -132), (⟨18, by decide⟩, 110), (⟨19, by decide⟩, -132), (⟨20, by decide⟩, 231), (⟨21, by decide⟩, -132), (⟨22, by decide⟩, 231)]
  | 2 => [(⟨2, by decide⟩, 3080), (⟨3, by decide⟩, -1155), (⟨4, by decide⟩, 660), (⟨5, by decide⟩, -550), (⟨7, by decide⟩, -385), (⟨8, by decide⟩, 330), (⟨9, by decide⟩, -330), (⟨10, by decide⟩, 220), (⟨11, by decide⟩, -220), (⟨12, by decide⟩, 308), (⟨13, by decide⟩, 264), (⟨15, by decide⟩, 110), (⟨16, by decide⟩, -165), (⟨17, by decide⟩, 264), (⟨18, by decide⟩, -110), (⟨19, by decide⟩, 176), (⟨20, by decide⟩, -330), (⟨21, by decide⟩, 132), (⟨22, by decide⟩, -275)]
  | 3 => [(⟨3, by decide⟩, 3465), (⟨4, by decide⟩, -1980), (⟨5, by decide⟩, 1650), (⟨8, by decide⟩, -495), (⟨9, by decide⟩, 660), (⟨11, by decide⟩, 165), (⟨12, by decide⟩, -396), (⟨13, by decide⟩, -198), (⟨16, by decide⟩, 165), (⟨17, by decide⟩, -396), (⟨19, by decide⟩, -99), (⟨20, by decide⟩, 198), (⟨22, by decide⟩, 99)]
  | 4 => [(⟨4, by decide⟩, 3960), (⟨5, by decide⟩, -3300), (⟨9, by decide⟩, -660), (⟨12, by decide⟩, 264), (⟨17, by decide⟩, 264)]
  | 5 => [(⟨5, by decide⟩, 4620)]
  | 6 => [(⟨6, by decide⟩, 3080), (⟨7, by decide⟩, -770), (⟨8, by decide⟩, 330), (⟨9, by decide⟩, -220), (⟨10, by decide⟩, 440), (⟨11, by decide⟩, -330), (⟨12, by decide⟩, 352), (⟨13, by decide⟩, 396), (⟨14, by decide⟩, -1155), (⟨15, by decide⟩, 550), (⟨16, by decide⟩, -385), (⟨17, by decide⟩, 396), (⟨18, by decide⟩, -440), (⟨19, by decide⟩, 484), (⟨20, by decide⟩, -825), (⟨21, by decide⟩, 528), (⟨22, by decide⟩, -880)]
  | 7 => [(⟨7, by decide⟩, 3465), (⟨8, by decide⟩, -1485), (⟨9, by decide⟩, 990), (⟨10, by decide⟩, -1980), (⟨11, by decide⟩, 1485), (⟨12, by decide⟩, -1584), (⟨13, by decide⟩, -1782), (⟨15, by decide⟩, -990), (⟨16, by decide⟩, 990), (⟨17, by decide⟩, -1188), (⟨18, by decide⟩, 990), (⟨19, by decide⟩, -1287), (⟨20, by decide⟩, 2376), (⟨21, by decide⟩, -1188), (⟨22, by decide⟩, 2178)]
  | 8 => [(⟨8, by decide⟩, 3960), (⟨9, by decide⟩, -2640), (⟨11, by decide⟩, -1320), (⟨12, by decide⟩, 2112), (⟨13, by decide⟩, 1584), (⟨16, by decide⟩, -1320), (⟨17, by decide⟩, 2112), (⟨19, by decide⟩, 792), (⟨20, by decide⟩, -1584), (⟨22, by decide⟩, -792)]
  | 9 => [(⟨9, by decide⟩, 4620), (⟨12, by decide⟩, -1848), (⟨17, by decide⟩, -1848)]
  | 11 => [(⟨10, by decide⟩, 3960), (⟨11, by decide⟩, -1980), (⟨12, by decide⟩, 1584), (⟨13, by decide⟩, 2376), (⟨18, by decide⟩, -660), (⟨19, by decide⟩, 792), (⟨20, by decide⟩, -1782), (⟨21, by decide⟩, 792), (⟨22, by decide⟩, -1386)]
  | 12 => [(⟨11, by decide⟩, 4620), (⟨12, by decide⟩, -3696), (⟨13, by decide⟩, -5544), (⟨19, by decide⟩, -924), (⟨20, by decide⟩, 2772), (⟨22, by decide⟩, 924)]
  | 13 => [(⟨12, by decide⟩, 5544)]
  | 14 => [(⟨13, by decide⟩, 5544), (⟨20, by decide⟩, -1386)]
  | 16 => [(⟨14, by decide⟩, 3465), (⟨15, by decide⟩, -990), (⟨16, by decide⟩, 495), (⟨17, by decide⟩, -396), (⟨18, by decide⟩, 660), (⟨19, by decide⟩, -594), (⟨20, by decide⟩, 891), (⟨21, by decide⟩, -792), (⟨22, by decide⟩, 1188)]
  | 17 => [(⟨15, by decide⟩, 3960), (⟨16, by decide⟩, -1980), (⟨17, by decide⟩, 1584), (⟨18, by decide⟩, -2640), (⟨19, by decide⟩, 2376), (⟨20, by decide⟩, -3564), (⟨21, by decide⟩, 3168), (⟨22, by decide⟩, -4752)]
  | 18 => [(⟨16, by decide⟩, 4620), (⟨17, by decide⟩, -3696), (⟨19, by decide⟩, -1848), (⟨20, by decide⟩, 2772), (⟨22, by decide⟩, 1848)]
  | 19 => [(⟨17, by decide⟩, 5544)]
  | 20 => [(⟨18, by decide⟩, 4620), (⟨19, by decide⟩, -2772), (⟨20, by decide⟩, 4158), (⟨21, by decide⟩, -5544), (⟨22, by decide⟩, 6930)]
  | 21 => [(⟨19, by decide⟩, 5544), (⟨20, by decide⟩, -8316), (⟨22, by decide⟩, -5544)]
  | 23 => [(⟨20, by decide⟩, 6930)]
  | 24 => [(⟨21, by decide⟩, 5544), (⟨22, by decide⟩, -4158)]
  | 25 => [(⟨22, by decide⟩, 6930)]
  | _ => []

def retainedCM_4_11C : Matrix (Fin 23) (Fin 27) ℚ := sparseRatMatrix retainedCM_4_11CS
def retainedCM_4_11U : Matrix (Fin 27) (Fin 4) ℚ := sparseRatScaledMatrix retainedCM_4_11D retainedCM_4_11WS
def retainedCM_4_11L : Matrix (Fin 4) (Fin 27) ℚ := sparseRatMatrix retainedCM_4_11LS
def retainedCM_4_11V : Matrix (Fin 27) (Fin 23) ℚ := sparseRatScaledMatrix retainedCM_4_11D retainedCM_4_11ZS

theorem retainedCM_4_11_sparse_check :
    SparseScaledFrameCheck retainedCM_4_11D retainedCM_4_11CS retainedCM_4_11WS retainedCM_4_11LS retainedCM_4_11ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_11_frame : HasKernelFrame retainedCM_4_11C retainedCM_4_11U retainedCM_4_11L retainedCM_4_11V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_11D≠0) retainedCM_4_11_sparse_check

theorem retainedCM_4_11_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_11C.mulVecLin)=4 :=
  kernelFrame_finrank retainedCM_4_11_frame

/- N=4, degree=12; rows=27, columns=34, nullity=7. -/
def retainedCM_4_12D : ℤ := 27720

def retainedCM_4_12CS : SparseIntMatrix 27 34 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 12), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 11), (⟨2, by decide⟩, 2), (⟨7, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 10), (⟨3, by decide⟩, 3), (⟨8, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 9), (⟨4, by decide⟩, 4), (⟨9, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 8), (⟨5, by decide⟩, 5), (⟨10, by decide⟩, 1)]
  | 5 => [(⟨5, by decide⟩, 7), (⟨6, by decide⟩, 12), (⟨11, by decide⟩, 1)]
  | 6 => [(⟨7, by decide⟩, 10), (⟨8, by decide⟩, 2), (⟨19, by decide⟩, 3)]
  | 7 => [(⟨8, by decide⟩, 9), (⟨9, by decide⟩, 3), (⟨12, by decide⟩, 4), (⟨20, by decide⟩, 2)]
  | 8 => [(⟨9, by decide⟩, 8), (⟨10, by decide⟩, 4), (⟨13, by decide⟩, 2), (⟨21, by decide⟩, 2)]
  | 9 => [(⟨10, by decide⟩, 7), (⟨11, by decide⟩, 5), (⟨14, by decide⟩, 2), (⟨22, by decide⟩, 2)]
  | 10 => [(⟨11, by decide⟩, 6), (⟨15, by decide⟩, 2), (⟨23, by decide⟩, 2)]
  | 11 => [(⟨12, by decide⟩, 8), (⟨13, by decide⟩, 3), (⟨24, by decide⟩, 1)]
  | 12 => [(⟨13, by decide⟩, 7), (⟨14, by decide⟩, 4), (⟨16, by decide⟩, 6), (⟨25, by decide⟩, 1)]
  | 13 => [(⟨14, by decide⟩, 6), (⟨15, by decide⟩, 10), (⟨17, by decide⟩, 3), (⟨26, by decide⟩, 1)]
  | 14 => [(⟨16, by decide⟩, 6), (⟨17, by decide⟩, 4), (⟨27, by decide⟩, 1)]
  | 15 => [(⟨17, by decide⟩, 5), (⟨18, by decide⟩, 12), (⟨28, by decide⟩, 1)]
  | 16 => [(⟨19, by decide⟩, 9), (⟨20, by decide⟩, 2)]
  | 17 => [(⟨20, by decide⟩, 8), (⟨21, by decide⟩, 3), (⟨24, by decide⟩, 4)]
  | 18 => [(⟨21, by decide⟩, 7), (⟨22, by decide⟩, 4), (⟨25, by decide⟩, 2)]
  | 19 => [(⟨22, by decide⟩, 6), (⟨23, by decide⟩, 10), (⟨26, by decide⟩, 2)]
  | 20 => [(⟨24, by decide⟩, 7), (⟨25, by decide⟩, 3), (⟨29, by decide⟩, 6)]
  | 21 => [(⟨25, by decide⟩, 6), (⟨26, by decide⟩, 4), (⟨27, by decide⟩, 6), (⟨30, by decide⟩, 4)]
  | 22 => [(⟨26, by decide⟩, 5), (⟨28, by decide⟩, 3), (⟨31, by decide⟩, 4)]
  | 23 => [(⟨27, by decide⟩, 5), (⟨28, by decide⟩, 8), (⟨32, by decide⟩, 2)]
  | 24 => [(⟨29, by decide⟩, 6), (⟨30, by decide⟩, 3)]
  | 25 => [(⟨30, by decide⟩, 5), (⟨31, by decide⟩, 8), (⟨32, by decide⟩, 6)]
  | 26 => [(⟨32, by decide⟩, 4), (⟨33, by decide⟩, 12)]
  | _ => []

def retainedCM_4_12WS : SparseIntMatrix 34 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 60), (⟨1, by decide⟩, -60), (⟨2, by decide⟩, 84), (⟨3, by decide⟩, -60), (⟨4, by decide⟩, 84), (⟨5, by decide⟩, 84), (⟨6, by decide⟩, -168)]
  | 1 => [(⟨0, by decide⟩, -720), (⟨1, by decide⟩, 720), (⟨2, by decide⟩, -1008), (⟨3, by decide⟩, 720), (⟨4, by decide⟩, -1008), (⟨5, by decide⟩, -1008), (⟨6, by decide⟩, 2016)]
  | 2 => [(⟨0, by decide⟩, 3960), (⟨1, by decide⟩, -1980), (⟨2, by decide⟩, 2376), (⟨3, by decide⟩, -1760), (⟨4, by decide⟩, 1716), (⟨5, by decide⟩, 1496), (⟨6, by decide⟩, -2772)]
  | 3 => [(⟨0, by decide⟩, -13200), (⟨1, by decide⟩, 3300), (⟨2, by decide⟩, -2640), (⟨3, by decide⟩, 3300), (⟨4, by decide⟩, -1452), (⟨5, by decide⟩, -1056), (⟨6, by decide⟩, 1320)]
  | 4 => [(⟨0, by decide⟩, 29700), (⟨1, by decide⟩, -3300), (⟨2, by decide⟩, 1188), (⟨3, by decide⟩, -3300), (⟨4, by decide⟩, 396), (⟨5, by decide⟩, 396)]
  | 5 => [(⟨0, by decide⟩, -47520), (⟨1, by decide⟩, 1320), (⟨3, by decide⟩, 1320)]
  | 6 => [(⟨0, by decide⟩, 27720)]
  | 7 => [(⟨1, by decide⟩, -1980), (⟨2, by decide⟩, 3168), (⟨3, by decide⟩, -2200), (⟨4, by decide⟩, 3828), (⟨5, by decide⟩, 4048), (⟨6, by decide⟩, -8316)]
  | 8 => [(⟨1, by decide⟩, 9900), (⟨2, by decide⟩, -15840), (⟨3, by decide⟩, 7700), (⟨4, by decide⟩, -12804), (⟨5, by decide⟩, -11792), (⟨6, by decide⟩, 23760)]
  | 9 => [(⟨1, by decide⟩, -16500), (⟨2, by decide⟩, 19008), (⟨3, by decide⟩, -16500), (⟨4, by decide⟩, 11484), (⟨5, by decide⟩, 7920), (⟨6, by decide⟩, -11880)]
  | 10 => [(⟨1, by decide⟩, 19800), (⟨2, by decide⟩, -9504), (⟨3, by decide⟩, 19800), (⟨4, by decide⟩, -3168), (⟨5, by decide⟩, -3168)]
  | 11 => [(⟨1, by decide⟩, -9240), (⟨3, by decide⟩, -9240)]
  | 12 => [(⟨1, by decide⟩, -9900), (⟨2, by decide⟩, 21384), (⟨4, by decide⟩, 10692), (⟨5, by decide⟩, 7920), (⟨6, by decide⟩, -17820)]
  | 13 => [(⟨1, by decide⟩, 26400), (⟨2, by decide⟩, -57024), (⟨4, by decide⟩, -20592), (⟨5, by decide⟩, -8448), (⟨6, by decide⟩, 19008)]
  | 14 => [(⟨1, by decide⟩, -46200), (⟨2, by decide⟩, 33264), (⟨4, by decide⟩, 5544), (⟨5, by decide⟩, 3696)]
  | 15 => [(⟨1, by decide⟩, 27720)]
  | 16 => [(⟨2, by decide⟩, 44352), (⟨4, by decide⟩, 11088), (⟨6, by decide⟩, -5544)]
  | 17 => [(⟨2, by decide⟩, -66528), (⟨4, by decide⟩, -5544)]
  | 18 => [(⟨2, by decide⟩, 27720)]
  | 19 => [(⟨3, by decide⟩, 2200), (⟨4, by decide⟩, -4224), (⟨5, by decide⟩, -5632), (⟨6, by decide⟩, 11880)]
  | 20 => [(⟨3, by decide⟩, -9900), (⟨4, by decide⟩, 19008), (⟨5, by decide⟩, 25344), (⟨6, by decide⟩, -53460)]
  | 21 => [(⟨3, by decide⟩, 26400), (⟨4, by decide⟩, -19008), (⟨5, by decide⟩, -16896), (⟨6, by decide⟩, 28512)]
  | 22 => [(⟨3, by decide⟩, -46200), (⟨4, by decide⟩, 5544), (⟨5, by decide⟩, 7392)]
  | 23 => [(⟨3, by decide⟩, 27720)]
  | 24 => [(⟨4, by decide⟩, -23760), (⟨5, by decide⟩, -38016), (⟨6, by decide⟩, 85536)]
  | 25 => [(⟨4, by decide⟩, 55440), (⟨5, by decide⟩, 44352), (⟨6, by decide⟩, -99792)]
  | 26 => [(⟨4, by decide⟩, -16632), (⟨5, by decide⟩, -22176)]
  | 27 => [(⟨4, by decide⟩, -44352), (⟨6, by decide⟩, 33264)]
  | 28 => [(⟨4, by decide⟩, 27720)]
  | 29 => [(⟨5, by decide⟩, 22176), (⟨6, by decide⟩, -49896)]
  | 30 => [(⟨5, by decide⟩, -44352), (⟨6, by decide⟩, 99792)]
  | 31 => [(⟨5, by decide⟩, 27720)]
  | 32 => [(⟨6, by decide⟩, -83160)]
  | 33 => [(⟨6, by decide⟩, 27720)]
  | _ => []

def retainedCM_4_12LS : SparseIntMatrix 7 34 := fun i =>
  match i.val with
  | 0 => [(⟨6, by decide⟩, 1)]
  | 1 => [(⟨15, by decide⟩, 1)]
  | 2 => [(⟨18, by decide⟩, 1)]
  | 3 => [(⟨23, by decide⟩, 1)]
  | 4 => [(⟨28, by decide⟩, 1)]
  | 5 => [(⟨31, by decide⟩, 1)]
  | 6 => [(⟨33, by decide⟩, 1)]
  | _ => []

def retainedCM_4_12ZS : SparseIntMatrix 34 27 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 2310), (⟨1, by decide⟩, -210), (⟨2, by decide⟩, 42), (⟨3, by decide⟩, -14), (⟨4, by decide⟩, 7), (⟨5, by decide⟩, -5), (⟨6, by decide⟩, 42), (⟨7, by decide⟩, -14), (⟨8, by decide⟩, 7), (⟨9, by decide⟩, -5), (⟨10, by decide⟩, 5), (⟨11, by decide⟩, 7), (⟨12, by decide⟩, -5), (⟨13, by decide⟩, 5), (⟨14, by decide⟩, 5), (⟨15, by decide⟩, -7), (⟨16, by decide⟩, -14), (⟨17, by decide⟩, 7), (⟨18, by decide⟩, -5), (⟨19, by decide⟩, 5), (⟨20, by decide⟩, -5), (⟨21, by decide⟩, 5), (⟨22, by decide⟩, -7), (⟨23, by decide⟩, -7), (⟨24, by decide⟩, 5), (⟨25, by decide⟩, -7), (⟨26, by decide⟩, 14)]
  | 1 => [(⟨1, by decide⟩, 2520), (⟨2, by decide⟩, -504), (⟨3, by decide⟩, 168), (⟨4, by decide⟩, -84), (⟨5, by decide⟩, 60), (⟨6, by decide⟩, -504), (⟨7, by decide⟩, 168), (⟨8, by decide⟩, -84), (⟨9, by decide⟩, 60), (⟨10, by decide⟩, -60), (⟨11, by decide⟩, -84), (⟨12, by decide⟩, 60), (⟨13, by decide⟩, -60), (⟨14, by decide⟩, -60), (⟨15, by decide⟩, 84), (⟨16, by decide⟩, 168), (⟨17, by decide⟩, -84), (⟨18, by decide⟩, 60), (⟨19, by decide⟩, -60), (⟨20, by decide⟩, 60), (⟨21, by decide⟩, -60), (⟨22, by decide⟩, 84), (⟨23, by decide⟩, 84), (⟨24, by decide⟩, -60), (⟨25, by decide⟩, 84), (⟨26, by decide⟩, -168)]
  | 2 => [(⟨2, by decide⟩, 2772), (⟨3, by decide⟩, -924), (⟨4, by decide⟩, 462), (⟨5, by decide⟩, -330), (⟨7, by decide⟩, -308), (⟨8, by decide⟩, 231), (⟨9, by decide⟩, -198), (⟨10, by decide⟩, 220), (⟨11, by decide⟩, 154), (⟨12, by decide⟩, -132), (⟨13, by decide⟩, 154), (⟨14, by decide⟩, 132), (⟨15, by decide⟩, -198), (⟨17, by decide⟩, 77), (⟨18, by decide⟩, -99), (⟨19, by decide⟩, 132), (⟨20, by decide⟩, -66), (⟨21, by decide⟩, 88), (⟨22, by decide⟩, -154), (⟨23, by decide⟩, -132), (⟨24, by decide⟩, 66), (⟨25, by decide⟩, -110), (⟨26, by decide⟩, 231)]
  | 3 => [(⟨3, by decide⟩, 3080), (⟨4, by decide⟩, -1540), (⟨5, by decide⟩, 1100), (⟨8, by decide⟩, -385), (⟨9, by decide⟩, 440), (⟨10, by decide⟩, -550), (⟨12, by decide⟩, 110), (⟨13, by decide⟩, -220), (⟨14, by decide⟩, -110), (⟨15, by decide⟩, 220), (⟨18, by decide⟩, 110), (⟨19, by decide⟩, -220), (⟨21, by decide⟩, -55), (⟨22, by decide⟩, 176), (⟨23, by decide⟩, 88), (⟨25, by decide⟩, 44), (⟨26, by decide⟩, -110)]
  | 4 => [(⟨4, by decide⟩, 3465), (⟨5, by decide⟩, -2475), (⟨9, by decide⟩, -495), (⟨10, by decide⟩, 825), (⟨13, by decide⟩, 165), (⟨15, by decide⟩, -99), (⟨19, by decide⟩, 165), (⟨22, by decide⟩, -99)]
  | 5 => [(⟨5, by decide⟩, 3960), (⟨10, by decide⟩, -660)]
  | 7 => [(⟨6, by decide⟩, 2772), (⟨7, by decide⟩, -616), (⟨8, by decide⟩, 231), (⟨9, by decide⟩, -132), (⟨10, by decide⟩, 110), (⟨11, by decide⟩, 308), (⟨12, by decide⟩, -198), (⟨13, by decide⟩, 176), (⟨14, by decide⟩, 198), (⟨15, by decide⟩, -264), (⟨16, by decide⟩, -924), (⟨17, by decide⟩, 385), (⟨18, by decide⟩, -231), (⟨19, by decide⟩, 198), (⟨20, by decide⟩, -264), (⟨21, by decide⟩, 242), (⟨22, by decide⟩, -308), (⟨23, by decide⟩, -330), (⟨24, by decide⟩, 264), (⟨25, by decide⟩, -352), (⟨26, by decide⟩, 693)]
  | 8 => [(⟨7, by decide⟩, 3080), (⟨8, by decide⟩, -1155), (⟨9, by decide⟩, 660), (⟨10, by decide⟩, -550), (⟨11, by decide⟩, -1540), (⟨12, by decide⟩, 990), (⟨13, by decide⟩, -880), (⟨14, by decide⟩, -990), (⟨15, by decide⟩, 1320), (⟨17, by decide⟩, -770), (⟨18, by decide⟩, 660), (⟨19, by decide⟩, -660), (⟨20, by decide⟩, 660), (⟨21, by decide⟩, -715), (⟨22, by decide⟩, 1012), (⟨23, by decide⟩, 1056), (⟨24, by decide⟩, -660), (⟨25, by decide⟩, 968), (⟨26, by decide⟩, -1980)]
  | 9 => [(⟨8, by decide⟩, 3465), (⟨9, by decide⟩, -1980), (⟨10, by decide⟩, 1650), (⟨12, by decide⟩, -990), (⟨13, by decide⟩, 1320), (⟨14, by decide⟩, 990), (⟨15, by decide⟩, -1584), (⟨18, by decide⟩, -990), (⟨19, by decide⟩, 1320), (⟨21, by decide⟩, 495), (⟨22, by decide⟩, -1188), (⟨23, by decide⟩, -792), (⟨25, by decide⟩, -396), (⟨26, by decide⟩, 990)]
  | 10 => [(⟨9, by decide⟩, 3960), (⟨10, by decide⟩, -3300), (⟨13, by decide⟩, -1320), (⟨15, by decide⟩, 792), (⟨19, by decide⟩, -1320), (⟨22, by decide⟩, 792)]
  | 11 => [(⟨10, by decide⟩, 4620)]
  | 12 => [(⟨11, by decide⟩, 3465), (⟨12, by decide⟩, -1485), (⟨13, by decide⟩, 990), (⟨14, by decide⟩, 1485), (⟨15, by decide⟩, -1782), (⟨20, by decide⟩, -495), (⟨21, by decide⟩, 495), (⟨22, by decide⟩, -594), (⟨23, by decide⟩, -891), (⟨24, by decide⟩, 495), (⟨25, by decide⟩, -693), (⟨26, by decide⟩, 1485)]
  | 13 => [(⟨12, by decide⟩, 3960), (⟨13, by decide⟩, -2640), (⟨14, by decide⟩, -3960), (⟨15, by decide⟩, 4752), (⟨21, by decide⟩, -660), (⟨22, by decide⟩, 1056), (⟨23, by decide⟩, 1584), (⟨25, by decide⟩, 528), (⟨26, by decide⟩, -1584)]
  | 14 => [(⟨13, by decide⟩, 4620), (⟨15, by decide⟩, -2772), (⟨22, by decide⟩, -924)]
  | 16 => [(⟨14, by decide⟩, 4620), (⟨15, by decide⟩, -3696), (⟨23, by decide⟩, -924), (⟨26, by decide⟩, 462)]
  | 17 => [(⟨15, by decide⟩, 5544)]
  | 19 => [(⟨16, by decide⟩, 3080), (⟨17, by decide⟩, -770), (⟨18, by decide⟩, 330), (⟨19, by decide⟩, -220), (⟨20, by decide⟩, 440), (⟨21, by decide⟩, -330), (⟨22, by decide⟩, 352), (⟨23, by decide⟩, 396), (⟨24, by decide⟩, -440), (⟨25, by decide⟩, 528), (⟨26, by decide⟩, -990)]
  | 20 => [(⟨17, by decide⟩, 3465), (⟨18, by decide⟩, -1485), (⟨19, by decide⟩, 990), (⟨20, by decide⟩, -1980), (⟨21, by decide⟩, 1485), (⟨22, by decide⟩, -1584), (⟨23, by decide⟩, -1782), (⟨24, by decide⟩, 1980), (⟨25, by decide⟩, -2376), (⟨26, by decide⟩, 4455)]
  | 21 => [(⟨18, by decide⟩, 3960), (⟨19, by decide⟩, -2640), (⟨21, by decide⟩, -1320), (⟨22, by decide⟩, 2112), (⟨23, by decide⟩, 1584), (⟨25, by decide⟩, 1056), (⟨26, by decide⟩, -2376)]
  | 22 => [(⟨19, by decide⟩, 4620), (⟨22, by decide⟩, -1848)]
  | 24 => [(⟨20, by decide⟩, 3960), (⟨21, by decide⟩, -1980), (⟨22, by decide⟩, 1584), (⟨23, by decide⟩, 2376), (⟨24, by decide⟩, -3960), (⟨25, by decide⟩, 3960), (⟨26, by decide⟩, -7128)]
  | 25 => [(⟨21, by decide⟩, 4620), (⟨22, by decide⟩, -3696), (⟨23, by decide⟩, -5544), (⟨25, by decide⟩, -3696), (⟨26, by decide⟩, 8316)]
  | 26 => [(⟨22, by decide⟩, 5544)]
  | 27 => [(⟨23, by decide⟩, 5544), (⟨26, by decide⟩, -2772)]
  | 29 => [(⟨24, by decide⟩, 4620), (⟨25, by decide⟩, -2772), (⟨26, by decide⟩, 4158)]
  | 30 => [(⟨25, by decide⟩, 5544), (⟨26, by decide⟩, -8316)]
  | 32 => [(⟨26, by decide⟩, 6930)]
  | _ => []

def retainedCM_4_12C : Matrix (Fin 27) (Fin 34) ℚ := sparseRatMatrix retainedCM_4_12CS
def retainedCM_4_12U : Matrix (Fin 34) (Fin 7) ℚ := sparseRatScaledMatrix retainedCM_4_12D retainedCM_4_12WS
def retainedCM_4_12L : Matrix (Fin 7) (Fin 34) ℚ := sparseRatMatrix retainedCM_4_12LS
def retainedCM_4_12V : Matrix (Fin 34) (Fin 27) ℚ := sparseRatScaledMatrix retainedCM_4_12D retainedCM_4_12ZS

theorem retainedCM_4_12_sparse_check :
    SparseScaledFrameCheck retainedCM_4_12D retainedCM_4_12CS retainedCM_4_12WS retainedCM_4_12LS retainedCM_4_12ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_12_frame : HasKernelFrame retainedCM_4_12C retainedCM_4_12U retainedCM_4_12L retainedCM_4_12V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_12D≠0) retainedCM_4_12_sparse_check

theorem retainedCM_4_12_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_12C.mulVecLin)=7 :=
  kernelFrame_finrank retainedCM_4_12_frame

/- N=4, degree=13; rows=34, columns=39, nullity=5. -/
def retainedCM_4_13D : ℤ := 360360

def retainedCM_4_13CS : SparseIntMatrix 34 39 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 13), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 12), (⟨2, by decide⟩, 2), (⟨7, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 11), (⟨3, by decide⟩, 3), (⟨8, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 10), (⟨4, by decide⟩, 4), (⟨9, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 9), (⟨5, by decide⟩, 5), (⟨10, by decide⟩, 1)]
  | 5 => [(⟨5, by decide⟩, 8), (⟨6, by decide⟩, 6), (⟨11, by decide⟩, 1)]
  | 6 => [(⟨6, by decide⟩, 7), (⟨12, by decide⟩, 1)]
  | 7 => [(⟨7, by decide⟩, 11), (⟨8, by decide⟩, 2), (⟨21, by decide⟩, 3)]
  | 8 => [(⟨8, by decide⟩, 10), (⟨9, by decide⟩, 3), (⟨13, by decide⟩, 4), (⟨22, by decide⟩, 2)]
  | 9 => [(⟨9, by decide⟩, 9), (⟨10, by decide⟩, 4), (⟨14, by decide⟩, 2), (⟨23, by decide⟩, 2)]
  | 10 => [(⟨10, by decide⟩, 8), (⟨11, by decide⟩, 5), (⟨15, by decide⟩, 2), (⟨24, by decide⟩, 2)]
  | 11 => [(⟨11, by decide⟩, 7), (⟨12, by decide⟩, 12), (⟨16, by decide⟩, 2), (⟨25, by decide⟩, 2)]
  | 12 => [(⟨13, by decide⟩, 9), (⟨14, by decide⟩, 3), (⟨26, by decide⟩, 1)]
  | 13 => [(⟨14, by decide⟩, 8), (⟨15, by decide⟩, 4), (⟨17, by decide⟩, 6), (⟨27, by decide⟩, 1)]
  | 14 => [(⟨15, by decide⟩, 7), (⟨16, by decide⟩, 5), (⟨18, by decide⟩, 3), (⟨28, by decide⟩, 1)]
  | 15 => [(⟨16, by decide⟩, 6), (⟨19, by decide⟩, 3), (⟨29, by decide⟩, 1)]
  | 16 => [(⟨17, by decide⟩, 7), (⟨18, by decide⟩, 4), (⟨30, by decide⟩, 1)]
  | 17 => [(⟨18, by decide⟩, 6), (⟨19, by decide⟩, 10), (⟨20, by decide⟩, 8), (⟨31, by decide⟩, 1)]
  | 18 => [(⟨20, by decide⟩, 5), (⟨32, by decide⟩, 1)]
  | 19 => [(⟨21, by decide⟩, 10), (⟨22, by decide⟩, 2)]
  | 20 => [(⟨22, by decide⟩, 9), (⟨23, by decide⟩, 3), (⟨26, by decide⟩, 4)]
  | 21 => [(⟨23, by decide⟩, 8), (⟨24, by decide⟩, 4), (⟨27, by decide⟩, 2)]
  | 22 => [(⟨24, by decide⟩, 7), (⟨25, by decide⟩, 5), (⟨28, by decide⟩, 2)]
  | 23 => [(⟨25, by decide⟩, 6), (⟨29, by decide⟩, 2)]
  | 24 => [(⟨26, by decide⟩, 8), (⟨27, by decide⟩, 3), (⟨33, by decide⟩, 6)]
  | 25 => [(⟨27, by decide⟩, 7), (⟨28, by decide⟩, 4), (⟨30, by decide⟩, 6), (⟨34, by decide⟩, 4)]
  | 26 => [(⟨28, by decide⟩, 6), (⟨29, by decide⟩, 10), (⟨31, by decide⟩, 3), (⟨35, by decide⟩, 4)]
  | 27 => [(⟨30, by decide⟩, 6), (⟨31, by decide⟩, 4), (⟨36, by decide⟩, 2)]
  | 28 => [(⟨31, by decide⟩, 5), (⟨32, by decide⟩, 12), (⟨37, by decide⟩, 2)]
  | 29 => [(⟨33, by decide⟩, 7), (⟨34, by decide⟩, 3)]
  | 30 => [(⟨34, by decide⟩, 6), (⟨35, by decide⟩, 4), (⟨36, by decide⟩, 6)]
  | 31 => [(⟨35, by decide⟩, 5), (⟨37, by decide⟩, 3)]
  | 32 => [(⟨36, by decide⟩, 5), (⟨37, by decide⟩, 8), (⟨38, by decide⟩, 9)]
  | 33 => [(⟨38, by decide⟩, 4)]
  | _ => []

def retainedCM_4_13WS : SparseIntMatrix 39 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, -390), (⟨1, by decide⟩, 455), (⟨2, by decide⟩, 455), (⟨3, by decide⟩, -728), (⟨4, by decide⟩, -728)]
  | 1 => [(⟨0, by decide⟩, 5070), (⟨1, by decide⟩, -5915), (⟨2, by decide⟩, -5915), (⟨3, by decide⟩, 9464), (⟨4, by decide⟩, 9464)]
  | 2 => [(⟨0, by decide⟩, -21060), (⟨1, by decide⟩, 15990), (⟨2, by decide⟩, 13130), (⟨3, by decide⟩, -18720), (⟨4, by decide⟩, -15288)]
  | 3 => [(⟨0, by decide⟩, 60060), (⟨1, by decide⟩, -22880), (⟨2, by decide⟩, -20020), (⟨3, by decide⟩, 19448), (⟨4, by decide⟩, 10868)]
  | 4 => [(⟨0, by decide⟩, -107250), (⟨1, by decide⟩, 17875), (⟨2, by decide⟩, 17875), (⟨3, by decide⟩, -8008), (⟨4, by decide⟩, -2860)]
  | 5 => [(⟨0, by decide⟩, 115830), (⟨1, by decide⟩, -6435), (⟨2, by decide⟩, -6435)]
  | 6 => [(⟨0, by decide⟩, -51480)]
  | 7 => [(⟨0, by decide⟩, -9360), (⟨1, by decide⟩, 19500), (⟨2, by decide⟩, 22360), (⟨3, by decide⟩, -38064), (⟨4, by decide⟩, -41496)]
  | 8 => [(⟨0, by decide⟩, 51480), (⟨1, by decide⟩, -107250), (⟨2, by decide⟩, -84370), (⟨3, by decide⟩, 147576), (⟨4, by decide⟩, 135564)]
  | 9 => [(⟨0, by decide⟩, -171600), (⟨1, by decide⟩, 157300), (⟨2, by decide⟩, 128700), (⟨3, by decide⟩, -162448), (⟨4, by decide⟩, -97240)]
  | 10 => [(⟨0, by decide⟩, 386100), (⟨1, by decide⟩, -128700), (⟨2, by decide⟩, -128700), (⟨3, by decide⟩, 72072), (⟨4, by decide⟩, 25740)]
  | 11 => [(⟨0, by decide⟩, -617760), (⟨1, by decide⟩, 51480), (⟨2, by decide⟩, 51480)]
  | 12 => [(⟨0, by decide⟩, 360360)]
  | 13 => [(⟨1, by decide⟩, 150150), (⟨2, by decide⟩, 50050), (⟨3, by decide⟩, -144144), (⟨4, by decide⟩, -111540)]
  | 14 => [(⟨1, by decide⟩, -450450), (⟨2, by decide⟩, -107250), (⟨3, by decide⟩, 339768), (⟨4, by decide⟩, 159588)]
  | 15 => [(⟨1, by decide⟩, 386100), (⟨2, by decide⟩, 128700), (⟨3, by decide⟩, -164736), (⟨4, by decide⟩, -41184)]
  | 16 => [(⟨1, by decide⟩, -180180), (⟨2, by decide⟩, -60060)]
  | 17 => [(⟨1, by decide⟩, 343200), (⟨3, by decide⟩, -219648), (⟨4, by decide⟩, -54912)]
  | 18 => [(⟨1, by decide⟩, -600600), (⟨3, by decide⟩, 240240), (⟨4, by decide⟩, 24024)]
  | 19 => [(⟨1, by decide⟩, 360360)]
  | 20 => [(⟨3, by decide⟩, -72072)]
  | 21 => [(⟨2, by decide⟩, -25740), (⟨3, by decide⟩, 41184), (⟨4, by decide⟩, 61776)]
  | 22 => [(⟨2, by decide⟩, 128700), (⟨3, by decide⟩, -205920), (⟨4, by decide⟩, -308880)]
  | 23 => [(⟨2, by decide⟩, -214500), (⟨3, by decide⟩, 247104), (⟨4, by decide⟩, 226512)]
  | 24 => [(⟨2, by decide⟩, 257400), (⟨3, by decide⟩, -123552), (⟨4, by decide⟩, -61776)]
  | 25 => [(⟨2, by decide⟩, -120120)]
  | 26 => [(⟨2, by decide⟩, -128700), (⟨3, by decide⟩, 277992), (⟨4, by decide⟩, 525096)]
  | 27 => [(⟨2, by decide⟩, 343200), (⟨3, by decide⟩, -741312), (⟨4, by decide⟩, -782496)]
  | 28 => [(⟨2, by decide⟩, -600600), (⟨3, by decide⟩, 432432), (⟨4, by decide⟩, 216216)]
  | 29 => [(⟨2, by decide⟩, 360360)]
  | 30 => [(⟨3, by decide⟩, 576576), (⟨4, by decide⟩, 288288)]
  | 31 => [(⟨3, by decide⟩, -864864), (⟨4, by decide⟩, -144144)]
  | 32 => [(⟨3, by decide⟩, 360360)]
  | 33 => [(⟨4, by decide⟩, -308880)]
  | 34 => [(⟨4, by decide⟩, 720720)]
  | 35 => [(⟨4, by decide⟩, -216216)]
  | 36 => [(⟨4, by decide⟩, -576576)]
  | 37 => [(⟨4, by decide⟩, 360360)]
  | _ => []

def retainedCM_4_13LS : SparseIntMatrix 5 39 := fun i =>
  match i.val with
  | 0 => [(⟨12, by decide⟩, 1)]
  | 1 => [(⟨19, by decide⟩, 1)]
  | 2 => [(⟨29, by decide⟩, 1)]
  | 3 => [(⟨32, by decide⟩, 1)]
  | 4 => [(⟨37, by decide⟩, 1)]
  | _ => []

def retainedCM_4_13ZS : SparseIntMatrix 39 34 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 27720), (⟨1, by decide⟩, -2310), (⟨2, by decide⟩, 420), (⟨3, by decide⟩, -126), (⟨4, by decide⟩, 56), (⟨5, by decide⟩, -35), (⟨6, by decide⟩, 30), (⟨7, by decide⟩, 420), (⟨8, by decide⟩, -126), (⟨9, by decide⟩, 56), (⟨10, by decide⟩, -35), (⟨11, by decide⟩, 30), (⟨12, by decide⟩, 56), (⟨13, by decide⟩, -35), (⟨14, by decide⟩, 30), (⟨15, by decide⟩, -35), (⟨16, by decide⟩, 30), (⟨17, by decide⟩, -35), (⟨18, by decide⟩, 56), (⟨19, by decide⟩, -126), (⟨20, by decide⟩, 56), (⟨21, by decide⟩, -35), (⟨22, by decide⟩, 30), (⟨23, by decide⟩, -35), (⟨24, by decide⟩, -35), (⟨25, by decide⟩, 30), (⟨26, by decide⟩, -35), (⟨27, by decide⟩, -35), (⟨28, by decide⟩, 56), (⟨29, by decide⟩, 30), (⟨30, by decide⟩, -35), (⟨31, by decide⟩, 56), (⟨32, by decide⟩, 56), (⟨33, by decide⟩, -126)]
  | 1 => [(⟨1, by decide⟩, 30030), (⟨2, by decide⟩, -5460), (⟨3, by decide⟩, 1638), (⟨4, by decide⟩, -728), (⟨5, by decide⟩, 455), (⟨6, by decide⟩, -390), (⟨7, by decide⟩, -5460), (⟨8, by decide⟩, 1638), (⟨9, by decide⟩, -728), (⟨10, by decide⟩, 455), (⟨11, by decide⟩, -390), (⟨12, by decide⟩, -728), (⟨13, by decide⟩, 455), (⟨14, by decide⟩, -390), (⟨15, by decide⟩, 455), (⟨16, by decide⟩, -390), (⟨17, by decide⟩, 455), (⟨18, by decide⟩, -728), (⟨19, by decide⟩, 1638), (⟨20, by decide⟩, -728), (⟨21, by decide⟩, 455), (⟨22, by decide⟩, -390), (⟨23, by decide⟩, 455), (⟨24, by decide⟩, 455), (⟨25, by decide⟩, -390), (⟨26, by decide⟩, 455), (⟨27, by decide⟩, 455), (⟨28, by decide⟩, -728), (⟨29, by decide⟩, -390), (⟨30, by decide⟩, 455), (⟨31, by decide⟩, -728), (⟨32, by decide⟩, -728), (⟨33, by decide⟩, 1638)]
  | 2 => [(⟨2, by decide⟩, 32760), (⟨3, by decide⟩, -9828), (⟨4, by decide⟩, 4368), (⟨5, by decide⟩, -2730), (⟨6, by decide⟩, 2340), (⟨8, by decide⟩, -3276), (⟨9, by decide⟩, 2184), (⟨10, by decide⟩, -1638), (⟨11, by decide⟩, 1560), (⟨12, by decide⟩, 1456), (⟨13, by decide⟩, -1092), (⟨14, by decide⟩, 1092), (⟨15, by decide⟩, -1430), (⟨16, by decide⟩, 936), (⟨17, by decide⟩, -1170), (⟨18, by decide⟩, 1872), (⟨20, by decide⟩, 728), (⟨21, by decide⟩, -819), (⟨22, by decide⟩, 936), (⟨23, by decide⟩, -1300), (⟨24, by decide⟩, -546), (⟨25, by decide⟩, 624), (⟨26, by decide⟩, -910), (⟨27, by decide⟩, -780), (⟨28, by decide⟩, 1404), (⟨29, by decide⟩, 468), (⟨30, by decide⟩, -650), (⟨31, by decide⟩, 1248), (⟨32, by decide⟩, 1092), (⟨33, by decide⟩, -2457)]
  | 3 => [(⟨3, by decide⟩, 36036), (⟨4, by decide⟩, -16016), (⟨5, by decide⟩, 10010), (⟨6, by decide⟩, -8580), (⟨9, by decide⟩, -4004), (⟨10, by decide⟩, 4004), (⟨11, by decide⟩, -4290), (⟨13, by decide⟩, 1001), (⟨14, by decide⟩, -1716), (⟨15, by decide⟩, 2860), (⟨16, by decide⟩, -858), (⟨17, by decide⟩, 1430), (⟨18, by decide⟩, -2288), (⟨21, by decide⟩, 1001), (⟨22, by decide⟩, -1716), (⟨23, by decide⟩, 2860), (⟨25, by decide⟩, -429), (⟨26, by decide⟩, 1144), (⟨27, by decide⟩, 572), (⟨28, by decide⟩, -1430), (⟨30, by decide⟩, 286), (⟨31, by decide⟩, -1144), (⟨32, by decide⟩, -572), (⟨33, by decide⟩, 1287)]
  | 4 => [(⟨4, by decide⟩, 40040), (⟨5, by decide⟩, -25025), (⟨6, by decide⟩, 21450), (⟨10, by decide⟩, -5005), (⟨11, by decide⟩, 7150), (⟨14, by decide⟩, 1430), (⟨15, by decide⟩, -3575), (⟨17, by decide⟩, -715), (⟨18, by decide⟩, 1144), (⟨22, by decide⟩, 1430), (⟨23, by decide⟩, -3575), (⟨26, by decide⟩, -715), (⟨28, by decide⟩, 572), (⟨31, by decide⟩, 572)]
  | 5 => [(⟨5, by decide⟩, 45045), (⟨6, by decide⟩, -38610), (⟨11, by decide⟩, -6435), (⟨15, by decide⟩, 2145), (⟨23, by decide⟩, 2145)]
  | 6 => [(⟨6, by decide⟩, 51480)]
  | 7 => [(⟨7, by decide⟩, 32760), (⟨8, by decide⟩, -6552), (⟨9, by decide⟩, 2184), (⟨10, by decide⟩, -1092), (⟨11, by decide⟩, 780), (⟨12, by decide⟩, 2912), (⟨13, by decide⟩, -1638), (⟨14, by decide⟩, 1248), (⟨15, by decide⟩, -1300), (⟨16, by decide⟩, 1404), (⟨17, by decide⟩, -1560), (⟨18, by decide⟩, 2496), (⟨19, by decide⟩, -9828), (⟨20, by decide⟩, 3640), (⟨21, by decide⟩, -1911), (⟨22, by decide⟩, 1404), (⟨23, by decide⟩, -1430), (⟨24, by decide⟩, -2184), (⟨25, by decide⟩, 1716), (⟨26, by decide⟩, -1820), (⟨27, by decide⟩, -1950), (⟨28, by decide⟩, 2964), (⟨29, by decide⟩, 1872), (⟨30, by decide⟩, -2080), (⟨31, by decide⟩, 3120), (⟨32, by decide⟩, 3276), (⟨33, by decide⟩, -7371)]
  | 8 => [(⟨8, by decide⟩, 36036), (⟨9, by decide⟩, -12012), (⟨10, by decide⟩, 6006), (⟨11, by decide⟩, -4290), (⟨12, by decide⟩, -16016), (⟨13, by decide⟩, 9009), (⟨14, by decide⟩, -6864), (⟨15, by decide⟩, 7150), (⟨16, by decide⟩, -7722), (⟨17, by decide⟩, 8580), (⟨18, by decide⟩, -13728), (⟨20, by decide⟩, -8008), (⟨21, by decide⟩, 6006), (⟨22, by decide⟩, -5148), (⟨23, by decide⟩, 5720), (⟨24, by decide⟩, 6006), (⟨25, by decide⟩, -5577), (⟨26, by decide⟩, 6578), (⟨27, by decide⟩, 6864), (⟨28, by decide⟩, -11154), (⟨29, by decide⟩, -5148), (⟨30, by decide⟩, 6292), (⟨31, by decide⟩, -10296), (⟨32, by decide⟩, -10296), (⟨33, by decide⟩, 23166)]
  | 9 => [(⟨9, by decide⟩, 40040), (⟨10, by decide⟩, -20020), (⟨11, by decide⟩, 14300), (⟨13, by decide⟩, -10010), (⟨14, by decide⟩, 11440), (⟨15, by decide⟩, -14300), (⟨16, by decide⟩, 8580), (⟨17, by decide⟩, -11440), (⟨18, by decide⟩, 18304), (⟨21, by decide⟩, -10010), (⟨22, by decide⟩, 11440), (⟨23, by decide⟩, -14300), (⟨25, by decide⟩, 4290), (⟨26, by decide⟩, -8580), (⟨27, by decide⟩, -5720), (⟨28, by decide⟩, 12012), (⟨30, by decide⟩, -2860), (⟨31, by decide⟩, 9152), (⟨32, by decide⟩, 5720), (⟨33, by decide⟩, -12870)]
  | 10 => [(⟨10, by decide⟩, 45045), (⟨11, by decide⟩, -32175), (⟨14, by decide⟩, -12870), (⟨15, by decide⟩, 21450), (⟨17, by decide⟩, 6435), (⟨18, by decide⟩, -10296), (⟨22, by decide⟩, -12870), (⟨23, by decide⟩, 21450), (⟨26, by decide⟩, 6435), (⟨28, by decide⟩, -5148), (⟨31, by decide⟩, -5148)]
  | 11 => [(⟨11, by decide⟩, 51480), (⟨15, by decide⟩, -17160), (⟨23, by decide⟩, -17160)]
  | 13 => [(⟨12, by decide⟩, 40040), (⟨13, by decide⟩, -15015), (⟨14, by decide⟩, 8580), (⟨15, by decide⟩, -7150), (⟨16, by decide⟩, 12870), (⟨17, by decide⟩, -12870), (⟨18, by decide⟩, 20592), (⟨24, by decide⟩, -5005), (⟨25, by decide⟩, 4290), (⟨26, by decide⟩, -4290), (⟨27, by decide⟩, -6435), (⟨28, by decide⟩, 10296), (⟨29, by decide⟩, 4290), (⟨30, by decide⟩, -5005), (⟨31, by decide⟩, 7436), (⟨32, by decide⟩, 8580), (⟨33, by decide⟩, -19305)]
  | 14 => [(⟨13, by decide⟩, 45045), (⟨14, by decide⟩, -25740), (⟨15, by decide⟩, 21450), (⟨16, by decide⟩, -38610), (⟨17, by decide⟩, 38610), (⟨18, by decide⟩, -61776), (⟨25, by decide⟩, -6435), (⟨26, by decide⟩, 8580), (⟨27, by decide⟩, 12870), (⟨28, by decide⟩, -23166), (⟨30, by decide⟩, 4290), (⟨31, by decide⟩, -10296), (⟨32, by decide⟩, -10296), (⟨33, by decide⟩, 23166)]
  | 15 => [(⟨14, by decide⟩, 51480), (⟨15, by decide⟩, -42900), (⟨17, by decide⟩, -25740), (⟨18, by decide⟩, 41184), (⟨26, by decide⟩, -8580), (⟨28, by decide⟩, 10296), (⟨31, by decide⟩, 6864)]
  | 16 => [(⟨15, by decide⟩, 60060)]
  | 17 => [(⟨16, by decide⟩, 51480), (⟨17, by decide⟩, -34320), (⟨18, by decide⟩, 54912), (⟨27, by decide⟩, -8580), (⟨28, by decide⟩, 13728), (⟨32, by decide⟩, 3432), (⟨33, by decide⟩, -7722)]
  | 18 => [(⟨17, by decide⟩, 60060), (⟨18, by decide⟩, -96096), (⟨28, by decide⟩, -12012)]
  | 20 => [(⟨18, by decide⟩, 72072)]
  | 21 => [(⟨19, by decide⟩, 36036), (⟨20, by decide⟩, -8008), (⟨21, by decide⟩, 3003), (⟨22, by decide⟩, -1716), (⟨23, by decide⟩, 1430), (⟨24, by decide⟩, 4004), (⟨25, by decide⟩, -2574), (⟨26, by decide⟩, 2288), (⟨27, by decide⟩, 2574), (⟨28, by decide⟩, -3432), (⟨29, by decide⟩, -3432), (⟨30, by decide⟩, 3432), (⟨31, by decide⟩, -4576), (⟨32, by decide⟩, -5148), (⟨33, by decide⟩, 11583)]
  | 22 => [(⟨20, by decide⟩, 40040), (⟨21, by decide⟩, -15015), (⟨22, by decide⟩, 8580), (⟨23, by decide⟩, -7150), (⟨24, by decide⟩, -20020), (⟨25, by decide⟩, 12870), (⟨26, by decide⟩, -11440), (⟨27, by decide⟩, -12870), (⟨28, by decide⟩, 17160), (⟨29, by decide⟩, 17160), (⟨30, by decide⟩, -17160), (⟨31, by decide⟩, 22880), (⟨32, by decide⟩, 25740), (⟨33, by decide⟩, -57915)]
  | 23 => [(⟨21, by decide⟩, 45045), (⟨22, by decide⟩, -25740), (⟨23, by decide⟩, 21450), (⟨25, by decide⟩, -12870), (⟨26, by decide⟩, 17160), (⟨27, by decide⟩, 12870), (⟨28, by decide⟩, -20592), (⟨30, by decide⟩, 8580), (⟨31, by decide⟩, -20592), (⟨32, by decide⟩, -15444), (⟨33, by decide⟩, 34749)]
  | 24 => [(⟨22, by decide⟩, 51480), (⟨23, by decide⟩, -42900), (⟨26, by decide⟩, -17160), (⟨28, by decide⟩, 10296), (⟨31, by decide⟩, 13728)]
  | 25 => [(⟨23, by decide⟩, 60060)]
  | 26 => [(⟨24, by decide⟩, 45045), (⟨25, by decide⟩, -19305), (⟨26, by decide⟩, 12870), (⟨27, by decide⟩, 19305), (⟨28, by decide⟩, -23166), (⟨29, by decide⟩, -38610), (⟨30, by decide⟩, 32175), (⟨31, by decide⟩, -36036), (⟨32, by decide⟩, -46332), (⟨33, by decide⟩, 104247)]
  | 27 => [(⟨25, by decide⟩, 51480), (⟨26, by decide⟩, -34320), (⟨27, by decide⟩, -51480), (⟨28, by decide⟩, 61776), (⟨30, by decide⟩, -34320), (⟨31, by decide⟩, 54912), (⟨32, by decide⟩, 61776), (⟨33, by decide⟩, -138996)]
  | 28 => [(⟨26, by decide⟩, 60060), (⟨28, by decide⟩, -36036), (⟨31, by decide⟩, -48048)]
  | 30 => [(⟨27, by decide⟩, 60060), (⟨28, by decide⟩, -48048), (⟨32, by decide⟩, -24024), (⟨33, by decide⟩, 54054)]
  | 31 => [(⟨28, by decide⟩, 72072)]
  | 33 => [(⟨29, by decide⟩, 51480), (⟨30, by decide⟩, -25740), (⟨31, by decide⟩, 20592), (⟨32, by decide⟩, 30888), (⟨33, by decide⟩, -69498)]
  | 34 => [(⟨30, by decide⟩, 60060), (⟨31, by decide⟩, -48048), (⟨32, by decide⟩, -72072), (⟨33, by decide⟩, 162162)]
  | 35 => [(⟨31, by decide⟩, 72072)]
  | 36 => [(⟨32, by decide⟩, 72072), (⟨33, by decide⟩, -162162)]
  | 38 => [(⟨33, by decide⟩, 90090)]
  | _ => []

def retainedCM_4_13C : Matrix (Fin 34) (Fin 39) ℚ := sparseRatMatrix retainedCM_4_13CS
def retainedCM_4_13U : Matrix (Fin 39) (Fin 5) ℚ := sparseRatScaledMatrix retainedCM_4_13D retainedCM_4_13WS
def retainedCM_4_13L : Matrix (Fin 5) (Fin 39) ℚ := sparseRatMatrix retainedCM_4_13LS
def retainedCM_4_13V : Matrix (Fin 39) (Fin 34) ℚ := sparseRatScaledMatrix retainedCM_4_13D retainedCM_4_13ZS

theorem retainedCM_4_13_sparse_check :
    SparseScaledFrameCheck retainedCM_4_13D retainedCM_4_13CS retainedCM_4_13WS retainedCM_4_13LS retainedCM_4_13ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_13_frame : HasKernelFrame retainedCM_4_13C retainedCM_4_13U retainedCM_4_13L retainedCM_4_13V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_13D≠0) retainedCM_4_13_sparse_check

theorem retainedCM_4_13_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_13C.mulVecLin)=5 :=
  kernelFrame_finrank retainedCM_4_13_frame

/- N=4, degree=14; rows=39, columns=47, nullity=8. -/
def retainedCM_4_14D : ℤ := 360360

def retainedCM_4_14CS : SparseIntMatrix 39 47 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 14), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 13), (⟨2, by decide⟩, 2), (⟨8, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 12), (⟨3, by decide⟩, 3), (⟨9, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 11), (⟨4, by decide⟩, 4), (⟨10, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 10), (⟨5, by decide⟩, 5), (⟨11, by decide⟩, 1)]
  | 5 => [(⟨5, by decide⟩, 9), (⟨6, by decide⟩, 6), (⟨12, by decide⟩, 1)]
  | 6 => [(⟨6, by decide⟩, 8), (⟨7, by decide⟩, 14), (⟨13, by decide⟩, 1)]
  | 7 => [(⟨8, by decide⟩, 12), (⟨9, by decide⟩, 2), (⟨24, by decide⟩, 3)]
  | 8 => [(⟨9, by decide⟩, 11), (⟨10, by decide⟩, 3), (⟨14, by decide⟩, 4), (⟨25, by decide⟩, 2)]
  | 9 => [(⟨10, by decide⟩, 10), (⟨11, by decide⟩, 4), (⟨15, by decide⟩, 2), (⟨26, by decide⟩, 2)]
  | 10 => [(⟨11, by decide⟩, 9), (⟨12, by decide⟩, 5), (⟨16, by decide⟩, 2), (⟨27, by decide⟩, 2)]
  | 11 => [(⟨12, by decide⟩, 8), (⟨13, by decide⟩, 6), (⟨17, by decide⟩, 2), (⟨28, by decide⟩, 2)]
  | 12 => [(⟨13, by decide⟩, 7), (⟨18, by decide⟩, 2), (⟨29, by decide⟩, 2)]
  | 13 => [(⟨14, by decide⟩, 10), (⟨15, by decide⟩, 3), (⟨30, by decide⟩, 1)]
  | 14 => [(⟨15, by decide⟩, 9), (⟨16, by decide⟩, 4), (⟨19, by decide⟩, 6), (⟨31, by decide⟩, 1)]
  | 15 => [(⟨16, by decide⟩, 8), (⟨17, by decide⟩, 5), (⟨20, by decide⟩, 3), (⟨32, by decide⟩, 1)]
  | 16 => [(⟨17, by decide⟩, 7), (⟨18, by decide⟩, 12), (⟨21, by decide⟩, 3), (⟨33, by decide⟩, 1)]
  | 17 => [(⟨19, by decide⟩, 8), (⟨20, by decide⟩, 4), (⟨34, by decide⟩, 1)]
  | 18 => [(⟨20, by decide⟩, 7), (⟨21, by decide⟩, 5), (⟨22, by decide⟩, 8), (⟨35, by decide⟩, 1)]
  | 19 => [(⟨21, by decide⟩, 6), (⟨23, by decide⟩, 4), (⟨36, by decide⟩, 1)]
  | 20 => [(⟨22, by decide⟩, 6), (⟨23, by decide⟩, 10), (⟨37, by decide⟩, 1)]
  | 21 => [(⟨24, by decide⟩, 11), (⟨25, by decide⟩, 2)]
  | 22 => [(⟨25, by decide⟩, 10), (⟨26, by decide⟩, 3), (⟨30, by decide⟩, 4)]
  | 23 => [(⟨26, by decide⟩, 9), (⟨27, by decide⟩, 4), (⟨31, by decide⟩, 2)]
  | 24 => [(⟨27, by decide⟩, 8), (⟨28, by decide⟩, 5), (⟨32, by decide⟩, 2)]
  | 25 => [(⟨28, by decide⟩, 7), (⟨29, by decide⟩, 12), (⟨33, by decide⟩, 2)]
  | 26 => [(⟨30, by decide⟩, 9), (⟨31, by decide⟩, 3), (⟨38, by decide⟩, 6)]
  | 27 => [(⟨31, by decide⟩, 8), (⟨32, by decide⟩, 4), (⟨34, by decide⟩, 6), (⟨39, by decide⟩, 4)]
  | 28 => [(⟨32, by decide⟩, 7), (⟨33, by decide⟩, 5), (⟨35, by decide⟩, 3), (⟨40, by decide⟩, 4)]
  | 29 => [(⟨33, by decide⟩, 6), (⟨36, by decide⟩, 3), (⟨41, by decide⟩, 4)]
  | 30 => [(⟨34, by decide⟩, 7), (⟨35, by decide⟩, 4), (⟨42, by decide⟩, 2)]
  | 31 => [(⟨35, by decide⟩, 6), (⟨36, by decide⟩, 10), (⟨37, by decide⟩, 8), (⟨43, by decide⟩, 2)]
  | 32 => [(⟨37, by decide⟩, 5), (⟨44, by decide⟩, 2)]
  | 33 => [(⟨38, by decide⟩, 8), (⟨39, by decide⟩, 3)]
  | 34 => [(⟨39, by decide⟩, 7), (⟨40, by decide⟩, 4), (⟨42, by decide⟩, 6)]
  | 35 => [(⟨40, by decide⟩, 6), (⟨41, by decide⟩, 10), (⟨43, by decide⟩, 3)]
  | 36 => [(⟨42, by decide⟩, 6), (⟨43, by decide⟩, 4), (⟨45, by decide⟩, 9)]
  | 37 => [(⟨43, by decide⟩, 5), (⟨44, by decide⟩, 12), (⟨46, by decide⟩, 6)]
  | 38 => [(⟨45, by decide⟩, 5), (⟨46, by decide⟩, 8)]
  | _ => []

def retainedCM_4_14WS : SparseIntMatrix 47 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, -210), (⟨1, by decide⟩, 210), (⟨2, by decide⟩, -280), (⟨3, by decide⟩, 210), (⟨4, by decide⟩, -280), (⟨5, by decide⟩, -280), (⟨6, by decide⟩, 504), (⟨7, by decide⟩, 504)]
  | 1 => [(⟨0, by decide⟩, 2940), (⟨1, by decide⟩, -2940), (⟨2, by decide⟩, 3920), (⟨3, by decide⟩, -2940), (⟨4, by decide⟩, 3920), (⟨5, by decide⟩, 3920), (⟨6, by decide⟩, -7056), (⟨7, by decide⟩, -7056)]
  | 2 => [(⟨0, by decide⟩, -19110), (⟨1, by decide⟩, 10530), (⟨2, by decide⟩, -11180), (⟨3, by decide⟩, 9750), (⟨4, by decide⟩, -8840), (⟨5, by decide⟩, -8060), (⟨6, by decide⟩, 13104), (⟨7, by decide⟩, 12012)]
  | 3 => [(⟨0, by decide⟩, 76440), (⟨1, by decide⟩, -24960), (⟨2, by decide⟩, 16120), (⟨3, by decide⟩, -24960), (⟨4, by decide⟩, 11830), (⟨5, by decide⟩, 10400), (⟨6, by decide⟩, -11856), (⟨7, by decide⟩, -8424)]
  | 4 => [(⟨0, by decide⟩, -210210), (⟨1, by decide⟩, 38610), (⟨2, by decide⟩, -11440), (⟨3, by decide⟩, 38610), (⟨4, by decide⟩, -8580), (⟨5, by decide⟩, -8580), (⟨6, by decide⟩, 4576), (⟨7, by decide⟩, 1716)]
  | 5 => [(⟨0, by decide⟩, 420420), (⟨1, by decide⟩, -34320), (⟨2, by decide⟩, 2860), (⟨3, by decide⟩, -34320), (⟨4, by decide⟩, 2860), (⟨5, by decide⟩, 2860)]
  | 6 => [(⟨0, by decide⟩, -630630), (⟨1, by decide⟩, 12870), (⟨3, by decide⟩, 12870)]
  | 7 => [(⟨0, by decide⟩, 360360)]
  | 8 => [(⟨1, by decide⟩, 8580), (⟨2, by decide⟩, -14300), (⟨3, by decide⟩, 9360), (⟨4, by decide⟩, -16640), (⟨5, by decide⟩, -17420), (⟨6, by decide⟩, 32760), (⟨7, by decide⟩, 33852)]
  | 9 => [(⟨1, by decide⟩, -51480), (⟨2, by decide⟩, 85800), (⟨3, by decide⟩, -42120), (⟨4, by decide⟩, 70590), (⟨5, by decide⟩, 65520), (⟨6, by decide⟩, -121680), (⟨7, by decide⟩, -118872)]
  | 10 => [(⟨1, by decide⟩, 120120), (⟨2, by decide⟩, -131560), (⟨3, by decide⟩, 120120), (⟨4, by decide⟩, -95810), (⟨5, by decide⟩, -80080), (⟨6, by decide⟩, 112112), (⟨7, by decide⟩, 85800)]
  | 11 => [(⟨1, by decide⟩, -214500), (⟨2, by decide⟩, 100100), (⟨3, by decide⟩, -214500), (⟨4, by decide⟩, 71500), (⟨5, by decide⟩, 71500), (⟨6, by decide⟩, -45760), (⟨7, by decide⟩, -17160)]
  | 12 => [(⟨1, by decide⟩, 231660), (⟨2, by decide⟩, -25740), (⟨3, by decide⟩, 231660), (⟨4, by decide⟩, -25740), (⟨5, by decide⟩, -25740)]
  | 13 => [(⟨1, by decide⟩, -102960), (⟨3, by decide⟩, -102960)]
  | 14 => [(⟨1, by decide⟩, 51480), (⟨2, by decide⟩, -137280), (⟨4, by decide⟩, -68640), (⟨5, by decide⟩, -48620), (⟨6, by decide⟩, 113256), (⟨7, by decide⟩, 108108)]
  | 15 => [(⟨1, by decide⟩, -171600), (⟨2, by decide⟩, 457600), (⟨4, by decide⟩, 178750), (⟨5, by decide⟩, 85800), (⟨6, by decide⟩, -212784), (⟨7, by decide⟩, -161304)]
  | 16 => [(⟨1, by decide⟩, 386100), (⟨2, by decide⟩, -386100), (⟨4, by decide⟩, -128700), (⟨5, by decide⟩, -85800), (⟨6, by decide⟩, 92664), (⟨7, by decide⟩, 30888)]
  | 17 => [(⟨1, by decide⟩, -617760), (⟨2, by decide⟩, 102960), (⟨4, by decide⟩, 51480), (⟨5, by decide⟩, 34320)]
  | 18 => [(⟨1, by decide⟩, 360360)]
  | 19 => [(⟨2, by decide⟩, -429000), (⟨4, by decide⟩, -107250), (⟨6, by decide⟩, 102960), (⟨7, by decide⟩, 61776)]
  | 20 => [(⟨2, by decide⟩, 858000), (⟨4, by decide⟩, 128700), (⟨6, by decide⟩, -96096), (⟨7, by decide⟩, -20592)]
  | 21 => [(⟨2, by decide⟩, -240240), (⟨4, by decide⟩, -60060)]
  | 22 => [(⟨2, by decide⟩, -600600), (⟨6, by decide⟩, 24024)]
  | 23 => [(⟨2, by decide⟩, 360360)]
  | 24 => [(⟨3, by decide⟩, -9360), (⟨4, by decide⟩, 19500), (⟨5, by decide⟩, 26000), (⟨6, by decide⟩, -49920), (⟨7, by decide⟩, -56160)]
  | 25 => [(⟨3, by decide⟩, 51480), (⟨4, by decide⟩, -107250), (⟨5, by decide⟩, -143000), (⟨6, by decide⟩, 274560), (⟨7, by decide⟩, 308880)]
  | 26 => [(⟨3, by decide⟩, -171600), (⟨4, by decide⟩, 157300), (⟨5, by decide⟩, 171600), (⟨6, by decide⟩, -256256), (⟨7, by decide⟩, -233376)]
  | 27 => [(⟨3, by decide⟩, 386100), (⟨4, by decide⟩, -128700), (⟨5, by decide⟩, -171600), (⟨6, by decide⟩, 113256), (⟨7, by decide⟩, 46332)]
  | 28 => [(⟨3, by decide⟩, -617760), (⟨4, by decide⟩, 51480), (⟨5, by decide⟩, 68640)]
  | 29 => [(⟨3, by decide⟩, 360360)]
  | 30 => [(⟨4, by decide⟩, 150150), (⟨5, by decide⟩, 228800), (⟨6, by decide⟩, -494208), (⟨7, by decide⟩, -597168)]
  | 31 => [(⟨4, by decide⟩, -450450), (⟨5, by decide⟩, -429000), (⟨6, by decide⟩, 926640), (⟨7, by decide⟩, 957528)]
  | 32 => [(⟨4, by decide⟩, 386100), (⟨5, by decide⟩, 514800), (⟨6, by decide⟩, -453024), (⟨7, by decide⟩, -185328)]
  | 33 => [(⟨4, by decide⟩, -180180), (⟨5, by decide⟩, -240240)]
  | 34 => [(⟨4, by decide⟩, 343200), (⟨6, by decide⟩, -439296), (⟨7, by decide⟩, -411840)]
  | 35 => [(⟨4, by decide⟩, -600600), (⟨6, by decide⟩, 480480), (⟨7, by decide⟩, 144144)]
  | 36 => [(⟨4, by decide⟩, 360360)]
  | 37 => [(⟨6, by decide⟩, -144144)]
  | 38 => [(⟨5, by decide⟩, -128700), (⟨6, by decide⟩, 277992), (⟨7, by decide⟩, 416988)]
  | 39 => [(⟨5, by decide⟩, 343200), (⟨6, by decide⟩, -741312), (⟨7, by decide⟩, -1111968)]
  | 40 => [(⟨5, by decide⟩, -600600), (⟨6, by decide⟩, 432432), (⟨7, by decide⟩, 216216)]
  | 41 => [(⟨5, by decide⟩, 360360)]
  | 42 => [(⟨6, by decide⟩, 576576), (⟨7, by decide⟩, 1153152)]
  | 43 => [(⟨6, by decide⟩, -864864), (⟨7, by decide⟩, -432432)]
  | 44 => [(⟨6, by decide⟩, 360360)]
  | 45 => [(⟨7, by decide⟩, -576576)]
  | 46 => [(⟨7, by decide⟩, 360360)]
  | _ => []

def retainedCM_4_14LS : SparseIntMatrix 8 47 := fun i =>
  match i.val with
  | 0 => [(⟨7, by decide⟩, 1)]
  | 1 => [(⟨18, by decide⟩, 1)]
  | 2 => [(⟨23, by decide⟩, 1)]
  | 3 => [(⟨29, by decide⟩, 1)]
  | 4 => [(⟨36, by decide⟩, 1)]
  | 5 => [(⟨41, by decide⟩, 1)]
  | 6 => [(⟨44, by decide⟩, 1)]
  | 7 => [(⟨46, by decide⟩, 1)]
  | _ => []

def retainedCM_4_14ZS : SparseIntMatrix 47 39 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 25740), (⟨1, by decide⟩, -1980), (⟨2, by decide⟩, 330), (⟨3, by decide⟩, -90), (⟨4, by decide⟩, 36), (⟨5, by decide⟩, -20), (⟨6, by decide⟩, 15), (⟨7, by decide⟩, 330), (⟨8, by decide⟩, -90), (⟨9, by decide⟩, 36), (⟨10, by decide⟩, -20), (⟨11, by decide⟩, 15), (⟨12, by decide⟩, -15), (⟨13, by decide⟩, 36), (⟨14, by decide⟩, -20), (⟨15, by decide⟩, 15), (⟨16, by decide⟩, -15), (⟨17, by decide⟩, 15), (⟨18, by decide⟩, -15), (⟨19, by decide⟩, 20), (⟨20, by decide⟩, 20), (⟨21, by decide⟩, -90), (⟨22, by decide⟩, 36), (⟨23, by decide⟩, -20), (⟨24, by decide⟩, 15), (⟨25, by decide⟩, -15), (⟨26, by decide⟩, -20), (⟨27, by decide⟩, 15), (⟨28, by decide⟩, -15), (⟨29, by decide⟩, 20), (⟨30, by decide⟩, -15), (⟨31, by decide⟩, 20), (⟨32, by decide⟩, -36), (⟨33, by decide⟩, 15), (⟨34, by decide⟩, -15), (⟨35, by decide⟩, 20), (⟨36, by decide⟩, 20), (⟨37, by decide⟩, -36), (⟨38, by decide⟩, -36)]
  | 1 => [(⟨1, by decide⟩, 27720), (⟨2, by decide⟩, -4620), (⟨3, by decide⟩, 1260), (⟨4, by decide⟩, -504), (⟨5, by decide⟩, 280), (⟨6, by decide⟩, -210), (⟨7, by decide⟩, -4620), (⟨8, by decide⟩, 1260), (⟨9, by decide⟩, -504), (⟨10, by decide⟩, 280), (⟨11, by decide⟩, -210), (⟨12, by decide⟩, 210), (⟨13, by decide⟩, -504), (⟨14, by decide⟩, 280), (⟨15, by decide⟩, -210), (⟨16, by decide⟩, 210), (⟨17, by decide⟩, -210), (⟨18, by decide⟩, 210), (⟨19, by decide⟩, -280), (⟨20, by decide⟩, -280), (⟨21, by decide⟩, 1260), (⟨22, by decide⟩, -504), (⟨23, by decide⟩, 280), (⟨24, by decide⟩, -210), (⟨25, by decide⟩, 210), (⟨26, by decide⟩, 280), (⟨27, by decide⟩, -210), (⟨28, by decide⟩, 210), (⟨29, by decide⟩, -280), (⟨30, by decide⟩, 210), (⟨31, by decide⟩, -280), (⟨32, by decide⟩, 504), (⟨33, by decide⟩, -210), (⟨34, by decide⟩, 210), (⟨35, by decide⟩, -280), (⟨36, by decide⟩, -280), (⟨37, by decide⟩, 504), (⟨38, by decide⟩, 504)]
  | 2 => [(⟨2, by decide⟩, 30030), (⟨3, by decide⟩, -8190), (⟨4, by decide⟩, 3276), (⟨5, by decide⟩, -1820), (⟨6, by decide⟩, 1365), (⟨8, by decide⟩, -2730), (⟨9, by decide⟩, 1638), (⟨10, by decide⟩, -1092), (⟨11, by decide⟩, 910), (⟨12, by decide⟩, -975), (⟨13, by decide⟩, 1092), (⟨14, by decide⟩, -728), (⟨15, by decide⟩, 637), (⟨16, by decide⟩, -715), (⟨17, by decide⟩, 546), (⟨18, by decide⟩, -585), (⟨19, by decide⟩, 845), (⟨20, by decide⟩, 780), (⟨22, by decide⟩, 546), (⟨23, by decide⟩, -546), (⟨24, by decide⟩, 546), (⟨25, by decide⟩, -650), (⟨26, by decide⟩, -364), (⟨27, by decide⟩, 364), (⟨28, by decide⟩, -455), (⟨29, by decide⟩, 715), (⟨30, by decide⟩, -390), (⟨31, by decide⟩, 585), (⟨32, by decide⟩, -1092), (⟨33, by decide⟩, 273), (⟨34, by decide⟩, -325), (⟨35, by decide⟩, 520), (⟨36, by decide⟩, 455), (⟨37, by decide⟩, -910), (⟨38, by decide⟩, -819)]
  | 3 => [(⟨3, by decide⟩, 32760), (⟨4, by decide⟩, -13104), (⟨5, by decide⟩, 7280), (⟨6, by decide⟩, -5460), (⟨9, by decide⟩, -3276), (⟨10, by decide⟩, 2912), (⟨11, by decide⟩, -2730), (⟨12, by decide⟩, 3120), (⟨14, by decide⟩, 728), (⟨15, by decide⟩, -1092), (⟨16, by decide⟩, 1560), (⟨17, by decide⟩, -546), (⟨18, by decide⟩, 780), (⟨19, by decide⟩, -1430), (⟨20, by decide⟩, -1040), (⟨23, by decide⟩, 728), (⟨24, by decide⟩, -1092), (⟨25, by decide⟩, 1560), (⟨27, by decide⟩, -273), (⟨28, by decide⟩, 624), (⟨29, by decide⟩, -1300), (⟨30, by decide⟩, 312), (⟨31, by decide⟩, -650), (⟨32, by decide⟩, 1248), (⟨34, by decide⟩, 156), (⟨35, by decide⟩, -520), (⟨36, by decide⟩, -260), (⟨37, by decide⟩, 780), (⟨38, by decide⟩, 468)]
  | 4 => [(⟨4, by decide⟩, 36036), (⟨5, by decide⟩, -20020), (⟨6, by decide⟩, 15015), (⟨10, by decide⟩, -4004), (⟨11, by decide⟩, 5005), (⟨12, by decide⟩, -6435), (⟨15, by decide⟩, 1001), (⟨16, by decide⟩, -2145), (⟨18, by decide⟩, -429), (⟨19, by decide⟩, 1430), (⟨20, by decide⟩, 572), (⟨24, by decide⟩, 1001), (⟨25, by decide⟩, -2145), (⟨28, by decide⟩, -429), (⟨29, by decide⟩, 1430), (⟨31, by decide⟩, 286), (⟨32, by decide⟩, -572), (⟨35, by decide⟩, 286), (⟨37, by decide⟩, -286)]
  | 5 => [(⟨5, by decide⟩, 40040), (⟨6, by decide⟩, -30030), (⟨11, by decide⟩, -5005), (⟨12, by decide⟩, 8580), (⟨16, by decide⟩, 1430), (⟨19, by decide⟩, -715), (⟨25, by decide⟩, 1430), (⟨29, by decide⟩, -715)]
  | 6 => [(⟨6, by decide⟩, 45045), (⟨12, by decide⟩, -6435)]
  | 8 => [(⟨7, by decide⟩, 30030), (⟨8, by decide⟩, -5460), (⟨9, by decide⟩, 1638), (⟨10, by decide⟩, -728), (⟨11, by decide⟩, 455), (⟨12, by decide⟩, -390), (⟨13, by decide⟩, 2184), (⟨14, by decide⟩, -1092), (⟨15, by decide⟩, 728), (⟨16, by decide⟩, -650), (⟨17, by decide⟩, 819), (⟨18, by decide⟩, -780), (⟨19, by decide⟩, 975), (⟨20, by decide⟩, 1040), (⟨21, by decide⟩, -8190), (⟨22, by decide⟩, 2730), (⟨23, by decide⟩, -1274), (⟨24, by decide⟩, 819), (⟨25, by decide⟩, -715), (⟨26, by decide⟩, -1456), (⟨27, by decide⟩, 1001), (⟨28, by decide⟩, -910), (⟨29, by decide⟩, 1105), (⟨30, by decide⟩, -975), (⟨31, by decide⟩, 1235), (⟨32, by decide⟩, -2184), (⟨33, by decide⟩, 1092), (⟨34, by decide⟩, -1040), (⟨35, by decide⟩, 1300), (⟨36, by decide⟩, 1365), (⟨37, by decide⟩, -2366), (⟨38, by decide⟩, -2457)]
  | 9 => [(⟨8, by decide⟩, 32760), (⟨9, by decide⟩, -9828), (⟨10, by decide⟩, 4368), (⟨11, by decide⟩, -2730), (⟨12, by decide⟩, 2340), (⟨13, by decide⟩, -13104), (⟨14, by decide⟩, 6552), (⟨15, by decide⟩, -4368), (⟨16, by decide⟩, 3900), (⟨17, by decide⟩, -4914), (⟨18, by decide⟩, 4680), (⟨19, by decide⟩, -5850), (⟨20, by decide⟩, -6240), (⟨22, by decide⟩, -6552), (⟨23, by decide⟩, 4368), (⟨24, by decide⟩, -3276), (⟨25, by decide⟩, 3120), (⟨26, by decide⟩, 4368), (⟨27, by decide⟩, -3549), (⟨28, by decide⟩, 3588), (⟨29, by decide⟩, -4680), (⟨30, by decide⟩, 3744), (⟨31, by decide⟩, -5070), (⟨32, by decide⟩, 9360), (⟨33, by decide⟩, -3276), (⟨34, by decide⟩, 3432), (⟨35, by decide⟩, -4680), (⟨36, by decide⟩, -4680), (⟨37, by decide⟩, 8580), (⟨38, by decide⟩, 8424)]
  | 10 => [(⟨9, by decide⟩, 36036), (⟨10, by decide⟩, -16016), (⟨11, by decide⟩, 10010), (⟨12, by decide⟩, -8580), (⟨14, by decide⟩, -8008), (⟨15, by decide⟩, 8008), (⟨16, by decide⟩, -8580), (⟨17, by decide⟩, 6006), (⟨18, by decide⟩, -6864), (⟨19, by decide⟩, 10010), (⟨20, by decide⟩, 9152), (⟨23, by decide⟩, -8008), (⟨24, by decide⟩, 8008), (⟨25, by decide⟩, -8580), (⟨27, by decide⟩, 3003), (⟨28, by decide⟩, -5148), (⟨29, by decide⟩, 8580), (⟨30, by decide⟩, -3432), (⟨31, by decide⟩, 6006), (⟨32, by decide⟩, -11440), (⟨34, by decide⟩, -1716), (⟨35, by decide⟩, 4576), (⟨36, by decide⟩, 2860), (⟨37, by decide⟩, -7436), (⟨38, by decide⟩, -5148)]
  | 11 => [(⟨10, by decide⟩, 40040), (⟨11, by decide⟩, -25025), (⟨12, by decide⟩, 21450), (⟨15, by decide⟩, -10010), (⟨16, by decide⟩, 14300), (⟨18, by decide⟩, 4290), (⟨19, by decide⟩, -10725), (⟨20, by decide⟩, -5720), (⟨24, by decide⟩, -10010), (⟨25, by decide⟩, 14300), (⟨28, by decide⟩, 4290), (⟨29, by decide⟩, -10725), (⟨31, by decide⟩, -2860), (⟨32, by decide⟩, 5720), (⟨35, by decide⟩, -2860), (⟨37, by decide⟩, 2860)]
  | 12 => [(⟨11, by decide⟩, 45045), (⟨12, by decide⟩, -38610), (⟨16, by decide⟩, -12870), (⟨19, by decide⟩, 6435), (⟨25, by decide⟩, -12870), (⟨29, by decide⟩, 6435)]
  | 13 => [(⟨12, by decide⟩, 51480)]
  | 14 => [(⟨13, by decide⟩, 36036), (⟨14, by decide⟩, -12012), (⟨15, by decide⟩, 6006), (⟨16, by decide⟩, -4290), (⟨17, by decide⟩, 9009), (⟨18, by decide⟩, -7722), (⟨19, by decide⟩, 8580), (⟨20, by decide⟩, 10296), (⟨26, by decide⟩, -4004), (⟨27, by decide⟩, 3003), (⟨28, by decide⟩, -2574), (⟨29, by decide⟩, 2860), (⟨30, by decide⟩, -3861), (⟨31, by decide⟩, 5148), (⟨32, by decide⟩, -10296), (⟨33, by decide⟩, 3003), (⟨34, by decide⟩, -3003), (⟨35, by decide⟩, 3718), (⟨36, by decide⟩, 4290), (⟨37, by decide⟩, -7722), (⟨38, by decide⟩, -7722)]
  | 15 => [(⟨14, by decide⟩, 40040), (⟨15, by decide⟩, -20020), (⟨16, by decide⟩, 14300), (⟨17, by decide⟩, -30030), (⟨18, by decide⟩, 25740), (⟨19, by decide⟩, -28600), (⟨20, by decide⟩, -34320), (⟨27, by decide⟩, -5005), (⟨28, by decide⟩, 5720), (⟨29, by decide⟩, -7150), (⟨30, by decide⟩, 8580), (⟨31, by decide⟩, -12870), (⟨32, by decide⟩, 27456), (⟨34, by decide⟩, 2860), (⟨35, by decide⟩, -5720), (⟨36, by decide⟩, -5720), (⟨37, by decide⟩, 13156), (⟨38, by decide⟩, 10296)]
  | 16 => [(⟨15, by decide⟩, 45045), (⟨16, by decide⟩, -32175), (⟨18, by decide⟩, -19305), (⟨19, by decide⟩, 32175), (⟨20, by decide⟩, 25740), (⟨28, by decide⟩, -6435), (⟨29, by decide⟩, 10725), (⟨31, by decide⟩, 6435), (⟨32, by decide⟩, -15444), (⟨35, by decide⟩, 4290), (⟨37, by decide⟩, -5148)]
  | 17 => [(⟨16, by decide⟩, 51480), (⟨19, by decide⟩, -25740), (⟨29, by decide⟩, -8580)]
  | 19 => [(⟨17, by decide⟩, 45045), (⟨18, by decide⟩, -25740), (⟨19, by decide⟩, 21450), (⟨20, by decide⟩, 34320), (⟨30, by decide⟩, -6435), (⟨31, by decide⟩, 8580), (⟨32, by decide⟩, -20592), (⟨36, by decide⟩, 2145), (⟨37, by decide⟩, -5148), (⟨38, by decide⟩, -3861)]
  | 20 => [(⟨18, by decide⟩, 51480), (⟨19, by decide⟩, -42900), (⟨20, by decide⟩, -68640), (⟨31, by decide⟩, -8580), (⟨32, by decide⟩, 27456), (⟨37, by decide⟩, 3432)]
  | 21 => [(⟨19, by decide⟩, 60060)]
  | 22 => [(⟨20, by decide⟩, 60060), (⟨32, by decide⟩, -12012)]
  | 24 => [(⟨21, by decide⟩, 32760), (⟨22, by decide⟩, -6552), (⟨23, by decide⟩, 2184), (⟨24, by decide⟩, -1092), (⟨25, by decide⟩, 780), (⟨26, by decide⟩, 2912), (⟨27, by decide⟩, -1638), (⟨28, by decide⟩, 1248), (⟨29, by decide⟩, -1300), (⟨30, by decide⟩, 1404), (⟨31, by decide⟩, -1560), (⟨32, by decide⟩, 2496), (⟨33, by decide⟩, -2184), (⟨34, by decide⟩, 1872), (⟨35, by decide⟩, -2080), (⟨36, by decide⟩, -2340), (⟨37, by decide⟩, 3744), (⟨38, by decide⟩, 4212)]
  | 25 => [(⟨22, by decide⟩, 36036), (⟨23, by decide⟩, -12012), (⟨24, by decide⟩, 6006), (⟨25, by decide⟩, -4290), (⟨26, by decide⟩, -16016), (⟨27, by decide⟩, 9009), (⟨28, by decide⟩, -6864), (⟨29, by decide⟩, 7150), (⟨30, by decide⟩, -7722), (⟨31, by decide⟩, 8580), (⟨32, by decide⟩, -13728), (⟨33, by decide⟩, 12012), (⟨34, by decide⟩, -10296), (⟨35, by decide⟩, 11440), (⟨36, by decide⟩, 12870), (⟨37, by decide⟩, -20592), (⟨38, by decide⟩, -23166)]
  | 26 => [(⟨23, by decide⟩, 40040), (⟨24, by decide⟩, -20020), (⟨25, by decide⟩, 14300), (⟨27, by decide⟩, -10010), (⟨28, by decide⟩, 11440), (⟨29, by decide⟩, -14300), (⟨30, by decide⟩, 8580), (⟨31, by decide⟩, -11440), (⟨32, by decide⟩, 18304), (⟨34, by decide⟩, 5720), (⟨35, by decide⟩, -11440), (⟨36, by decide⟩, -8580), (⟨37, by decide⟩, 18304), (⟨38, by decide⟩, 15444)]
  | 27 => [(⟨24, by decide⟩, 45045), (⟨25, by decide⟩, -32175), (⟨28, by decide⟩, -12870), (⟨29, by decide⟩, 21450), (⟨31, by decide⟩, 6435), (⟨32, by decide⟩, -10296), (⟨35, by decide⟩, 8580), (⟨37, by decide⟩, -7722)]
  | 28 => [(⟨25, by decide⟩, 51480), (⟨29, by decide⟩, -17160)]
  | 30 => [(⟨26, by decide⟩, 40040), (⟨27, by decide⟩, -15015), (⟨28, by decide⟩, 8580), (⟨29, by decide⟩, -7150), (⟨30, by decide⟩, 12870), (⟨31, by decide⟩, -12870), (⟨32, by decide⟩, 20592), (⟨33, by decide⟩, -30030), (⟨34, by decide⟩, 21450), (⟨35, by decide⟩, -20020), (⟨36, by decide⟩, -25740), (⟨37, by decide⟩, 37752), (⟨38, by decide⟩, 46332)]
  | 31 => [(⟨27, by decide⟩, 45045), (⟨28, by decide⟩, -25740), (⟨29, by decide⟩, 21450), (⟨30, by decide⟩, -38610), (⟨31, by decide⟩, 38610), (⟨32, by decide⟩, -61776), (⟨34, by decide⟩, -25740), (⟨35, by decide⟩, 34320), (⟨36, by decide⟩, 38610), (⟨37, by decide⟩, -66924), (⟨38, by decide⟩, -69498)]
  | 32 => [(⟨28, by decide⟩, 51480), (⟨29, by decide⟩, -42900), (⟨31, by decide⟩, -25740), (⟨32, by decide⟩, 41184), (⟨35, by decide⟩, -34320), (⟨37, by decide⟩, 30888)]
  | 33 => [(⟨29, by decide⟩, 60060)]
  | 34 => [(⟨30, by decide⟩, 51480), (⟨31, by decide⟩, -34320), (⟨32, by decide⟩, 54912), (⟨36, by decide⟩, -17160), (⟨37, by decide⟩, 27456), (⟨38, by decide⟩, 30888)]
  | 35 => [(⟨31, by decide⟩, 60060), (⟨32, by decide⟩, -96096), (⟨37, by decide⟩, -24024)]
  | 37 => [(⟨32, by decide⟩, 72072)]
  | 38 => [(⟨33, by decide⟩, 45045), (⟨34, by decide⟩, -19305), (⟨35, by decide⟩, 12870), (⟨36, by decide⟩, 19305), (⟨37, by decide⟩, -23166), (⟨38, by decide⟩, -34749)]
  | 39 => [(⟨34, by decide⟩, 51480), (⟨35, by decide⟩, -34320), (⟨36, by decide⟩, -51480), (⟨37, by decide⟩, 61776), (⟨38, by decide⟩, 92664)]
  | 40 => [(⟨35, by decide⟩, 60060), (⟨37, by decide⟩, -36036)]
  | 42 => [(⟨36, by decide⟩, 60060), (⟨37, by decide⟩, -48048), (⟨38, by decide⟩, -108108)]
  | 43 => [(⟨37, by decide⟩, 72072)]
  | 45 => [(⟨38, by decide⟩, 72072)]
  | _ => []

def retainedCM_4_14C : Matrix (Fin 39) (Fin 47) ℚ := sparseRatMatrix retainedCM_4_14CS
def retainedCM_4_14U : Matrix (Fin 47) (Fin 8) ℚ := sparseRatScaledMatrix retainedCM_4_14D retainedCM_4_14WS
def retainedCM_4_14L : Matrix (Fin 8) (Fin 47) ℚ := sparseRatMatrix retainedCM_4_14LS
def retainedCM_4_14V : Matrix (Fin 47) (Fin 39) ℚ := sparseRatScaledMatrix retainedCM_4_14D retainedCM_4_14ZS

theorem retainedCM_4_14_sparse_check :
    SparseScaledFrameCheck retainedCM_4_14D retainedCM_4_14CS retainedCM_4_14WS retainedCM_4_14LS retainedCM_4_14ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_14_frame : HasKernelFrame retainedCM_4_14C retainedCM_4_14U retainedCM_4_14L retainedCM_4_14V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_14D≠0) retainedCM_4_14_sparse_check

theorem retainedCM_4_14_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_14C.mulVecLin)=8 :=
  kernelFrame_finrank retainedCM_4_14_frame

/- N=4, degree=15; rows=47, columns=54, nullity=7. -/
def retainedCM_4_15D : ℤ := 360360

def retainedCM_4_15CS : SparseIntMatrix 47 54 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 15), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 14), (⟨2, by decide⟩, 2), (⟨8, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 13), (⟨3, by decide⟩, 3), (⟨9, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 12), (⟨4, by decide⟩, 4), (⟨10, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 11), (⟨5, by decide⟩, 5), (⟨11, by decide⟩, 1)]
  | 5 => [(⟨5, by decide⟩, 10), (⟨6, by decide⟩, 6), (⟨12, by decide⟩, 1)]
  | 6 => [(⟨6, by decide⟩, 9), (⟨7, by decide⟩, 7), (⟨13, by decide⟩, 1)]
  | 7 => [(⟨7, by decide⟩, 8), (⟨14, by decide⟩, 1)]
  | 8 => [(⟨8, by decide⟩, 13), (⟨9, by decide⟩, 2), (⟨27, by decide⟩, 3)]
  | 9 => [(⟨9, by decide⟩, 12), (⟨10, by decide⟩, 3), (⟨15, by decide⟩, 4), (⟨28, by decide⟩, 2)]
  | 10 => [(⟨10, by decide⟩, 11), (⟨11, by decide⟩, 4), (⟨16, by decide⟩, 2), (⟨29, by decide⟩, 2)]
  | 11 => [(⟨11, by decide⟩, 10), (⟨12, by decide⟩, 5), (⟨17, by decide⟩, 2), (⟨30, by decide⟩, 2)]
  | 12 => [(⟨12, by decide⟩, 9), (⟨13, by decide⟩, 6), (⟨18, by decide⟩, 2), (⟨31, by decide⟩, 2)]
  | 13 => [(⟨13, by decide⟩, 8), (⟨14, by decide⟩, 14), (⟨19, by decide⟩, 2), (⟨32, by decide⟩, 2)]
  | 14 => [(⟨15, by decide⟩, 11), (⟨16, by decide⟩, 3), (⟨33, by decide⟩, 1)]
  | 15 => [(⟨16, by decide⟩, 10), (⟨17, by decide⟩, 4), (⟨20, by decide⟩, 6), (⟨34, by decide⟩, 1)]
  | 16 => [(⟨17, by decide⟩, 9), (⟨18, by decide⟩, 5), (⟨21, by decide⟩, 3), (⟨35, by decide⟩, 1)]
  | 17 => [(⟨18, by decide⟩, 8), (⟨19, by decide⟩, 6), (⟨22, by decide⟩, 3), (⟨36, by decide⟩, 1)]
  | 18 => [(⟨19, by decide⟩, 7), (⟨23, by decide⟩, 3), (⟨37, by decide⟩, 1)]
  | 19 => [(⟨20, by decide⟩, 9), (⟨21, by decide⟩, 4), (⟨38, by decide⟩, 1)]
  | 20 => [(⟨21, by decide⟩, 8), (⟨22, by decide⟩, 5), (⟨24, by decide⟩, 8), (⟨39, by decide⟩, 1)]
  | 21 => [(⟨22, by decide⟩, 7), (⟨23, by decide⟩, 12), (⟨25, by decide⟩, 4), (⟨40, by decide⟩, 1)]
  | 22 => [(⟨24, by decide⟩, 7), (⟨25, by decide⟩, 5), (⟨41, by decide⟩, 1)]
  | 23 => [(⟨25, by decide⟩, 6), (⟨26, by decide⟩, 15), (⟨42, by decide⟩, 1)]
  | 24 => [(⟨27, by decide⟩, 12), (⟨28, by decide⟩, 2)]
  | 25 => [(⟨28, by decide⟩, 11), (⟨29, by decide⟩, 3), (⟨33, by decide⟩, 4)]
  | 26 => [(⟨29, by decide⟩, 10), (⟨30, by decide⟩, 4), (⟨34, by decide⟩, 2)]
  | 27 => [(⟨30, by decide⟩, 9), (⟨31, by decide⟩, 5), (⟨35, by decide⟩, 2)]
  | 28 => [(⟨31, by decide⟩, 8), (⟨32, by decide⟩, 6), (⟨36, by decide⟩, 2)]
  | 29 => [(⟨32, by decide⟩, 7), (⟨37, by decide⟩, 2)]
  | 30 => [(⟨33, by decide⟩, 10), (⟨34, by decide⟩, 3), (⟨43, by decide⟩, 6)]
  | 31 => [(⟨34, by decide⟩, 9), (⟨35, by decide⟩, 4), (⟨38, by decide⟩, 6), (⟨44, by decide⟩, 4)]
  | 32 => [(⟨35, by decide⟩, 8), (⟨36, by decide⟩, 5), (⟨39, by decide⟩, 3), (⟨45, by decide⟩, 4)]
  | 33 => [(⟨36, by decide⟩, 7), (⟨37, by decide⟩, 12), (⟨40, by decide⟩, 3), (⟨46, by decide⟩, 4)]
  | 34 => [(⟨38, by decide⟩, 8), (⟨39, by decide⟩, 4), (⟨47, by decide⟩, 2)]
  | 35 => [(⟨39, by decide⟩, 7), (⟨40, by decide⟩, 5), (⟨41, by decide⟩, 8), (⟨48, by decide⟩, 2)]
  | 36 => [(⟨40, by decide⟩, 6), (⟨42, by decide⟩, 4), (⟨49, by decide⟩, 2)]
  | 37 => [(⟨41, by decide⟩, 6), (⟨42, by decide⟩, 10), (⟨50, by decide⟩, 2)]
  | 38 => [(⟨43, by decide⟩, 9), (⟨44, by decide⟩, 3)]
  | 39 => [(⟨44, by decide⟩, 8), (⟨45, by decide⟩, 4), (⟨47, by decide⟩, 6)]
  | 40 => [(⟨45, by decide⟩, 7), (⟨46, by decide⟩, 5), (⟨48, by decide⟩, 3)]
  | 41 => [(⟨46, by decide⟩, 6), (⟨49, by decide⟩, 3)]
  | 42 => [(⟨47, by decide⟩, 7), (⟨48, by decide⟩, 4), (⟨51, by decide⟩, 9)]
  | 43 => [(⟨48, by decide⟩, 6), (⟨49, by decide⟩, 10), (⟨50, by decide⟩, 8), (⟨52, by decide⟩, 6)]
  | 44 => [(⟨50, by decide⟩, 5), (⟨53, by decide⟩, 3)]
  | 45 => [(⟨51, by decide⟩, 6), (⟨52, by decide⟩, 4)]
  | 46 => [(⟨52, by decide⟩, 5), (⟨53, by decide⟩, 12)]
  | _ => []

def retainedCM_4_15WS : SparseIntMatrix 54 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 105), (⟨1, by decide⟩, -120), (⟨2, by decide⟩, 180), (⟨3, by decide⟩, -120), (⟨4, by decide⟩, 180), (⟨5, by decide⟩, 180), (⟨6, by decide⟩, -360)]
  | 1 => [(⟨0, by decide⟩, -1575), (⟨1, by decide⟩, 1800), (⟨2, by decide⟩, -2700), (⟨3, by decide⟩, 1800), (⟨4, by decide⟩, -2700), (⟨5, by decide⟩, -2700), (⟨6, by decide⟩, 5400)]
  | 2 => [(⟨0, by decide⟩, 8085), (⟨1, by decide⟩, -6120), (⟨2, by decide⟩, 8400), (⟨3, by decide⟩, -5340), (⟨4, by decide⟩, 6580), (⟨5, by decide⟩, 5670), (⟨6, by decide⟩, -10248)]
  | 3 => [(⟨0, by decide⟩, -28665), (⟨1, by decide⟩, 12480), (⟨2, by decide⟩, -13650), (⟨3, by decide⟩, 11700), (⟨4, by decide⟩, -8970), (⟨5, by decide⟩, -6630), (⟨6, by decide⟩, 8736)]
  | 4 => [(⟨0, by decide⟩, 66885), (⟨1, by decide⟩, -16380), (⟨2, by decide⟩, 11700), (⟨3, by decide⟩, -16380), (⟨4, by decide⟩, 5980), (⟨5, by decide⟩, 4550), (⟨6, by decide⟩, -2808)]
  | 5 => [(⟨0, by decide⟩, -105105), (⟨1, by decide⟩, 12870), (⟨2, by decide⟩, -4290), (⟨3, by decide⟩, 12870), (⟨4, by decide⟩, -1430), (⟨5, by decide⟩, -1430)]
  | 6 => [(⟨0, by decide⟩, 105105), (⟨1, by decide⟩, -4290), (⟨3, by decide⟩, -4290)]
  | 7 => [(⟨0, by decide⟩, -45045)]
  | 8 => [(⟨0, by decide⟩, 2940), (⟨1, by decide⟩, -6480), (⟨2, by decide⟩, 10500), (⟨3, by decide⟩, -7260), (⟨4, by decide⟩, 12320), (⟨5, by decide⟩, 13230), (⟨6, by decide⟩, -27552)]
  | 9 => [(⟨0, by decide⟩, -19110), (⟨1, by decide⟩, 42120), (⟨2, by decide⟩, -68250), (⟨3, by decide⟩, 34320), (⟨4, by decide⟩, -58630), (⟨5, by decide⟩, -53820), (⟨6, by decide⟩, 107016)]
  | 10 => [(⟨0, by decide⟩, 76440), (⟨1, by decide⟩, -84240), (⟨2, by decide⟩, 117000), (⟨3, by decide⟩, -74880), (⟨4, by decide⟩, 83720), (⟨5, by decide⟩, 61360), (⟨6, by decide⟩, -93600)]
  | 11 => [(⟨0, by decide⟩, -210210), (⟨1, by decide⟩, 115830), (⟨2, by decide⟩, -107250), (⟨3, by decide⟩, 115830), (⟨4, by decide⟩, -58630), (⟨5, by decide⟩, -42900), (⟨6, by decide⟩, 30888)]
  | 12 => [(⟨0, by decide⟩, 420420), (⟨1, by decide⟩, -102960), (⟨2, by decide⟩, 42900), (⟨3, by decide⟩, -102960), (⟨4, by decide⟩, 14300), (⟨5, by decide⟩, 14300)]
  | 13 => [(⟨0, by decide⟩, -630630), (⟨1, by decide⟩, 38610), (⟨3, by decide⟩, 38610)]
  | 14 => [(⟨0, by decide⟩, 360360)]
  | 15 => [(⟨1, by decide⟩, -63180), (⟨2, by decide⟩, 117000), (⟨3, by decide⟩, -21060), (⟨4, by decide⟩, 70200), (⟨5, by decide⟩, 51090), (⟨6, by decide⟩, -106704)]
  | 16 => [(⟨1, by decide⟩, 231660), (⟨2, by decide⟩, -429000), (⟨3, by decide⟩, 60060), (⟨4, by decide⟩, -211640), (⟨5, by decide⟩, -105820), (⟨6, by decide⟩, 192192)]
  | 17 => [(⟨1, by decide⟩, -321750), (⟨2, by decide⟩, 429000), (⟨3, by decide⟩, -107250), (⟨4, by decide⟩, 157300), (⟨5, by decide⟩, 71500), (⟨6, by decide⟩, -65208)]
  | 18 => [(⟨1, by decide⟩, 347490), (⟨2, by decide⟩, -193050), (⟨3, by decide⟩, 115830), (⟨4, by decide⟩, -38610), (⟨5, by decide⟩, -25740)]
  | 19 => [(⟨1, by decide⟩, -154440), (⟨3, by decide⟩, -51480)]
  | 20 => [(⟨1, by decide⟩, -171600), (⟨2, by decide⟩, 429000), (⟨4, by decide⟩, 171600), (⟨5, by decide⟩, 42900), (⟨6, by decide⟩, -89232)]
  | 21 => [(⟨1, by decide⟩, 386100), (⟨2, by decide⟩, -965250), (⟨4, by decide⟩, -278850), (⟨5, by decide⟩, -42900), (⟨6, by decide⟩, 61776)]
  | 22 => [(⟨1, by decide⟩, -617760), (⟨2, by decide⟩, 514800), (⟨4, by decide⟩, 68640), (⟨5, by decide⟩, 17160)]
  | 23 => [(⟨1, by decide⟩, 360360)]
  | 24 => [(⟨2, by decide⟩, 643500), (⟨4, by decide⟩, 128700), (⟨6, by decide⟩, -10296)]
  | 25 => [(⟨2, by decide⟩, -900900), (⟨4, by decide⟩, -60060)]
  | 26 => [(⟨2, by decide⟩, 360360)]
  | 27 => [(⟨3, by decide⟩, 8580), (⟨4, by decide⟩, -14300), (⟨5, by decide⟩, -21450), (⟨6, by decide⟩, 48048)]
  | 28 => [(⟨3, by decide⟩, -51480), (⟨4, by decide⟩, 85800), (⟨5, by decide⟩, 128700), (⟨6, by decide⟩, -288288)]
  | 29 => [(⟨3, by decide⟩, 120120), (⟨4, by decide⟩, -131560), (⟨5, by decide⟩, -145860), (⟨6, by decide⟩, 260832)]
  | 30 => [(⟨3, by decide⟩, -214500), (⟨4, by decide⟩, 100100), (⟨5, by decide⟩, 107250), (⟨6, by decide⟩, -89232)]
  | 31 => [(⟨3, by decide⟩, 231660), (⟨4, by decide⟩, -25740), (⟨5, by decide⟩, -38610)]
  | 32 => [(⟨3, by decide⟩, -102960)]
  | 33 => [(⟨3, by decide⟩, 51480), (⟨4, by decide⟩, -137280), (⟨5, by decide⟩, -244530), (⟨6, by decide⟩, 597168)]
  | 34 => [(⟨3, by decide⟩, -171600), (⟨4, by decide⟩, 457600), (⟨5, by decide⟩, 514800), (⟨6, by decide⟩, -1125696)]
  | 35 => [(⟨3, by decide⟩, 386100), (⟨4, by decide⟩, -386100), (⟨5, by decide⟩, -386100), (⟨6, by decide⟩, 401544)]
  | 36 => [(⟨3, by decide⟩, -617760), (⟨4, by decide⟩, 102960), (⟨5, by decide⟩, 154440)]
  | 37 => [(⟨3, by decide⟩, 360360)]
  | 38 => [(⟨4, by decide⟩, -429000), (⟨5, by decide⟩, -214500), (⟨6, by decide⟩, 555984)]
  | 39 => [(⟨4, by decide⟩, 858000), (⟨5, by decide⟩, 257400), (⟨6, by decide⟩, -411840)]
  | 40 => [(⟨4, by decide⟩, -240240), (⟨5, by decide⟩, -120120)]
  | 41 => [(⟨4, by decide⟩, -600600), (⟨6, by decide⟩, 72072)]
  | 42 => [(⟨4, by decide⟩, 360360)]
  | 43 => [(⟨5, by decide⟩, 150150), (⟨6, by decide⟩, -432432)]
  | 44 => [(⟨5, by decide⟩, -450450), (⟨6, by decide⟩, 1297296)]
  | 45 => [(⟨5, by decide⟩, 386100), (⟨6, by decide⟩, -494208)]
  | 46 => [(⟨5, by decide⟩, -180180)]
  | 47 => [(⟨5, by decide⟩, 343200), (⟨6, by decide⟩, -1400256)]
  | 48 => [(⟨5, by decide⟩, -600600), (⟨6, by decide⟩, 1153152)]
  | 49 => [(⟨5, by decide⟩, 360360)]
  | 50 => [(⟨6, by decide⟩, -216216)]
  | 51 => [(⟨6, by decide⟩, 576576)]
  | 52 => [(⟨6, by decide⟩, -864864)]
  | 53 => [(⟨6, by decide⟩, 360360)]
  | _ => []

def retainedCM_4_15LS : SparseIntMatrix 7 54 := fun i =>
  match i.val with
  | 0 => [(⟨14, by decide⟩, 1)]
  | 1 => [(⟨23, by decide⟩, 1)]
  | 2 => [(⟨26, by decide⟩, 1)]
  | 3 => [(⟨37, by decide⟩, 1)]
  | 4 => [(⟨42, by decide⟩, 1)]
  | 5 => [(⟨49, by decide⟩, 1)]
  | 6 => [(⟨53, by decide⟩, 1)]
  | _ => []

def retainedCM_4_15ZS : SparseIntMatrix 54 47 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 24024), (⟨1, by decide⟩, -1716), (⟨2, by decide⟩, 264), (⟨3, by decide⟩, -66), (⟨4, by decide⟩, 24), (⟨5, by decide⟩, -12), (⟨6, by decide⟩, 8), (⟨7, by decide⟩, -7), (⟨8, by decide⟩, 264), (⟨9, by decide⟩, -66), (⟨10, by decide⟩, 24), (⟨11, by decide⟩, -12), (⟨12, by decide⟩, 8), (⟨13, by decide⟩, -7), (⟨14, by decide⟩, 24), (⟨15, by decide⟩, -12), (⟨16, by decide⟩, 8), (⟨17, by decide⟩, -7), (⟨18, by decide⟩, 8), (⟨19, by decide⟩, 8), (⟨20, by decide⟩, -7), (⟨21, by decide⟩, 8), (⟨22, by decide⟩, 8), (⟨23, by decide⟩, -12), (⟨24, by decide⟩, -66), (⟨25, by decide⟩, 24), (⟨26, by decide⟩, -12), (⟨27, by decide⟩, 8), (⟨28, by decide⟩, -7), (⟨29, by decide⟩, 8), (⟨30, by decide⟩, -12), (⟨31, by decide⟩, 8), (⟨32, by decide⟩, -7), (⟨33, by decide⟩, 8), (⟨34, by decide⟩, -7), (⟨35, by decide⟩, 8), (⟨36, by decide⟩, -12), (⟨37, by decide⟩, -12), (⟨38, by decide⟩, 8), (⟨39, by decide⟩, -7), (⟨40, by decide⟩, 8), (⟨41, by decide⟩, -12), (⟨42, by decide⟩, 8), (⟨43, by decide⟩, -12), (⟨44, by decide⟩, 24), (⟨45, by decide⟩, -12), (⟨46, by decide⟩, 24)]
  | 1 => [(⟨1, by decide⟩, 25740), (⟨2, by decide⟩, -3960), (⟨3, by decide⟩, 990), (⟨4, by decide⟩, -360), (⟨5, by decide⟩, 180), (⟨6, by decide⟩, -120), (⟨7, by decide⟩, 105), (⟨8, by decide⟩, -3960), (⟨9, by decide⟩, 990), (⟨10, by decide⟩, -360), (⟨11, by decide⟩, 180), (⟨12, by decide⟩, -120), (⟨13, by decide⟩, 105), (⟨14, by decide⟩, -360), (⟨15, by decide⟩, 180), (⟨16, by decide⟩, -120), (⟨17, by decide⟩, 105), (⟨18, by decide⟩, -120), (⟨19, by decide⟩, -120), (⟨20, by decide⟩, 105), (⟨21, by decide⟩, -120), (⟨22, by decide⟩, -120), (⟨23, by decide⟩, 180), (⟨24, by decide⟩, 990), (⟨25, by decide⟩, -360), (⟨26, by decide⟩, 180), (⟨27, by decide⟩, -120), (⟨28, by decide⟩, 105), (⟨29, by decide⟩, -120), (⟨30, by decide⟩, 180), (⟨31, by decide⟩, -120), (⟨32, by decide⟩, 105), (⟨33, by decide⟩, -120), (⟨34, by decide⟩, 105), (⟨35, by decide⟩, -120), (⟨36, by decide⟩, 180), (⟨37, by decide⟩, 180), (⟨38, by decide⟩, -120), (⟨39, by decide⟩, 105), (⟨40, by decide⟩, -120), (⟨41, by decide⟩, 180), (⟨42, by decide⟩, -120), (⟨43, by decide⟩, 180), (⟨44, by decide⟩, -360), (⟨45, by decide⟩, 180), (⟨46, by decide⟩, -360)]
  | 2 => [(⟨2, by decide⟩, 27720), (⟨3, by decide⟩, -6930), (⟨4, by decide⟩, 2520), (⟨5, by decide⟩, -1260), (⟨6, by decide⟩, 840), (⟨7, by decide⟩, -735), (⟨9, by decide⟩, -2310), (⟨10, by decide⟩, 1260), (⟨11, by decide⟩, -756), (⟨12, by decide⟩, 560), (⟨13, by decide⟩, -525), (⟨14, by decide⟩, 840), (⟨15, by decide⟩, -504), (⟨16, by decide⟩, 392), (⟨17, by decide⟩, -385), (⟨18, by decide⟩, 480), (⟨19, by decide⟩, 336), (⟨20, by decide⟩, -315), (⟨21, by decide⟩, 390), (⟨22, by decide⟩, 360), (⟨23, by decide⟩, -560), (⟨25, by decide⟩, 420), (⟨26, by decide⟩, -378), (⟨27, by decide⟩, 336), (⟨28, by decide⟩, -350), (⟨29, by decide⟩, 450), (⟨30, by decide⟩, -252), (⟨31, by decide⟩, 224), (⟨32, by decide⟩, -245), (⟨33, by decide⟩, 330), (⟨34, by decide⟩, -210), (⟨35, by decide⟩, 270), (⟨36, by decide⟩, -455), (⟨37, by decide⟩, -420), (⟨38, by decide⟩, 168), (⟨39, by decide⟩, -175), (⟨40, by decide⟩, 240), (⟨41, by decide⟩, -420), (⟨42, by decide⟩, 210), (⟨43, by decide⟩, -350), (⟨44, by decide⟩, 728), (⟨45, by decide⟩, -315), (⟨46, by decide⟩, 672)]
  | 3 => [(⟨3, by decide⟩, 30030), (⟨4, by decide⟩, -10920), (⟨5, by decide⟩, 5460), (⟨6, by decide⟩, -3640), (⟨7, by decide⟩, 3185), (⟨10, by decide⟩, -2730), (⟨11, by decide⟩, 2184), (⟨12, by decide⟩, -1820), (⟨13, by decide⟩, 1820), (⟨15, by decide⟩, 546), (⟨16, by decide⟩, -728), (⟨17, by decide⟩, 910), (⟨18, by decide⟩, -1300), (⟨19, by decide⟩, -364), (⟨20, by decide⟩, 455), (⟨21, by decide⟩, -715), (⟨22, by decide⟩, -520), (⟨23, by decide⟩, 910), (⟨26, by decide⟩, 546), (⟨27, by decide⟩, -728), (⟨28, by decide⟩, 910), (⟨29, by decide⟩, -1300), (⟨31, by decide⟩, -182), (⟨32, by decide⟩, 364), (⟨33, by decide⟩, -650), (⟨34, by decide⟩, 182), (⟨35, by decide⟩, -325), (⟨36, by decide⟩, 715), (⟨37, by decide⟩, 520), (⟨39, by decide⟩, 91), (⟨40, by decide⟩, -260), (⟨41, by decide⟩, 650), (⟨42, by decide⟩, -130), (⟨43, by decide⟩, 325), (⟨44, by decide⟩, -728), (⟨45, by decide⟩, 195), (⟨46, by decide⟩, -546)]
  | 4 => [(⟨4, by decide⟩, 32760), (⟨5, by decide⟩, -16380), (⟨6, by decide⟩, 10920), (⟨7, by decide⟩, -9555), (⟨11, by decide⟩, -3276), (⟨12, by decide⟩, 3640), (⟨13, by decide⟩, -4095), (⟨16, by decide⟩, 728), (⟨17, by decide⟩, -1365), (⟨18, by decide⟩, 2340), (⟨20, by decide⟩, -273), (⟨21, by decide⟩, 780), (⟨22, by decide⟩, 312), (⟨23, by decide⟩, -780), (⟨27, by decide⟩, 728), (⟨28, by decide⟩, -1365), (⟨29, by decide⟩, 2340), (⟨32, by decide⟩, -273), (⟨33, by decide⟩, 780), (⟨35, by decide⟩, 156), (⟨36, by decide⟩, -650), (⟨37, by decide⟩, -260), (⟨40, by decide⟩, 156), (⟨41, by decide⟩, -650), (⟨43, by decide⟩, -130), (⟨44, by decide⟩, 312), (⟨46, by decide⟩, 156)]
  | 5 => [(⟨5, by decide⟩, 36036), (⟨6, by decide⟩, -24024), (⟨7, by decide⟩, 21021), (⟨12, by decide⟩, -4004), (⟨13, by decide⟩, 6006), (⟨17, by decide⟩, 1001), (⟨18, by decide⟩, -2574), (⟨21, by decide⟩, -429), (⟨23, by decide⟩, 286), (⟨28, by decide⟩, 1001), (⟨29, by decide⟩, -2574), (⟨33, by decide⟩, -429), (⟨36, by decide⟩, 286), (⟨41, by decide⟩, 286)]
  | 6 => [(⟨6, by decide⟩, 40040), (⟨7, by decide⟩, -35035), (⟨13, by decide⟩, -5005), (⟨18, by decide⟩, 1430), (⟨29, by decide⟩, 1430)]
  | 7 => [(⟨7, by decide⟩, 45045)]
  | 8 => [(⟨8, by decide⟩, 27720), (⟨9, by decide⟩, -4620), (⟨10, by decide⟩, 1260), (⟨11, by decide⟩, -504), (⟨12, by decide⟩, 280), (⟨13, by decide⟩, -210), (⟨14, by decide⟩, 1680), (⟨15, by decide⟩, -756), (⟨16, by decide⟩, 448), (⟨17, by decide⟩, -350), (⟨18, by decide⟩, 360), (⟨19, by decide⟩, 504), (⟨20, by decide⟩, -420), (⟨21, by decide⟩, 450), (⟨22, by decide⟩, 480), (⟨23, by decide⟩, -700), (⟨24, by decide⟩, -6930), (⟨25, by decide⟩, 2100), (⟨26, by decide⟩, -882), (⟨27, by decide⟩, 504), (⟨28, by decide⟩, -385), (⟨29, by decide⟩, 390), (⟨30, by decide⟩, -1008), (⟨31, by decide⟩, 616), (⟨32, by decide⟩, -490), (⟨33, by decide⟩, 510), (⟨34, by decide⟩, -525), (⟨35, by decide⟩, 570), (⟨36, by decide⟩, -805), (⟨37, by decide⟩, -840), (⟨38, by decide⟩, 672), (⟨39, by decide⟩, -560), (⟨40, by decide⟩, 600), (⟨41, by decide⟩, -840), (⟨42, by decide⟩, 630), (⟨43, by decide⟩, -910), (⟨44, by decide⟩, 1792), (⟨45, by decide⟩, -945), (⟨46, by decide⟩, 1848)]
  | 9 => [(⟨9, by decide⟩, 30030), (⟨10, by decide⟩, -8190), (⟨11, by decide⟩, 3276), (⟨12, by decide⟩, -1820), (⟨13, by decide⟩, 1365), (⟨14, by decide⟩, -10920), (⟨15, by decide⟩, 4914), (⟨16, by decide⟩, -2912), (⟨17, by decide⟩, 2275), (⟨18, by decide⟩, -2340), (⟨19, by decide⟩, -3276), (⟨20, by decide⟩, 2730), (⟨21, by decide⟩, -2925), (⟨22, by decide⟩, -3120), (⟨23, by decide⟩, 4550), (⟨25, by decide⟩, -5460), (⟨26, by decide⟩, 3276), (⟨27, by decide⟩, -2184), (⟨28, by decide⟩, 1820), (⟨29, by decide⟩, -1950), (⟨30, by decide⟩, 3276), (⟨31, by decide⟩, -2366), (⟨32, by decide⟩, 2093), (⟨33, by decide⟩, -2340), (⟨34, by decide⟩, 2184), (⟨35, by decide⟩, -2535), (⟨36, by decide⟩, 3770), (⟨37, by decide⟩, 3900), (⟨38, by decide⟩, -2184), (⟨39, by decide⟩, 2002), (⟨40, by decide⟩, -2340), (⟨41, by decide⟩, 3510), (⟨42, by decide⟩, -2340), (⟨43, by decide⟩, 3575), (⟨44, by decide⟩, -7280), (⟨45, by decide⟩, 3510), (⟨46, by decide⟩, -7098)]
  | 10 => [(⟨10, by decide⟩, 32760), (⟨11, by decide⟩, -13104), (⟨12, by decide⟩, 7280), (⟨13, by decide⟩, -5460), (⟨15, by decide⟩, -6552), (⟨16, by decide⟩, 5824), (⟨17, by decide⟩, -5460), (⟨18, by decide⟩, 6240), (⟨19, by decide⟩, 4368), (⟨20, by decide⟩, -4368), (⟨21, by decide⟩, 5460), (⟨22, by decide⟩, 4992), (⟨23, by decide⟩, -7800), (⟨26, by decide⟩, -6552), (⟨27, by decide⟩, 5824), (⟨28, by decide⟩, -5460), (⟨29, by decide⟩, 6240), (⟨31, by decide⟩, 2184), (⟨32, by decide⟩, -3276), (⟨33, by decide⟩, 4680), (⟨34, by decide⟩, -2184), (⟨35, by decide⟩, 3276), (⟨36, by decide⟩, -5980), (⟨37, by decide⟩, -5200), (⟨39, by decide⟩, -1092), (⟨40, by decide⟩, 2496), (⟨41, by decide⟩, -5200), (⟨42, by decide⟩, 1560), (⟨43, by decide⟩, -3380), (⟨44, by decide⟩, 7488), (⟨45, by decide⟩, -2340), (⟨46, by decide⟩, 5928)]
  | 11 => [(⟨11, by decide⟩, 36036), (⟨12, by decide⟩, -20020), (⟨13, by decide⟩, 15015), (⟨16, by decide⟩, -8008), (⟨17, by decide⟩, 10010), (⟨18, by decide⟩, -12870), (⟨20, by decide⟩, 3003), (⟨21, by decide⟩, -6435), (⟨22, by decide⟩, -3432), (⟨23, by decide⟩, 7150), (⟨27, by decide⟩, -8008), (⟨28, by decide⟩, 10010), (⟨29, by decide⟩, -12870), (⟨32, by decide⟩, 3003), (⟨33, by decide⟩, -6435), (⟨35, by decide⟩, -1716), (⟨36, by decide⟩, 5720), (⟨37, by decide⟩, 2860), (⟨40, by decide⟩, -1716), (⟨41, by decide⟩, 5720), (⟨43, by decide⟩, 1430), (⟨44, by decide⟩, -3432), (⟨46, by decide⟩, -1716)]
  | 12 => [(⟨12, by decide⟩, 40040), (⟨13, by decide⟩, -30030), (⟨17, by decide⟩, -10010), (⟨18, by decide⟩, 17160), (⟨21, by decide⟩, 4290), (⟨23, by decide⟩, -2860), (⟨28, by decide⟩, -10010), (⟨29, by decide⟩, 17160), (⟨33, by decide⟩, 4290), (⟨36, by decide⟩, -2860), (⟨41, by decide⟩, -2860)]
  | 13 => [(⟨13, by decide⟩, 45045), (⟨18, by decide⟩, -12870), (⟨29, by decide⟩, -12870)]
  | 15 => [(⟨14, by decide⟩, 32760), (⟨15, by decide⟩, -9828), (⟨16, by decide⟩, 4368), (⟨17, by decide⟩, -2730), (⟨18, by decide⟩, 2340), (⟨19, by decide⟩, 6552), (⟨20, by decide⟩, -4914), (⟨21, by decide⟩, 4680), (⟨22, by decide⟩, 5616), (⟨23, by decide⟩, -7800), (⟨30, by decide⟩, -3276), (⟨31, by decide⟩, 2184), (⟨32, by decide⟩, -1638), (⟨33, by decide⟩, 1560), (⟨34, by decide⟩, -2457), (⟨35, by decide⟩, 2808), (⟨36, by decide⟩, -3900), (⟨37, by decide⟩, -4680), (⟨38, by decide⟩, 2184), (⟨39, by decide⟩, -1911), (⟨40, by decide⟩, 2028), (⟨41, by decide⟩, -2730), (⟨42, by decide⟩, 2340), (⟨43, by decide⟩, -3510), (⟨44, by decide⟩, 7488), (⟨45, by decide⟩, -3510), (⟨46, by decide⟩, 7020)]
  | 16 => [(⟨15, by decide⟩, 36036), (⟨16, by decide⟩, -16016), (⟨17, by decide⟩, 10010), (⟨18, by decide⟩, -8580), (⟨19, by decide⟩, -24024), (⟨20, by decide⟩, 18018), (⟨21, by decide⟩, -17160), (⟨22, by decide⟩, -20592), (⟨23, by decide⟩, 28600), (⟨31, by decide⟩, -4004), (⟨32, by decide⟩, 4004), (⟨33, by decide⟩, -4290), (⟨34, by decide⟩, 6006), (⟨35, by decide⟩, -7722), (⟨36, by decide⟩, 11440), (⟨37, by decide⟩, 13728), (⟨39, by decide⟩, 2002), (⟨40, by decide⟩, -3432), (⟨41, by decide⟩, 5720), (⟨42, by decide⟩, -3432), (⟨43, by decide⟩, 6578), (⟨44, by decide⟩, -16016), (⟨45, by decide⟩, 5148), (⟨46, by decide⟩, -12012)]
  | 17 => [(⟨16, by decide⟩, 40040), (⟨17, by decide⟩, -25025), (⟨18, by decide⟩, 21450), (⟨20, by decide⟩, -15015), (⟨21, by decide⟩, 21450), (⟨22, by decide⟩, 17160), (⟨23, by decide⟩, -28600), (⟨32, by decide⟩, -5005), (⟨33, by decide⟩, 7150), (⟨35, by decide⟩, 4290), (⟨36, by decide⟩, -10725), (⟨37, by decide⟩, -8580), (⟨40, by decide⟩, 2860), (⟨41, by decide⟩, -7150), (⟨43, by decide⟩, -2860), (⟨44, by decide⟩, 8008), (⟨46, by decide⟩, 3432)]
  | 18 => [(⟨17, by decide⟩, 45045), (⟨18, by decide⟩, -38610), (⟨21, by decide⟩, -19305), (⟨23, by decide⟩, 12870), (⟨33, by decide⟩, -6435), (⟨36, by decide⟩, 6435), (⟨41, by decide⟩, 4290)]
  | 19 => [(⟨18, by decide⟩, 51480)]
  | 20 => [(⟨19, by decide⟩, 40040), (⟨20, by decide⟩, -20020), (⟨21, by decide⟩, 14300), (⟨22, by decide⟩, 22880), (⟨23, by decide⟩, -28600), (⟨34, by decide⟩, -5005), (⟨35, by decide⟩, 5720), (⟨36, by decide⟩, -7150), (⟨37, by decide⟩, -11440), (⟨42, by decide⟩, 1430), (⟨43, by decide⟩, -2860), (⟨44, by decide⟩, 9152), (⟨45, by decide⟩, -2145), (⟨46, by decide⟩, 5148)]
  | 21 => [(⟨20, by decide⟩, 45045), (⟨21, by decide⟩, -32175), (⟨22, by decide⟩, -51480), (⟨23, by decide⟩, 64350), (⟨35, by decide⟩, -6435), (⟨36, by decide⟩, 10725), (⟨37, by decide⟩, 17160), (⟨43, by decide⟩, 2145), (⟨44, by decide⟩, -10296), (⟨46, by decide⟩, -2574)]
  | 22 => [(⟨21, by decide⟩, 51480), (⟨23, by decide⟩, -34320), (⟨36, by decide⟩, -8580)]
  | 24 => [(⟨22, by decide⟩, 51480), (⟨23, by decide⟩, -42900), (⟨37, by decide⟩, -8580), (⟨44, by decide⟩, 3432)]
  | 25 => [(⟨23, by decide⟩, 60060)]
  | 27 => [(⟨24, by decide⟩, 30030), (⟨25, by decide⟩, -5460), (⟨26, by decide⟩, 1638), (⟨27, by decide⟩, -728), (⟨28, by decide⟩, 455), (⟨29, by decide⟩, -390), (⟨30, by decide⟩, 2184), (⟨31, by decide⟩, -1092), (⟨32, by decide⟩, 728), (⟨33, by decide⟩, -650), (⟨34, by decide⟩, 819), (⟨35, by decide⟩, -780), (⟨36, by decide⟩, 975), (⟨37, by decide⟩, 1040), (⟨38, by decide⟩, -1456), (⟨39, by decide⟩, 1092), (⟨40, by decide⟩, -1040), (⟨41, by decide⟩, 1300), (⟨42, by decide⟩, -1170), (⟨43, by decide⟩, 1560), (⟨44, by decide⟩, -2912), (⟨45, by decide⟩, 1755), (⟨46, by decide⟩, -3276)]
  | 28 => [(⟨25, by decide⟩, 32760), (⟨26, by decide⟩, -9828), (⟨27, by decide⟩, 4368), (⟨28, by decide⟩, -2730), (⟨29, by decide⟩, 2340), (⟨30, by decide⟩, -13104), (⟨31, by decide⟩, 6552), (⟨32, by decide⟩, -4368), (⟨33, by decide⟩, 3900), (⟨34, by decide⟩, -4914), (⟨35, by decide⟩, 4680), (⟨36, by decide⟩, -5850), (⟨37, by decide⟩, -6240), (⟨38, by decide⟩, 8736), (⟨39, by decide⟩, -6552), (⟨40, by decide⟩, 6240), (⟨41, by decide⟩, -7800), (⟨42, by decide⟩, 7020), (⟨43, by decide⟩, -9360), (⟨44, by decide⟩, 17472), (⟨45, by decide⟩, -10530), (⟨46, by decide⟩, 19656)]
  | 29 => [(⟨26, by decide⟩, 36036), (⟨27, by decide⟩, -16016), (⟨28, by decide⟩, 10010), (⟨29, by decide⟩, -8580), (⟨31, by decide⟩, -8008), (⟨32, by decide⟩, 8008), (⟨33, by decide⟩, -8580), (⟨34, by decide⟩, 6006), (⟨35, by decide⟩, -6864), (⟨36, by decide⟩, 10010), (⟨37, by decide⟩, 9152), (⟨39, by decide⟩, 4004), (⟨40, by decide⟩, -6864), (⟨41, by decide⟩, 11440), (⟨42, by decide⟩, -5148), (⟨43, by decide⟩, 9152), (⟨44, by decide⟩, -18304), (⟨45, by decide⟩, 7722), (⟨46, by decide⟩, -17160)]
  | 30 => [(⟨27, by decide⟩, 40040), (⟨28, by decide⟩, -25025), (⟨29, by decide⟩, 21450), (⟨32, by decide⟩, -10010), (⟨33, by decide⟩, 14300), (⟨35, by decide⟩, 4290), (⟨36, by decide⟩, -10725), (⟨37, by decide⟩, -5720), (⟨40, by decide⟩, 5720), (⟨41, by decide⟩, -14300), (⟨43, by decide⟩, -4290), (⟨44, by decide⟩, 9152), (⟨46, by decide⟩, 5148)]
  | 31 => [(⟨28, by decide⟩, 45045), (⟨29, by decide⟩, -38610), (⟨33, by decide⟩, -12870), (⟨36, by decide⟩, 6435), (⟨41, by decide⟩, 8580)]
  | 32 => [(⟨29, by decide⟩, 51480)]
  | 33 => [(⟨30, by decide⟩, 36036), (⟨31, by decide⟩, -12012), (⟨32, by decide⟩, 6006), (⟨33, by decide⟩, -4290), (⟨34, by decide⟩, 9009), (⟨35, by decide⟩, -7722), (⟨36, by decide⟩, 8580), (⟨37, by decide⟩, 10296), (⟨38, by decide⟩, -24024), (⟨39, by decide⟩, 15015), (⟨40, by decide⟩, -12012), (⟨41, by decide⟩, 12870), (⟨42, by decide⟩, -15444), (⟨43, by decide⟩, 18876), (⟨44, by decide⟩, -34320), (⟨45, by decide⟩, 23166), (⟨46, by decide⟩, -41184)]
  | 34 => [(⟨31, by decide⟩, 40040), (⟨32, by decide⟩, -20020), (⟨33, by decide⟩, 14300), (⟨34, by decide⟩, -30030), (⟨35, by decide⟩, 25740), (⟨36, by decide⟩, -28600), (⟨37, by decide⟩, -34320), (⟨39, by decide⟩, -20020), (⟨40, by decide⟩, 22880), (⟨41, by decide⟩, -28600), (⟨42, by decide⟩, 25740), (⟨43, by decide⟩, -37180), (⟨44, by decide⟩, 73216), (⟨45, by decide⟩, -38610), (⟨46, by decide⟩, 75504)]
  | 35 => [(⟨32, by decide⟩, 45045), (⟨33, by decide⟩, -32175), (⟨35, by decide⟩, -19305), (⟨36, by decide⟩, 32175), (⟨37, by decide⟩, 25740), (⟨40, by decide⟩, -25740), (⟨41, by decide⟩, 42900), (⟨43, by decide⟩, 19305), (⟨44, by decide⟩, -41184), (⟨46, by decide⟩, -23166)]
  | 36 => [(⟨33, by decide⟩, 51480), (⟨36, by decide⟩, -25740), (⟨41, by decide⟩, -34320)]
  | 38 => [(⟨34, by decide⟩, 45045), (⟨35, by decide⟩, -25740), (⟨36, by decide⟩, 21450), (⟨37, by decide⟩, 34320), (⟨42, by decide⟩, -12870), (⟨43, by decide⟩, 17160), (⟨44, by decide⟩, -41184), (⟨45, by decide⟩, 19305), (⟨46, by decide⟩, -36036)]
  | 39 => [(⟨35, by decide⟩, 51480), (⟨36, by decide⟩, -42900), (⟨37, by decide⟩, -68640), (⟨43, by decide⟩, -17160), (⟨44, by decide⟩, 54912), (⟨46, by decide⟩, 20592)]
  | 40 => [(⟨36, by decide⟩, 60060)]
  | 41 => [(⟨37, by decide⟩, 60060), (⟨44, by decide⟩, -24024)]
  | 43 => [(⟨38, by decide⟩, 40040), (⟨39, by decide⟩, -15015), (⟨40, by decide⟩, 8580), (⟨41, by decide⟩, -7150), (⟨42, by decide⟩, 12870), (⟨43, by decide⟩, -12870), (⟨44, by decide⟩, 20592), (⟨45, by decide⟩, -19305), (⟨46, by decide⟩, 30888)]
  | 44 => [(⟨39, by decide⟩, 45045), (⟨40, by decide⟩, -25740), (⟨41, by decide⟩, 21450), (⟨42, by decide⟩, -38610), (⟨43, by decide⟩, 38610), (⟨44, by decide⟩, -61776), (⟨45, by decide⟩, 57915), (⟨46, by decide⟩, -92664)]
  | 45 => [(⟨40, by decide⟩, 51480), (⟨41, by decide⟩, -42900), (⟨43, by decide⟩, -25740), (⟨44, by decide⟩, 41184), (⟨46, by decide⟩, 30888)]
  | 46 => [(⟨41, by decide⟩, 60060)]
  | 47 => [(⟨42, by decide⟩, 51480), (⟨43, by decide⟩, -34320), (⟨44, by decide⟩, 54912), (⟨45, by decide⟩, -77220), (⟨46, by decide⟩, 102960)]
  | 48 => [(⟨43, by decide⟩, 60060), (⟨44, by decide⟩, -96096), (⟨46, by decide⟩, -72072)]
  | 50 => [(⟨44, by decide⟩, 72072)]
  | 51 => [(⟨45, by decide⟩, 60060), (⟨46, by decide⟩, -48048)]
  | 52 => [(⟨46, by decide⟩, 72072)]
  | _ => []

def retainedCM_4_15C : Matrix (Fin 47) (Fin 54) ℚ := sparseRatMatrix retainedCM_4_15CS
def retainedCM_4_15U : Matrix (Fin 54) (Fin 7) ℚ := sparseRatScaledMatrix retainedCM_4_15D retainedCM_4_15WS
def retainedCM_4_15L : Matrix (Fin 7) (Fin 54) ℚ := sparseRatMatrix retainedCM_4_15LS
def retainedCM_4_15V : Matrix (Fin 54) (Fin 47) ℚ := sparseRatScaledMatrix retainedCM_4_15D retainedCM_4_15ZS

theorem retainedCM_4_15_sparse_check :
    SparseScaledFrameCheck retainedCM_4_15D retainedCM_4_15CS retainedCM_4_15WS retainedCM_4_15LS retainedCM_4_15ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_15_frame : HasKernelFrame retainedCM_4_15C retainedCM_4_15U retainedCM_4_15L retainedCM_4_15V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_15D≠0) retainedCM_4_15_sparse_check

theorem retainedCM_4_15_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_15C.mulVecLin)=7 :=
  kernelFrame_finrank retainedCM_4_15_frame

/- N=4, degree=16; rows=54, columns=64, nullity=10. -/
def retainedCM_4_16D : ℤ := 720720

def retainedCM_4_16CS : SparseIntMatrix 54 64 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 16), (⟨1, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 15), (⟨2, by decide⟩, 2), (⟨9, by decide⟩, 2)]
  | 2 => [(⟨2, by decide⟩, 14), (⟨3, by decide⟩, 3), (⟨10, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 13), (⟨4, by decide⟩, 4), (⟨11, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 12), (⟨5, by decide⟩, 5), (⟨12, by decide⟩, 1)]
  | 5 => [(⟨5, by decide⟩, 11), (⟨6, by decide⟩, 6), (⟨13, by decide⟩, 1)]
  | 6 => [(⟨6, by decide⟩, 10), (⟨7, by decide⟩, 7), (⟨14, by decide⟩, 1)]
  | 7 => [(⟨7, by decide⟩, 9), (⟨8, by decide⟩, 16), (⟨15, by decide⟩, 1)]
  | 8 => [(⟨9, by decide⟩, 14), (⟨10, by decide⟩, 2), (⟨30, by decide⟩, 3)]
  | 9 => [(⟨10, by decide⟩, 13), (⟨11, by decide⟩, 3), (⟨16, by decide⟩, 4), (⟨31, by decide⟩, 2)]
  | 10 => [(⟨11, by decide⟩, 12), (⟨12, by decide⟩, 4), (⟨17, by decide⟩, 2), (⟨32, by decide⟩, 2)]
  | 11 => [(⟨12, by decide⟩, 11), (⟨13, by decide⟩, 5), (⟨18, by decide⟩, 2), (⟨33, by decide⟩, 2)]
  | 12 => [(⟨13, by decide⟩, 10), (⟨14, by decide⟩, 6), (⟨19, by decide⟩, 2), (⟨34, by decide⟩, 2)]
  | 13 => [(⟨14, by decide⟩, 9), (⟨15, by decide⟩, 7), (⟨20, by decide⟩, 2), (⟨35, by decide⟩, 2)]
  | 14 => [(⟨15, by decide⟩, 8), (⟨21, by decide⟩, 2), (⟨36, by decide⟩, 2)]
  | 15 => [(⟨16, by decide⟩, 12), (⟨17, by decide⟩, 3), (⟨37, by decide⟩, 1)]
  | 16 => [(⟨17, by decide⟩, 11), (⟨18, by decide⟩, 4), (⟨22, by decide⟩, 6), (⟨38, by decide⟩, 1)]
  | 17 => [(⟨18, by decide⟩, 10), (⟨19, by decide⟩, 5), (⟨23, by decide⟩, 3), (⟨39, by decide⟩, 1)]
  | 18 => [(⟨19, by decide⟩, 9), (⟨20, by decide⟩, 6), (⟨24, by decide⟩, 3), (⟨40, by decide⟩, 1)]
  | 19 => [(⟨20, by decide⟩, 8), (⟨21, by decide⟩, 14), (⟨25, by decide⟩, 3), (⟨41, by decide⟩, 1)]
  | 20 => [(⟨22, by decide⟩, 10), (⟨23, by decide⟩, 4), (⟨42, by decide⟩, 1)]
  | 21 => [(⟨23, by decide⟩, 9), (⟨24, by decide⟩, 5), (⟨26, by decide⟩, 8), (⟨43, by decide⟩, 1)]
  | 22 => [(⟨24, by decide⟩, 8), (⟨25, by decide⟩, 6), (⟨27, by decide⟩, 4), (⟨44, by decide⟩, 1)]
  | 23 => [(⟨25, by decide⟩, 7), (⟨28, by decide⟩, 4), (⟨45, by decide⟩, 1)]
  | 24 => [(⟨26, by decide⟩, 8), (⟨27, by decide⟩, 5), (⟨46, by decide⟩, 1)]
  | 25 => [(⟨27, by decide⟩, 7), (⟨28, by decide⟩, 12), (⟨29, by decide⟩, 10), (⟨47, by decide⟩, 1)]
  | 26 => [(⟨29, by decide⟩, 6), (⟨48, by decide⟩, 1)]
  | 27 => [(⟨30, by decide⟩, 13), (⟨31, by decide⟩, 2)]
  | 28 => [(⟨31, by decide⟩, 12), (⟨32, by decide⟩, 3), (⟨37, by decide⟩, 4)]
  | 29 => [(⟨32, by decide⟩, 11), (⟨33, by decide⟩, 4), (⟨38, by decide⟩, 2)]
  | 30 => [(⟨33, by decide⟩, 10), (⟨34, by decide⟩, 5), (⟨39, by decide⟩, 2)]
  | 31 => [(⟨34, by decide⟩, 9), (⟨35, by decide⟩, 6), (⟨40, by decide⟩, 2)]
  | 32 => [(⟨35, by decide⟩, 8), (⟨36, by decide⟩, 14), (⟨41, by decide⟩, 2)]
  | 33 => [(⟨37, by decide⟩, 11), (⟨38, by decide⟩, 3), (⟨49, by decide⟩, 6)]
  | 34 => [(⟨38, by decide⟩, 10), (⟨39, by decide⟩, 4), (⟨42, by decide⟩, 6), (⟨50, by decide⟩, 4)]
  | 35 => [(⟨39, by decide⟩, 9), (⟨40, by decide⟩, 5), (⟨43, by decide⟩, 3), (⟨51, by decide⟩, 4)]
  | 36 => [(⟨40, by decide⟩, 8), (⟨41, by decide⟩, 6), (⟨44, by decide⟩, 3), (⟨52, by decide⟩, 4)]
  | 37 => [(⟨41, by decide⟩, 7), (⟨45, by decide⟩, 3), (⟨53, by decide⟩, 4)]
  | 38 => [(⟨42, by decide⟩, 9), (⟨43, by decide⟩, 4), (⟨54, by decide⟩, 2)]
  | 39 => [(⟨43, by decide⟩, 8), (⟨44, by decide⟩, 5), (⟨46, by decide⟩, 8), (⟨55, by decide⟩, 2)]
  | 40 => [(⟨44, by decide⟩, 7), (⟨45, by decide⟩, 12), (⟨47, by decide⟩, 4), (⟨56, by decide⟩, 2)]
  | 41 => [(⟨46, by decide⟩, 7), (⟨47, by decide⟩, 5), (⟨57, by decide⟩, 2)]
  | 42 => [(⟨47, by decide⟩, 6), (⟨48, by decide⟩, 15), (⟨58, by decide⟩, 2)]
  | 43 => [(⟨49, by decide⟩, 10), (⟨50, by decide⟩, 3)]
  | 44 => [(⟨50, by decide⟩, 9), (⟨51, by decide⟩, 4), (⟨54, by decide⟩, 6)]
  | 45 => [(⟨51, by decide⟩, 8), (⟨52, by decide⟩, 5), (⟨55, by decide⟩, 3)]
  | 46 => [(⟨52, by decide⟩, 7), (⟨53, by decide⟩, 12), (⟨56, by decide⟩, 3)]
  | 47 => [(⟨54, by decide⟩, 8), (⟨55, by decide⟩, 4), (⟨59, by decide⟩, 9)]
  | 48 => [(⟨55, by decide⟩, 7), (⟨56, by decide⟩, 5), (⟨57, by decide⟩, 8), (⟨60, by decide⟩, 6)]
  | 49 => [(⟨56, by decide⟩, 6), (⟨58, by decide⟩, 4), (⟨61, by decide⟩, 6)]
  | 50 => [(⟨57, by decide⟩, 6), (⟨58, by decide⟩, 10), (⟨62, by decide⟩, 3)]
  | 51 => [(⟨59, by decide⟩, 7), (⟨60, by decide⟩, 4)]
  | 52 => [(⟨60, by decide⟩, 6), (⟨61, by decide⟩, 10), (⟨62, by decide⟩, 8)]
  | 53 => [(⟨62, by decide⟩, 5), (⟨63, by decide⟩, 16)]
  | _ => []

def retainedCM_4_16WS : SparseIntMatrix 64 10 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 112), (⟨1, by decide⟩, -112), (⟨2, by decide⟩, 144), (⟨3, by decide⟩, -112), (⟨4, by decide⟩, 144), (⟨5, by decide⟩, -240), (⟨6, by decide⟩, 144), (⟨7, by decide⟩, -240), (⟨8, by decide⟩, -240), (⟨9, by decide⟩, 528)]
  | 1 => [(⟨0, by decide⟩, -1792), (⟨1, by decide⟩, 1792), (⟨2, by decide⟩, -2304), (⟨3, by decide⟩, 1792), (⟨4, by decide⟩, -2304), (⟨5, by decide⟩, 3840), (⟨6, by decide⟩, -2304), (⟨7, by decide⟩, 3840), (⟨8, by decide⟩, 3840), (⟨9, by decide⟩, -8448)]
  | 2 => [(⟨0, by decide⟩, 13440), (⟨1, by decide⟩, -7980), (⟨2, by decide⟩, 7920), (⟨3, by decide⟩, -7560), (⟨4, by decide⟩, 6660), (⟨5, by decide⟩, -10400), (⟨6, by decide⟩, 6240), (⟨7, by decide⟩, -8720), (⟨8, by decide⟩, -8160), (⟨9, by decide⟩, 17280)]
  | 3 => [(⟨0, by decide⟩, -62720), (⟨1, by decide⟩, 24500), (⟨2, by decide⟩, -15120), (⟨3, by decide⟩, 24500), (⟨4, by decide⟩, -12780), (⟨5, by decide⟩, 16100), (⟨6, by decide⟩, -12000), (⟨7, by decide⟩, 10640), (⟨8, by decide⟩, 8820), (⟨9, by decide⟩, -16128)]
  | 4 => [(⟨0, by decide⟩, 203840), (⟨1, by decide⟩, -50960), (⟨2, by decide⟩, 17160), (⟨3, by decide⟩, -50960), (⟨4, by decide⟩, 15600), (⟨5, by decide⟩, -13000), (⟨6, by decide⟩, 15600), (⟨7, by decide⟩, -6760), (⟨8, by decide⟩, -5200), (⟨9, by decide⟩, 5824)]
  | 5 => [(⟨0, by decide⟩, -489216), (⟨1, by decide⟩, 68796), (⟨2, by decide⟩, -11232), (⟨3, by decide⟩, 68796), (⟨4, by decide⟩, -11232), (⟨5, by decide⟩, 4420), (⟨6, by decide⟩, -11232), (⟨7, by decide⟩, 1560), (⟨8, by decide⟩, 1560)]
  | 6 => [(⟨0, by decide⟩, 896896), (⟨1, by decide⟩, -56056), (⟨2, by decide⟩, 3432), (⟨3, by decide⟩, -56056), (⟨4, by decide⟩, 3432), (⟨6, by decide⟩, 3432)]
  | 7 => [(⟨0, by decide⟩, -1281280), (⟨1, by decide⟩, 20020), (⟨3, by decide⟩, 20020)]
  | 8 => [(⟨0, by decide⟩, 720720)]
  | 9 => [(⟨1, by decide⟩, -5460), (⟨2, by decide⟩, 9360), (⟨3, by decide⟩, -5880), (⟨4, by decide⟩, 10620), (⟨5, by decide⟩, -18400), (⟨6, by decide⟩, 11040), (⟨7, by decide⟩, -20080), (⟨8, by decide⟩, -20640), (⟨9, by decide⟩, 46080)]
  | 10 => [(⟨1, by decide⟩, 38220), (⟨2, by decide⟩, -65520), (⟨3, by decide⟩, 32340), (⟨4, by decide⟩, -54900), (⟨5, by decide⟩, 97300), (⟨6, by decide⟩, -51360), (⟨7, by decide⟩, 90160), (⟨8, by decide⟩, 87780), (⟨9, by decide⟩, -193536)]
  | 11 => [(⟨1, by decide⟩, -114660), (⟨2, by decide⟩, 127920), (⟨3, by decide⟩, -114660), (⟨4, by decide⟩, 103740), (⟨5, by decide⟩, -157300), (⟨6, by decide⟩, 93600), (⟨7, by decide⟩, -111280), (⟨8, by decide⟩, -93860), (⟨9, by decide⟩, 186368)]
  | 12 => [(⟨1, by decide⟩, 267540), (⟨2, by decide⟩, -149760), (⟨3, by decide⟩, 267540), (⟨4, by decide⟩, -131040), (⟨5, by decide⟩, 133900), (⟨6, by decide⟩, -131040), (⟨7, by decide⟩, 73320), (⟨8, by decide⟩, 54600), (⟨9, by decide⟩, -69888)]
  | 13 => [(⟨1, by decide⟩, -420420), (⟨2, by decide⟩, 102960), (⟨3, by decide⟩, -420420), (⟨4, by decide⟩, 102960), (⟨5, by decide⟩, -48620), (⟨6, by decide⟩, 102960), (⟨7, by decide⟩, -17160), (⟨8, by decide⟩, -17160)]
  | 14 => [(⟨1, by decide⟩, 420420), (⟨2, by decide⟩, -34320), (⟨3, by decide⟩, 420420), (⟨4, by decide⟩, -34320), (⟨6, by decide⟩, -34320)]
  | 15 => [(⟨1, by decide⟩, -180180), (⟨3, by decide⟩, -180180)]
  | 16 => [(⟨1, by decide⟩, -38220), (⟨2, by decide⟩, 117000), (⟨4, by decide⟩, 58500), (⟨5, by decide⟩, -130000), (⟨6, by decide⟩, 40560), (⟨7, by decide⟩, -100360), (⟨8, by decide⟩, -92040), (⟨9, by decide⟩, 209664)]
  | 17 => [(⟨1, by decide⟩, 152880), (⟨2, by decide⟩, -468000), (⟨4, by decide⟩, -191880), (⟨5, by decide⟩, 442000), (⟨6, by decide⟩, -99840), (⟨7, by decide⟩, 250640), (⟨8, by decide⟩, 188760), (⟨9, by decide⟩, -419328)]
  | 18 => [(⟨1, by decide⟩, -420420), (⟨2, by decide⟩, 566280), (⟨4, by decide⟩, 231660), (⟨5, by decide⟩, -400400), (⟨6, by decide⟩, 154440), (⟨7, by decide⟩, -171600), (⟨8, by decide⟩, -102960), (⟨9, by decide⟩, 164736)]
  | 19 => [(⟨1, by decide⟩, 840840), (⟨2, by decide⟩, -411840), (⟨4, by decide⟩, -205920), (⟨5, by decide⟩, 157300), (⟨6, by decide⟩, -137280), (⟨7, by decide⟩, 40040), (⟨8, by decide⟩, 34320)]
  | 20 => [(⟨1, by decide⟩, -1261260), (⟨2, by decide⟩, 154440), (⟨4, by decide⟩, 77220), (⟨6, by decide⟩, 51480)]
  | 21 => [(⟨1, by decide⟩, 720720)]
  | 22 => [(⟨2, by decide⟩, 480480), (⟨4, by decide⟩, 120120), (⟨5, by decide⟩, -400400), (⟨7, by decide⟩, -160160), (⟨8, by decide⟩, -85800), (⟨9, by decide⟩, 219648)]
  | 23 => [(⟨2, by decide⟩, -1201200), (⟨4, by decide⟩, -214500), (⟨5, by decide⟩, 786500), (⟨7, by decide⟩, 228800), (⟨8, by decide⟩, 71500), (⟨9, by decide⟩, -183040)]
  | 24 => [(⟨2, by decide⟩, 926640), (⟨4, by decide⟩, 231660), (⟨5, by decide⟩, -343200), (⟨7, by decide⟩, -51480), (⟨8, by decide⟩, -25740)]
  | 25 => [(⟨2, by decide⟩, -411840), (⟨4, by decide⟩, -102960)]
  | 26 => [(⟨2, by decide⟩, 772200), (⟨5, by decide⟩, -429000), (⟨7, by decide⟩, -85800), (⟨9, by decide⟩, 41184)]
  | 27 => [(⟨2, by decide⟩, -1235520), (⟨5, by decide⟩, 429000), (⟨7, by decide⟩, 34320)]
  | 28 => [(⟨2, by decide⟩, 720720)]
  | 29 => [(⟨5, by decide⟩, -120120)]
  | 30 => [(⟨3, by decide⟩, 5880), (⟨4, by decide⟩, -12960), (⟨5, by decide⟩, 21000), (⟨6, by decide⟩, -17280), (⟨7, by decide⟩, 33600), (⟨8, by decide⟩, 37800), (⟨9, by decide⟩, -86016)]
  | 31 => [(⟨3, by decide⟩, -38220), (⟨4, by decide⟩, 84240), (⟨5, by decide⟩, -136500), (⟨6, by decide⟩, 112320), (⟨7, by decide⟩, -218400), (⟨8, by decide⟩, -245700), (⟨9, by decide⟩, 559104)]
  | 32 => [(⟨3, by decide⟩, 152880), (⟨4, by decide⟩, -168480), (⟨5, by decide⟩, 234000), (⟨6, by decide⟩, -199680), (⟨7, by decide⟩, 270400), (⟨8, by decide⟩, 265200), (⟨9, by decide⟩, -559104)]
  | 33 => [(⟨3, by decide⟩, -420420), (⟨4, by decide⟩, 231660), (⟨5, by decide⟩, -214500), (⟨6, by decide⟩, 308880), (⟨7, by decide⟩, -188760), (⟨8, by decide⟩, -154440), (⟨9, by decide⟩, 219648)]
  | 34 => [(⟨3, by decide⟩, 840840), (⟨4, by decide⟩, -205920), (⟨5, by decide⟩, 85800), (⟨6, by decide⟩, -274560), (⟨7, by decide⟩, 45760), (⟨8, by decide⟩, 51480)]
  | 35 => [(⟨3, by decide⟩, -1261260), (⟨4, by decide⟩, 77220), (⟨6, by decide⟩, 102960)]
  | 36 => [(⟨3, by decide⟩, 720720)]
  | 37 => [(⟨4, by decide⟩, -126360), (⟨5, by decide⟩, 234000), (⟨6, by decide⟩, -187200), (⟨7, by decide⟩, 452400), (⟨8, by decide⟩, 538200), (⟨9, by decide⟩, -1257984)]
  | 38 => [(⟨4, by decide⟩, 463320), (⟨5, by decide⟩, -858000), (⟨6, by decide⟩, 480480), (⟨7, by decide⟩, -1109680), (⟨8, by decide⟩, -1149720), (⟨9, by decide⟩, 2635776)]
  | 39 => [(⟨4, by decide⟩, -643500), (⟨5, by decide⟩, 858000), (⟨6, by decide⟩, -858000), (⟨7, by decide⟩, 829400), (⟨8, by decide⟩, 643500), (⟨9, by decide⟩, -1098240)]
  | 40 => [(⟨4, by decide⟩, 694980), (⟨5, by decide⟩, -386100), (⟨6, by decide⟩, 926640), (⟨7, by decide⟩, -205920), (⟨8, by decide⟩, -231660)]
  | 41 => [(⟨4, by decide⟩, -308880), (⟨6, by decide⟩, -411840)]
  | 42 => [(⟨4, by decide⟩, -343200), (⟨5, by decide⟩, 858000), (⟨7, by decide⟩, 686400), (⟨8, by decide⟩, 572000), (⟨9, by decide⟩, -1464320)]
  | 43 => [(⟨4, by decide⟩, 772200), (⟨5, by decide⟩, -1930500), (⟨7, by decide⟩, -1115400), (⟨8, by decide⟩, -514800), (⟨9, by decide⟩, 1317888)]
  | 44 => [(⟨4, by decide⟩, -1235520), (⟨5, by decide⟩, 1029600), (⟨7, by decide⟩, 274560), (⟨8, by decide⟩, 205920)]
  | 45 => [(⟨4, by decide⟩, 720720)]
  | 46 => [(⟨5, by decide⟩, 1287000), (⟨7, by decide⟩, 514800), (⟨9, by decide⟩, -329472)]
  | 47 => [(⟨5, by decide⟩, -1801800), (⟨7, by decide⟩, -240240)]
  | 48 => [(⟨5, by decide⟩, 720720)]
  | 49 => [(⟨6, by decide⟩, 102960), (⟨7, by decide⟩, -274560), (⟨8, by decide⟩, -411840), (⟨9, by decide⟩, 988416)]
  | 50 => [(⟨6, by decide⟩, -343200), (⟨7, by decide⟩, 915200), (⟨8, by decide⟩, 1372800), (⟨9, by decide⟩, -3294720)]
  | 51 => [(⟨6, by decide⟩, 772200), (⟨7, by decide⟩, -772200), (⟨8, by decide⟩, -772200), (⟨9, by decide⟩, 1482624)]
  | 52 => [(⟨6, by decide⟩, -1235520), (⟨7, by decide⟩, 205920), (⟨8, by decide⟩, 308880)]
  | 53 => [(⟨6, by decide⟩, 720720)]
  | 54 => [(⟨7, by decide⟩, -858000), (⟨8, by decide⟩, -1544400), (⟨9, by decide⟩, 3953664)]
  | 55 => [(⟨7, by decide⟩, 1716000), (⟨8, by decide⟩, 1544400), (⟨9, by decide⟩, -3953664)]
  | 56 => [(⟨7, by decide⟩, -480480), (⟨8, by decide⟩, -720720)]
  | 57 => [(⟨7, by decide⟩, -1201200), (⟨9, by decide⟩, 1153152)]
  | 58 => [(⟨7, by decide⟩, 720720)]
  | 59 => [(⟨8, by decide⟩, 686400), (⟨9, by decide⟩, -1757184)]
  | 60 => [(⟨8, by decide⟩, -1201200), (⟨9, by decide⟩, 3075072)]
  | 61 => [(⟨8, by decide⟩, 720720)]
  | 62 => [(⟨9, by decide⟩, -2306304)]
  | 63 => [(⟨9, by decide⟩, 720720)]
  | _ => []

def retainedCM_4_16LS : SparseIntMatrix 10 64 := fun i =>
  match i.val with
  | 0 => [(⟨8, by decide⟩, 1)]
  | 1 => [(⟨21, by decide⟩, 1)]
  | 2 => [(⟨28, by decide⟩, 1)]
  | 3 => [(⟨36, by decide⟩, 1)]
  | 4 => [(⟨45, by decide⟩, 1)]
  | 5 => [(⟨48, by decide⟩, 1)]
  | 6 => [(⟨53, by decide⟩, 1)]
  | 7 => [(⟨58, by decide⟩, 1)]
  | 8 => [(⟨61, by decide⟩, 1)]
  | 9 => [(⟨63, by decide⟩, 1)]
  | _ => []

def retainedCM_4_16ZS : SparseIntMatrix 64 54 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 45045), (⟨1, by decide⟩, -3003), (⟨2, by decide⟩, 429), (⟨3, by decide⟩, -99), (⟨4, by decide⟩, 33), (⟨5, by decide⟩, -15), (⟨6, by decide⟩, 9), (⟨7, by decide⟩, -7), (⟨8, by decide⟩, 429), (⟨9, by decide⟩, -99), (⟨10, by decide⟩, 33), (⟨11, by decide⟩, -15), (⟨12, by decide⟩, 9), (⟨13, by decide⟩, -7), (⟨14, by decide⟩, 7), (⟨15, by decide⟩, 33), (⟨16, by decide⟩, -15), (⟨17, by decide⟩, 9), (⟨18, by decide⟩, -7), (⟨19, by decide⟩, 7), (⟨20, by decide⟩, 9), (⟨21, by decide⟩, -7), (⟨22, by decide⟩, 7), (⟨23, by decide⟩, -9), (⟨24, by decide⟩, 7), (⟨25, by decide⟩, -9), (⟨26, by decide⟩, 15), (⟨27, by decide⟩, -99), (⟨28, by decide⟩, 33), (⟨29, by decide⟩, -15), (⟨30, by decide⟩, 9), (⟨31, by decide⟩, -7), (⟨32, by decide⟩, 7), (⟨33, by decide⟩, -15), (⟨34, by decide⟩, 9), (⟨35, by decide⟩, -7), (⟨36, by decide⟩, 7), (⟨37, by decide⟩, -9), (⟨38, by decide⟩, -7), (⟨39, by decide⟩, 7), (⟨40, by decide⟩, -9), (⟨41, by decide⟩, -9), (⟨42, by decide⟩, 15), (⟨43, by decide⟩, 9), (⟨44, by decide⟩, -7), (⟨45, by decide⟩, 7), (⟨46, by decide⟩, -9), (⟨47, by decide⟩, 7), (⟨48, by decide⟩, -9), (⟨49, by decide⟩, 15), (⟨50, by decide⟩, 15), (⟨51, by decide⟩, -9), (⟨52, by decide⟩, 15), (⟨53, by decide⟩, -33)]
  | 1 => [(⟨1, by decide⟩, 48048), (⟨2, by decide⟩, -6864), (⟨3, by decide⟩, 1584), (⟨4, by decide⟩, -528), (⟨5, by decide⟩, 240), (⟨6, by decide⟩, -144), (⟨7, by decide⟩, 112), (⟨8, by decide⟩, -6864), (⟨9, by decide⟩, 1584), (⟨10, by decide⟩, -528), (⟨11, by decide⟩, 240), (⟨12, by decide⟩, -144), (⟨13, by decide⟩, 112), (⟨14, by decide⟩, -112), (⟨15, by decide⟩, -528), (⟨16, by decide⟩, 240), (⟨17, by decide⟩, -144), (⟨18, by decide⟩, 112), (⟨19, by decide⟩, -112), (⟨20, by decide⟩, -144), (⟨21, by decide⟩, 112), (⟨22, by decide⟩, -112), (⟨23, by decide⟩, 144), (⟨24, by decide⟩, -112), (⟨25, by decide⟩, 144), (⟨26, by decide⟩, -240), (⟨27, by decide⟩, 1584), (⟨28, by decide⟩, -528), (⟨29, by decide⟩, 240), (⟨30, by decide⟩, -144), (⟨31, by decide⟩, 112), (⟨32, by decide⟩, -112), (⟨33, by decide⟩, 240), (⟨34, by decide⟩, -144), (⟨35, by decide⟩, 112), (⟨36, by decide⟩, -112), (⟨37, by decide⟩, 144), (⟨38, by decide⟩, 112), (⟨39, by decide⟩, -112), (⟨40, by decide⟩, 144), (⟨41, by decide⟩, 144), (⟨42, by decide⟩, -240), (⟨43, by decide⟩, -144), (⟨44, by decide⟩, 112), (⟨45, by decide⟩, -112), (⟨46, by decide⟩, 144), (⟨47, by decide⟩, -112), (⟨48, by decide⟩, 144), (⟨49, by decide⟩, -240), (⟨50, by decide⟩, -240), (⟨51, by decide⟩, 144), (⟨52, by decide⟩, -240), (⟨53, by decide⟩, 528)]
  | 2 => [(⟨2, by decide⟩, 51480), (⟨3, by decide⟩, -11880), (⟨4, by decide⟩, 3960), (⟨5, by decide⟩, -1800), (⟨6, by decide⟩, 1080), (⟨7, by decide⟩, -840), (⟨9, by decide⟩, -3960), (⟨10, by decide⟩, 1980), (⟨11, by decide⟩, -1080), (⟨12, by decide⟩, 720), (⟨13, by decide⟩, -600), (⟨14, by decide⟩, 630), (⟨15, by decide⟩, 1320), (⟨16, by decide⟩, -720), (⟨17, by decide⟩, 504), (⟨18, by decide⟩, -440), (⟨19, by decide⟩, 480), (⟨20, by decide⟩, 432), (⟨21, by decide⟩, -360), (⟨22, by decide⟩, 390), (⟨23, by decide⟩, -540), (⟨24, by decide⟩, 360), (⟨25, by decide⟩, -480), (⟨26, by decide⟩, 800), (⟨28, by decide⟩, 660), (⟨29, by decide⟩, -540), (⟨30, by decide⟩, 432), (⟨31, by decide⟩, -400), (⟨32, by decide⟩, 450), (⟨33, by decide⟩, -360), (⟨34, by decide⟩, 288), (⟨35, by decide⟩, -280), (⟨36, by decide⟩, 330), (⟨37, by decide⟩, -480), (⟨38, by decide⟩, -240), (⟨39, by decide⟩, 270), (⟨40, by decide⟩, -390), (⟨41, by decide⟩, -360), (⟨42, by decide⟩, 640), (⟨43, by decide⟩, 216), (⟨44, by decide⟩, -200), (⟨45, by decide⟩, 240), (⟨46, by decide⟩, -360), (⟨47, by decide⟩, 210), (⟨48, by decide⟩, -300), (⟨49, by decide⟩, 560), (⟨50, by decide⟩, 520), (⟨51, by decide⟩, -270), (⟨52, by decide⟩, 480), (⟨53, by decide⟩, -1080)]
  | 3 => [(⟨3, by decide⟩, 55440), (⟨4, by decide⟩, -18480), (⟨5, by decide⟩, 8400), (⟨6, by decide⟩, -5040), (⟨7, by decide⟩, 3920), (⟨10, by decide⟩, -4620), (⟨11, by decide⟩, 3360), (⟨12, by decide⟩, -2520), (⟨13, by decide⟩, 2240), (⟨14, by decide⟩, -2450), (⟨16, by decide⟩, 840), (⟨17, by decide⟩, -1008), (⟨18, by decide⟩, 1120), (⟨19, by decide⟩, -1400), (⟨20, by decide⟩, -504), (⟨21, by decide⟩, 560), (⟨22, by decide⟩, -770), (⟨23, by decide⟩, 1260), (⟨24, by decide⟩, -560), (⟨25, by decide⟩, 840), (⟨26, by decide⟩, -1400), (⟨29, by decide⟩, 840), (⟨30, by decide⟩, -1008), (⟨31, by decide⟩, 1120), (⟨32, by decide⟩, -1400), (⟨34, by decide⟩, -252), (⟨35, by decide⟩, 448), (⟨36, by decide⟩, -700), (⟨37, by decide⟩, 1200), (⟨38, by decide⟩, 224), (⟨39, by decide⟩, -350), (⟨40, by decide⟩, 660), (⟨41, by decide⟩, 480), (⟨42, by decide⟩, -980), (⟨44, by decide⟩, 112), (⟨45, by decide⟩, -280), (⟨46, by decide⟩, 600), (⟨47, by decide⟩, -140), (⟨48, by decide⟩, 300), (⟨49, by decide⟩, -770), (⟨50, by decide⟩, -560), (⟨51, by decide⟩, 180), (⟨52, by decide⟩, -420), (⟨53, by decide⟩, 1008)]
  | 4 => [(⟨4, by decide⟩, 60060), (⟨5, by decide⟩, -27300), (⟨6, by decide⟩, 16380), (⟨7, by decide⟩, -12740), (⟨11, by decide⟩, -5460), (⟨12, by decide⟩, 5460), (⟨13, by decide⟩, -5460), (⟨14, by decide⟩, 6370), (⟨17, by decide⟩, 1092), (⟨18, by decide⟩, -1820), (⟨19, by decide⟩, 2730), (⟨21, by decide⟩, -364), (⟨22, by decide⟩, 910), (⟨23, by decide⟩, -1950), (⟨24, by decide⟩, 364), (⟨25, by decide⟩, -780), (⟨26, by decide⟩, 1300), (⟨30, by decide⟩, 1092), (⟨31, by decide⟩, -1820), (⟨32, by decide⟩, 2730), (⟨35, by decide⟩, -364), (⟨36, by decide⟩, 910), (⟨37, by decide⟩, -1950), (⟨39, by decide⟩, 182), (⟨40, by decide⟩, -650), (⟨41, by decide⟩, -260), (⟨42, by decide⟩, 780), (⟨45, by decide⟩, 182), (⟨46, by decide⟩, -650), (⟨48, by decide⟩, -130), (⟨49, by decide⟩, 650), (⟨50, by decide⟩, 260), (⟨52, by decide⟩, 130), (⟨53, by decide⟩, -364)]
  | 5 => [(⟨5, by decide⟩, 65520), (⟨6, by decide⟩, -39312), (⟨7, by decide⟩, 30576), (⟨12, by decide⟩, -6552), (⟨13, by decide⟩, 8736), (⟨14, by decide⟩, -11466), (⟨18, by decide⟩, 1456), (⟨19, by decide⟩, -3276), (⟨22, by decide⟩, -546), (⟨23, by decide⟩, 1872), (⟨25, by decide⟩, 312), (⟨26, by decide⟩, -520), (⟨31, by decide⟩, 1456), (⟨32, by decide⟩, -3276), (⟨36, by decide⟩, -546), (⟨37, by decide⟩, 1872), (⟨40, by decide⟩, 312), (⟨42, by decide⟩, -260), (⟨46, by decide⟩, 312), (⟨49, by decide⟩, -260)]
  | 6 => [(⟨6, by decide⟩, 72072), (⟨7, by decide⟩, -56056), (⟨13, by decide⟩, -8008), (⟨14, by decide⟩, 14014), (⟨19, by decide⟩, 2002), (⟨23, by decide⟩, -858), (⟨32, by decide⟩, 2002), (⟨37, by decide⟩, -858)]
  | 7 => [(⟨7, by decide⟩, 80080), (⟨14, by decide⟩, -10010)]
  | 9 => [(⟨8, by decide⟩, 51480), (⟨9, by decide⟩, -7920), (⟨10, by decide⟩, 1980), (⟨11, by decide⟩, -720), (⟨12, by decide⟩, 360), (⟨13, by decide⟩, -240), (⟨14, by decide⟩, 210), (⟨15, by decide⟩, 2640), (⟨16, by decide⟩, -1080), (⟨17, by decide⟩, 576), (⟨18, by decide⟩, -400), (⟨19, by decide⟩, 360), (⟨20, by decide⟩, 648), (⟨21, by decide⟩, -480), (⟨22, by decide⟩, 450), (⟨23, by decide⟩, -540), (⟨24, by decide⟩, 480), (⟨25, by decide⟩, -600), (⟨26, by decide⟩, 1000), (⟨27, by decide⟩, -11880), (⟨28, by decide⟩, 3300), (⟨29, by decide⟩, -1260), (⟨30, by decide⟩, 648), (⟨31, by decide⟩, -440), (⟨32, by decide⟩, 390), (⟨33, by decide⟩, -1440), (⟨34, by decide⟩, 792), (⟨35, by decide⟩, -560), (⟨36, by decide⟩, 510), (⟨37, by decide⟩, -600), (⟨38, by decide⟩, -600), (⟨39, by decide⟩, 570), (⟨40, by decide⟩, -690), (⟨41, by decide⟩, -720), (⟨42, by decide⟩, 1160), (⟨43, by decide⟩, 864), (⟨44, by decide⟩, -640), (⟨45, by decide⟩, 600), (⟨46, by decide⟩, -720), (⟨47, by decide⟩, 630), (⟨48, by decide⟩, -780), (⟨49, by decide⟩, 1240), (⟨50, by decide⟩, 1280), (⟨51, by decide⟩, -810), (⟨52, by decide⟩, 1320), (⟨53, by decide⟩, -2880)]
  | 10 => [(⟨9, by decide⟩, 55440), (⟨10, by decide⟩, -13860), (⟨11, by decide⟩, 5040), (⟨12, by decide⟩, -2520), (⟨13, by decide⟩, 1680), (⟨14, by decide⟩, -1470), (⟨15, by decide⟩, -18480), (⟨16, by decide⟩, 7560), (⟨17, by decide⟩, -4032), (⟨18, by decide⟩, 2800), (⟨19, by decide⟩, -2520), (⟨20, by decide⟩, -4536), (⟨21, by decide⟩, 3360), (⟨22, by decide⟩, -3150), (⟨23, by decide⟩, 3780), (⟨24, by decide⟩, -3360), (⟨25, by decide⟩, 4200), (⟨26, by decide⟩, -7000), (⟨28, by decide⟩, -9240), (⟨29, by decide⟩, 5040), (⟨30, by decide⟩, -3024), (⟨31, by decide⟩, 2240), (⟨32, by decide⟩, -2100), (⟨33, by decide⟩, 5040), (⟨34, by decide⟩, -3276), (⟨35, by decide⟩, 2576), (⟨36, by decide⟩, -2520), (⟨37, by decide⟩, 3120), (⟨38, by decide⟩, 2688), (⟨39, by decide⟩, -2730), (⟨40, by decide⟩, 3480), (⟨41, by decide⟩, 3600), (⟨42, by decide⟩, -6020), (⟨43, by decide⟩, -3024), (⟨44, by decide⟩, 2464), (⟨45, by decide⟩, -2520), (⟨46, by decide⟩, 3240), (⟨47, by decide⟩, -2520), (⟨48, by decide⟩, 3300), (⟨49, by decide⟩, -5530), (⟨50, by decide⟩, -5600), (⟨51, by decide⟩, 3240), (⟨52, by decide⟩, -5460), (⟨53, by decide⟩, 12096)]
  | 11 => [(⟨10, by decide⟩, 60060), (⟨11, by decide⟩, -21840), (⟨12, by decide⟩, 10920), (⟨13, by decide⟩, -7280), (⟨14, by decide⟩, 6370), (⟨16, by decide⟩, -10920), (⟨17, by decide⟩, 8736), (⟨18, by decide⟩, -7280), (⟨19, by decide⟩, 7280), (⟨20, by decide⟩, 6552), (⟨21, by decide⟩, -5824), (⟨22, by decide⟩, 6370), (⟨23, by decide⟩, -8580), (⟨24, by decide⟩, 5824), (⟨25, by decide⟩, -7800), (⟨26, by decide⟩, 13000), (⟨29, by decide⟩, -10920), (⟨30, by decide⟩, 8736), (⟨31, by decide⟩, -7280), (⟨32, by decide⟩, 7280), (⟨34, by decide⟩, 3276), (⟨35, by decide⟩, -4368), (⟨36, by decide⟩, 5460), (⟨37, by decide⟩, -7800), (⟨38, by decide⟩, -2912), (⟨39, by decide⟩, 3822), (⟨40, by decide⟩, -5980), (⟨41, by decide⟩, -5200), (⟨42, by decide⟩, 9620), (⟨44, by decide⟩, -1456), (⟨45, by decide⟩, 2912), (⟨46, by decide⟩, -5200), (⟨47, by decide⟩, 1820), (⟨48, by decide⟩, -3380), (⟨49, by decide⟩, 7410), (⟨50, by decide⟩, 6240), (⟨51, by decide⟩, -2340), (⟨52, by decide⟩, 4940), (⟨53, by decide⟩, -11648)]
  | 12 => [(⟨11, by decide⟩, 65520), (⟨12, by decide⟩, -32760), (⟨13, by decide⟩, 21840), (⟨14, by decide⟩, -19110), (⟨17, by decide⟩, -13104), (⟨18, by decide⟩, 14560), (⟨19, by decide⟩, -16380), (⟨21, by decide⟩, 4368), (⟨22, by decide⟩, -8190), (⟨23, by decide⟩, 14040), (⟨24, by decide⟩, -4368), (⟨25, by decide⟩, 7800), (⟨26, by decide⟩, -13000), (⟨30, by decide⟩, -13104), (⟨31, by decide⟩, 14560), (⟨32, by decide⟩, -16380), (⟨35, by decide⟩, 4368), (⟨36, by decide⟩, -8190), (⟨37, by decide⟩, 14040), (⟨39, by decide⟩, -2184), (⟨40, by decide⟩, 6240), (⟨41, by decide⟩, 3120), (⟨42, by decide⟩, -8060), (⟨45, by decide⟩, -2184), (⟨46, by decide⟩, 6240), (⟨48, by decide⟩, 1560), (⟨49, by decide⟩, -6500), (⟨50, by decide⟩, -3120), (⟨52, by decide⟩, -1560), (⟨53, by decide⟩, 4368)]
  | 13 => [(⟨12, by decide⟩, 72072), (⟨13, by decide⟩, -48048), (⟨14, by decide⟩, 42042), (⟨18, by decide⟩, -16016), (⟨19, by decide⟩, 24024), (⟨22, by decide⟩, 6006), (⟨23, by decide⟩, -15444), (⟨25, by decide⟩, -3432), (⟨26, by decide⟩, 5720), (⟨31, by decide⟩, -16016), (⟨32, by decide⟩, 24024), (⟨36, by decide⟩, 6006), (⟨37, by decide⟩, -15444), (⟨40, by decide⟩, -3432), (⟨42, by decide⟩, 2860), (⟨46, by decide⟩, -3432), (⟨49, by decide⟩, 2860)]
  | 14 => [(⟨13, by decide⟩, 80080), (⟨14, by decide⟩, -70070), (⟨19, by decide⟩, -20020), (⟨23, by decide⟩, 8580), (⟨32, by decide⟩, -20020), (⟨37, by decide⟩, 8580)]
  | 15 => [(⟨14, by decide⟩, 90090)]
  | 16 => [(⟨15, by decide⟩, 60060), (⟨16, by decide⟩, -16380), (⟨17, by decide⟩, 6552), (⟨18, by decide⟩, -3640), (⟨19, by decide⟩, 2730), (⟨20, by decide⟩, 9828), (⟨21, by decide⟩, -6552), (⟨22, by decide⟩, 5460), (⟨23, by decide⟩, -5850), (⟨24, by decide⟩, 6552), (⟨25, by decide⟩, -7800), (⟨26, by decide⟩, 13000), (⟨33, by decide⟩, -5460), (⟨34, by decide⟩, 3276), (⟨35, by decide⟩, -2184), (⟨36, by decide⟩, 1820), (⟨37, by decide⟩, -1950), (⟨38, by decide⟩, -3276), (⟨39, by decide⟩, 3276), (⟨40, by decide⟩, -3900), (⟨41, by decide⟩, -4680), (⟨42, by decide⟩, 7800), (⟨43, by decide⟩, 3276), (⟨44, by decide⟩, -2548), (⟨45, by decide⟩, 2366), (⟨46, by decide⟩, -2730), (⟨47, by decide⟩, 2730), (⟨48, by decide⟩, -3510), (⟨49, by decide⟩, 5590), (⟨50, by decide⟩, 6240), (⟨51, by decide⟩, -3510), (⟨52, by decide⟩, 5850), (⟨53, by decide⟩, -13104)]
  | 17 => [(⟨16, by decide⟩, 65520), (⟨17, by decide⟩, -26208), (⟨18, by decide⟩, 14560), (⟨19, by decide⟩, -10920), (⟨20, by decide⟩, -39312), (⟨21, by decide⟩, 26208), (⟨22, by decide⟩, -21840), (⟨23, by decide⟩, 23400), (⟨24, by decide⟩, -26208), (⟨25, by decide⟩, 31200), (⟨26, by decide⟩, -52000), (⟨34, by decide⟩, -6552), (⟨35, by decide⟩, 5824), (⟨36, by decide⟩, -5460), (⟨37, by decide⟩, 6240), (⟨38, by decide⟩, 8736), (⟨39, by decide⟩, -9828), (⟨40, by decide⟩, 12480), (⟨41, by decide⟩, 14976), (⟨42, by decide⟩, -26000), (⟨44, by decide⟩, 2912), (⟨45, by decide⟩, -4368), (⟨46, by decide⟩, 6240), (⟨47, by decide⟩, -4368), (⟨48, by decide⟩, 7176), (⟨49, by decide⟩, -13260), (⟨50, by decide⟩, -14560), (⟨51, by decide⟩, 5616), (⟨52, by decide⟩, -10920), (⟨53, by decide⟩, 26208)]
  | 18 => [(⟨17, by decide⟩, 72072), (⟨18, by decide⟩, -40040), (⟨19, by decide⟩, 30030), (⟨21, by decide⟩, -24024), (⟨22, by decide⟩, 30030), (⟨23, by decide⟩, -38610), (⟨24, by decide⟩, 24024), (⟨25, by decide⟩, -34320), (⟨26, by decide⟩, 57200), (⟨35, by decide⟩, -8008), (⟨36, by decide⟩, 10010), (⟨37, by decide⟩, -12870), (⟨39, by decide⟩, 6006), (⟨40, by decide⟩, -12870), (⟨41, by decide⟩, -10296), (⟨42, by decide⟩, 22880), (⟨45, by decide⟩, 4004), (⟨46, by decide⟩, -8580), (⟨48, by decide⟩, -3432), (⟨49, by decide⟩, 11440), (⟨50, by decide⟩, 8008), (⟨52, by decide⟩, 3432), (⟨53, by decide⟩, -10296)]
  | 19 => [(⟨18, by decide⟩, 80080), (⟨19, by decide⟩, -60060), (⟨22, by decide⟩, -30030), (⟨23, by decide⟩, 51480), (⟨25, by decide⟩, 17160), (⟨26, by decide⟩, -28600), (⟨36, by decide⟩, -10010), (⟨37, by decide⟩, 17160), (⟨40, by decide⟩, 8580), (⟨42, by decide⟩, -8580), (⟨46, by decide⟩, 5720), (⟨49, by decide⟩, -5720)]
  | 20 => [(⟨19, by decide⟩, 90090), (⟨23, by decide⟩, -38610), (⟨37, by decide⟩, -12870)]
  | 22 => [(⟨20, by decide⟩, 72072), (⟨21, by decide⟩, -32032), (⟨22, by decide⟩, 20020), (⟨23, by decide⟩, -17160), (⟨24, by decide⟩, 32032), (⟨25, by decide⟩, -34320), (⟨26, by decide⟩, 57200), (⟨38, by decide⟩, -8008), (⟨39, by decide⟩, 8008), (⟨40, by decide⟩, -8580), (⟨41, by decide⟩, -13728), (⟨42, by decide⟩, 22880), (⟨47, by decide⟩, 2002), (⟨48, by decide⟩, -3432), (⟨49, by decide⟩, 5720), (⟨50, by decide⟩, 9152), (⟨51, by decide⟩, -2574), (⟨52, by decide⟩, 5148), (⟨53, by decide⟩, -13728)]
  | 23 => [(⟨21, by decide⟩, 80080), (⟨22, by decide⟩, -50050), (⟨23, by decide⟩, 42900), (⟨24, by decide⟩, -80080), (⟨25, by decide⟩, 85800), (⟨26, by decide⟩, -143000), (⟨39, by decide⟩, -10010), (⟨40, by decide⟩, 14300), (⟨41, by decide⟩, 22880), (⟨42, by decide⟩, -42900), (⟨48, by decide⟩, 2860), (⟨49, by decide⟩, -7150), (⟨50, by decide⟩, -11440), (⟨52, by decide⟩, -2860), (⟨53, by decide⟩, 11440)]
  | 24 => [(⟨22, by decide⟩, 90090), (⟨23, by decide⟩, -77220), (⟨25, by decide⟩, -51480), (⟨26, by decide⟩, 85800), (⟨40, by decide⟩, -12870), (⟨42, by decide⟩, 17160), (⟨49, by decide⟩, 4290)]
  | 25 => [(⟨23, by decide⟩, 102960)]
  | 26 => [(⟨24, by decide⟩, 90090), (⟨25, by decide⟩, -64350), (⟨26, by decide⟩, 107250), (⟨41, by decide⟩, -12870), (⟨42, by decide⟩, 21450), (⟨50, by decide⟩, 4290), (⟨53, by decide⟩, -2574)]
  | 27 => [(⟨25, by decide⟩, 102960), (⟨26, by decide⟩, -171600), (⟨42, by decide⟩, -17160)]
  | 29 => [(⟨26, by decide⟩, 120120)]
  | 30 => [(⟨27, by decide⟩, 55440), (⟨28, by decide⟩, -9240), (⟨29, by decide⟩, 2520), (⟨30, by decide⟩, -1008), (⟨31, by decide⟩, 560), (⟨32, by decide⟩, -420), (⟨33, by decide⟩, 3360), (⟨34, by decide⟩, -1512), (⟨35, by decide⟩, 896), (⟨36, by decide⟩, -700), (⟨37, by decide⟩, 720), (⟨38, by decide⟩, 1008), (⟨39, by decide⟩, -840), (⟨40, by decide⟩, 900), (⟨41, by decide⟩, 960), (⟨42, by decide⟩, -1400), (⟨43, by decide⟩, -2016), (⟨44, by decide⟩, 1344), (⟨45, by decide⟩, -1120), (⟨46, by decide⟩, 1200), (⟨47, by decide⟩, -1260), (⟨48, by decide⟩, 1440), (⟨49, by decide⟩, -2100), (⟨50, by decide⟩, -2240), (⟨51, by decide⟩, 1620), (⟨52, by decide⟩, -2520), (⟨53, by decide⟩, 5376)]
  | 31 => [(⟨28, by decide⟩, 60060), (⟨29, by decide⟩, -16380), (⟨30, by decide⟩, 6552), (⟨31, by decide⟩, -3640), (⟨32, by decide⟩, 2730), (⟨33, by decide⟩, -21840), (⟨34, by decide⟩, 9828), (⟨35, by decide⟩, -5824), (⟨36, by decide⟩, 4550), (⟨37, by decide⟩, -4680), (⟨38, by decide⟩, -6552), (⟨39, by decide⟩, 5460), (⟨40, by decide⟩, -5850), (⟨41, by decide⟩, -6240), (⟨42, by decide⟩, 9100), (⟨43, by decide⟩, 13104), (⟨44, by decide⟩, -8736), (⟨45, by decide⟩, 7280), (⟨46, by decide⟩, -7800), (⟨47, by decide⟩, 8190), (⟨48, by decide⟩, -9360), (⟨49, by decide⟩, 13650), (⟨50, by decide⟩, 14560), (⟨51, by decide⟩, -10530), (⟨52, by decide⟩, 16380), (⟨53, by decide⟩, -34944)]
  | 32 => [(⟨29, by decide⟩, 65520), (⟨30, by decide⟩, -26208), (⟨31, by decide⟩, 14560), (⟨32, by decide⟩, -10920), (⟨34, by decide⟩, -13104), (⟨35, by decide⟩, 11648), (⟨36, by decide⟩, -10920), (⟨37, by decide⟩, 12480), (⟨38, by decide⟩, 8736), (⟨39, by decide⟩, -8736), (⟨40, by decide⟩, 10920), (⟨41, by decide⟩, 9984), (⟨42, by decide⟩, -15600), (⟨44, by decide⟩, 5824), (⟨45, by decide⟩, -8736), (⟨46, by decide⟩, 12480), (⟨47, by decide⟩, -6552), (⟨48, by decide⟩, 9984), (⟨49, by decide⟩, -18200), (⟨50, by decide⟩, -16640), (⟨51, by decide⟩, 8424), (⟨52, by decide⟩, -15600), (⟨53, by decide⟩, 34944)]
  | 33 => [(⟨30, by decide⟩, 72072), (⟨31, by decide⟩, -40040), (⟨32, by decide⟩, 30030), (⟨35, by decide⟩, -16016), (⟨36, by decide⟩, 20020), (⟨37, by decide⟩, -25740), (⟨39, by decide⟩, 6006), (⟨40, by decide⟩, -12870), (⟨41, by decide⟩, -6864), (⟨42, by decide⟩, 14300), (⟨45, by decide⟩, 8008), (⟨46, by decide⟩, -17160), (⟨48, by decide⟩, -5148), (⟨49, by decide⟩, 17160), (⟨50, by decide⟩, 9152), (⟨52, by decide⟩, 5148), (⟨53, by decide⟩, -13728)]
  | 34 => [(⟨31, by decide⟩, 80080), (⟨32, by decide⟩, -60060), (⟨36, by decide⟩, -20020), (⟨37, by decide⟩, 34320), (⟨40, by decide⟩, 8580), (⟨42, by decide⟩, -5720), (⟨46, by decide⟩, 11440), (⟨49, by decide⟩, -8580)]
  | 35 => [(⟨32, by decide⟩, 90090), (⟨37, by decide⟩, -25740)]
  | 37 => [(⟨33, by decide⟩, 65520), (⟨34, by decide⟩, -19656), (⟨35, by decide⟩, 8736), (⟨36, by decide⟩, -5460), (⟨37, by decide⟩, 4680), (⟨38, by decide⟩, 13104), (⟨39, by decide⟩, -9828), (⟨40, by decide⟩, 9360), (⟨41, by decide⟩, 11232), (⟨42, by decide⟩, -15600), (⟨43, by decide⟩, -39312), (⟨44, by decide⟩, 21840), (⟨45, by decide⟩, -15288), (⟨46, by decide⟩, 14040), (⟨47, by decide⟩, -19656), (⟨48, by decide⟩, 20592), (⟨49, by decide⟩, -27300), (⟨50, by decide⟩, -31200), (⟨51, by decide⟩, 25272), (⟨52, by decide⟩, -37440), (⟨53, by decide⟩, 78624)]
  | 38 => [(⟨34, by decide⟩, 72072), (⟨35, by decide⟩, -32032), (⟨36, by decide⟩, 20020), (⟨37, by decide⟩, -17160), (⟨38, by decide⟩, -48048), (⟨39, by decide⟩, 36036), (⟨40, by decide⟩, -34320), (⟨41, by decide⟩, -41184), (⟨42, by decide⟩, 57200), (⟨44, by decide⟩, -32032), (⟨45, by decide⟩, 32032), (⟨46, by decide⟩, -34320), (⟨47, by decide⟩, 36036), (⟨48, by decide⟩, -44616), (⟨49, by decide⟩, 65780), (⟨50, by decide⟩, 73216), (⟨51, by decide⟩, -46332), (⟨52, by decide⟩, 75504), (⟨53, by decide⟩, -164736)]
  | 39 => [(⟨35, by decide⟩, 80080), (⟨36, by decide⟩, -50050), (⟨37, by decide⟩, 42900), (⟨39, by decide⟩, -30030), (⟨40, by decide⟩, 42900), (⟨41, by decide⟩, 34320), (⟨42, by decide⟩, -57200), (⟨45, by decide⟩, -40040), (⟨46, by decide⟩, 57200), (⟨48, by decide⟩, 25740), (⟨49, by decide⟩, -64350), (⟨50, by decide⟩, -45760), (⟨52, by decide⟩, -25740), (⟨53, by decide⟩, 68640)]
  | 40 => [(⟨36, by decide⟩, 90090), (⟨37, by decide⟩, -77220), (⟨40, by decide⟩, -38610), (⟨42, by decide⟩, 25740), (⟨46, by decide⟩, -51480), (⟨49, by decide⟩, 38610)]
  | 41 => [(⟨37, by decide⟩, 102960)]
  | 42 => [(⟨38, by decide⟩, 80080), (⟨39, by decide⟩, -40040), (⟨40, by decide⟩, 28600), (⟨41, by decide⟩, 45760), (⟨42, by decide⟩, -57200), (⟨47, by decide⟩, -20020), (⟨48, by decide⟩, 22880), (⟨49, by decide⟩, -28600), (⟨50, by decide⟩, -45760), (⟨51, by decide⟩, 25740), (⟨52, by decide⟩, -40040), (⟨53, by decide⟩, 91520)]
  | 43 => [(⟨39, by decide⟩, 90090), (⟨40, by decide⟩, -64350), (⟨41, by decide⟩, -102960), (⟨42, by decide⟩, 128700), (⟨48, by decide⟩, -25740), (⟨49, by decide⟩, 42900), (⟨50, by decide⟩, 68640), (⟨52, by decide⟩, 25740), (⟨53, by decide⟩, -82368)]
  | 44 => [(⟨40, by decide⟩, 102960), (⟨42, by decide⟩, -68640), (⟨49, by decide⟩, -34320)]
  | 46 => [(⟨41, by decide⟩, 102960), (⟨42, by decide⟩, -85800), (⟨50, by decide⟩, -34320), (⟨53, by decide⟩, 20592)]
  | 47 => [(⟨42, by decide⟩, 120120)]
  | 49 => [(⟨43, by decide⟩, 72072), (⟨44, by decide⟩, -24024), (⟨45, by decide⟩, 12012), (⟨46, by decide⟩, -8580), (⟨47, by decide⟩, 18018), (⟨48, by decide⟩, -15444), (⟨49, by decide⟩, 17160), (⟨50, by decide⟩, 20592), (⟨51, by decide⟩, -23166), (⟨52, by decide⟩, 30888), (⟨53, by decide⟩, -61776)]
  | 50 => [(⟨44, by decide⟩, 80080), (⟨45, by decide⟩, -40040), (⟨46, by decide⟩, 28600), (⟨47, by decide⟩, -60060), (⟨48, by decide⟩, 51480), (⟨49, by decide⟩, -57200), (⟨50, by decide⟩, -68640), (⟨51, by decide⟩, 77220), (⟨52, by decide⟩, -102960), (⟨53, by decide⟩, 205920)]
  | 51 => [(⟨45, by decide⟩, 90090), (⟨46, by decide⟩, -64350), (⟨48, by decide⟩, -38610), (⟨49, by decide⟩, 64350), (⟨50, by decide⟩, 51480), (⟨52, by decide⟩, 38610), (⟨53, by decide⟩, -92664)]
  | 52 => [(⟨46, by decide⟩, 102960), (⟨49, by decide⟩, -51480)]
  | 54 => [(⟨47, by decide⟩, 90090), (⟨48, by decide⟩, -51480), (⟨49, by decide⟩, 42900), (⟨50, by decide⟩, 68640), (⟨51, by decide⟩, -115830), (⟨52, by decide⟩, 128700), (⟨53, by decide⟩, -247104)]
  | 55 => [(⟨48, by decide⟩, 102960), (⟨49, by decide⟩, -85800), (⟨50, by decide⟩, -137280), (⟨52, by decide⟩, -102960), (⟨53, by decide⟩, 247104)]
  | 56 => [(⟨49, by decide⟩, 120120)]
  | 57 => [(⟨50, by decide⟩, 120120), (⟨53, by decide⟩, -72072)]
  | 59 => [(⟨51, by decide⟩, 102960), (⟨52, by decide⟩, -68640), (⟨53, by decide⟩, 109824)]
  | 60 => [(⟨52, by decide⟩, 120120), (⟨53, by decide⟩, -192192)]
  | 62 => [(⟨53, by decide⟩, 144144)]
  | _ => []

def retainedCM_4_16C : Matrix (Fin 54) (Fin 64) ℚ := sparseRatMatrix retainedCM_4_16CS
def retainedCM_4_16U : Matrix (Fin 64) (Fin 10) ℚ := sparseRatScaledMatrix retainedCM_4_16D retainedCM_4_16WS
def retainedCM_4_16L : Matrix (Fin 10) (Fin 64) ℚ := sparseRatMatrix retainedCM_4_16LS
def retainedCM_4_16V : Matrix (Fin 64) (Fin 54) ℚ := sparseRatScaledMatrix retainedCM_4_16D retainedCM_4_16ZS

theorem retainedCM_4_16_sparse_check :
    SparseScaledFrameCheck retainedCM_4_16D retainedCM_4_16CS retainedCM_4_16WS retainedCM_4_16LS retainedCM_4_16ZS := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem retainedCM_4_16_frame : HasKernelFrame retainedCM_4_16C retainedCM_4_16U retainedCM_4_16L retainedCM_4_16V :=
  sparseScaledFrameCheck_sound (by decide : retainedCM_4_16D≠0) retainedCM_4_16_sparse_check

theorem retainedCM_4_16_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker retainedCM_4_16C.mulVecLin)=10 :=
  kernelFrame_finrank retainedCM_4_16_frame

end BosonicLaughlin

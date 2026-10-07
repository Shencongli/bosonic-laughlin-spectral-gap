import BosonicLaughlin.SparseIntegerMatrix

/-!
An exact sparse certificate for rational kernel frames. A common nonzero
integer denominator D clears U and V: W=D U and Z=D V. The executable
conditions only manipulate integer sparse rows. Their soundness below derives
all three rational matrix identities required by HasKernelFrame.
-/
namespace BosonicLaughlin
open scoped Matrix

def SparseScaledFrameCheck {m n k : ℕ} (D : ℤ)
    (C : SparseIntMatrix m n) (W : SparseIntMatrix n k)
    (L : SparseIntMatrix k n) (Z : SparseIntMatrix n m) : Prop :=
  (∀ i, sparseIntMulRow (C i) W=[]) ∧
  (∀ i, sparseIntMulRow (L i) W=[(i,D)]) ∧
  (∀ i, sparseIntRowAdd (sparseIntMulRow (W i) L) (sparseIntMulRow (Z i) C)=[(i,D)])

theorem sparseScaledFrameCheck_integer {m n k : ℕ} {D : ℤ}
    {C : SparseIntMatrix m n} {W : SparseIntMatrix n k}
    {L : SparseIntMatrix k n} {Z : SparseIntMatrix n m}
    (h : SparseScaledFrameCheck D C W L Z) :
    sparseIntToMatrix C * sparseIntToMatrix W=0 ∧
      sparseIntToMatrix L * sparseIntToMatrix W=D • 1 ∧
      sparseIntToMatrix W * sparseIntToMatrix L + sparseIntToMatrix Z * sparseIntToMatrix C=D • 1 := by
  constructor
  · ext i j
    rw [← sparseIntMulRow_matrix, h.1 i]
    rfl
  constructor
  · ext i j
    rw [← sparseIntMulRow_matrix, h.2.1 i, sparseInt_single_eval]
  · ext i j
    change (sparseIntToMatrix W * sparseIntToMatrix L) i j +
      (sparseIntToMatrix Z * sparseIntToMatrix C) i j = _
    rw [← sparseIntMulRow_matrix, ← sparseIntMulRow_matrix,
      ← sparseIntRowAdd_eval, h.2.2 i, sparseInt_single_eval]

def sparseRatMatrix {m n : ℕ} (A : SparseIntMatrix m n) : Matrix (Fin m) (Fin n) ℚ :=
  (sparseIntToMatrix A).map (Int.castRingHom ℚ)

def sparseRatScaledMatrix {m n : ℕ} (D : ℤ) (A : SparseIntMatrix m n) :
    Matrix (Fin m) (Fin n) ℚ := (D : ℚ)⁻¹ • sparseRatMatrix A

theorem sparseRatMatrix_apply {m n : ℕ} (A : SparseIntMatrix m n) (i : Fin m) (j : Fin n) :
    sparseRatMatrix A i j = (sparseIntRowEval (A i) j : ℚ) := rfl

theorem intMatrix_map_scaled_one (D : ℤ) (n : ℕ) :
    ((D • (1 : Matrix (Fin n) (Fin n) ℤ)).map (Int.castRingHom ℚ)) =
      (D : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  ext i j
  change ((D * (1 : Matrix (Fin n) (Fin n) ℤ) i j : ℤ) : ℚ) =
    (D : ℚ) * (1 : Matrix (Fin n) (Fin n) ℚ) i j
  simp [Matrix.one_apply]

/-- The sparse integer checks imply the full exact rational kernel-frame identities. -/
theorem sparseScaledFrameCheck_sound {m n k : ℕ} {D : ℤ} (hD : D≠0)
    {C : SparseIntMatrix m n} {W : SparseIntMatrix n k}
    {L : SparseIntMatrix k n} {Z : SparseIntMatrix n m}
    (h : SparseScaledFrameCheck D C W L Z) :
    HasKernelFrame (sparseRatMatrix C) (sparseRatScaledMatrix D W)
      (sparseRatMatrix L) (sparseRatScaledMatrix D Z) := by
  have hqD : (D : ℚ)≠0 := by exact_mod_cast hD
  obtain ⟨hCW,hLW,hWZ⟩ := sparseScaledFrameCheck_integer h
  have hqCW : sparseRatMatrix C * sparseRatMatrix W=0 := by
    simpa only [sparseRatMatrix, Matrix.map_mul, Matrix.map_zero, map_zero]
      using congrArg (fun A => A.map (Int.castRingHom ℚ)) hCW
  have hqLW : sparseRatMatrix L * sparseRatMatrix W=(D : ℚ) • 1 := by
    simpa only [sparseRatMatrix, Matrix.map_mul, intMatrix_map_scaled_one]
      using congrArg (fun A => A.map (Int.castRingHom ℚ)) hLW
  have hqWZ : sparseRatMatrix W * sparseRatMatrix L + sparseRatMatrix Z * sparseRatMatrix C=
      (D : ℚ) • 1 := by
    simpa only [sparseRatMatrix, Matrix.map_add _ (map_add (Int.castRingHom ℚ)),
      Matrix.map_mul, intMatrix_map_scaled_one]
      using congrArg (fun A => A.map (Int.castRingHom ℚ)) hWZ
  unfold HasKernelFrame sparseRatScaledMatrix
  constructor
  · rw [Matrix.mul_smul, hqCW, smul_zero]
  constructor
  · rw [Matrix.mul_smul, hqLW, smul_smul, inv_mul_cancel₀ hqD, one_smul]
  · rw [Matrix.smul_mul, Matrix.smul_mul, ← smul_add, hqWZ,
      smul_smul, inv_mul_cancel₀ hqD, one_smul]

end BosonicLaughlin

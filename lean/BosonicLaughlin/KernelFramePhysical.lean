import BosonicLaughlin.KernelFrameTransport
import BosonicLaughlin.OccupationCMBlocks
import BosonicLaughlin.IndexedOccupationCM

/-!
Transport exact rational kernel frames to the actual physical highest-weight
space. The matrix-entry identification is an explicit premise, to be discharged
by the chosen complete enumeration and its coefficient checks.
-/
namespace BosonicLaughlin
noncomputable section
open scoped Matrix

def occupationCMKernelMatrixEquiv (Q N d : ℕ)
    (A : Matrix (WeightOccupation Q N (d-1)) (WeightOccupation Q N d) ℂ)
    (hA : A=occupationCMBlockMatrix Q N d) :
    LinearMap.ker A.mulVecLin ≃ₗ[ℂ] LinearMap.ker (occupationCMBlock Q N d) where
  toFun v := ⟨v.val, by
    change occupationCMBlock Q N d v.val=0
    rw [← occupationCMBlockMatrix_mulVec, ← hA]
    exact v.property⟩
  invFun v := ⟨v.val, by
    change A *ᵥ v.val=0
    rw [hA, occupationCMBlockMatrix_mulVec]
    exact v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A complete rational frame and an exact identification of its matrix give
complete coordinates on the actual physical highest-weight subspace. -/
def kernelFramePhysicalEquiv {Q N d m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) ℚ} {U : Matrix (Fin n) (Fin k) ℚ}
    {L : Matrix (Fin k) (Fin n) ℚ} {V : Matrix (Fin n) (Fin m) ℚ}
    (h : HasKernelFrame C U L V)
    (eRow : WeightOccupation Q N (d-1) ≃ Fin m)
    (eCol : WeightOccupation Q N d ≃ Fin n)
    (hC : (C.map (Rat.castHom ℂ)).submatrix eRow eCol=occupationCMBlockMatrix Q N d) :
    (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d :=
  (kernelFrameRatCastReindexEquiv h eRow eCol).trans
    ((occupationCMKernelMatrixEquiv Q N d _ hC).trans (occupationHighestWeightEquiv Q N d))

theorem kernelFramePhysicalEquiv_apply {Q N d m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) ℚ} {U : Matrix (Fin n) (Fin k) ℚ}
    {L : Matrix (Fin k) (Fin n) ℚ} {V : Matrix (Fin n) (Fin m) ℚ}
    (h : HasKernelFrame C U L V)
    (eRow : WeightOccupation Q N (d-1) ≃ Fin m)
    (eCol : WeightOccupation Q N d ≃ Fin n)
    (hC : (C.map (Rat.castHom ℂ)).submatrix eRow eCol=occupationCMBlockMatrix Q N d)
    (v : Fin k → ℂ) :
    (kernelFramePhysicalEquiv h eRow eCol hC v).val =
      (polynomialWeightCoordinates Q N d).symm
        (polynomialWeightOccupationInclude (((U.map (Rat.castHom ℂ)) *ᵥ v) ∘ eCol)) := rfl

theorem kernelFramePhysical_finrank {Q N d m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) ℚ} {U : Matrix (Fin n) (Fin k) ℚ}
    {L : Matrix (Fin k) (Fin n) ℚ} {V : Matrix (Fin n) (Fin m) ℚ}
    (h : HasKernelFrame C U L V)
    (eRow : WeightOccupation Q N (d-1) ≃ Fin m)
    (eCol : WeightOccupation Q N d ≃ Fin n)
    (hC : (C.map (Rat.castHom ℂ)).submatrix eRow eCol=occupationCMBlockMatrix Q N d) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q N d)=k := by
  rw [← (kernelFramePhysicalEquiv h eRow eCol hC).finrank_eq]
  simp

theorem indexedOccupationCMMatrix_reindex {Q N d rows cols : ℕ} (hd : d≤Q)
    (src : SortedTupleEnumeration N d cols)
    (dst : SortedTupleEnumeration N (d-1) rows) :
    (indexedOccupationCMMatrix hd src dst).submatrix
      (dst.occupationEquiv (Nat.le_trans (Nat.sub_le _ _) hd)).symm
      (src.occupationEquiv hd).symm = occupationCMBlockMatrix Q N d := by
  ext B A
  simp only [Matrix.submatrix_apply, indexedOccupationCMMatrix, Equiv.apply_symm_apply]

def sortedKernelFramePhysicalEquiv {Q N d m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) ℚ} {U : Matrix (Fin n) (Fin k) ℚ}
    {L : Matrix (Fin k) (Fin n) ℚ} {V : Matrix (Fin n) (Fin m) ℚ}
    (h : HasKernelFrame C U L V) (hd : d≤Q)
    (src : SortedTupleEnumeration N d n) (dst : SortedTupleEnumeration N (d-1) m)
    (hC : C.map (Rat.castHom ℂ)=indexedOccupationCMMatrix hd src dst) :
    (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d :=
  kernelFramePhysicalEquiv h
    (dst.occupationEquiv (Nat.le_trans (Nat.sub_le _ _) hd)).symm
    (src.occupationEquiv hd).symm (by rw [hC]; exact indexedOccupationCMMatrix_reindex hd src dst)

theorem sortedKernelFramePhysical_finrank {Q N d m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) ℚ} {U : Matrix (Fin n) (Fin k) ℚ}
    {L : Matrix (Fin k) (Fin n) ℚ} {V : Matrix (Fin n) (Fin m) ℚ}
    (h : HasKernelFrame C U L V) (hd : d≤Q)
    (src : SortedTupleEnumeration N d n) (dst : SortedTupleEnumeration N (d-1) m)
    (hC : C.map (Rat.castHom ℂ)=indexedOccupationCMMatrix hd src dst) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q N d)=k := by
  rw [← (sortedKernelFramePhysicalEquiv h hd src dst hC).finrank_eq]
  simp

theorem indexedKernelFrame_matrix_reindex {Q N d m n : ℕ} (hd : d≤Q)
    (src : SortedTupleEnumeration N d n) (dst : SortedTupleEnumeration N (d-1) m)
    (C : Matrix (Fin m) (Fin n) ℚ)
    (hC : indexedOccupationCMMatrix hd src dst=C.map (Rat.castHom ℂ)) :
    (C.map (Rat.castHom ℂ)).submatrix
      (dst.occupationEquiv (Nat.le_trans (Nat.sub_le _ _) hd)).symm
      (src.occupationEquiv hd).symm = occupationCMBlockMatrix Q N d := by
  rw [← hC]
  exact indexedOccupationCMMatrix_reindex hd src dst

def indexedKernelFramePhysicalEquiv {Q N d m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) ℚ} {U : Matrix (Fin n) (Fin k) ℚ}
    {L : Matrix (Fin k) (Fin n) ℚ} {V : Matrix (Fin n) (Fin m) ℚ}
    (h : HasKernelFrame C U L V) (hd : d≤Q)
    (src : SortedTupleEnumeration N d n) (dst : SortedTupleEnumeration N (d-1) m)
    (hC : indexedOccupationCMMatrix hd src dst=C.map (Rat.castHom ℂ)) :
    (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d :=
  sortedKernelFramePhysicalEquiv h hd src dst hC.symm

theorem indexedKernelFramePhysical_finrank {Q N d m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) ℚ} {U : Matrix (Fin n) (Fin k) ℚ}
    {L : Matrix (Fin k) (Fin n) ℚ} {V : Matrix (Fin n) (Fin m) ℚ}
    (h : HasKernelFrame C U L V) (hd : d≤Q)
    (src : SortedTupleEnumeration N d n) (dst : SortedTupleEnumeration N (d-1) m)
    (hC : indexedOccupationCMMatrix hd src dst=C.map (Rat.castHom ℂ)) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q N d)=k :=
  sortedKernelFramePhysical_finrank h hd src dst hC.symm

end
end BosonicLaughlin

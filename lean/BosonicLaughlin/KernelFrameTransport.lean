import BosonicLaughlin.KernelFrames
import Mathlib.Basic.Complex.Basic

/-!
Exact scalar extension and reindexing of kernel-frame certificates.
The rational identities are mapped into the complex field. Index transport
is an explicit linear equivalence; no numerical rank comparison is used.
-/
namespace BosonicLaughlin
noncomputable section
open scoped Matrix

theorem HasKernelFrame.map {K F : Type*} [Field K] [Field F] {m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) K} {U : Matrix (Fin n) (Fin k) K}
    {L : Matrix (Fin k) (Fin n) K} {V : Matrix (Fin n) (Fin m) K}
    (h : HasKernelFrame C U L V) (f : K →+* F) :
    HasKernelFrame (C.map f) (U.map f) (L.map f) (V.map f) := by
  constructor
  · have he := congrArg (fun M : Matrix (Fin m) (Fin k) K => M.map f) h.1
    simpa using he
  constructor
  · have he := congrArg (fun M : Matrix (Fin k) (Fin k) K => M.map f) h.2.1
    simpa using he
  · have he := congrArg (fun M : Matrix (Fin n) (Fin n) K => M.map f) h.2.2
    rw [Matrix.map_add f f.map_add] at he
    simpa using he

theorem HasKernelFrame.ratCast {m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) ℚ} {U : Matrix (Fin n) (Fin k) ℚ}
    {L : Matrix (Fin k) (Fin n) ℚ} {V : Matrix (Fin n) (Fin m) ℚ}
    (h : HasKernelFrame C U L V) :
    HasKernelFrame (C.map (Rat.castHom ℂ)) (U.map (Rat.castHom ℂ))
      (L.map (Rat.castHom ℂ)) (V.map (Rat.castHom ℂ)) := h.map (Rat.castHom ℂ)

theorem matrix_reindex_mulVec {K I J I' J' : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    (C : Matrix I J K) (eRow : I' ≃ I) (eCol : J' ≃ J) (v : J → K) :
    C.submatrix eRow eCol *ᵥ (v ∘ eCol) = (C *ᵥ v) ∘ eRow := by
  funext i
  exact Equiv.sum_comp eCol (fun j => C (eRow i) j * v j)

theorem matrix_reindex_mulVec_zero_iff {K I J I' J' : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    (C : Matrix I J K) (eRow : I' ≃ I) (eCol : J' ≃ J) (v : J → K) :
    C.submatrix eRow eCol *ᵥ (v ∘ eCol) = 0 ↔ C *ᵥ v = 0 := by
  rw [matrix_reindex_mulVec]
  constructor
  · intro h
    funext i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using
      congrFun h (eRow.symm i)
  · intro h
    rw [h]
    rfl

/-- Reindex a vector by composition with the column equivalence. -/
def matrixKernelReindexEquiv {K I J I' J' : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    (C : Matrix I J K) (eRow : I' ≃ I) (eCol : J' ≃ J) :
    LinearMap.ker C.mulVecLin ≃ₗ[K] LinearMap.ker (C.submatrix eRow eCol).mulVecLin where
  toFun v := ⟨v.val ∘ eCol,
    (matrix_reindex_mulVec_zero_iff C eRow eCol v.val).mpr v.property⟩
  invFun v := ⟨v.val ∘ eCol.symm, by
    apply (matrix_reindex_mulVec_zero_iff C eRow eCol _).mp
    have hv : C.submatrix eRow eCol *ᵥ v.val = 0 := v.property
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hv⟩
  left_inv v := by
    apply Subtype.ext
    funext j
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv v := by
    apply Subtype.ext
    funext j
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem matrixKernelReindexEquiv_apply {K I J I' J' : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    (C : Matrix I J K) (eRow : I' ≃ I) (eCol : J' ≃ J)
    (v : LinearMap.ker C.mulVecLin) :
    (matrixKernelReindexEquiv C eRow eCol v).val = v.val ∘ eCol := rfl

theorem matrixKernelReindex_finrank {K I J I' J' : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    (C : Matrix I J K) (eRow : I' ≃ I) (eCol : J' ≃ J) :
    Module.finrank K (LinearMap.ker (C.submatrix eRow eCol).mulVecLin) =
      Module.finrank K (LinearMap.ker C.mulVecLin) :=
  (matrixKernelReindexEquiv C eRow eCol).finrank_eq.symm

def kernelFrameReindexEquiv {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    {m n k : ℕ} {C : Matrix (Fin m) (Fin n) K} {U : Matrix (Fin n) (Fin k) K}
    {L : Matrix (Fin k) (Fin n) K} {V : Matrix (Fin n) (Fin m) K}
    (h : HasKernelFrame C U L V) (eRow : I ≃ Fin m) (eCol : J ≃ Fin n) :
    (Fin k → K) ≃ₗ[K] LinearMap.ker (C.submatrix eRow eCol).mulVecLin :=
  (kernelFrameEquiv h).trans (matrixKernelReindexEquiv C eRow eCol)

theorem kernelFrameReindexEquiv_apply {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    {m n k : ℕ} {C : Matrix (Fin m) (Fin n) K} {U : Matrix (Fin n) (Fin k) K}
    {L : Matrix (Fin k) (Fin n) K} {V : Matrix (Fin n) (Fin m) K}
    (h : HasKernelFrame C U L V) (eRow : I ≃ Fin m) (eCol : J ≃ Fin n) (c : Fin k → K) :
    (kernelFrameReindexEquiv h eRow eCol c).val = (U *ᵥ c) ∘ eCol := rfl

theorem kernelFrameReindex_finrank {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    {m n k : ℕ} {C : Matrix (Fin m) (Fin n) K} {U : Matrix (Fin n) (Fin k) K}
    {L : Matrix (Fin k) (Fin n) K} {V : Matrix (Fin n) (Fin m) K}
    (h : HasKernelFrame C U L V) (eRow : I ≃ Fin m) (eCol : J ≃ Fin n) :
    Module.finrank K (LinearMap.ker (C.submatrix eRow eCol).mulVecLin) = k := by
  rw [matrixKernelReindex_finrank]
  exact kernelFrame_finrank h

def kernelFrameRatCastReindexEquiv {I J : Type*} [Fintype I] [Fintype J]
    {m n k : ℕ} {C : Matrix (Fin m) (Fin n) ℚ} {U : Matrix (Fin n) (Fin k) ℚ}
    {L : Matrix (Fin k) (Fin n) ℚ} {V : Matrix (Fin n) (Fin m) ℚ}
    (h : HasKernelFrame C U L V) (eRow : I ≃ Fin m) (eCol : J ≃ Fin n) :
    (Fin k → ℂ) ≃ₗ[ℂ] LinearMap.ker
      ((C.map (Rat.castHom ℂ)).submatrix eRow eCol).mulVecLin :=
  kernelFrameReindexEquiv h.ratCast eRow eCol

theorem kernelFrameRatCastReindex_finrank {I J : Type*} [Fintype I] [Fintype J]
    {m n k : ℕ} {C : Matrix (Fin m) (Fin n) ℚ} {U : Matrix (Fin n) (Fin k) ℚ}
    {L : Matrix (Fin k) (Fin n) ℚ} {V : Matrix (Fin n) (Fin m) ℚ}
    (h : HasKernelFrame C U L V) (eRow : I ≃ Fin m) (eCol : J ≃ Fin n) :
    Module.finrank ℂ (LinearMap.ker
      ((C.map (Rat.castHom ℂ)).submatrix eRow eCol).mulVecLin) = k :=
  kernelFrameReindex_finrank h.ratCast eRow eCol

end
end BosonicLaughlin

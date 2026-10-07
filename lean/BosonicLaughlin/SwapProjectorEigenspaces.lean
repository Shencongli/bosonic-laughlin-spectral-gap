import BosonicLaughlin.SwapProjectors
import BosonicLaughlin.RecouplingValues

/-! The spectral projector ranges are exactly the physical auxiliary eigenspaces. -/
namespace BosonicLaughlin
noncomputable section
open Finset
open scoped Matrix

theorem compressedSwapProjector_eigen_left (Q : ℕ) (z : Fin (Q+1)) :
    compressedSwapProjector Q z * compressedSwapMatrix Q =
      (recouplingEigenvalue Q z.val : ℂ) • compressedSwapProjector Q z := by
  rw [compressedSwap_projector_resolution, Finset.mul_sum]
  simp only [Matrix.mul_smul, compressedSwapProjector_mul]
  simp

theorem compressedSwapProjector_eigenvector_other (Q : ℕ) (z w : Fin (Q+1))
    (hzw : w ≠ z) (v : ThreeBodyIndex Q → ℂ)
    (hv : compressedSwapMatrix Q *ᵥ v = (recouplingEigenvalue Q z.val : ℂ) • v) :
    compressedSwapProjector Q w *ᵥ v = 0 := by
  have he : (recouplingEigenvalue Q w.val : ℂ) • (compressedSwapProjector Q w *ᵥ v) =
      (recouplingEigenvalue Q z.val : ℂ) • (compressedSwapProjector Q w *ᵥ v) := by
    calc
      _ = (compressedSwapProjector Q w * compressedSwapMatrix Q) *ᵥ v := by
        rw [compressedSwapProjector_eigen_left, Matrix.smul_mulVec]
      _ = compressedSwapProjector Q w *ᵥ (compressedSwapMatrix Q *ᵥ v) := by
        rw [Matrix.mulVec_mulVec]
      _ = _ := by rw [hv, Matrix.mulVec_smul]
  have hn : (recouplingEigenvalue Q w.val : ℂ) - (recouplingEigenvalue Q z.val : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hh
    exact hzw (recouplingEigenvalue_injective Q (Complex.ofReal_injective hh))
  have hz : ((recouplingEigenvalue Q w.val : ℂ) - (recouplingEigenvalue Q z.val : ℂ)) •
      (compressedSwapProjector Q w *ᵥ v) = 0 := by
    rw [sub_smul, he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left hn

theorem compressedSwapProjector_fixed_iff (Q : ℕ) (z : Fin (Q+1))
    (v : ThreeBodyIndex Q → ℂ) :
    compressedSwapProjector Q z *ᵥ v = v ↔
      compressedSwapMatrix Q *ᵥ v = (recouplingEigenvalue Q z.val : ℂ) • v := by
  constructor
  · intro hv
    calc
      _ = compressedSwapMatrix Q *ᵥ (compressedSwapProjector Q z *ᵥ v) := by rw [hv]
      _ = (compressedSwapMatrix Q * compressedSwapProjector Q z) *ᵥ v := by
        rw [Matrix.mulVec_mulVec]
      _ = _ := by rw [compressedSwapProjector_eigen, Matrix.smul_mulVec, hv]
  · intro hv
    have hs : (∑ w : Fin (Q+1), compressedSwapProjector Q w *ᵥ v) =
        compressedSwapProjector Q z *ᵥ v := by
      apply Finset.sum_eq_single z
      · intro w _ hw
        exact compressedSwapProjector_eigenvector_other Q z w hw v hv
      · simp
    rw [← Matrix.sum_mulVec, compressedSwapProjector_sum, Matrix.one_mulVec] at hs
    exact hs.symm

def compressedSwapProjectorLinear (Q : ℕ) (z : Fin (Q+1)) :
    ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q where
  toFun φ := fun p k => (compressedSwapProjector Q z *ᵥ (fun a => φ a.1 a.2)) (p,k)
  map_add' φ χ := by
    funext p k
    change (compressedSwapProjector Q z *ᵥ
      ((fun a => φ a.1 a.2) + (fun a => χ a.1 a.2))) (p,k) = _
    rw [Matrix.mulVec_add]
    rfl
  map_smul' c φ := by
    funext p k
    change (compressedSwapProjector Q z *ᵥ (c • (fun a => φ a.1 a.2))) (p,k) = _
    rw [Matrix.mulVec_smul]
    rfl

theorem compressedSwapProjectorLinear_fixed_iff (Q : ℕ) (z : Fin (Q+1))
    (φ : ThreeBodyAux Q) :
    compressedSwapProjectorLinear Q z φ = φ ↔
      compressedSwap φ = (recouplingEigenvalue Q z.val : ℂ) • φ := by
  have h := compressedSwapProjector_fixed_iff Q z (fun a => φ a.1 a.2)
  rw [compressedSwapMatrix_mulVec] at h
  constructor
  · intro he
    have hm : compressedSwapProjector Q z *ᵥ (fun a => φ a.1 a.2) =
        (fun a => φ a.1 a.2) := by
      funext a
      exact congrFun (congrFun he a.1) a.2
    have ht := h.mp hm
    funext p k
    exact congrFun ht (p,k)
  · intro he
    have hm : compressedSwapMatrix Q *ᵥ (fun a => φ a.1 a.2) =
        (recouplingEigenvalue Q z.val : ℂ) • (fun a => φ a.1 a.2) := by
      rw [compressedSwapMatrix_mulVec, he]
      rfl
    have ht := (compressedSwapProjector_fixed_iff Q z (fun a => φ a.1 a.2)).mpr hm
    funext p k
    exact congrFun ht (p,k)

theorem compressedSwapProjectorLinear_idempotent (Q : ℕ) (z : Fin (Q+1))
    (φ : ThreeBodyAux Q) :
    compressedSwapProjectorLinear Q z (compressedSwapProjectorLinear Q z φ) =
      compressedSwapProjectorLinear Q z φ := by
  funext p k
  change (compressedSwapProjector Q z *ᵥ
    (compressedSwapProjector Q z *ᵥ (fun a => φ a.1 a.2))) (p,k) = _
  rw [Matrix.mulVec_mulVec, compressedSwapProjector_idempotent]
  rfl

theorem compressedSwapProjector_range (Q : ℕ) (z : Fin (Q+1)) :
    LinearMap.range (compressedSwapProjectorLinear Q z) =
      Module.End.eigenspace (compressedSwapLinear Q) (recouplingEigenvalue Q z.val : ℂ) := by
  ext φ
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨ψ, rfl⟩
    exact (compressedSwapProjectorLinear_fixed_iff Q z _).mp
      (compressedSwapProjectorLinear_idempotent Q z ψ)
  · intro he
    exact ⟨φ, (compressedSwapProjectorLinear_fixed_iff Q z φ).mpr he⟩

end
end BosonicLaughlin

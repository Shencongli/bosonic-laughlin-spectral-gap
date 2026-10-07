import BosonicLaughlin.SwapProjectors
import BosonicLaughlin.ThreeBodyNormal

/-! Return the complete compressed-exchange resolution to the physical
three-particle Gram map and normal-order coefficient. -/
namespace BosonicLaughlin
noncomputable section
open Finset Matrix

def auxSpectralProject {Q : ℕ} (z : Fin (Q+1)) (φ : ThreeBodyAux Q) : ThreeBodyAux Q :=
  fun p k => (compressedSwapProjector Q z *ᵥ (fun a => φ a.1 a.2)) (p,k)

def threeBodyMapLinear (Q : ℕ) : ThreeBodyAux Q →ₗ[ℂ] State Q 3 where
  toFun := threeBodyMap
  map_add' := threeBodyMap_add
  map_smul' := threeBodyMap_smul

def threeBodyGramMatrix (Q : ℕ) : Matrix (ThreeBodyIndex Q) (ThreeBodyIndex Q) ℂ :=
  1 + (2 : ℂ) • compressedSwapMatrix Q

theorem threeBodyGramMatrix_apply (Q : ℕ) (φ : ThreeBodyAux Q) :
    threeBodyGramMatrix Q *ᵥ (fun a => φ a.1 a.2) =
      (fun a => threeBodyAdjoint (threeBodyMap φ) a.1 a.2) := by
  rw [threeBodyGramMatrix, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, compressedSwapMatrix_mulVec, threeBody_gram]
  rfl

/-- The manuscript's auxiliary Gram eigenvalues, with actual orthogonal projectors. -/
theorem threeBodyGram_projector_resolution (Q : ℕ) :
    threeBodyGramMatrix Q = ∑ z : Fin (Q+1),
      ((1 + 2 * recouplingEigenvalue Q z.val : ℝ) : ℂ) • compressedSwapProjector Q z := by
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_ofNat, add_smul, one_smul, mul_smul, Finset.sum_add_distrib,
    ← Finset.smul_sum]
  rw [compressedSwapProjector_sum, ← compressedSwap_projector_resolution]
  rfl

theorem compressedSwap_aux_resolution {Q : ℕ} (φ : ThreeBodyAux Q) :
    compressedSwap φ = ∑ z : Fin (Q+1),
      (recouplingEigenvalue Q z.val : ℂ) • auxSpectralProject z φ := by
  have h := compressedSwapMatrix_mulVec φ
  rw [compressedSwap_projector_resolution, Matrix.sum_mulVec] at h
  simp only [Matrix.smul_mulVec] at h
  funext p k
  simpa only [Finset.sum_apply, Pi.smul_apply, auxSpectralProject]
    using (congrFun h (p,k)).symm

/-- On three bosons, S₃ = Σz 2(-1)^z fz W₃ Πz W₃†, with no spectral hypothesis. -/
theorem threeBody_normal_spectral_resolution {Q : ℕ} (ψ : State Q 3)
    (hψ : IsBosonic ψ) :
    normalThreeBodyApply ψ = ∑ z : Fin (Q+1),
      ((2 : ℂ) * (recouplingEigenvalue Q z.val : ℂ)) •
        threeBodyMap (auxSpectralProject z (threeBodyAdjoint ψ)) := by
  rw [threeBody_normal_coefficient ψ hψ, compressedSwap_aux_resolution]
  change (2 : ℂ) • (threeBodyMapLinear Q)
    (∑ z : Fin (Q+1), (recouplingEigenvalue Q z.val : ℂ) •
      auxSpectralProject z (threeBodyAdjoint ψ)) = _
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul, smul_smul]
  rfl

end
end BosonicLaughlin

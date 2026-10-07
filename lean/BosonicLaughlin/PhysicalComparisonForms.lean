import BosonicLaughlin.CertificateGram
import BosonicLaughlin.RetainedCMPhysical

/-! Exact pullback of physical sesquilinear forms to a finite, generally
nonorthonormal frame.  Positivity is preserved on its full image; no matrix
supplied by an external program is identified by a success flag. -/
namespace BosonicLaughlin
noncomputable section
open Finset
open scoped Matrix ComplexOrder

def physicalFrameMatrix {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) : Matrix (Configuration Q N) I ℂ :=
  LinearMap.toMatrix' P

theorem physicalFrameMatrix_mulVec {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (v : I → ℂ) :
    physicalFrameMatrix P *ᵥ v=P v := LinearMap.toMatrix'_mulVec P v

def physicalFormMatrix {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (A : State Q N →ₗ[ℂ] State Q N) : Matrix I I ℂ :=
  (physicalFrameMatrix P)ᴴ * (LinearMap.toMatrix' A) * physicalFrameMatrix P

theorem physicalFormMatrix_form {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (A : State Q N →ₗ[ℂ] State Q N) (v w : I → ℂ) :
    star v ⬝ᵥ (physicalFormMatrix P A *ᵥ w) = inner (P v) (A (P w)) := by
  unfold physicalFormMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rw [physicalFrameMatrix_mulVec, physicalFrameMatrix_mulVec, LinearMap.toMatrix'_mulVec]
  rfl

theorem physicalFormMatrix_apply {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (A : State Q N →ₗ[ℂ] State Q N) (i j : I) :
    physicalFormMatrix P A i j = inner (P (Pi.single i 1)) (A (P (Pi.single j 1))) := by
  have h := physicalFormMatrix_form P A (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using h

theorem physicalFormMatrix_add {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (A B : State Q N →ₗ[ℂ] State Q N) :
    physicalFormMatrix P (A+B)=physicalFormMatrix P A+physicalFormMatrix P B := by
  simp [physicalFormMatrix, map_add, Matrix.mul_add, Matrix.add_mul]

theorem physicalFormMatrix_sub {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (A B : State Q N →ₗ[ℂ] State Q N) :
    physicalFormMatrix P (A-B)=physicalFormMatrix P A-physicalFormMatrix P B := by
  simp [physicalFormMatrix, map_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem physicalFormMatrix_smul {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (c : ℂ) (A : State Q N →ₗ[ℂ] State Q N) :
    physicalFormMatrix P (c • A)=c • physicalFormMatrix P A := by
  simp [physicalFormMatrix, map_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem physicalFormMatrix_comp_frame {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (A : State Q N →ₗ[ℂ] State Q N)
    (U : Matrix I J ℂ) :
    physicalFormMatrix (P.comp U.mulVecLin) A = Uᴴ * physicalFormMatrix P A * U := by
  have hU : LinearMap.toMatrix' U.mulVecLin=U := by
    ext i j
    simp [LinearMap.toMatrix'_apply]
  simp only [physicalFormMatrix, physicalFrameMatrix, LinearMap.toMatrix'_comp,
    hU, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem physicalFormMatrix_nonneg_iff {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (A : State Q N →ₗ[ℂ] State Q N) :
    (∀ v, 0 ≤ (star v ⬝ᵥ (physicalFormMatrix P A *ᵥ v)).re) ↔
      ∀ ψ ∈ LinearMap.range P, 0 ≤ (inner ψ (A ψ)).re := by
  simp only [physicalFormMatrix_form, LinearMap.mem_range, forall_exists_index, forall_apply_eq_imp_iff]

theorem certificateHamiltonianFormMatrix_eq_pullback (Q N d : ℕ) :
    certificateHamiltonianFormMatrix Q N d =
      physicalFormMatrix (certificateWeightCoordinates Q N d) (hamiltonianLinear Q N) := by
  ext i j
  rw [physicalFormMatrix_apply]
  rfl

/-- A complete physical highest-weight frame, including its inclusion into
the ordered-tensor state space. The equivalence need not preserve norms. -/
def highestWeightPhysicalFrame {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d) :
    (Fin k → ℂ) →ₗ[ℂ] State Q N :=
  (weightIncludeLinear Q N d).comp
    ((physicalHighestWeightSubspace Q N d).subtype.comp E.toLinearMap)

theorem highestWeightPhysicalFrame_range {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d) :
    LinearMap.range (highestWeightPhysicalFrame E)=
      (physicalHighestWeightSubspace Q N d).map (weightIncludeLinear Q N d) := by
  ext ψ
  constructor
  · rintro ⟨c,rfl⟩
    exact ⟨(E c).val,(E c).property,rfl⟩
  · rintro ⟨φ,hφ,rfl⟩
    obtain ⟨c,hc⟩ := E.surjective ⟨φ,hφ⟩
    refine ⟨c,?_⟩
    change weightInclude d (E c).val=weightInclude d φ
    rw [hc]

theorem highestWeightPhysicalFrame_nonneg_iff {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d)
    (A : State Q N →ₗ[ℂ] State Q N) :
    (∀ v, 0 ≤ (star v ⬝ᵥ (physicalFormMatrix (highestWeightPhysicalFrame E) A *ᵥ v)).re) ↔
      ∀ φ ∈ physicalHighestWeightSubspace Q N d,
        0 ≤ (inner (weightInclude d φ) (A (weightInclude d φ))).re := by
  simp only [physicalFormMatrix_form]
  constructor
  · intro h φ hφ
    obtain ⟨c,hc⟩ := E.surjective ⟨φ,hφ⟩
    have hh := h c
    change 0 ≤ (inner (weightInclude d (E c).val) (A (weightInclude d (E c).val))).re at hh
    rw [hc] at hh
    exact hh
  · intro h c
    exact h (E c).val (E c).property

end
end BosonicLaughlin

import BosonicLaughlin.AngularMomentum
import BosonicLaughlin.WeightCoordinates
import BosonicLaughlin.NumberAnnihilation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
The spherical total raising operator on the actual ordered N-particle tensor
coordinates. Orbital labels are deficits from the north-pole orbital. Thus
raising lowers their total deficit by one. Bose symmetry is imposed separately
and is proved to be preserved. All definitions include Q=0 and N=0.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def tensorRaise {Q N : ℕ} (ψ : State Q N) : State Q N := fun a =>
  ∑ k : Fin N, if h : (a k).val < Q then
    (spinRaiseCoeff Q (a k).val : ℂ) *
      ψ (Function.update a k ⟨(a k).val+1, by omega⟩) else 0

theorem tensorRaise_add {Q N : ℕ} (ψ φ : State Q N) :
    tensorRaise (ψ+φ) = tensorRaise ψ + tensorRaise φ := by
  funext a
  simp only [tensorRaise, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp [mul_add]

theorem tensorRaise_smul {Q N : ℕ} (c : ℂ) (ψ : State Q N) :
    tensorRaise (c • ψ) = c • tensorRaise ψ := by
  funext a
  simp only [tensorRaise, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

def tensorRaiseLinear (Q N : ℕ) : State Q N →ₗ[ℂ] State Q N where
  toFun := tensorRaise
  map_add' := tensorRaise_add
  map_smul' := tensorRaise_smul

theorem tensorRaise_isBosonic {Q N : ℕ} (ψ : State Q N)
    (hψ : IsBosonic ψ) : IsBosonic (tensorRaise ψ) := by
  intro σ a
  simp only [tensorRaise, Function.comp_apply, update_permute, hψ σ]
  exact Equiv.sum_comp σ (fun k => if h : (a k).val < Q then
    (spinRaiseCoeff Q (a k).val : ℂ) *
      ψ (Function.update a k ⟨(a k).val+1, by omega⟩) else 0)

theorem configurationWeight_raise_update {Q N : ℕ} (a : Configuration Q N)
    (k : Fin N) (h : (a k).val < Q) :
    configurationWeight (Function.update a k ⟨(a k).val+1, by omega⟩) =
      configurationWeight a + 1 := by
  have he := configurationWeight_update a k (⟨(a k).val+1, by omega⟩ : Orbital Q)
  change _ + (a k).val = _ + ((a k).val+1) at he
  omega

theorem tensorRaise_weightSupported {Q N : ℕ} (d : ℕ) (ψ : State Q N)
    (hψ : WeightSupported d ψ) : WeightSupported (d-1) (tensorRaise ψ) := by
  intro a ha
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hk
  · have hz : ψ (Function.update a k ⟨(a k).val+1, by omega⟩)=0 := by
      apply hψ
      rw [configurationWeight_raise_update a k hk]
      omega
    rw [hz, mul_zero]
  · rfl

theorem tensorRaise_zero_weight {Q N : ℕ} (ψ : State Q N)
    (hψ : WeightSupported 0 ψ) : tensorRaise ψ = 0 := by
  funext a
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hk
  · have hz : ψ (Function.update a k ⟨(a k).val+1, by omega⟩)=0 := by
      apply hψ
      rw [configurationWeight_raise_update a k hk]
      omega
    rw [hz, mul_zero]
  · rfl

theorem tensorRaise_zero_flux {N : ℕ} (ψ : State 0 N) : tensorRaise ψ = 0 := by
  funext a
  simp [tensorRaise]

theorem tensorRaise_vacuum {Q : ℕ} (ψ : State Q 0) : tensorRaise ψ = 0 := by
  funext a
  simp [tensorRaise]

/-- The exact raising map from the total-deficit d block to d-1. -/
def weightTensorRaise (Q N d : ℕ) : WeightState Q N d →ₗ[ℂ] WeightState Q N (d-1) :=
  (weightRestrictLinear Q N (d-1)).comp
    ((tensorRaiseLinear Q N).comp (weightIncludeLinear Q N d))

theorem weightTensorRaise_apply {Q N d : ℕ} (φ : WeightState Q N d) :
    weightTensorRaise Q N d φ = weightRestrict (d-1) (tensorRaise (weightInclude d φ)) := rfl

theorem weightTensorRaise_include {Q N d : ℕ} (φ : WeightState Q N d) :
    weightInclude (d-1) (weightTensorRaise Q N d φ) = tensorRaise (weightInclude d φ) := by
  rw [weightTensorRaise_apply, weightInclude_restrict_supported]
  exact tensorRaise_weightSupported d _ (weightInclude_supported φ)

theorem weightTensorRaise_isBosonic {Q N d : ℕ} (φ : WeightState Q N d)
    (hφ : WeightIsBosonic φ) : WeightIsBosonic (weightTensorRaise Q N d φ) := by
  unfold WeightIsBosonic
  rw [weightTensorRaise_include]
  exact tensorRaise_isBosonic _ hφ

theorem weightTensorRaise_zero_iff {Q N d : ℕ} (φ : WeightState Q N d) :
    weightTensorRaise Q N d φ=0 ↔ tensorRaise (weightInclude d φ)=0 := by
  constructor
  · intro h
    rw [← weightTensorRaise_include, h]
    exact (weightIncludeLinear Q N (d-1)).map_zero
  · intro h
    rw [weightTensorRaise_apply, h]
    rfl

def tensorRaiseMatrix (Q N d : ℕ) :
    Matrix (WeightConfiguration Q N (d-1)) (WeightConfiguration Q N d) ℂ :=
  LinearMap.toMatrix' (weightTensorRaise Q N d)

theorem tensorRaiseMatrix_mulVec {Q N d : ℕ} (φ : WeightState Q N d) :
    (tensorRaiseMatrix Q N d).mulVec φ = weightTensorRaise Q N d φ :=
  LinearMap.toMatrix'_mulVec _ _

theorem tensorRaiseMatrix_zero_iff {Q N d : ℕ} (φ : WeightState Q N d) :
    (tensorRaiseMatrix Q N d).mulVec φ=0 ↔ tensorRaise (weightInclude d φ)=0 := by
  rw [tensorRaiseMatrix_mulVec, weightTensorRaise_zero_iff]

def physicalHighestWeightSubspace (Q N d : ℕ) : Submodule ℂ (WeightState Q N d) :=
  (bosonicSubspace Q N).comap (weightIncludeLinear Q N d) ⊓
    LinearMap.ker (weightTensorRaise Q N d)

theorem mem_physicalHighestWeightSubspace {Q N d : ℕ} (φ : WeightState Q N d) :
    φ ∈ physicalHighestWeightSubspace Q N d ↔
      WeightIsBosonic φ ∧ tensorRaise (weightInclude d φ)=0 := by
  change (WeightIsBosonic φ ∧ weightTensorRaise Q N d φ=0) ↔ _
  rw [weightTensorRaise_zero_iff]

end
end BosonicLaughlin

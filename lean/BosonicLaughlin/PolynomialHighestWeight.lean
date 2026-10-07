import BosonicLaughlin.TensorHighestWeight
import BosonicLaughlin.PolynomialWeightCoordinates

/-!
The exact polynomial-coordinate form of the spherical total raising operator.
The integer coefficient map polynomialCM is the sum of the single-coordinate
degree-lowering maps. Its kernel is transported from the actual raising kernel
by the previously defined nonunitary diagonal map, before any choice of an
occupation or relative-polynomial basis.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def polynomialCM {Q N : ℕ} (χ : State Q N) : State Q N := fun a =>
  ∑ k : Fin N, if h : (a k).val < Q then
    (((a k).val+1 : ℕ) : ℂ) *
      χ (Function.update a k ⟨(a k).val+1, by omega⟩) else 0

theorem polynomialCM_add {Q N : ℕ} (χ η : State Q N) :
    polynomialCM (χ+η) = polynomialCM χ + polynomialCM η := by
  funext a
  simp only [polynomialCM, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp [mul_add]

theorem polynomialCM_smul {Q N : ℕ} (c : ℂ) (χ : State Q N) :
    polynomialCM (c • χ) = c • polynomialCM χ := by
  funext a
  simp only [polynomialCM, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

def polynomialCMLinear (Q N : ℕ) : State Q N →ₗ[ℂ] State Q N where
  toFun := polynomialCM
  map_add' := polynomialCM_add
  map_smul' := polynomialCM_smul

theorem polynomialCM_isBosonic {Q N : ℕ} (χ : State Q N)
    (hχ : IsBosonic χ) : IsBosonic (polynomialCM χ) := by
  intro σ a
  simp only [polynomialCM, Function.comp_apply, update_permute, hχ σ]
  exact Equiv.sum_comp σ (fun k => if h : (a k).val < Q then
    (((a k).val+1 : ℕ) : ℂ) *
      χ (Function.update a k ⟨(a k).val+1, by omega⟩) else 0)

theorem polynomialCM_weightSupported {Q N : ℕ} (d : ℕ) (χ : State Q N)
    (hχ : WeightSupported d χ) : WeightSupported (d-1) (polynomialCM χ) := by
  intro a ha
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hk
  · have hz : χ (Function.update a k ⟨(a k).val+1, by omega⟩)=0 := by
      apply hχ
      rw [configurationWeight_raise_update a k hk]
      omega
    rw [hz, mul_zero]
  · rfl

theorem polynomialCM_zero_weight {Q N : ℕ} (χ : State Q N)
    (hχ : WeightSupported 0 χ) : polynomialCM χ=0 := by
  funext a
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hk
  · have hz : χ (Function.update a k ⟨(a k).val+1, by omega⟩)=0 := by
      apply hχ
      rw [configurationWeight_raise_update a k hk]
      omega
    rw [hz, mul_zero]
  · rfl

theorem polynomialCM_zero_flux {N : ℕ} (χ : State 0 N) : polynomialCM χ=0 := by
  funext a
  simp [polynomialCM]

theorem polynomialCM_vacuum {Q : ℕ} (χ : State Q 0) : polynomialCM χ=0 := by
  funext a
  simp [polynomialCM]

theorem polynomialScale_update {Q N : ℕ} (a : Configuration Q N) (k : Fin N)
    (x : Orbital Q) :
    polynomialScale (Function.update a k x) =
      binomialRoot Q x.val * ∏ j ∈ (univ : Finset (Fin N)).erase k,
        binomialRoot Q (a j).val := by
  have he : (fun j => binomialRoot Q (Function.update a k x j).val) =
      Function.update (fun j => binomialRoot Q (a j).val) k (binomialRoot Q x.val) := by
    funext j
    by_cases hj : j=k <;> simp [hj]
  unfold polynomialScale
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ k)]
  simp only [Finset.sdiff_singleton_eq_erase]

theorem polynomialScale_eq_mul_erase {Q N : ℕ} (a : Configuration Q N) (k : Fin N) :
    polynomialScale a = binomialRoot Q (a k).val *
      ∏ j ∈ (univ : Finset (Fin N)).erase k, binomialRoot Q (a j).val :=
  (Finset.mul_prod_erase univ (fun j => binomialRoot Q (a j).val) (mem_univ k)).symm

theorem polynomialScale_raise_coefficient {Q N : ℕ} (a : Configuration Q N)
    (k : Fin N) (h : (a k).val < Q) :
    polynomialScale a * spinRaiseCoeff Q (a k).val =
      (((a k).val+1 : ℕ) : ℝ) *
        polynomialScale (Function.update a k ⟨(a k).val+1, by omega⟩) := by
  rw [polynomialScale_eq_mul_erase a k, polynomialScale_update]
  have he := binomialRoot_ladder_right Q (a k).val
  change spinRaiseCoeff Q (a k).val * binomialRoot Q (a k).val =
    (((a k).val+1 : ℕ) : ℝ) * binomialRoot Q ((a k).val+1) at he
  linear_combination (∏ j ∈ (univ : Finset (Fin N)).erase k,
    binomialRoot Q (a j).val) * he

/-- Exact conjugation of the physical total raising map, including cap boundaries. -/
theorem polynomialCoordinates_tensorRaise {Q N : ℕ} (ψ : State Q N) :
    polynomialCoordinates Q N (tensorRaise ψ) =
      polynomialCM (polynomialCoordinates Q N ψ) := by
  funext a
  simp only [polynomialCoordinates_apply, tensorRaise, polynomialCM, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · rw [← mul_assoc, ← Complex.ofReal_mul, polynomialScale_raise_coefficient a k hk]
    push_cast
    ring
  · simp

theorem polynomialCM_coordinates_zero_iff {Q N : ℕ} (ψ : State Q N) :
    polynomialCM (polynomialCoordinates Q N ψ)=0 ↔ tensorRaise ψ=0 := by
  rw [← polynomialCoordinates_tensorRaise, (polynomialCoordinates Q N).map_eq_zero_iff]

def weightPolynomialCM (Q N d : ℕ) : WeightState Q N d →ₗ[ℂ] WeightState Q N (d-1) :=
  (weightRestrictLinear Q N (d-1)).comp
    ((polynomialCMLinear Q N).comp (weightIncludeLinear Q N d))

theorem weightPolynomialCM_apply {Q N d : ℕ} (χ : WeightState Q N d) :
    weightPolynomialCM Q N d χ = weightRestrict (d-1) (polynomialCM (weightInclude d χ)) := rfl

theorem weightPolynomialCM_include {Q N d : ℕ} (χ : WeightState Q N d) :
    weightInclude (d-1) (weightPolynomialCM Q N d χ) = polynomialCM (weightInclude d χ) := by
  rw [weightPolynomialCM_apply, weightInclude_restrict_supported]
  exact polynomialCM_weightSupported d _ (weightInclude_supported χ)

theorem weightPolynomialCM_isBosonic {Q N d : ℕ} (χ : WeightState Q N d)
    (hχ : WeightIsBosonic χ) : WeightIsBosonic (weightPolynomialCM Q N d χ) := by
  unfold WeightIsBosonic
  rw [weightPolynomialCM_include]
  exact polynomialCM_isBosonic _ hχ

theorem weightPolynomialCM_zero_iff {Q N d : ℕ} (χ : WeightState Q N d) :
    weightPolynomialCM Q N d χ=0 ↔ polynomialCM (weightInclude d χ)=0 := by
  constructor
  · intro h
    rw [← weightPolynomialCM_include, h]
    exact (weightIncludeLinear Q N (d-1)).map_zero
  · intro h
    rw [weightPolynomialCM_apply, h]
    rfl

theorem polynomialWeightCoordinates_tensorRaise {Q N d : ℕ} (φ : WeightState Q N d) :
    polynomialWeightCoordinates Q N (d-1) (weightTensorRaise Q N d φ) =
      weightPolynomialCM Q N d (polynomialWeightCoordinates Q N d φ) := by
  apply weightInclude_injective Q N (d-1)
  rw [polynomialWeightCoordinates_include, weightTensorRaise_include,
    weightPolynomialCM_include, polynomialWeightCoordinates_include,
    polynomialCoordinates_tensorRaise]

def polynomialCMMatrix (Q N d : ℕ) :
    Matrix (WeightConfiguration Q N (d-1)) (WeightConfiguration Q N d) ℂ :=
  LinearMap.toMatrix' (weightPolynomialCM Q N d)

theorem polynomialCMMatrix_mulVec {Q N d : ℕ} (χ : WeightState Q N d) :
    (polynomialCMMatrix Q N d).mulVec χ = weightPolynomialCM Q N d χ :=
  LinearMap.toMatrix'_mulVec _ _

theorem tensorRaiseMatrix_zero_iff_polynomialCMMatrix {Q N d : ℕ}
    (φ : WeightState Q N d) :
    (tensorRaiseMatrix Q N d).mulVec φ=0 ↔
      (polynomialCMMatrix Q N d).mulVec (polynomialWeightCoordinates Q N d φ)=0 := by
  rw [tensorRaiseMatrix_mulVec, polynomialCMMatrix_mulVec,
    ← polynomialWeightCoordinates_tensorRaise,
    (polynomialWeightCoordinates Q N (d-1)).map_eq_zero_iff]

def polynomialHighestWeightSubspace (Q N d : ℕ) : Submodule ℂ (WeightState Q N d) :=
  (bosonicSubspace Q N).comap (weightIncludeLinear Q N d) ⊓
    LinearMap.ker (weightPolynomialCM Q N d)

theorem mem_polynomialHighestWeightSubspace {Q N d : ℕ} (χ : WeightState Q N d) :
    χ ∈ polynomialHighestWeightSubspace Q N d ↔
      WeightIsBosonic χ ∧ polynomialCM (weightInclude d χ)=0 := by
  change (WeightIsBosonic χ ∧ weightPolynomialCM Q N d χ=0) ↔ _
  rw [weightPolynomialCM_zero_iff]

theorem polynomialWeightCoordinates_highest_iff {Q N d : ℕ} (φ : WeightState Q N d) :
    polynomialWeightCoordinates Q N d φ ∈ polynomialHighestWeightSubspace Q N d ↔
      φ ∈ physicalHighestWeightSubspace Q N d := by
  change (WeightIsBosonic (polynomialWeightCoordinates Q N d φ) ∧
      weightPolynomialCM Q N d (polynomialWeightCoordinates Q N d φ)=0) ↔
    (WeightIsBosonic φ ∧ weightTensorRaise Q N d φ=0)
  rw [polynomialWeightCoordinates_bosonic_iff,
    ← polynomialWeightCoordinates_tensorRaise,
    (polynomialWeightCoordinates Q N (d-1)).map_eq_zero_iff]

/-- The highest-weight coordinate identification is constructed from the actual
raising operator, without importing a relative-basis or RREF certificate. -/
def highestWeightPolynomialEquiv (Q N d : ℕ) :
    physicalHighestWeightSubspace Q N d ≃ₗ[ℂ] polynomialHighestWeightSubspace Q N d where
  toFun φ := ⟨polynomialWeightCoordinates Q N d φ.val,
    (polynomialWeightCoordinates_highest_iff φ.val).mpr φ.property⟩
  invFun χ := ⟨(polynomialWeightCoordinates Q N d).symm χ.val, by
    apply (polynomialWeightCoordinates_highest_iff _).mp
    simpa only [LinearEquiv.apply_symm_apply] using χ.property⟩
  left_inv φ := by apply Subtype.ext; exact (polynomialWeightCoordinates Q N d).symm_apply_apply φ.val
  right_inv χ := by apply Subtype.ext; exact (polynomialWeightCoordinates Q N d).apply_symm_apply χ.val
  map_add' φ η := by apply Subtype.ext; exact (polynomialWeightCoordinates Q N d).map_add φ.val η.val
  map_smul' c φ := by
    apply Subtype.ext
    exact (polynomialWeightCoordinates Q N d).map_smul c φ.val

end
end BosonicLaughlin

import BosonicLaughlin.PolynomialCoordinates
import BosonicLaughlin.WeightCoordinates

/-! The physical/polynomial coordinate bridge on an exact finite weight block. -/
namespace BosonicLaughlin
noncomputable section

def polynomialWeightCoordinates (Q N d : ℕ) : WeightState Q N d ≃ₗ[ℂ] WeightState Q N d where
  toFun φ := fun a => (polynomialScale a.val : ℂ) * φ a
  invFun χ := fun a => (polynomialScale a.val : ℂ)⁻¹ * χ a
  left_inv φ := by funext a; simp [← mul_assoc, polynomialScale_ne_zero a.val]
  right_inv χ := by funext a; simp [← mul_assoc, polynomialScale_ne_zero a.val]
  map_add' φ χ := by funext a; simp [mul_add]
  map_smul' c φ := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem polynomialWeightCoordinates_apply {Q N d : ℕ} (φ : WeightState Q N d)
    (a : WeightConfiguration Q N d) :
    polynomialWeightCoordinates Q N d φ a = (polynomialScale a.val : ℂ) * φ a := rfl

theorem polynomialWeightCoordinates_include {Q N d : ℕ} (φ : WeightState Q N d) :
    weightInclude d (polynomialWeightCoordinates Q N d φ) =
      polynomialCoordinates Q N (weightInclude d φ) := by
  funext a
  simp only [weightInclude, polynomialCoordinates_apply]
  split_ifs <;> simp [polynomialWeightCoordinates_apply]

theorem polynomialWeightCoordinates_restrict {Q N : ℕ} (d : ℕ) (ψ : State Q N) :
    polynomialWeightCoordinates Q N d (weightRestrict d ψ) =
      weightRestrict d (polynomialCoordinates Q N ψ) := rfl

theorem polynomialWeightCoordinates_bosonic_iff {Q N d : ℕ} (φ : WeightState Q N d) :
    WeightIsBosonic (polynomialWeightCoordinates Q N d φ) ↔ WeightIsBosonic φ := by
  unfold WeightIsBosonic
  rw [polynomialWeightCoordinates_include, polynomialCoordinates_bosonic_iff]

theorem weightHamiltonian_zero_iff_include {Q N d : ℕ} (φ : WeightState Q N d) :
    weightHamiltonian Q N d φ = 0 ↔ hamiltonian (weightInclude d φ) = 0 := by
  rw [← weightHamiltonian_include]
  constructor
  · intro h
    rw [h]
    exact (weightIncludeLinear Q N d).map_zero
  · intro h
    apply weightInclude_injective Q N d
    change weightInclude d (weightHamiltonian Q N d φ) = weightInclude d 0
    rw [show weightInclude d (0 : WeightState Q N d) = 0 from
      (weightIncludeLinear Q N d).map_zero]
    exact h

/-- A finite physical block's exact zero space is the common polynomial pair kernel. -/
theorem weightHamiltonian_zero_iff_polynomialChannels {Q N d : ℕ}
    (φ : WeightState Q (N+2) d) (hφ : WeightIsBosonic φ) :
    weightHamiltonian Q (N+2) d φ = 0 ↔ ∀ p : Fin (2*Q+1),
      polynomialPairChannel p.val
        (weightInclude d (polynomialWeightCoordinates Q (N+2) d φ)) = 0 := by
  rw [weightHamiltonian_zero_iff_include,
    hamiltonian_zero_iff_polynomialPairChannels _ hφ,
    polynomialWeightCoordinates_include]

end
end BosonicLaughlin

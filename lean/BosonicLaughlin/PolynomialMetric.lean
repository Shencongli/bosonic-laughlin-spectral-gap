import BosonicLaughlin.PolynomialCoordinates

/-! The metric and actual Hamiltonian under the nonunitary polynomial coordinate change. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem polynomialCoordinates_symm_apply {Q N : ℕ} (χ : State Q N)
    (a : Configuration Q N) :
    (polynomialCoordinates Q N).symm χ a = (polynomialScale a : ℂ)⁻¹ * χ a := rfl

def polynomialInner {Q N : ℕ} (χ η : State Q N) : ℂ :=
  inner ((polynomialCoordinates Q N).symm χ) ((polynomialCoordinates Q N).symm η)

theorem polynomialInner_diagonal {Q N : ℕ} (χ η : State Q N) :
    polynomialInner χ η = ∑ a : Configuration Q N,
      star (χ a) * η a / (polynomialScale a : ℂ)^2 := by
  simp only [polynomialInner, inner, polynomialCoordinates_symm_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [star_mul, star_inv₀]
  have hs : star (polynomialScale a : ℂ) = (polynomialScale a : ℂ) := by simp
  rw [hs]
  field_simp

theorem polynomialInner_nonneg {Q N : ℕ} (χ : State Q N) :
    0 ≤ (polynomialInner χ χ).re := stateNormSq_nonneg _

theorem polynomialInner_zero_iff {Q N : ℕ} (χ : State Q N) :
    (polynomialInner χ χ).re = 0 ↔ χ = 0 := by
  change normSq ((polynomialCoordinates Q N).symm χ) = 0 ↔ χ = 0
  rw [stateNormSq_zero_iff]
  exact (polynomialCoordinates Q N).symm.map_eq_zero_iff

theorem polynomialInner_coordinates {Q N : ℕ} (ψ φ : State Q N) :
    polynomialInner (polynomialCoordinates Q N ψ) (polynomialCoordinates Q N φ) =
      inner ψ φ := by
  simp only [polynomialInner, LinearEquiv.symm_apply_apply]

def polynomialHamiltonian (Q N : ℕ) : State Q N →ₗ[ℂ] State Q N :=
  (polynomialCoordinates Q N).toLinearMap.comp
    ((hamiltonianLinear Q N).comp (polynomialCoordinates Q N).symm.toLinearMap)

theorem polynomialHamiltonian_apply {Q N : ℕ} (χ : State Q N) :
    polynomialHamiltonian Q N χ = polynomialCoordinates Q N
      (hamiltonian ((polynomialCoordinates Q N).symm χ)) := rfl

theorem polynomialHamiltonian_intertwine {Q N : ℕ} (ψ : State Q N) :
    polynomialHamiltonian Q N (polynomialCoordinates Q N ψ) =
      polynomialCoordinates Q N (hamiltonian ψ) := by
  rw [polynomialHamiltonian_apply, LinearEquiv.symm_apply_apply]

theorem polynomialHamiltonian_inner {Q N : ℕ} (χ η : State Q N) :
    polynomialInner χ (polynomialHamiltonian Q N η) =
      inner ((polynomialCoordinates Q N).symm χ)
        (hamiltonian ((polynomialCoordinates Q N).symm η)) := by
  rw [polynomialHamiltonian_apply]
  simp only [polynomialInner, LinearEquiv.symm_apply_apply]

theorem polynomialHamiltonian_hermitian {Q N : ℕ} (χ η : State Q N) :
    polynomialInner χ (polynomialHamiltonian Q N η) =
      polynomialInner (polynomialHamiltonian Q N χ) η := by
  rw [polynomialHamiltonian_inner, polynomialHamiltonian_apply]
  simp only [polynomialInner, LinearEquiv.symm_apply_apply]
  exact hamiltonian_hermitian _ _

theorem polynomialHamiltonian_kernel {Q N : ℕ} (χ : State Q (N+2))
    (hχ : IsBosonic χ) :
    polynomialHamiltonian Q (N+2) χ = 0 ↔
      ∀ p : Fin (2*Q+1), polynomialPairChannel p.val χ = 0 := by
  have hp : IsBosonic ((polynomialCoordinates Q (N+2)).symm χ) := by
    apply (polynomialCoordinates_bosonic_iff _).mp
    simpa using hχ
  rw [polynomialHamiltonian_apply, (polynomialCoordinates Q (N+2)).map_eq_zero_iff,
    hamiltonian_zero_iff_polynomialPairChannels _ hp]
  simp only [LinearEquiv.apply_symm_apply]

end
end BosonicLaughlin

import BosonicLaughlin.ThreeBodyLift

/-! Preservation of physical self-adjointness under the normalized three-body lift. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem threeBodyLiftAbove_hermitian (Q N : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3)
    (hA : ∀ χ η, IsBosonic χ → IsBosonic η → inner χ (A η) = inner (A χ) η)
    (ψ φ : State Q (N+3)) :
    inner ψ (threeBodyLiftAbove Q N A φ) = inner (threeBodyLiftAbove Q N A ψ) φ := by
  conv_rhs => rw [← inner_star, threeBodyLiftAbove_inner]
  rw [threeBodyLiftAbove_inner]
  simp only [star_mul, star_natCast, star_sum, inner_star]
  rw [mul_comm _ ((N+3).choose 3 : ℂ)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact hA _ _
    (threeBodySlice_isBosonic _ (bosonicProjection_isBosonic ψ) a)
    (threeBodySlice_isBosonic _ (bosonicProjection_isBosonic φ) a)

theorem threeBodyLift_hermitian (Q M : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3)
    (hA : ∀ χ η, IsBosonic χ → IsBosonic η → inner χ (A η) = inner (A χ) η)
    (ψ φ : State Q M) :
    inner ψ (threeBodyLift Q M A φ) = inner (threeBodyLift Q M A ψ) φ := by
  rcases M with _ | (_ | (_ | N))
  · simp [threeBodyLift, inner]
  · simp [threeBodyLift, inner]
  · simp [threeBodyLift, inner]
  · exact threeBodyLiftAbove_hermitian Q N A hA ψ φ

end
end BosonicLaughlin

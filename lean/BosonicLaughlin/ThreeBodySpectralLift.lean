import BosonicLaughlin.ThreeBodyLiftIdentity
import BosonicLaughlin.ThreeBodyCoefficient
import BosonicLaughlin.ThreeBodyLiftHermitian

/-! All-particle recoupling formula, using the actual positive three-body lift. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem normalThreeBody_eq_recoupling_lift {Q M : ℕ} (ψ : State Q M)
    (hψ : IsBosonic ψ) :
    normalThreeBodyApply ψ = threeBodyLift Q M
      ((2 : ℂ) • threeBodyAuxCoefficient Q (compressedSwapLinear Q)) ψ := by
  rw [normalThreeBody_eq_lift ψ hψ]
  have hc := threeBodyLift_congr Q M (normalThreeBodyLinear Q 3)
    ((2 : ℂ) • threeBodyAuxCoefficient Q (compressedSwapLinear Q)) (by
      intro χ hχ
      exact threeBody_normal_coefficient χ hχ)
  rw [hc]

/-- The full normal-order coefficient on every physical finite particle sector. -/
theorem normalThreeBody_spectral_lift {Q M : ℕ} (ψ : State Q M)
    (hψ : IsBosonic ψ) :
    normalThreeBodyApply ψ = ∑ z : Fin (Q+1),
      ((2 : ℂ) * (recouplingEigenvalue Q z.val : ℂ)) •
        threeBodyLift Q M (threeBodySpectralBlock Q z) ψ := by
  rw [normalThreeBody_eq_lift ψ hψ]
  have hc := threeBodyLift_congr Q M (normalThreeBodyLinear Q 3)
    (∑ z : Fin (Q+1), ((2 : ℂ) * (recouplingEigenvalue Q z.val : ℂ)) •
      threeBodySpectralBlock Q z) (by
        intro χ hχ
        have hb (z : Fin (Q+1)) : threeBodySpectralBlock Q z χ =
            threeBodyMap (auxSpectralProject z (threeBodyAdjoint χ)) := rfl
        simpa only [normalThreeBodyLinear, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.sum_apply, LinearMap.smul_apply, hb] using
          threeBody_normal_spectral_resolution χ hχ)
  rw [hc]
  change (threeBodyLiftLinear Q M
    (∑ z : Fin (Q+1), ((2 : ℂ) * (recouplingEigenvalue Q z.val : ℂ)) •
      threeBodySpectralBlock Q z)) ψ = _
  rw [map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

theorem threeBodyAux_lift_nonneg (Q M : ℕ)
    (A : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q)
    (hA : ∀ φ : ThreeBodyAux Q,
      0 ≤ (∑ p : Fin (2*Q+1), ∑ k : Orbital Q, star (φ p k) * A φ p k).re)
    (ψ : State Q M) :
    0 ≤ (inner ψ (threeBodyLift Q M (threeBodyAuxCoefficient Q A) ψ)).re :=
  threeBodyLift_nonneg Q M _ (threeBodyAuxCoefficient_nonneg Q A hA) ψ

theorem threeBodySpectralBlock_lift_nonneg (Q M : ℕ) (z : Fin (Q+1))
    (ψ : State Q M) :
    0 ≤ (inner ψ (threeBodyLift Q M (threeBodySpectralBlock Q z) ψ)).re :=
  threeBodyLift_nonneg Q M _ (threeBodySpectralBlock_nonneg Q z) ψ

theorem threeBodySpectralBlock_lift_hermitian (Q M : ℕ) (z : Fin (Q+1))
    (ψ φ : State Q M) :
    inner ψ (threeBodyLift Q M (threeBodySpectralBlock Q z) φ) =
      inner (threeBodyLift Q M (threeBodySpectralBlock Q z) ψ) φ :=
  threeBodyLift_hermitian Q M _ (threeBodySpectralBlock_hermitian Q z) ψ φ

/-- H² with the three-body coefficient fully connected to its lifted spectral blocks. -/
theorem hamiltonian_square_lifted_recoupling {Q M : ℕ} (ψ : State Q M)
    (hψ : IsBosonic ψ) :
    hamiltonian (hamiltonian ψ) = hamiltonian ψ +
      (∑ z : Fin (Q+1), ((2 : ℂ) * (recouplingEigenvalue Q z.val : ℂ)) •
        threeBodyLift Q M (threeBodySpectralBlock Q z) ψ) + normalFourBodyApply ψ := by
  rw [hamiltonian_normal_order, normalThreeBody_spectral_lift ψ hψ]

end
end BosonicLaughlin

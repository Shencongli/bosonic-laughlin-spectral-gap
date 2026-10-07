import BosonicLaughlin.OccupationPairChannels
import BosonicLaughlin.OccupationWeightCoordinates

/-! The factorial polynomial occupation basis is complete in the bosonic space.
The positive factorial rescaling is explicitly invertible and is not unitary. -/
namespace BosonicLaughlin
noncomputable section

def occupationFactorialCoordinates (Q N : ℕ) : OccupationState Q N ≃ₗ[ℂ] OccupationState Q N where
  toFun c := fun A => (occupationFactorial A : ℂ) * c A
  invFun e := fun A => (occupationFactorial A : ℂ)⁻¹ * e A
  left_inv c := by
    funext A
    have hn : (occupationFactorial A : ℂ) ≠ 0 := by exact_mod_cast (occupationFactorial_pos A).ne'
    simp [hn]
  right_inv e := by
    funext A
    have hn : (occupationFactorial A : ℂ) ≠ 0 := by exact_mod_cast (occupationFactorial_pos A).ne'
    simp [hn]
  map_add' c e := by funext A; simp [mul_add]
  map_smul' z c := by
    funext A
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def polynomialOccupationCoordinateEquiv (Q N : ℕ) :
    OccupationState Q N ≃ₗ[ℂ] bosonicSubspace Q N :=
  (occupationFactorialCoordinates Q N).trans (occupationCoordinateEquiv Q N)

theorem polynomialOccupationCoordinateEquiv_apply {Q N : ℕ} (c : OccupationState Q N) :
    (polynomialOccupationCoordinateEquiv Q N c).val = polynomialOccupationInclude c := rfl

theorem polynomialOccupationInclude_surjective_bosonic {Q N : ℕ}
    (ψ : State Q N) (hψ : IsBosonic ψ) : ∃ c, polynomialOccupationInclude c = ψ := by
  refine ⟨(polynomialOccupationCoordinateEquiv Q N).symm ⟨ψ,hψ⟩, ?_⟩
  exact congrArg Subtype.val ((polynomialOccupationCoordinateEquiv Q N).apply_symm_apply ⟨ψ,hψ⟩)

def occupationWeightFactorialCoordinates (Q N d : ℕ) :
    WeightOccupationState Q N d ≃ₗ[ℂ] WeightOccupationState Q N d where
  toFun c := fun A => (occupationFactorial A.val : ℂ) * c A
  invFun e := fun A => (occupationFactorial A.val : ℂ)⁻¹ * e A
  left_inv c := by
    funext A
    have hn : (occupationFactorial A.val : ℂ) ≠ 0 := by exact_mod_cast (occupationFactorial_pos A.val).ne'
    simp [hn]
  right_inv e := by
    funext A
    have hn : (occupationFactorial A.val : ℂ) ≠ 0 := by exact_mod_cast (occupationFactorial_pos A.val).ne'
    simp [hn]
  map_add' c e := by funext A; simp [mul_add]
  map_smul' z c := by
    funext A
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def polynomialWeightOccupationInclude {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    WeightState Q N d := weightOccupationInclude (occupationWeightFactorialCoordinates Q N d c)

def polynomialWeightOccupationIncludeLinear (Q N d : ℕ) :
    WeightOccupationState Q N d →ₗ[ℂ] WeightState Q N d :=
  (weightOccupationIncludeLinear Q N d).comp (occupationWeightFactorialCoordinates Q N d).toLinearMap

theorem polynomialWeightOccupationInclude_isBosonic {Q N d : ℕ}
    (c : WeightOccupationState Q N d) : WeightIsBosonic (polynomialWeightOccupationInclude c) :=
  weightOccupationInclude_isBosonic _

theorem polynomialWeightOccupationInclude_injective (Q N d : ℕ) :
    Function.Injective (@polynomialWeightOccupationInclude Q N d) :=
  (weightOccupationInclude_injective Q N d).comp (occupationWeightFactorialCoordinates Q N d).injective

theorem polynomialWeightOccupationInclude_surjective_bosonic {Q N d : ℕ}
    (φ : WeightState Q N d) (hφ : WeightIsBosonic φ) :
    ∃ c, polynomialWeightOccupationInclude c = φ := by
  obtain ⟨e,he⟩ := weightOccupationInclude_surjective_bosonic φ hφ
  refine ⟨(occupationWeightFactorialCoordinates Q N d).symm e, ?_⟩
  simp only [polynomialWeightOccupationInclude, LinearEquiv.apply_symm_apply, he]

theorem polynomialWeightOccupationInclude_include {Q N d : ℕ}
    (c : WeightOccupationState Q N d) :
    weightInclude d (polynomialWeightOccupationInclude c) =
      polynomialOccupationInclude (occupationWeightExtend d c) := by
  funext a
  simp only [weightInclude, polynomialOccupationInclude, occupationWeightExtend,
    occupationOfConfiguration_weight]
  split_ifs with ha
  · rfl
  · simp

end
end BosonicLaughlin

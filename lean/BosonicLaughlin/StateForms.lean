import BosonicLaughlin.Occupation
import BosonicLaughlin.NormalOrdering

/-! Coordinate inner-product facts and the independently defined three-body operator. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem stateInner_add_right {Q N : ℕ} (ψ φ χ : State Q N) :
    inner ψ (φ + χ) = inner ψ φ + inner ψ χ := by
  simp [inner, mul_add, Finset.sum_add_distrib]

theorem stateInner_smul_right {Q N : ℕ} (c : ℂ) (ψ φ : State Q N) :
    inner ψ (c • φ) = c * inner ψ φ := by
  simp only [inner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem stateInner_smul_left {Q N : ℕ} (c : ℂ) (ψ φ : State Q N) :
    inner (c • ψ) φ = star c * inner ψ φ := by
  simp only [inner, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem stateInner_ext {Q N : ℕ} (φ χ : State Q N)
    (h : ∀ ψ, inner ψ φ = inner ψ χ) : φ = χ := by
  classical
  funext a
  have ha := h (fun b => if b = a then 1 else 0)
  simpa [inner] using ha

theorem normalThreeBody_add {Q N : ℕ} (ψ φ : State Q N) :
    normalThreeBodyApply (ψ + φ) = normalThreeBodyApply ψ + normalThreeBodyApply φ := by
  classical
  funext a
  simp only [normalThreeBodyApply, pairApply_add, Pi.add_apply]
  simp only [ite_add_zero, Finset.sum_add_distrib]

theorem normalThreeBody_smul {Q N : ℕ} (c : ℂ) (ψ : State Q N) :
    normalThreeBodyApply (c • ψ) = c • normalThreeBodyApply ψ := by
  classical
  funext a
  simp only [normalThreeBodyApply, pairApply_smul, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, mul_ite, mul_zero]

def normalThreeBodyLinear (Q N : ℕ) : State Q N →ₗ[ℂ] State Q N where
  toFun := normalThreeBodyApply
  map_add' := normalThreeBody_add
  map_smul' := normalThreeBody_smul

end
end BosonicLaughlin

import BosonicLaughlin.TensorSpin
import BosonicLaughlin.PolynomialHighestWeight

/-! Exact total lowering in the factorial polynomial coordinates.
At an output orbital i>0, the source orbital is i-1 and the coefficient
is Q-(i-1). Boundary terms are included explicitly. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def polynomialLower {Q N : ℕ} (χ : State Q N) : State Q N := fun a =>
  ∑ k : Fin N, if h : 0<(a k).val then
    ((Q-((a k).val-1) : ℕ) : ℂ)*χ (Function.update a k ⟨(a k).val-1, by omega⟩) else 0

theorem polynomialLower_add {Q N : ℕ} (χ η : State Q N) :
    polynomialLower (χ+η)=polynomialLower χ+polynomialLower η := by
  funext a
  simp only [polynomialLower, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp [mul_add]

theorem polynomialLower_smul {Q N : ℕ} (c : ℂ) (χ : State Q N) :
    polynomialLower (c • χ)=c • polynomialLower χ := by
  funext a
  simp only [polynomialLower, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

theorem polynomialScale_lower_coefficient {Q N : ℕ} (a : Configuration Q N)
    (k : Fin N) (h : 0<(a k).val) :
    polynomialScale a * spinRaiseCoeff Q ((a k).val-1)=
      ((Q-((a k).val-1) : ℕ) : ℝ)*
        polynomialScale (Function.update a k ⟨(a k).val-1, by omega⟩) := by
  rw [polynomialScale_eq_mul_erase a k, polynomialScale_update]
  have he := binomialRoot_ladder_left Q ((a k).val-1)
  change spinRaiseCoeff Q ((a k).val-1)*binomialRoot Q ((a k).val-1+1) = _ at he
  rw [Nat.sub_add_cancel (by omega : 1≤(a k).val)] at he
  linear_combination (∏ j ∈ (univ : Finset (Fin N)).erase k, binomialRoot Q (a j).val)*he

theorem polynomialCoordinates_tensorLower {Q N : ℕ} (ψ : State Q N) :
    polynomialCoordinates Q N (tensorLower ψ)=polynomialLower (polynomialCoordinates Q N ψ) := by
  funext a
  simp only [polynomialCoordinates_apply, tensorLower_apply, polynomialLower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · rw [← mul_assoc, ← Complex.ofReal_mul, polynomialScale_lower_coefficient a k hk]
    push_cast
    ring
  · simp

end
end BosonicLaughlin

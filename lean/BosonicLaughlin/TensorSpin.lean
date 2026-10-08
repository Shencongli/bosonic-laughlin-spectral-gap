import BosonicLaughlin.TensorSlotLinear
import BosonicLaughlin.AngularCommutators

/-! Actual total angular momentum on the spherical N-particle tensor space.
Orbital labels are deficits; tensorWeight is 2 J_z and tensorLower is J_-.
No occupation cutoff or auxiliary-space substitution is used. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def tensorLowerLinear (Q N : ℕ) : State Q N →ₗ[ℂ] State Q N :=
  tensorSumLinear Q N (spinLowerLinear Q)

def tensorLower {Q N : ℕ} (ψ : State Q N) : State Q N := tensorLowerLinear Q N ψ

def tensorWeightLinear (Q N : ℕ) : State Q N →ₗ[ℂ] State Q N where
  toFun ψ a := ((N*Q : ℕ) - 2*(configurationWeight a : ℂ)) * ψ a
  map_add' ψ φ := by funext a; simp [mul_add]
  map_smul' c ψ := by funext a; simp [mul_left_comm]

def tensorWeight {Q N : ℕ} (ψ : State Q N) : State Q N := tensorWeightLinear Q N ψ

theorem tensorLower_apply {Q N : ℕ} (ψ : State Q N) (a : Configuration Q N) :
    tensorLower ψ a = ∑ k : Fin N, if h : 0<(a k).val then
      (spinRaiseCoeff Q ((a k).val-1) : ℂ) *
        ψ (Function.update a k ⟨(a k).val-1, by omega⟩) else 0 := by
  simp [tensorLower, tensorLowerLinear, tensorSumLinear_apply, spinLowerLinear, spinLower]

theorem tensorWeight_apply {Q N : ℕ} (ψ : State Q N) (a : Configuration Q N) :
    tensorWeight ψ a = ((N*Q : ℕ) - 2*(configurationWeight a : ℂ)) * ψ a := rfl

theorem tensorRaise_eq_tensorSum (Q N : ℕ) :
    tensorRaiseLinear Q N = tensorSumLinear Q N (spinRaiseLinear Q) := by
  apply LinearMap.ext
  intro ψ
  funext a
  simp [tensorRaiseLinear, tensorRaise, tensorSumLinear_apply, spinRaiseLinear, spinRaise]

def spinWeightLinear (Q : ℕ) : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ) where
  toFun := spinWeight
  map_add' u v := by funext i; simp [spinWeight, mul_add]
  map_smul' c u := by funext i; simp [spinWeight, mul_left_comm]

theorem tensorWeight_eq_tensorSum (Q N : ℕ) :
    tensorWeightLinear Q N = tensorSumLinear Q N (spinWeightLinear Q) := by
  apply LinearMap.ext
  intro ψ
  funext a
  simp only [tensorWeightLinear, LinearMap.coe_mk, AddHom.coe_mk, tensorSumLinear_apply,
    spinWeightLinear, spinWeight, Function.update_eq_self]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  simp [configurationWeight, Finset.mul_sum, Nat.cast_sum]

theorem tensorRaise_lower_commutator {Q N : ℕ} (ψ : State Q N) :
    tensorRaise (tensorLower ψ) - tensorLower (tensorRaise ψ) = tensorWeight ψ := by
  have hs : spinRaiseLinear Q * spinLowerLinear Q - spinLowerLinear Q * spinRaiseLinear Q = spinWeightLinear Q := by
    apply LinearMap.ext
    exact spinRaise_lower_commutator
  have h := tensorSumLinear_commutator Q N (spinRaiseLinear Q) (spinLowerLinear Q)
  rw [hs, ← tensorWeight_eq_tensorSum, ← tensorRaise_eq_tensorSum] at h
  exact LinearMap.congr_fun h ψ

theorem tensorWeight_lower_commutator {Q N : ℕ} (ψ : State Q N) :
    tensorWeight (tensorLower ψ) - tensorLower (tensorWeight ψ) = (-2 : ℂ) • tensorLower ψ := by
  have hs : spinWeightLinear Q * spinLowerLinear Q - spinLowerLinear Q * spinWeightLinear Q = (-2 : ℂ) • spinLowerLinear Q := by
    apply LinearMap.ext
    exact spinWeight_lower_commutator
  have h := tensorSumLinear_commutator Q N (spinWeightLinear Q) (spinLowerLinear Q)
  rw [hs, ← tensorWeight_eq_tensorSum] at h
  have hsum : tensorSumLinear Q N ((-2 : ℂ) • spinLowerLinear Q) =
      (-2 : ℂ) • tensorLowerLinear Q N := by
    unfold tensorSumLinear tensorLowerLinear
    simp only [tensorSumLinear, slotLinear_smul, Finset.smul_sum]
  rw [hsum] at h
  exact LinearMap.congr_fun h ψ

theorem tensorRaise_adjoint {Q N : ℕ} (ψ φ : State Q N) :
    inner ψ (tensorRaise φ) = inner (tensorLower ψ) φ := by
  change inner ψ (tensorRaiseLinear Q N φ) = _
  rw [tensorRaise_eq_tensorSum]
  exact tensorSumLinear_adjoint _ _ spinRaise_adjoint ψ φ

theorem tensorLower_adjoint {Q N : ℕ} (ψ φ : State Q N) :
    inner ψ (tensorLower φ) = inner (tensorRaise ψ) φ := by
  have h := congrArg star (tensorRaise_adjoint φ ψ)
  rw [inner_star, inner_star] at h
  exact h.symm

theorem tensorLower_isBosonic {Q N : ℕ} (ψ : State Q N) (hψ : IsBosonic ψ) :
    IsBosonic (tensorLower ψ) := by
  intro σ a
  simp only [tensorLower_apply, Function.comp_apply, update_permute, hψ σ]
  exact Equiv.sum_comp σ (fun k => if h : 0<(a k).val then
    (spinRaiseCoeff Q ((a k).val-1) : ℂ) *
      ψ (Function.update a k ⟨(a k).val-1, by omega⟩) else 0)

theorem tensorLower_weightSupported {Q N : ℕ} (d : ℕ) (ψ : State Q N)
    (hψ : WeightSupported d ψ) : WeightSupported (d+1) (tensorLower ψ) := by
  intro a ha
  rw [tensorLower_apply]
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hk
  · have he := configurationWeight_update a k (⟨(a k).val-1, by omega⟩ : Orbital Q)
    have hz : ψ (Function.update a k ⟨(a k).val-1, by omega⟩)=0 := by
      apply hψ
      change _ + (a k).val = _ + ((a k).val-1) at he
      omega
    rw [hz, mul_zero]
  · rfl

theorem tensorWeight_of_supported {Q N d : ℕ} (ψ : State Q N)
    (hψ : WeightSupported d ψ) : tensorWeight ψ = ((N*Q : ℕ) - 2*(d : ℂ)) • ψ := by
  funext a
  by_cases ha : configurationWeight a=d
  · simp [tensorWeight_apply, ha]
  · simp [tensorWeight_apply, hψ a ha]

end
end BosonicLaughlin

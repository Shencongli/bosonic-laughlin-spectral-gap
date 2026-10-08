import BosonicLaughlin.TensorHighestWeight
import BosonicLaughlin.CertificateRowNormalOrder

/-! Lifting a one-orbital linear map to a specified ordered tensor slot.
The remaining slots are unchanged. These maps act on the full tensor space;
Bose symmetry is imposed only when restricting their sum to physical states. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def slotLinear {Q N : ℕ} (i : Fin N)
    (A : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ)) : State Q N →ₗ[ℂ] State Q N where
  toFun ψ a := A (fun x => ψ (Function.update a i x)) (a i)
  map_add' ψ φ := by
    funext a
    change A ((fun x => ψ (Function.update a i x)) + (fun x => φ (Function.update a i x))) (a i) = _
    rw [map_add]
    rfl
  map_smul' c ψ := by
    funext a
    change A (c • (fun x => ψ (Function.update a i x))) (a i) = _
    rw [map_smul]
    rfl

theorem slotLinear_apply {Q N : ℕ} (i : Fin N)
    (A : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ)) (ψ : State Q N) (a : Configuration Q N) :
    slotLinear i A ψ a = A (fun x => ψ (Function.update a i x)) (a i) := rfl

theorem slotLinear_add {Q N : ℕ} (i : Fin N)
    (A B : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ)) :
    slotLinear i (A+B) = slotLinear i A + slotLinear i B := rfl

theorem slotLinear_sub {Q N : ℕ} (i : Fin N)
    (A B : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ)) :
    slotLinear i (A-B) = slotLinear i A - slotLinear i B := rfl

theorem slotLinear_smul {Q N : ℕ} (i : Fin N) (c : ℂ)
    (A : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ)) :
    slotLinear i (c • A) = c • slotLinear i A := rfl

theorem slotLinear_mul {Q N : ℕ} (i : Fin N)
    (A B : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ)) :
    slotLinear i (A*B) = slotLinear i A * slotLinear i B := by
  apply LinearMap.ext
  intro ψ
  funext a
  simp [slotLinear_apply, Module.End.mul_apply, Function.update_idem]

theorem slotLinear_matrix {Q N : ℕ} (i : Fin N)
    (A : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ)) (ψ : State Q N) (a : Configuration Q N) :
    slotLinear i A ψ a = ∑ x, LinearMap.toMatrix' A (a i) x * ψ (Function.update a i x) := by
  exact congrFun (LinearMap.toMatrix'_mulVec A (fun x => ψ (Function.update a i x))).symm (a i)

theorem slotLinear_commute {Q N : ℕ} (i j : Fin N) (hij : i≠j)
    (A B : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ)) :
    slotLinear i A * slotLinear j B = slotLinear j B * slotLinear i A := by
  apply LinearMap.ext
  intro ψ
  funext a
  simp only [Module.End.mul_apply, slotLinear_matrix, Function.update_of_ne hij,
    Function.update_of_ne hij.symm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [Function.update_comm hij]
  ring

theorem slotLinear_adjoint {Q N : ℕ} (i : Fin N)
    (A B : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ))
    (hAB : ∀ u v, (∑ x, star (u x) * A v x) = ∑ x, star (B u x) * v x)
    (ψ φ : State Q N) : inner ψ (slotLinear i A φ) = inner (slotLinear i B ψ) φ := by
  unfold inner
  rw [sum_configurations_slot i, sum_configurations_slot i]
  apply Finset.sum_congr rfl
  intro s _
  have hu (x y : Orbital Q) : Function.update (slotConfiguration i s x) i y = slotConfiguration i s y := by
    rw [← slotConfiguration_spectator, slotSpectator_configuration]
  simp only [slotLinear_apply, slotConfiguration_at_slot, hu]
  exact hAB (fun x => ψ (slotConfiguration i s x)) (fun x => φ (slotConfiguration i s x))

def tensorSumLinear (Q N : ℕ)
    (A : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ)) : State Q N →ₗ[ℂ] State Q N :=
  ∑ i : Fin N, slotLinear i A

theorem tensorSumLinear_apply {Q N : ℕ}
    (A : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ)) (ψ : State Q N) (a : Configuration Q N) :
    tensorSumLinear Q N A ψ a = ∑ i, A (fun x => ψ (Function.update a i x)) (a i) := by
  simp [tensorSumLinear, slotLinear_apply]

theorem tensorSumLinear_commutator (Q N : ℕ)
    (A B : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ)) :
    tensorSumLinear Q N A * tensorSumLinear Q N B -
      tensorSumLinear Q N B * tensorSumLinear Q N A = tensorSumLinear Q N (A*B-B*A) := by
  unfold tensorSumLinear
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => slotLinear i B * slotLinear j A)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · rw [slotLinear_sub, slotLinear_mul, slotLinear_mul]
  · intro j _ hji
    rw [slotLinear_commute i j (Ne.symm hji), sub_self]
  · simp

theorem tensorSumLinear_adjoint {Q N : ℕ}
    (A B : (Orbital Q → ℂ) →ₗ[ℂ] (Orbital Q → ℂ))
    (hAB : ∀ u v, (∑ x, star (u x) * A v x) = ∑ x, star (B u x) * v x)
    (ψ φ : State Q N) :
    inner ψ (tensorSumLinear Q N A φ) = inner (tensorSumLinear Q N B ψ) φ := by
  simp only [tensorSumLinear, LinearMap.sum_apply, stateInner_sum_right, stateInner_sum_left]
  exact Finset.sum_congr rfl (fun i _ => slotLinear_adjoint i A B hAB ψ φ)

end
end BosonicLaughlin

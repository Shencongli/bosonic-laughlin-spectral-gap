import BosonicLaughlin.Model
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace BosonicLaughlin
noncomputable section
open Finset Matrix

/-- Tensor-slot coordinates remaining after one orbital is specified. -/
abbrev SlotSpectator (Q N : ℕ) (i : Fin N) := {k : Fin N // k ≠ i} → Orbital Q

def slotSpectator {Q N : ℕ} (i : Fin N) (a : Configuration Q N) : SlotSpectator Q N i :=
  fun k => a k

def slotConfiguration {Q N : ℕ} (i : Fin N) (s : SlotSpectator Q N i)
    (x : Orbital Q) : Configuration Q N :=
  fun k => if h : k = i then x else s ⟨k, h⟩

@[simp] theorem slotConfiguration_at_slot {Q N : ℕ} (i : Fin N)
    (s : SlotSpectator Q N i) (x : Orbital Q) :
    slotConfiguration i s x i = x := by simp [slotConfiguration]

@[simp] theorem slotSpectator_configuration {Q N : ℕ} (i : Fin N)
    (s : SlotSpectator Q N i) (x : Orbital Q) :
    slotSpectator i (slotConfiguration i s x) = s := by
  funext k
  simp [slotSpectator, slotConfiguration, k.property]

theorem slotConfiguration_spectator {Q N : ℕ} (i : Fin N)
    (a : Configuration Q N) (x : Orbital Q) :
    slotConfiguration i (slotSpectator i a) x = Function.update a i x := by
  funext k
  by_cases h : k = i
  · subst k; simp [slotConfiguration]
  · simp [slotConfiguration, slotSpectator, h]

def slotConfigurationEquiv {Q N : ℕ} (i : Fin N) :
    (SlotSpectator Q N i × Orbital Q) ≃ Configuration Q N where
  toFun := fun z => slotConfiguration i z.1 z.2
  invFun := fun a => (slotSpectator i a, a i)
  left_inv := by intro ⟨s,x⟩; simp
  right_inv := by
    intro a
    change slotConfiguration i (slotSpectator i a) (a i) = a
    rw [slotConfiguration_spectator]
    exact Function.update_eq_self i a

theorem sum_configurations_slot {Q N : ℕ} (i : Fin N)
    {A : Type*} [AddCommMonoid A] (f : Configuration Q N → A) :
    ∑ a, f a = ∑ s : SlotSpectator Q N i,
      ∑ x : Orbital Q, f (slotConfiguration i s x) := by
  rw [← (slotConfigurationEquiv i).sum_comp f]
  simp only [Fintype.sum_prod_type, slotConfigurationEquiv, Equiv.coe_fn_mk]

/-- The one-slot rank-one projector kernel, with the other tensor slots unchanged. -/
def modeMatrix {Q N : ℕ} (i : Fin N) (β : Orbital Q → ℂ) :
    Matrix (Configuration Q N) (Configuration Q N) ℂ :=
  fun a b => if slotSpectator i a = slotSpectator i b
    then β (a i) * star (β (b i)) else 0

def modeApply {Q N : ℕ} (i : Fin N) (β : Orbital Q → ℂ) (ψ : State Q N) :
    State Q N := fun a => β (a i) * ∑ x, star (β x) * ψ (Function.update a i x)

theorem modeMatrix_mulVec {Q N : ℕ} (i : Fin N) (β : Orbital Q → ℂ)
    (ψ : State Q N) : modeMatrix i β *ᵥ ψ = modeApply i β ψ := by
  funext a
  simp only [Matrix.mulVec, dotProduct, modeMatrix, modeApply]
  rw [sum_configurations_slot i]
  simp only [slotSpectator_configuration, slotConfiguration_at_slot]
  simp_rw [ite_mul, zero_mul, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    slotConfiguration_spectator, Finset.mul_sum, mul_assoc]

theorem modeMatrix_hermitian {Q N : ℕ} (i : Fin N) (β : Orbital Q → ℂ) :
    (modeMatrix i β).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, modeMatrix]
  by_cases h : slotSpectator i a = slotSpectator i b
  · simp only [ite_eq_left h, ite_eq_left h.symm, star_mul, star_star]
  · have h' : slotSpectator i b ≠ slotSpectator i a := Ne.symm h
    simp [h, h']

theorem modeApply_idempotent {Q N : ℕ} (i : Fin N) (β : Orbital Q → ℂ)
    (hβ : ∑ x, Complex.normSq (β x) = 1) (ψ : State Q N) :
    modeApply i β (modeApply i β ψ) = modeApply i β ψ := by
  have hb : ∑ x, star (β x) * β x = (1 : ℂ) := by
    simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.ofReal_sum, hβ, Complex.ofReal_one]
  funext a
  simp only [modeApply, Function.update_self, Function.update_idem]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [hb, one_mul]

theorem modeMatrix_idempotent {Q N : ℕ} (i : Fin N) (β : Orbital Q → ℂ)
    (hβ : ∑ x, Complex.normSq (β x) = 1) :
    modeMatrix i β * modeMatrix i β = modeMatrix i β := by
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  rw [← Matrix.mulVec_mulVec, modeMatrix_mulVec, modeMatrix_mulVec,
    modeApply_idempotent i β hβ]

theorem modeApply_commute_of_ne {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (β γ : Orbital Q → ℂ) (ψ : State Q N) :
    modeApply i β (modeApply j γ ψ) = modeApply j γ (modeApply i β ψ) := by
  funext a
  simp only [modeApply, Function.update_of_ne hij, Function.update_of_ne hij.symm]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [Function.update_comm hij]
  ring

/-- Projectors acting in different tensor slots commute, including arbitrary orbitals. -/
theorem modeMatrix_commute {Q N : ℕ} (i j : Fin N) (β : Orbital Q → ℂ) :
    Commute (modeMatrix i β) (modeMatrix j β) := by
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  change modeMatrix i β * modeMatrix j β = modeMatrix j β * modeMatrix i β
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  simp only [← Matrix.mulVec_mulVec, modeMatrix_mulVec]
  exact modeApply_commute_of_ne i j hij β β ψ

end
end BosonicLaughlin

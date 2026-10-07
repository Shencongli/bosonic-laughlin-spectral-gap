import BosonicLaughlin.Model
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Nat.Choose.Cast

namespace BosonicLaughlin
noncomputable section
open Finset

/-- The standard bosonic annihilation map in normalized symmetric tensor coordinates.
Its domain has N+1 particles; its codomain has N particles. -/
def annihilate {Q N : ℕ} (α : Orbital Q → ℂ) (ψ : State Q (N+1)) : State Q N :=
  fun a => (Real.sqrt (N+1) : ℂ) * ∑ x : Orbital Q, star (α x) * ψ (Fin.cons x a)

def annihilateLinear (Q N : ℕ) (α : Orbital Q → ℂ) :
    State Q (N+1) →ₗ[ℂ] State Q N where
  toFun := annihilate α
  map_add' := by
    intro ψ φ
    funext a
    simp [annihilate, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c ψ
    funext a
    simp only [annihilate, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (star (α _)) c, ← Finset.mul_sum]
    ring

/-- The normalized double annihilator Bα=aα²/√2 in fixed particle sectors.
The factor is sqrt(choose(N+2,2)); no flux or orbital truncation occurs. -/
def pairAnnihilate {Q N : ℕ} (α : Orbital Q → ℂ) (ψ : State Q (N+2)) : State Q N :=
  fun a => (Real.sqrt ((N+2).choose 2) : ℂ) *
    ∑ x : Orbital Q, ∑ y : Orbital Q,
      star (α x) * star (α y) * ψ (Fin.cons x (Fin.cons y a))

def pairAnnihilateLinear (Q N : ℕ) (α : Orbital Q → ℂ) :
    State Q (N+2) →ₗ[ℂ] State Q N where
  toFun := pairAnnihilate α
  map_add' := by
    intro ψ φ
    funext a
    simp [pairAnnihilate, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c ψ
    funext a
    simp only [pairAnnihilate, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (star (α _) * star (α _)) c, ← Finset.mul_sum]
    ring

/-- Extend a particle permutation by fixing the newly inserted first tensor slot. -/
def fixFirstPermutation {N : ℕ} (σ : Equiv.Perm (Fin N)) : Equiv.Perm (Fin (N+1)) where
  toFun := Fin.cases 0 (fun k => (σ k).succ)
  invFun := Fin.cases 0 (fun k => (σ.symm k).succ)
  left_inv := by
    intro k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  right_inv := by
    intro k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp

theorem cons_comp_fixFirst {Q N : ℕ} (x : Orbital Q) (a : Configuration Q N)
    (σ : Equiv.Perm (Fin N)) :
    Fin.cons x (a ∘ σ) = Fin.cons x a ∘ fixFirstPermutation σ := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k <;> simp [fixFirstPermutation, Function.comp_def]

theorem annihilate_isBosonic {Q N : ℕ} (α : Orbital Q → ℂ)
    (ψ : State Q (N+1)) (hψ : IsBosonic ψ) : IsBosonic (annihilate α ψ) := by
  intro σ a
  simp only [annihilate, cons_comp_fixFirst, hψ (fixFirstPermutation σ)]

theorem pairAnnihilate_isBosonic {Q N : ℕ} (α : Orbital Q → ℂ)
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) : IsBosonic (pairAnnihilate α ψ) := by
  intro σ a
  simp only [pairAnnihilate, cons_comp_fixFirst,
    hψ (fixFirstPermutation (fixFirstPermutation σ))]

theorem pairAnnihilate_factor (N : ℕ) :
    Real.sqrt ((N+2).choose 2) =
      Real.sqrt (N+1) * Real.sqrt (N+2) / Real.sqrt 2 := by
  have hn : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  have hc : (((N+2).choose 2 : ℕ) : ℝ) = ((N : ℝ)+1)*((N : ℝ)+2)/2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  rw [hc, Real.sqrt_div (by positivity), Real.sqrt_mul hn]

theorem pairAnnihilate_eq_annihilate_twice {Q N : ℕ} (α : Orbital Q → ℂ)
    (ψ : State Q (N+2)) :
    pairAnnihilate α ψ = (1 / (Real.sqrt 2 : ℂ)) • annihilate α (annihilate α ψ) := by
  funext a
  simp only [pairAnnihilate, annihilate, Pi.smul_apply, smul_eq_mul]
  rw [pairAnnihilate_factor N]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [Nat.cast_add, Nat.cast_one]
  have hN : (N : ℝ)+1+1 = (N : ℝ)+2 := by ring
  rw [hN]
  ring

end
end BosonicLaughlin

import BosonicLaughlin.Pair
import Mathlib.Basic.Complex.Basic

/-!
Full spherical LLL model, in the orthonormal orbital basis e_0,...,e_Q.
The ambient tensor-product coordinates are functions on configurations.
The physical bosonic sector is specified by `IsBosonic` (permutation invariance).
No orbital, particle-number, or polynomial-degree truncation is imposed.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

abbrev Orbital (Q : ℕ) := Fin (Q+1)
abbrev Configuration (Q N : ℕ) := Fin N → Orbital Q
abbrev State (Q N : ℕ) := Configuration Q N → ℂ

def IsBosonic {Q N : ℕ} (ψ : State Q N) : Prop :=
  ∀ (σ : Equiv.Perm (Fin N)) (a : Configuration Q N), ψ (a ∘ σ) = ψ a

/-- The symmetric tensor subspace is the physical fixed-N bosonic sector. -/
def bosonicSubspace (Q N : ℕ) : Submodule ℂ (State Q N) where
  carrier := {ψ | IsBosonic ψ}
  zero_mem' := by intro σ a; rfl
  add_mem' := by
    intro ψ φ hψ hφ σ a
    simp only [Pi.add_apply, hψ σ a, hφ σ a]
  smul_mem' := by
    intro c ψ hψ σ a
    simp only [Pi.smul_apply, hψ σ a]

/-- Coefficient of the normalized pair-spin-Q vector with orbital sum p. -/
def pairVector (Q p : ℕ) (x y : Orbital Q) : ℝ :=
  if x.val + y.val = p then pairCoefficient Q p x.val else 0

theorem pairVector_exchange (Q p : ℕ) (x y : Orbital Q) :
    pairVector Q p x y = pairVector Q p y x := by
  unfold pairVector
  by_cases h : x.val + y.val = p
  · have h' : y.val + x.val = p := by omega
    rw [ite_eq_left h, ite_eq_left h']
    have hx : x.val ≤ p := by omega
    have hy : p-x.val = y.val := by omega
    simpa only [hy] using (pairCoefficient_exchange Q p x.val hx).symm
  · have h' : ¬ y.val + x.val = p := by omega
    rw [ite_eq_right h, ite_eq_right h']

def replacePair {Q N : ℕ} (a : Configuration Q N) (i j : Fin N)
    (x y : Orbital Q) : Configuration Q N :=
  Function.update (Function.update a i x) j y

/-- Action of the two-particle V₀ kernel in tensor slots i and j.
Only distinct slots are used in `hamiltonian`. -/
def pairApply {Q N : ℕ} (i j : Fin N) (ψ : State Q N) : State Q N :=
  fun a => ∑ p : Fin (2*Q+1),
    (pairVector Q p.val (a i) (a j) : ℂ) *
      ∑ x : Orbital Q, ∑ y : Orbital Q,
        (pairVector Q p.val x y : ℂ) * ψ (replacePair a i j x y)

/-- Sum over unordered pairs, with pair coefficient one. -/
def hamiltonian {Q N : ℕ} (ψ : State Q N) : State Q N :=
  fun a => ∑ i : Fin N, ∑ j : Fin N, if i < j then pairApply i j ψ a else 0

def inner {Q N : ℕ} (ψ φ : State Q N) : ℂ :=
  ∑ a : Configuration Q N, star (ψ a) * φ a

def normSq {Q N : ℕ} (ψ : State Q N) : ℝ := (inner ψ ψ).re

def energy {Q N : ℕ} (ψ : State Q N) : ℝ := (inner ψ (hamiltonian ψ)).re

theorem pairApply_add {Q N : ℕ} (i j : Fin N) (ψ φ : State Q N) :
    pairApply i j (ψ+φ) = pairApply i j ψ + pairApply i j φ := by
  funext a
  simp [pairApply, mul_add, Finset.sum_add_distrib]

theorem pairApply_smul {Q N : ℕ} (i j : Fin N) (c : ℂ) (ψ : State Q N) :
    pairApply i j (c • ψ) = c • pairApply i j ψ := by
  funext a
  simp only [pairApply, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (pairVector Q _ _ _ : ℂ) c, ← Finset.mul_sum]
  simp_rw [mul_left_comm (pairVector Q _ _ _ : ℂ) c, ← Finset.mul_sum]

theorem hamiltonian_zero {Q N : ℕ} :
    hamiltonian (0 : State Q N) = 0 := by
  funext a
  simp [hamiltonian, pairApply]

theorem hamiltonian_add {Q N : ℕ} (ψ φ : State Q N) :
    hamiltonian (ψ+φ) = hamiltonian ψ + hamiltonian φ := by
  funext a
  simp only [hamiltonian, pairApply_add, Pi.add_apply]
  simp_rw [ite_add_zero, Finset.sum_add_distrib]

theorem hamiltonian_smul {Q N : ℕ} (c : ℂ) (ψ : State Q N) :
    hamiltonian (c • ψ) = c • hamiltonian ψ := by
  funext a
  simp only [hamiltonian, pairApply_smul, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, mul_ite, mul_zero]

/-- The ambient tensor-space Hamiltonian as a complex linear map. -/
def hamiltonianLinear (Q N : ℕ) : State Q N →ₗ[ℂ] State Q N where
  toFun := hamiltonian
  map_add' := hamiltonian_add
  map_smul' := hamiltonian_smul

theorem hamiltonian_small_sector {Q N : ℕ} (hN : N ≤ 1) (ψ : State Q N) :
    hamiltonian ψ = 0 := by
  funext a
  have h : ∀ i j : Fin N, ¬ i < j := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    change i.val < j.val at hij
    omega
  simp [hamiltonian, h]

/-- The desired full-model estimate. This is a proposition, not a proved theorem.
With self-adjointness proved in HamiltonianForms, it expresses H_Q² ≥ H_Q/3
on Sym^N U_Q. The quantification over all N is essential to the uniform claim. -/
def UniformGapTarget : Prop :=
  ∀ Q : ℕ, 3088 ≤ Q → ∀ N : ℕ, ∀ ψ : State Q N,
    IsBosonic ψ → (1/3 : ℝ) * energy ψ ≤ normSq (hamiltonian ψ)

end
end BosonicLaughlin

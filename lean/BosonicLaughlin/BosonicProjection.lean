import BosonicLaughlin.FockCorrespondence
import Mathlib.Data.Fintype.Perm

/-!
The orthogonal projection from ordered tensor coordinates to the symmetric
N-boson sector. Its normalization is the order N! of the permutation group.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def bosonicProjection {Q N : ℕ} (ψ : State Q N) : State Q N := fun a =>
  (N.factorial : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N), ψ (a ∘ σ)

theorem bosonicProjection_add {Q N : ℕ} (φ ψ : State Q N) :
    bosonicProjection (φ+ψ) = bosonicProjection φ + bosonicProjection ψ := by
  funext a
  simp only [bosonicProjection, Pi.add_apply, Finset.sum_add_distrib, mul_add]

theorem bosonicProjection_smul {Q N : ℕ} (c : ℂ) (ψ : State Q N) :
    bosonicProjection (c • ψ) = c • bosonicProjection ψ := by
  funext a
  simp only [bosonicProjection, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

def bosonicProjectionLinear (Q N : ℕ) : State Q N →ₗ[ℂ] State Q N where
  toFun := bosonicProjection
  map_add' := bosonicProjection_add
  map_smul' := bosonicProjection_smul

theorem bosonicProjection_isBosonic {Q N : ℕ} (ψ : State Q N) :
    IsBosonic (bosonicProjection ψ) := by
  intro τ a
  simp only [bosonicProjection]
  congr 1
  change (∑ σ : Equiv.Perm (Fin N), ψ (a ∘ (τ * σ : Equiv.Perm (Fin N)))) = _
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => ψ (a ∘ σ))

theorem bosonicProjection_eq_self {Q N : ℕ} (ψ : State Q N) (hψ : IsBosonic ψ) :
    bosonicProjection ψ = ψ := by
  have hn : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  unfold IsBosonic at hψ
  funext a
  simp only [bosonicProjection, hψ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem bosonicProjection_idempotent {Q N : ℕ} (ψ : State Q N) :
    bosonicProjection (bosonicProjection ψ) = bosonicProjection ψ :=
  bosonicProjection_eq_self _ (bosonicProjection_isBosonic ψ)

/-- Permutation action is unitary on the ambient finite tensor coordinates. -/
theorem inner_permutation_adjoint {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (φ ψ : State Q N) :
    inner φ (fun a => ψ (a ∘ σ)) = inner (fun a => φ (a ∘ σ.symm)) ψ := by
  unfold inner
  rw [← Equiv.sum_comp (configurationPermutation σ.symm)
    (fun a => star (φ a) * ψ (a ∘ σ))]
  apply Finset.sum_congr rfl
  intro a _
  change star (φ (a ∘ σ.symm)) * ψ ((a ∘ σ.symm) ∘ σ) = _
  have he : (a ∘ σ.symm) ∘ σ = a := by funext i; simp
  rw [he]

theorem bosonicProjection_inner_right {Q N : ℕ} (φ ψ : State Q N) :
    inner φ (bosonicProjection ψ) =
      (N.factorial : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
        inner φ (fun a => ψ (a ∘ σ)) := by
  simp only [inner, bosonicProjection]
  simp_rw [mul_left_comm (star (φ _)) (N.factorial : ℂ)⁻¹, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem bosonicProjection_inner_left {Q N : ℕ} (φ ψ : State Q N) :
    inner (bosonicProjection φ) ψ =
      (N.factorial : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
        inner (fun a => φ (a ∘ σ)) ψ := by
  simp only [inner, bosonicProjection, star_mul, star_inv₀, star_natCast,
    star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Exact self-adjointness, with the repository's conjugate-linear first slot. -/
theorem bosonicProjection_hermitian {Q N : ℕ} (φ ψ : State Q N) :
    inner φ (bosonicProjection ψ) = inner (bosonicProjection φ) ψ := by
  rw [bosonicProjection_inner_right, bosonicProjection_inner_left]
  simp_rw [inner_permutation_adjoint]
  congr 1
  exact Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))
    (fun σ => inner (fun a => φ (a ∘ σ)) ψ)

theorem bosonicProjection_fixed_iff {Q N : ℕ} (ψ : State Q N) :
    bosonicProjection ψ = ψ ↔ IsBosonic ψ := by
  constructor
  · intro h
    rw [← h]
    exact bosonicProjection_isBosonic ψ
  · exact bosonicProjection_eq_self ψ

end
end BosonicLaughlin

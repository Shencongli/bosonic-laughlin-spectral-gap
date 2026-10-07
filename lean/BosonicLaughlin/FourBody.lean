import BosonicLaughlin.FockCorrespondence
import Mathlib.Logic.Equiv.Fintype

/-!
The disjoint-pair part of the exact V₀ normal-order identity. Operators act
on the full finite tensor space; permutation invariance is used only when
identifying the sum with physical pair-annihilator norms.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem replacePair_at_other {Q N : ℕ} (a : Configuration Q N)
    (i j k : Fin N) (hki : k ≠ i) (hkj : k ≠ j) (x y : Orbital Q) :
    replacePair a i j x y k = a k := by
  simp [replacePair, hki, hkj]

theorem replacePair_commute_disjoint {Q N : ℕ} (a : Configuration Q N)
    (i j k l : Fin N) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (x y u v : Orbital Q) :
    replacePair (replacePair a i j x y) k l u v =
      replacePair (replacePair a k l u v) i j x y := by
  unfold replacePair
  rw [Function.update_comm hjk y u (Function.update a i x),
    Function.update_comm hik x u a,
    Function.update_comm hjl y v (Function.update (Function.update a k u) i x),
    Function.update_comm hil x v (Function.update a k u)]

theorem fourBody_sum_six_exchange {A B C D E F R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F]
    [AddCommMonoid R] (f : A → B → C → D → E → F → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g) =
      ∑ d, ∑ e, ∑ g, ∑ a, ∑ b, ∑ c, f a b c d e g := by
  have h := Finset.sum_comm (s := (univ : Finset (A × B × C)))
    (t := (univ : Finset (D × E × F)))
    (f := fun x y => f x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2)
  simpa only [Fintype.sum_prod_type] using h

/-- V₀ projections acting on disjoint tensor slots commute exactly. -/
theorem pairApply_commute_disjoint {Q N : ℕ} (i j k l : Fin N)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (ψ : State Q N) :
    pairApply i j (pairApply k l ψ) = pairApply k l (pairApply i j ψ) := by
  funext a
  simp only [pairApply, replacePair_at_other _ i j k hik.symm hjk.symm,
    replacePair_at_other _ i j l hil.symm hjl.symm,
    replacePair_at_other _ k l i hik hil, replacePair_at_other _ k l j hjk hjl,
    Finset.mul_sum]
  rw [fourBody_sum_six_exchange]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [replacePair_commute_disjoint a i j k l hik hil hjk hjl]
  ring

/-- A product of disjoint pair projectors is itself an orthogonal projection. -/
theorem pairApply_product_energy_eq_normSq {Q N : ℕ} (i j k l : Fin N)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (ψ : State Q N) :
    (inner ψ (pairApply i j (pairApply k l ψ))).re =
      normSq (pairApply i j (pairApply k l ψ)) := by
  unfold normSq
  congr 1
  rw [← pairApply_hermitian i j hij,
    pairApply_idempotent i j hij,
    ← pairApply_hermitian k l hkl,
    pairApply_commute_disjoint k l i j hik.symm hjk.symm hil.symm hjl.symm,
    pairApply_idempotent k l hkl]

theorem pairApply_product_energy_nonneg {Q N : ℕ} (i j k l : Fin N)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (ψ : State Q N) : 0 ≤ (inner ψ (pairApply i j (pairApply k l ψ))).re := by
  rw [pairApply_product_energy_eq_normSq i j k l hij hkl hik hil hjk hjl,
    normSq_eq_sum]
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

end
end BosonicLaughlin

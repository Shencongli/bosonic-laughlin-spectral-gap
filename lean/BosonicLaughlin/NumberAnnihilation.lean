import BosonicLaughlin.PairAnnihilation
import BosonicLaughlin.ModeProjectors
import BosonicLaughlin.ProjectionOccupation
import BosonicLaughlin.Occupation

namespace BosonicLaughlin
noncomputable section
open Finset Matrix

def configurationPermutation {Q N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Equiv.Perm (Configuration Q N) where
  toFun := fun a => a ∘ σ
  invFun := fun a => a ∘ σ.symm
  left_inv := by intro a; funext k; simp
  right_inv := by intro a; funext k; simp

theorem update_permute {Q N : ℕ} (a : Configuration Q N)
    (σ : Equiv.Perm (Fin N)) (i : Fin N) (x : Orbital Q) :
    Function.update (a ∘ σ) i x = Function.update a (σ i) x ∘ σ := by
  funext k
  by_cases h : k=i
  · subst k; simp
  · have hs : σ k ≠ σ i := fun he => h (σ.injective he)
    simp [h, hs]

theorem modeApply_permute_bosonic {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (i : Fin N) (β : Orbital Q → ℂ) (ψ : State Q N) (hψ : IsBosonic ψ)
    (a : Configuration Q N) :
    modeApply i β ψ (a ∘ σ) = modeApply (σ i) β ψ a := by
  simp only [modeApply, Function.comp_apply, update_permute, hψ σ]

theorem mode_energy_permute_bosonic {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (i : Fin N) (β : Orbital Q → ℂ) (ψ : State Q N) (hψ : IsBosonic ψ) :
    inner ψ (modeApply i β ψ) = inner ψ (modeApply (σ i) β ψ) := by
  unfold inner
  rw [← Equiv.sum_comp (configurationPermutation σ)
    (fun a => star (ψ a) * modeApply i β ψ a)]
  simp only [configurationPermutation, Equiv.coe_fn_mk,
    modeApply_permute_bosonic σ i β ψ hψ, hψ σ]

def consConfigurationEquiv (Q N : ℕ) :
    (Orbital Q × Configuration Q N) ≃ Configuration Q (N+1) where
  toFun := fun z => Fin.cons z.1 z.2
  invFun := fun a => (a 0, fun k => a k.succ)
  left_inv := by intro ⟨x,a⟩; simp
  right_inv := by
    intro a
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp

theorem sum_configurations_cons {Q N : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Configuration Q (N+1) → A) :
    ∑ a, f a = ∑ x : Orbital Q, ∑ a : Configuration Q N, f (Fin.cons x a) := by
  rw [← (consConfigurationEquiv Q N).sum_comp f]
  simp only [Fintype.sum_prod_type, consConfigurationEquiv, Equiv.coe_fn_mk]

theorem update_cons_zero {Q N : ℕ} (a : Configuration Q N) (x y : Orbital Q) :
    Function.update (Fin.cons x a : Configuration Q (N+1)) 0 y = Fin.cons y a := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · simp

theorem mode_zero_energy {Q N : ℕ} (β : Orbital Q → ℂ) (ψ : State Q (N+1)) :
    (inner ψ (modeApply 0 β ψ)).re =
      ∑ a : Configuration Q N, Complex.normSq (∑ x, star (β x) * ψ (Fin.cons x a)) := by
  have hinner : inner ψ (modeApply 0 β ψ) =
      ∑ a : Configuration Q N,
        star (∑ x, star (β x) * ψ (Fin.cons x a)) *
          (∑ x, star (β x) * ψ (Fin.cons x a)) := by
    unfold inner
    rw [sum_configurations_cons, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp only [modeApply, Fin.cons_zero, update_cons_zero, Complex.star_def,
      map_sum, map_mul, starRingEnd_self_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hinner]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (starRingEnd ℂ _ * _).re = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem annihilate_normSq {Q N : ℕ} (β : Orbital Q → ℂ)
    (ψ : State Q (N+1)) :
    normSq (annihilate β ψ) = ((N : ℝ)+1) *
      ∑ a : Configuration Q N, Complex.normSq (∑ x, star (β x) * ψ (Fin.cons x a)) := by
  rw [normSq_eq_sum]
  change (∑ a : Configuration Q N,
    Complex.normSq ((Real.sqrt ((N : ℝ)+1) : ℂ) *
      ∑ x, star (β x) * ψ (Fin.cons x a))) = _
  simp_rw [Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (show (0 : ℝ) ≤ (N : ℝ)+1 by positivity)]
  exact (Finset.mul_sum _ _ _).symm

/-- On the physical symmetric tensor sector, the number matrix is aβ†aβ
as an exact quadratic-form identity, including the sqrt(N+1) normalization. -/
theorem projectionNumber_eq_annihilate_normSq {Q N : ℕ} (β : Orbital Q → ℂ)
    (ψ : State Q (N+1)) (hψ : IsBosonic ψ) :
    matrixQuadratic (projectionNumber (fun i : Fin (N+1) => modeMatrix i β)) ψ =
      normSq (annihilate β ψ) := by
  have hall : ∀ i : Fin (N+1), inner ψ (modeApply i β ψ) = inner ψ (modeApply 0 β ψ) := by
    intro i
    simpa only [Equiv.swap_apply_left] using
      mode_energy_permute_bosonic (Equiv.swap i 0) i β ψ hψ
  change (inner ψ (projectionNumber (fun i : Fin (N+1) => modeMatrix i β) *ᵥ ψ)).re = _
  simp only [projectionNumber, Matrix.sum_mulVec, inner, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ i : Fin (N+1), inner ψ (modeMatrix i β *ᵥ ψ)).re = _
  simp only [modeMatrix_mulVec, hall, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero]
  rw [mode_zero_energy, annihilate_normSq]
  norm_cast

end
end BosonicLaughlin

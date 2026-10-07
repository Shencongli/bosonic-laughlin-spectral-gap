import BosonicLaughlin.FockCorrespondence

/-!
The concrete three-particle pair-creation map. The auxiliary coordinates are
the pair spin-Q index and the remaining one-particle orbital. The physical
codomain is the symmetric subspace of the full three-slot tensor space.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

abbrev ThreeBodyAux (Q : ℕ) := Fin (2*Q+1) → Orbital Q → ℂ

def threeBodyInsertion {Q : ℕ} (φ : ThreeBodyAux Q) (x y z : Orbital Q) : ℂ :=
  ∑ p : Fin (2*Q+1), (pairVector Q p.val x y : ℂ) * φ p z

theorem threeBodyInsertion_exchange {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) : threeBodyInsertion φ x y z = threeBodyInsertion φ y x z := by
  simp only [threeBodyInsertion, pairVector_exchange Q _ x y]

/-- W₃ = √3 times symmetrized pair insertion, in normalized tensor coordinates. -/
def threeBodyMap {Q : ℕ} (φ : ThreeBodyAux Q) : State Q 3 := fun a =>
  (1 / (Real.sqrt 3 : ℂ)) *
    (threeBodyInsertion φ (a 0) (a 1) (a 2) +
     threeBodyInsertion φ (a 0) (a 2) (a 1) +
     threeBodyInsertion φ (a 1) (a 2) (a 0))

/-- The physical adjoint: its domain will always be restricted to bosonic states. -/
def threeBodyAdjoint {Q : ℕ} (ψ : State Q 3) : ThreeBodyAux Q := fun p k =>
  (Real.sqrt 3 : ℂ) * ∑ x : Orbital Q, ∑ y : Orbital Q,
    (pairVector Q p.val x y : ℂ) * ψ ![x, y, k]

/-- Compression of the exchange of the second pair orbital with the spectator. -/
def compressedSwap {Q : ℕ} (φ : ThreeBodyAux Q) : ThreeBodyAux Q := fun p k =>
  ∑ x : Orbital Q, ∑ y : Orbital Q, ∑ q : Fin (2*Q+1),
    (pairVector Q p.val x y : ℂ) * (pairVector Q q.val x k : ℂ) * φ q y

theorem threeBodyMap_isBosonic {Q : ℕ} (φ : ThreeBodyAux Q) :
    IsBosonic (threeBodyMap φ) := by
  intro σ a
  have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  generalize h0 : σ 0 = i0 at *
  generalize h1 : σ 1 = i1 at *
  generalize h2 : σ 2 = i2 at *
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;>
    simp_all only [ne_eq, Fin.reduceFinMk, not_true_eq_false]
  all_goals
    simp only [threeBodyMap, Function.comp_apply, h0, h1, h2] <;>
    simp only [threeBodyInsertion_exchange φ (a 1) (a 0),
      threeBodyInsertion_exchange φ (a 2) (a 0),
      threeBodyInsertion_exchange φ (a 2) (a 1)] <;> ring

theorem threeBodyInsertion_contraction {Q : ℕ} (φ : ThreeBodyAux Q)
    (p : Fin (2*Q+1)) (k : Orbital Q) :
    (∑ x : Orbital Q, ∑ y : Orbital Q,
      (pairVector Q p.val x y : ℂ) * threeBodyInsertion φ x y k) = φ p k := by
  simp only [threeBodyInsertion, Finset.mul_sum]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  simp_rw [pairVector_overlap_complex Q p.val _ (by omega)]
  simp [Fin.val_inj]

theorem threeBodyInsertion_cross_contraction {Q : ℕ} (φ : ThreeBodyAux Q)
    (p : Fin (2*Q+1)) (k : Orbital Q) :
    (∑ x : Orbital Q, ∑ y : Orbital Q,
      (pairVector Q p.val x y : ℂ) * threeBodyInsertion φ y k x) =
        compressedSwap φ p k := by
  rw [Finset.sum_comm]
  simp only [threeBodyInsertion, compressedSwap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [pairVector_exchange Q p.val y x, mul_assoc]

/-- The exact auxiliary Gram identity; no spectral decomposition is assumed. -/
theorem threeBody_gram {Q : ℕ} (φ : ThreeBodyAux Q) :
    threeBodyAdjoint (threeBodyMap φ) = φ + (2 : ℂ) • compressedSwap φ := by
  funext p k
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)))
  change (Real.sqrt 3 : ℂ) * (∑ x : Orbital Q, ∑ y : Orbital Q,
    (pairVector Q p.val x y : ℂ) * ((1 / (Real.sqrt 3 : ℂ)) *
      (threeBodyInsertion φ x y k + threeBodyInsertion φ x k y +
        threeBodyInsertion φ y k x))) = _
  simp_rw [← mul_assoc, mul_comm (pairVector Q p.val _ _ : ℂ) (1 / (Real.sqrt 3 : ℂ)),
    mul_assoc, ← Finset.mul_sum]
  rw [← mul_assoc, mul_one_div_cancel hs, one_mul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [threeBodyInsertion_contraction, threeBodyInsertion_cross_contraction]
  change φ p k + (∑ x : Orbital Q, ∑ y : Orbital Q,
    (pairVector Q p.val x y : ℂ) * threeBodyInsertion φ x k y) + compressedSwap φ p k = _
  simp only [threeBodyInsertion, Finset.mul_sum, ← mul_assoc]
  change φ p k + compressedSwap φ p k + compressedSwap φ p k = _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem threeBodyMap_add {Q : ℕ} (φ χ : ThreeBodyAux Q) :
    threeBodyMap (φ + χ) = threeBodyMap φ + threeBodyMap χ := by
  funext a
  simp only [threeBodyMap, threeBodyInsertion, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem threeBodyMap_smul {Q : ℕ} (c : ℂ) (φ : ThreeBodyAux Q) :
    threeBodyMap (c • φ) = c • threeBodyMap φ := by
  funext a
  simp only [threeBodyMap, threeBodyInsertion, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (pairVector Q _ _ _ : ℂ) c, ← Finset.mul_sum]
  ring

theorem threeBodyAdjoint_add {Q : ℕ} (ψ χ : State Q 3) :
    threeBodyAdjoint (ψ + χ) = threeBodyAdjoint ψ + threeBodyAdjoint χ := by
  funext p k
  simp [threeBodyAdjoint, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem threeBodyAdjoint_smul {Q : ℕ} (c : ℂ) (ψ : State Q 3) :
    threeBodyAdjoint (c • ψ) = c • threeBodyAdjoint ψ := by
  funext p k
  simp only [threeBodyAdjoint, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (pairVector Q _ _ _ : ℂ) c, ← Finset.mul_sum]
  ring

theorem bosonic_three_swap12 {Q : ℕ} (ψ : State Q 3) (hψ : IsBosonic ψ)
    (x y z : Orbital Q) : ψ ![x, z, y] = ψ ![x, y, z] := by
  have he : (![x, y, z] : Configuration Q 3) ∘ Equiv.swap 1 2 = ![x, z, y] := by
    funext i
    fin_cases i <;> simp [Function.comp_apply, Equiv.swap_apply_def]
  simpa only [he] using hψ (Equiv.swap 1 2) ![x, y, z]

theorem bosonic_three_cycle {Q : ℕ} (ψ : State Q 3) (hψ : IsBosonic ψ)
    (x y z : Orbital Q) : ψ ![z, x, y] = ψ ![x, y, z] := by
  have he : (![x, y, z] : Configuration Q 3) ∘
      ((Equiv.swap 0 2).trans (Equiv.swap 0 1)) = ![z, x, y] := by
    funext i
    fin_cases i <;> simp [Function.comp_apply, Equiv.swap_apply_def]
  simpa only [he] using hψ ((Equiv.swap 0 2).trans (Equiv.swap 0 1)) ![x, y, z]

/-- The opposite product is the actual three-particle Hamiltonian on bosons. -/
theorem threeBody_hamiltonian {Q : ℕ} (ψ : State Q 3) (hψ : IsBosonic ψ) :
    threeBodyMap (threeBodyAdjoint ψ) = hamiltonian ψ := by
  funext a
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)))
  have h01 : ∀ x y, replacePair a 0 1 x y = ![x, y, a 2] := by
    intro x y; funext i; fin_cases i <;> simp [replacePair]
  have h02 : ∀ x y, replacePair a 0 2 x y = ![x, a 1, y] := by
    intro x y; funext i; fin_cases i <;> simp [replacePair]
  have h12 : ∀ x y, replacePair a 1 2 x y = ![a 0, x, y] := by
    intro x y; funext i; fin_cases i <;> simp [replacePair]
  have h02ψ : ∀ x y, ψ (replacePair a 0 2 x y) = ψ ![x, y, a 1] := by
    intro x y; rw [h02]; exact bosonic_three_swap12 ψ hψ x y (a 1)
  have h12ψ : ∀ x y, ψ (replacePair a 1 2 x y) = ψ ![x, y, a 0] := by
    intro x y; rw [h12]; exact bosonic_three_cycle ψ hψ x y (a 0)
  simp only [hamiltonian, Fin.sum_univ_three, show ¬ (0 : Fin 3) < 0 by decide,
    show (0 : Fin 3) < 1 by decide, show (0 : Fin 3) < 2 by decide,
    show ¬ (1 : Fin 3) < 0 by decide, show ¬ (1 : Fin 3) < 1 by decide,
    show (1 : Fin 3) < 2 by decide, show ¬ (2 : Fin 3) < 0 by decide,
    show ¬ (2 : Fin 3) < 1 by decide, show ¬ (2 : Fin 3) < 2 by decide,
    ite_true, ite_false, zero_add, add_zero]
  simp only [threeBodyMap, threeBodyInsertion, threeBodyAdjoint, pairApply, h01, h02ψ, h12ψ]
  simp_rw [mul_left_comm (pairVector Q _ _ _ : ℂ) (Real.sqrt 3 : ℂ), ← Finset.mul_sum]
  field_simp

def threeConfigurationEquiv (Q : ℕ) :
    (Orbital Q × Orbital Q × Orbital Q) ≃ Configuration Q 3 where
  toFun := fun xyz => ![xyz.1, xyz.2.1, xyz.2.2]
  invFun := fun a => (a 0, a 1, a 2)
  left_inv := by intro ⟨x,y,z⟩; rfl
  right_inv := by intro a; funext i; fin_cases i <;> rfl

theorem sum_configurations_three {Q : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Configuration Q 3 → A) :
    (∑ a, f a) = ∑ x : Orbital Q, ∑ y : Orbital Q, ∑ z : Orbital Q, f ![x,y,z] := by
  rw [← (threeConfigurationEquiv Q).sum_comp f]
  simp only [Fintype.sum_prod_type, threeConfigurationEquiv, Equiv.coe_fn_mk]

theorem threeBodyInsertion_inner {Q : ℕ} (φ : ThreeBodyAux Q) (ψ : State Q 3) :
    (∑ x : Orbital Q, ∑ y : Orbital Q, ∑ z : Orbital Q,
      star (threeBodyInsertion φ x y z) * ψ ![x,y,z]) =
    ∑ p : Fin (2*Q+1), ∑ z : Orbital Q, star (φ p z) *
      ∑ x : Orbital Q, ∑ y : Orbital Q,
        (pairVector Q p.val x y : ℂ) * ψ ![x,y,z] := by
  simp only [threeBodyInsertion, star_sum, star_mul, Complex.star_def,
    Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext x; arg 2; ext y; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The defining adjoint identity with the physical bosonic codomain. -/
theorem threeBody_adjoint_inner {Q : ℕ} (φ : ThreeBodyAux Q)
    (ψ : State Q 3) (hψ : IsBosonic ψ) :
    inner (threeBodyMap φ) ψ =
      ∑ p : Fin (2*Q+1), ∑ z : Orbital Q, star (φ p z) * threeBodyAdjoint ψ p z := by
  let c : ℂ := ∑ x : Orbital Q, ∑ y : Orbital Q, ∑ z : Orbital Q,
    star (threeBodyInsertion φ x y z) * ψ ![x,y,z]
  have hc2 : (∑ x : Orbital Q, ∑ y : Orbital Q, ∑ z : Orbital Q,
      star (threeBodyInsertion φ x z y) * ψ ![x,y,z]) = c := by
    unfold c
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    rw [bosonic_three_swap12 ψ hψ x y z]
  have hc3 : (∑ x : Orbital Q, ∑ y : Orbital Q, ∑ z : Orbital Q,
      star (threeBodyInsertion φ y z x) * ψ ![x,y,z]) = c := by
    unfold c
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro x _
    rw [bosonic_three_cycle ψ hψ y z x]
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs0 : (Real.sqrt 3 : ℂ) ≠ 0 := by intro hz; rw [hz] at hs; norm_num at hs
  have hfactor : ∀ u v : ℂ, star ((1 / (Real.sqrt 3 : ℂ)) * u) * v =
      (1 / (Real.sqrt 3 : ℂ)) * (star u * v) := by
    intro u v
    simp [star_mul, mul_comm, mul_left_comm]
  unfold inner
  rw [sum_configurations_three]
  change (∑ x : Orbital Q, ∑ y : Orbital Q, ∑ z : Orbital Q,
    star ((1 / (Real.sqrt 3 : ℂ)) *
      (threeBodyInsertion φ x y z + threeBodyInsertion φ x z y +
        threeBodyInsertion φ y z x)) * ψ ![x,y,z]) = _
  simp only [hfactor, star_add, add_mul, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hc2, hc3]
  change (1 / (Real.sqrt 3 : ℂ)) * c + (1 / (Real.sqrt 3 : ℂ)) * c +
    (1 / (Real.sqrt 3 : ℂ)) * c = _
  have hr : (∑ p : Fin (2*Q+1), ∑ z : Orbital Q,
      star (φ p z) * threeBodyAdjoint ψ p z) = (Real.sqrt 3 : ℂ) * c := by
    simp only [threeBodyAdjoint]
    simp_rw [mul_left_comm (star (φ _ _)) (Real.sqrt 3 : ℂ), ← Finset.mul_sum]
    rw [← threeBodyInsertion_inner]
  rw [hr]
  field_simp
  linear_combination -c * hs

end
end BosonicLaughlin

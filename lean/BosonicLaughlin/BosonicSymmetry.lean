import BosonicLaughlin.PairTensor

/-!
Permutation invariance of the full tensor-space Hamiltonian.  This verifies
that the existing unordered-pair operator preserves the physical bosonic
subspace, with no particle-number or flux restriction.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem replacePair_swap {Q N : ℕ} (a : Configuration Q N)
    (i j : Fin N) (hij : i ≠ j) (x y : Orbital Q) :
    replacePair a i j x y = replacePair a j i y x := by
  exact Function.update_comm hij x y a

theorem pairApply_swap {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State Q N) : pairApply i j ψ = pairApply j i ψ := by
  funext a
  apply Finset.sum_congr rfl
  intro p _
  rw [pairVector_exchange Q p.val (a i) (a j)]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [pairVector_exchange Q p.val x y, replacePair_swap a i j hij x y]

theorem replacePair_permute {Q N : ℕ} (a : Configuration Q N)
    (σ : Equiv.Perm (Fin N)) (i j : Fin N) (x y : Orbital Q) :
    replacePair (a ∘ σ) i j x y = (replacePair a (σ i) (σ j) x y) ∘ σ := by
  funext k
  by_cases hj : k=j
  · subst k
    simp [replacePair]
  · have hσj : σ k ≠ σ j := fun h => hj (σ.injective h)
    by_cases hi : k=i
    · subst k
      simp [replacePair, hj, hσj]
    · have hσi : σ k ≠ σ i := fun h => hi (σ.injective h)
      simp [replacePair, hi, hj, hσi, hσj]

theorem pairApply_permute {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (i j : Fin N) (ψ : State Q N) (a : Configuration Q N) :
    pairApply i j ψ (a ∘ σ) =
      pairApply (σ i) (σ j) (fun b => ψ (b ∘ σ)) a := by
  simp only [pairApply, Function.comp_apply, replacePair_permute]

theorem pairApply_permute_bosonic {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (i j : Fin N) (ψ : State Q N) (hψ : IsBosonic ψ) (a : Configuration Q N) :
    pairApply i j ψ (a ∘ σ) = pairApply (σ i) (σ j) ψ a := by
  rw [pairApply_permute]
  have he : (fun b => ψ (b ∘ σ)) = ψ := funext (hψ σ)
  rw [he]

/-- The unordered-pair normalization is one half of the ordered distinct-slot sum. -/
theorem hamiltonian_double {Q N : ℕ} (ψ : State Q N) (a : Configuration Q N) :
    hamiltonian ψ a + hamiltonian ψ a =
      ∑ i : Fin N, ∑ j : Fin N, if i ≠ j then pairApply i j ψ a else 0 := by
  have he : ∀ i j : Fin N, (if i ≠ j then pairApply i j ψ a else 0) =
      (if i < j then pairApply i j ψ a else 0) +
      (if j < i then pairApply j i ψ a else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [ne_of_lt h, h, not_lt_of_ge (le_of_lt h)]
    · subst j
      simp
    · have hij : i ≠ j := (ne_of_lt h).symm
      simp [hij, h, not_lt_of_ge (le_of_lt h), pairApply_swap i j hij]
  simp_rw [he, Finset.sum_add_distrib]
  change hamiltonian ψ a + hamiltonian ψ a = hamiltonian ψ a + _
  congr 1
  exact Finset.sum_comm

/-- The full V₀ Hamiltonian preserves the symmetric N-boson tensor subspace. -/
theorem hamiltonian_isBosonic {Q N : ℕ} (ψ : State Q N) (hψ : IsBosonic ψ) :
    IsBosonic (hamiltonian ψ) := by
  intro σ a
  have he : hamiltonian ψ (a ∘ σ) + hamiltonian ψ (a ∘ σ) =
      hamiltonian ψ a + hamiltonian ψ a := by
    rw [hamiltonian_double, hamiltonian_double]
    simp_rw [pairApply_permute_bosonic σ _ _ ψ hψ]
    have hi : ∀ i j : Fin N, i ≠ j ↔ σ i ≠ σ j := by
      intro i j
      exact σ.injective.ne_iff.symm
    calc
      _ = ∑ i : Fin N, ∑ j : Fin N,
          if σ i ≠ σ j then pairApply (σ i) (σ j) ψ a else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [← hi i j]
      _ = ∑ i : Fin N, ∑ j : Fin N,
          if σ i ≠ j then pairApply (σ i) j ψ a else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp σ (fun j => if σ i ≠ j then pairApply (σ i) j ψ a else 0)
      _ = _ := Equiv.sum_comp σ (fun i => ∑ j : Fin N,
        if i ≠ j then pairApply i j ψ a else 0)
  have htwo : (2 : ℂ) * hamiltonian ψ (a ∘ σ) = 2 * hamiltonian ψ a := by
    simpa only [two_mul] using he
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwo

end
end BosonicLaughlin

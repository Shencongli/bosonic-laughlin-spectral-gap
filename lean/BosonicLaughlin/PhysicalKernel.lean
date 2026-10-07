import BosonicLaughlin.FockCorrespondence
import BosonicLaughlin.PairTensor

/-!
The kernel of the actual spherical V₀ Hamiltonian. Positivity and the exact
Fock correspondence identify zero energy with the common pair-annihilator
kernel on each physical bosonic sector, at every flux and particle number.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem stateNormSq_nonneg {Q N : ℕ} (ψ : State Q N) : 0 ≤ normSq ψ := by
  rw [normSq_eq_sum]
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

theorem stateNormSq_zero_iff {Q N : ℕ} (ψ : State Q N) : normSq ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    rw [normSq_eq_sum] at h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a (_ : a ∈ (univ : Finset (Configuration Q N))) => Complex.normSq_nonneg (ψ a))).mp h
    funext a
    exact Complex.normSq_eq_zero.mp (hz a (Finset.mem_univ a))
  · rintro rfl
    simp [normSq_eq_sum]

theorem pairApply_energy_eq_normSq {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State Q N) : (inner ψ (pairApply i j ψ)).re = normSq (pairApply i j ψ) := by
  unfold normSq
  rw [← pairApply_hermitian i j hij ψ (pairApply i j ψ), pairApply_idempotent i j hij]

theorem pairApply_energy_zero_iff {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State Q N) : (inner ψ (pairApply i j ψ)).re = 0 ↔ pairApply i j ψ = 0 := by
  rw [pairApply_energy_eq_normSq i j hij, stateNormSq_zero_iff]

theorem energy_eq_sum_pair_normSq {Q N : ℕ} (ψ : State Q N) :
    energy ψ = ∑ i : Fin N, ∑ j : Fin N,
      if i < j then normSq (pairApply i j ψ) else 0 := by
  rw [energy_eq_sum_pairs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · exact pairApply_energy_eq_normSq i j (ne_of_lt hij) ψ
  · rfl

theorem energy_zero_iff_ordered_pairs_zero {Q N : ℕ} (ψ : State Q N) :
    energy ψ = 0 ↔ ∀ i j : Fin N, i < j → pairApply i j ψ = 0 := by
  have hn : ∀ i j : Fin N, 0 ≤ (if i < j then normSq (pairApply i j ψ) else 0) := by
    intro i j
    split_ifs
    · exact stateNormSq_nonneg _
    · exact le_rfl
  rw [energy_eq_sum_pair_normSq]
  constructor
  · intro h i j hij
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hn i j))).mp h i (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hn i j)).mp hi j (Finset.mem_univ j)
    apply (stateNormSq_zero_iff _).mp
    simpa only [ite_eq_left hij] using hj
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hij : i < j
    · simp only [ite_eq_left hij, h i j hij]
      exact (stateNormSq_zero_iff (0 : State Q N)).mpr rfl
    · simp [hij]

theorem hamiltonian_zero_of_ordered_pairs_zero {Q N : ℕ} (ψ : State Q N)
    (h : ∀ i j : Fin N, i < j → pairApply i j ψ = 0) : hamiltonian ψ = 0 := by
  funext a
  simp only [hamiltonian, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i < j
  · simp [hij, h i j hij]
  · simp [hij]

theorem energy_zero_iff_hamiltonian_zero {Q N : ℕ} (ψ : State Q N) :
    energy ψ = 0 ↔ hamiltonian ψ = 0 := by
  constructor
  · intro h
    exact hamiltonian_zero_of_ordered_pairs_zero ψ
      ((energy_zero_iff_ordered_pairs_zero ψ).mp h)
  · intro h
    simp [energy, h, inner]

theorem hamiltonian_zero_iff_ordered_pairs_zero {Q N : ℕ} (ψ : State Q N) :
    hamiltonian ψ = 0 ↔ ∀ i j : Fin N, i < j → pairApply i j ψ = 0 :=
  (energy_zero_iff_hamiltonian_zero ψ).symm.trans (energy_zero_iff_ordered_pairs_zero ψ)

/-- The ambient tensor-space kernel is the common kernel of all distinct-slot pair projectors. -/
theorem hamiltonian_zero_iff_pairs_zero {Q N : ℕ} (ψ : State Q N) :
    hamiltonian ψ = 0 ↔ ∀ i j : Fin N, i ≠ j → pairApply i j ψ = 0 := by
  rw [hamiltonian_zero_iff_ordered_pairs_zero]
  constructor
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact h i j hlt
    · rw [pairApply_swap i j hij]
      exact h j i hgt
  · intro h i j hij
    exact h i j (ne_of_lt hij)

theorem energy_zero_iff_v0PairAnnihilate_zero {Q N : ℕ}
    (ψ : State Q (N + 2)) (hψ : IsBosonic ψ) :
    energy ψ = 0 ↔ ∀ p : Fin (2 * Q + 1), v0PairAnnihilate p ψ = 0 := by
  rw [energy_eq_sum_v0PairAnnihilate_normSq ψ hψ]
  constructor
  · intro h p
    apply (stateNormSq_zero_iff _).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => stateNormSq_nonneg (v0PairAnnihilate p ψ))).mp h p (Finset.mem_univ p)
  · intro h
    apply Finset.sum_eq_zero
    intro p _
    exact (stateNormSq_zero_iff _).mpr (h p)

/-- Exact common-kernel characterization for the normalized physical pair annihilators. -/
theorem hamiltonian_zero_iff_v0PairAnnihilate_zero {Q N : ℕ}
    (ψ : State Q (N + 2)) (hψ : IsBosonic ψ) :
    hamiltonian ψ = 0 ↔ ∀ p : Fin (2 * Q + 1), v0PairAnnihilate p ψ = 0 :=
  (energy_zero_iff_hamiltonian_zero ψ).symm.trans
    (energy_zero_iff_v0PairAnnihilate_zero ψ hψ)

/-- Equality of physical kernel subspaces, with all maps still defined on full tensor coordinates. -/
theorem physicalHamiltonian_kernel_eq_common_pair_kernel (Q N : ℕ) :
    bosonicSubspace Q (N + 2) ⊓ LinearMap.ker (hamiltonianLinear Q (N + 2)) =
      bosonicSubspace Q (N + 2) ⊓
        ⨅ p : Fin (2 * Q + 1), LinearMap.ker (v0PairAnnihilateLinear Q N p) := by
  ext ψ
  simp only [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_iInf]
  change (IsBosonic ψ ∧ hamiltonian ψ = 0) ↔
    (IsBosonic ψ ∧ ∀ p : Fin (2 * Q + 1), v0PairAnnihilate p ψ = 0)
  constructor
  · rintro ⟨hψ, hH⟩
    exact ⟨hψ, (hamiltonian_zero_iff_v0PairAnnihilate_zero ψ hψ).mp hH⟩
  · rintro ⟨hψ, hB⟩
    exact ⟨hψ, (hamiltonian_zero_iff_v0PairAnnihilate_zero ψ hψ).mpr hB⟩

end
end BosonicLaughlin

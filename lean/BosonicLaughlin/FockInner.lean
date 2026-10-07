import BosonicLaughlin.FockCorrespondence
import BosonicLaughlin.StateForms
import BosonicLaughlin.FourBodyFock

/-! Sesquilinear, rather than only energy, factorization of the actual V0
Hamiltonian. This fixes all matrix entries in later changes of basis. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem pair_cross_permute_bosonic {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (i j : Fin N) (ψ φ : State Q N) (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner ψ (pairApply i j φ) = inner ψ (pairApply (σ i) (σ j) φ) := by
  unfold inner
  rw [← Equiv.sum_comp (configurationPermutation σ)
    (fun a => star (ψ a) * pairApply i j φ a)]
  simp only [configurationPermutation, Equiv.coe_fn_mk,
    pairApply_permute_bosonic σ i j φ hφ, hψ σ]

theorem pair_cross_first_bosonic {Q N : ℕ} (i j : Fin (N+2)) (hij : i ≠ j)
    (ψ φ : State Q (N+2)) (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner ψ (pairApply i j φ) = inner ψ (pairApply 0 1 φ) := by
  obtain ⟨σ, hi, hj⟩ := exists_pair_permutation N i j hij
  simpa only [hi, hj] using pair_cross_permute_bosonic σ i j ψ φ hψ hφ

theorem v0PairAnnihilate_inner {Q N : ℕ} (p : Fin (2*Q+1))
    (ψ φ : State Q (N+2)) :
    inner (v0PairAnnihilate p ψ) (v0PairAnnihilate p φ) =
      ((N+2).choose 2 : ℂ) * inner (v0PairAmplitude p ψ) (v0PairAmplitude p φ) := by
  change inner ((Real.sqrt ((N+2).choose 2) : ℂ) • v0PairAmplitude p ψ)
    ((Real.sqrt ((N+2).choose 2) : ℂ) • v0PairAmplitude p φ) = _
  rw [stateInner_smul_left, stateInner_smul_right, ← mul_assoc]
  have hs : star (Real.sqrt ((N+2).choose 2) : ℂ) *
      (Real.sqrt ((N+2).choose 2) : ℂ) = ((N+2).choose 2 : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity)]
    norm_cast
  rw [hs]

theorem hamiltonian_inner_eq_first_pair {Q N : ℕ}
    (ψ φ : State Q (N+2)) (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner ψ (hamiltonian φ) =
      ((N+2).choose 2 : ℂ) * inner ψ (pairApply 0 1 φ) := by
  rw [hamiltonian_inner]
  have he : ∀ i j : Fin (N+2),
      (if i < j then inner ψ (pairApply i j φ) else 0) =
      (if i < j then (1 : ℂ) else 0) * inner ψ (pairApply 0 1 φ) := by
    intro i j
    by_cases hij : i < j
    · simp only [ite_eq_left hij, one_mul,
        pair_cross_first_bosonic i j (ne_of_lt hij) ψ φ hψ hφ]
    · simp [hij]
  simp_rw [he, ← Finset.sum_mul]
  have hc : (∑ i : Fin (N+2), ∑ j : Fin (N+2), if i<j then (1 : ℂ) else 0) =
      ((N+2).choose 2 : ℂ) := by exact_mod_cast unordered_pair_count (N+2)
  rw [hc]

/-- Full matrix-element factorization on the physical bosonic sector. -/
theorem hamiltonian_inner_eq_sum_pair_inner {Q N : ℕ}
    (ψ φ : State Q (N+2)) (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner ψ (hamiltonian φ) =
      ∑ p : Fin (2*Q+1), inner (v0PairAnnihilate p ψ) (v0PairAnnihilate p φ) := by
  rw [hamiltonian_inner_eq_first_pair ψ φ hψ hφ, first_pair_inner_identity]
  simp_rw [v0PairAnnihilate_inner]
  exact Finset.mul_sum _ _ _

end
end BosonicLaughlin

import BosonicLaughlin.NumberAnnihilation
import BosonicLaughlin.BosonicSymmetry
import BosonicLaughlin.HamiltonianForms

namespace BosonicLaughlin
noncomputable section
open Finset

/-- Contraction against one normalized spherical V₀ pair vector. -/
def v0PairAmplitude {Q N : ℕ} (p : Fin (2*Q+1)) (ψ : State Q (N+2)) : State Q N :=
  fun a => ∑ x : Orbital Q, ∑ y : Orbital Q,
    (pairVector Q p.val x y : ℂ) * ψ (Fin.cons x (Fin.cons y a))

/-- The physical V₀ pair annihilator in normalized symmetric-tensor coordinates. -/
def v0PairAnnihilate {Q N : ℕ} (p : Fin (2*Q+1)) (ψ : State Q (N+2)) : State Q N :=
  fun a => (Real.sqrt ((N+2).choose 2) : ℂ) * v0PairAmplitude p ψ a

def v0PairAnnihilateLinear (Q N : ℕ) (p : Fin (2*Q+1)) :
    State Q (N+2) →ₗ[ℂ] State Q N where
  toFun := v0PairAnnihilate p
  map_add' := by
    intro ψ φ
    funext a
    simp [v0PairAnnihilate, v0PairAmplitude, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c ψ
    funext a
    simp only [v0PairAnnihilate, v0PairAmplitude, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (pairVector Q p.val _ _ : ℂ) c, ← Finset.mul_sum]
    ring

theorem v0PairAnnihilate_isBosonic {Q N : ℕ} (p : Fin (2*Q+1))
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) : IsBosonic (v0PairAnnihilate p ψ) := by
  intro σ a
  simp only [v0PairAnnihilate, v0PairAmplitude, cons_comp_fixFirst,
    hψ (fixFirstPermutation (fixFirstPermutation σ))]

theorem v0PairAnnihilate_normSq {Q N : ℕ} (p : Fin (2*Q+1))
    (ψ : State Q (N+2)) :
    normSq (v0PairAnnihilate p ψ) = ((N+2).choose 2 : ℝ) *
      ∑ a : Configuration Q N, Complex.normSq (v0PairAmplitude p ψ a) := by
  rw [normSq_eq_sum]
  change (∑ a : Configuration Q N,
    Complex.normSq ((Real.sqrt ((N+2).choose 2) : ℂ) * v0PairAmplitude p ψ a)) = _
  simp_rw [Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (show (0 : ℝ) ≤ ((N+2).choose 2 : ℝ) by positivity)]
  exact (Finset.mul_sum _ _ _).symm

theorem pair_energy_permute_bosonic {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (i j : Fin N) (ψ : State Q N) (hψ : IsBosonic ψ) :
    inner ψ (pairApply i j ψ) = inner ψ (pairApply (σ i) (σ j) ψ) := by
  unfold inner
  rw [← Equiv.sum_comp (configurationPermutation σ)
    (fun a => star (ψ a) * pairApply i j ψ a)]
  simp only [configurationPermutation, Equiv.coe_fn_mk,
    pairApply_permute_bosonic σ i j ψ hψ, hψ σ]

theorem exists_pair_permutation (N : ℕ) (i j : Fin (N+2)) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin (N+2)), σ i = 0 ∧ σ j = 1 := by
  let σ₁ := Equiv.swap i 0
  have hi : σ₁ i = 0 := Equiv.swap_apply_left i 0
  have hj : σ₁ j ≠ 0 := by
    intro h
    exact hij (σ₁.injective (h.trans hi.symm)).symm
  refine ⟨σ₁.trans (Equiv.swap (σ₁ j) 1), ?_, ?_⟩
  · change Equiv.swap (σ₁ j) 1 (σ₁ i) = 0
    rw [hi]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hj) (by norm_num)
  · exact Equiv.swap_apply_left (σ₁ j) 1

theorem pair_energy_eq_first_bosonic {Q N : ℕ} (i j : Fin (N+2)) (hij : i ≠ j)
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    inner ψ (pairApply i j ψ) = inner ψ (pairApply 0 1 ψ) := by
  obtain ⟨σ, hi, hj⟩ := exists_pair_permutation N i j hij
  simpa only [hi, hj] using pair_energy_permute_bosonic σ i j ψ hψ

theorem unordered_pair_count (M : ℕ) :
    (∑ i : Fin M, ∑ j : Fin M, if i < j then (1 : ℝ) else 0) = (M.choose 2 : ℝ) := by
  have h : (∑ i : Fin M, ∑ j : Fin M, if i < j then (1 : ℕ) else 0) = M.choose 2 := by
    simpa [selectedPairs, selectedCount] using selectedPairs_eq_choose (fun _ : Fin M => true)
  exact_mod_cast h

theorem energy_eq_first_pair_bosonic {Q N : ℕ} (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    energy ψ = ((N+2).choose 2 : ℝ) * (inner ψ (pairApply 0 1 ψ)).re := by
  rw [energy_eq_sum_pairs]
  have he : ∀ i j : Fin (N+2),
      (if i < j then (inner ψ (pairApply i j ψ)).re else 0) =
      (if i < j then (1 : ℝ) else 0) * (inner ψ (pairApply 0 1 ψ)).re := by
    intro i j
    by_cases hij : i < j
    · simp only [ite_eq_left hij, one_mul, pair_energy_eq_first_bosonic i j (ne_of_lt hij) ψ hψ]
    · simp [hij]
  simp_rw [he, ← Finset.sum_mul]
  rw [unordered_pair_count]

theorem replacePair_cons_zero_one {Q N : ℕ} (a : Configuration Q N)
    (x y u v : Orbital Q) :
    replacePair (Fin.cons x (Fin.cons y a) : Configuration Q (N+2)) 0 1 u v =
      Fin.cons u (Fin.cons v a) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [replacePair]
  · refine Fin.cases ?_ (fun k => ?_) k
    · simp [replacePair]
    · have hk : k.succ.succ ≠ (1 : Fin (N+2)) := by
        intro h
        have he := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_one] at he
        omega
      simp [replacePair, hk]

theorem pairApply_cons_zero_one {Q N : ℕ} (ψ : State Q (N+2))
    (a : Configuration Q N) (x y : Orbital Q) :
    pairApply 0 1 ψ (Fin.cons x (Fin.cons y a)) =
      ∑ p : Fin (2*Q+1), (pairVector Q p.val x y : ℂ) * v0PairAmplitude p ψ a := by
  simp only [pairApply, Fin.cons_zero, replacePair_cons_zero_one, v0PairAmplitude]
  rfl

theorem first_pair_energy_identity {Q N : ℕ} (ψ : State Q (N+2)) :
    (inner ψ (pairApply 0 1 ψ)).re =
      ∑ p : Fin (2*Q+1), ∑ a : Configuration Q N,
        Complex.normSq (v0PairAmplitude p ψ a) := by
  have hinner : inner ψ (pairApply 0 1 ψ) =
      ∑ p : Fin (2*Q+1), ∑ a : Configuration Q N,
        star (v0PairAmplitude p ψ a) * v0PairAmplitude p ψ a := by
    unfold inner
    rw [sum_configurations_cons]
    simp_rw [sum_configurations_cons, pairApply_cons_zero_one, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (univ : Finset (Orbital Q)))
      (t := (univ : Finset (Configuration Q N)))]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (univ : Finset (Orbital Q)))
      (t := (univ : Finset (Fin (2*Q+1))))]
    simp_rw [Finset.sum_comm (s := (univ : Finset (Configuration Q N)))
      (t := (univ : Finset (Fin (2*Q+1))))]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    simp only [v0PairAmplitude, Complex.star_def, map_sum, map_mul,
      Complex.conj_ofReal, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hinner]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro a _
  change (starRingEnd ℂ _ * _).re = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- Exact quadratic-form version of H=Σp Bp†Bp on the physical bosonic sector.
The pair coefficient is one for every unordered pair, fixing the Fock normalization. -/
theorem energy_eq_sum_v0PairAnnihilate_normSq {Q N : ℕ}
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    energy ψ = ∑ p : Fin (2*Q+1), normSq (v0PairAnnihilate p ψ) := by
  rw [energy_eq_first_pair_bosonic ψ hψ, first_pair_energy_identity]
  simp_rw [v0PairAnnihilate_normSq]
  exact Finset.mul_sum _ _ _

end
end BosonicLaughlin

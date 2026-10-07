import BosonicLaughlin.ModeForms
import BosonicLaughlin.FockCorrespondence

namespace BosonicLaughlin
noncomputable section
open Finset Matrix

theorem modeApply_permute {Q N : ℕ} (σ : Equiv.Perm (Fin N)) (i : Fin N)
    (β : Orbital Q → ℂ) (ψ : State Q N) (a : Configuration Q N) :
    modeApply i β ψ (a ∘ σ) = modeApply (σ i) β (fun b => ψ (b ∘ σ)) a := by
  simp only [modeApply, Function.comp_apply, update_permute]

theorem modePairApply_permute_bosonic {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (i j : Fin N) (β : Orbital Q → ℂ) (ψ : State Q N) (hψ : IsBosonic ψ)
    (a : Configuration Q N) :
    modeApply i β (modeApply j β ψ) (a ∘ σ) =
      modeApply (σ i) β (modeApply (σ j) β ψ) a := by
  rw [modeApply_permute]
  have he : (fun b => modeApply j β ψ (b ∘ σ)) = modeApply (σ j) β ψ :=
    funext (modeApply_permute_bosonic σ j β ψ hψ)
  rw [he]

theorem modePair_energy_permute_bosonic {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (i j : Fin N) (β : Orbital Q → ℂ) (ψ : State Q N) (hψ : IsBosonic ψ) :
    inner ψ (modeApply i β (modeApply j β ψ)) =
      inner ψ (modeApply (σ i) β (modeApply (σ j) β ψ)) := by
  unfold inner
  rw [← Equiv.sum_comp (configurationPermutation σ)
    (fun a => star (ψ a) * modeApply i β (modeApply j β ψ) a)]
  simp only [configurationPermutation, Equiv.coe_fn_mk,
    modePairApply_permute_bosonic σ i j β ψ hψ, hψ σ]

theorem modePair_energy_eq_first_bosonic {Q N : ℕ} (i j : Fin (N+2)) (hij : i ≠ j)
    (β : Orbital Q → ℂ) (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    inner ψ (modeApply i β (modeApply j β ψ)) =
      inner ψ (modeApply 0 β (modeApply 1 β ψ)) := by
  obtain ⟨σ, hi, hj⟩ := exists_pair_permutation N i j hij
  simpa only [hi, hj] using modePair_energy_permute_bosonic σ i j β ψ hψ

theorem pairAnnihilate_normSq {Q N : ℕ} (β : Orbital Q → ℂ)
    (ψ : State Q (N+2)) :
    normSq (pairAnnihilate β ψ) = ((N+2).choose 2 : ℝ) *
      ∑ a : Configuration Q N, Complex.normSq
        (∑ x : Orbital Q, ∑ y : Orbital Q,
          star (β x) * star (β y) * ψ (Fin.cons x (Fin.cons y a))) := by
  rw [normSq_eq_sum]
  change (∑ a : Configuration Q N, Complex.normSq
    ((Real.sqrt ((N+2).choose 2) : ℂ) *
      ∑ x : Orbital Q, ∑ y : Orbital Q,
        star (β x) * star (β y) * ψ (Fin.cons x (Fin.cons y a)))) = _
  simp_rw [Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (show (0 : ℝ) ≤ ((N+2).choose 2 : ℝ) by positivity)]
  exact (Finset.mul_sum _ _ _).symm

theorem modeApply_pair_formula {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (β : Orbital Q → ℂ) (ψ : State Q N) (a : Configuration Q N) :
    modeApply i β (modeApply j β ψ) a =
      β (a i) * β (a j) * ∑ u : Orbital Q, ∑ v : Orbital Q,
        star (β u) * star (β v) * ψ (replacePair a i j u v) := by
  simp only [modeApply, Function.update_of_ne hij.symm, replacePair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem modeApply_cons_zero_one {Q N : ℕ} (β : Orbital Q → ℂ)
    (ψ : State Q (N+2)) (a : Configuration Q N) (x y : Orbital Q) :
    modeApply 0 β (modeApply 1 β ψ) (Fin.cons x (Fin.cons y a)) =
      β x * β y * ∑ u : Orbital Q, ∑ v : Orbital Q,
        star (β u) * star (β v) * ψ (Fin.cons u (Fin.cons v a)) := by
  rw [modeApply_pair_formula 0 1 (by norm_num)]
  simp only [Fin.cons_zero, replacePair_cons_zero_one]
  rfl

theorem modePair_first_energy_identity {Q N : ℕ} (β : Orbital Q → ℂ)
    (ψ : State Q (N+2)) :
    (inner ψ (modeApply 0 β (modeApply 1 β ψ))).re =
      ∑ a : Configuration Q N, Complex.normSq
        (∑ x : Orbital Q, ∑ y : Orbital Q,
          star (β x) * star (β y) * ψ (Fin.cons x (Fin.cons y a))) := by
  let c : Configuration Q N → ℂ := fun a => ∑ x : Orbital Q, ∑ y : Orbital Q,
    star (β x) * star (β y) * ψ (Fin.cons x (Fin.cons y a))
  have hinner : inner ψ (modeApply 0 β (modeApply 1 β ψ)) =
      ∑ a : Configuration Q N, star (c a) * c a := by
    unfold inner
    rw [sum_configurations_cons]
    simp_rw [sum_configurations_cons, modeApply_cons_zero_one]
    simp_rw [Finset.sum_comm (s := (univ : Finset (Orbital Q)))
      (t := (univ : Finset (Configuration Q N)))]
    apply Finset.sum_congr rfl
    intro a _
    simp only [c, Complex.star_def, map_sum, map_mul, starRingEnd_self_apply,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hinner]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (starRingEnd ℂ (c a) * c a).re = Complex.normSq (c a)
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- The unordered same-orbital pair form is B_beta† B_beta, with the
normalization B_beta = a_beta² / sqrt(2), on the actual bosonic tensor sector.
For normalized beta, the left side is the second factorial occupation moment. -/
theorem projectionPairs_eq_pairAnnihilate_normSq {Q N : ℕ} (β : Orbital Q → ℂ)
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    matrixQuadratic (projectionPairs (fun i : Fin (N+2) => modeMatrix i β)) ψ =
      normSq (pairAnnihilate β ψ) := by
  change (inner ψ (projectionPairs (fun i : Fin (N+2) => modeMatrix i β) *ᵥ ψ)).re = _
  rw [projectionPairs_mode_energy_identity]
  have he : ∀ i j : Fin (N+2),
      (if i < j then ∑ s : PairSpectator Q (N+2) i j,
        Complex.normSq (modePairContraction β i j ψ s) else 0) =
      (if i < j then (1 : ℝ) else 0) *
        (inner ψ (modeApply 0 β (modeApply 1 β ψ))).re := by
    intro i j
    by_cases hij : i < j
    · simp only [ite_eq_left hij, one_mul]
      rw [← modeMatrix_pair_energy_identity i j (ne_of_lt hij),
        ← Matrix.mulVec_mulVec, modeMatrix_mulVec, modeMatrix_mulVec,
        modePair_energy_eq_first_bosonic i j (ne_of_lt hij) β ψ hψ]
    · simp [hij]
  simp_rw [he, ← Finset.sum_mul]
  rw [unordered_pair_count, modePair_first_energy_identity, pairAnnihilate_normSq]

end
end BosonicLaughlin

import BosonicLaughlin.NormalOrdering
import BosonicLaughlin.CoherentOccupation

/-!
Identification of the disjoint-pair contribution with Σp,q (Bq Bp)†(Bq Bp).
The factorial normalization and slot count are proved explicitly. The input
sector is N+4 and both annihilators remove exactly two physical bosons.
-/

namespace BosonicLaughlin
noncomputable section
open Finset

theorem first_pair_inner_identity {Q N : ℕ} (ψ φ : State Q (N+2)) :
    inner ψ (pairApply 0 1 φ) =
      ∑ p : Fin (2*Q+1), inner (v0PairAmplitude p ψ) (v0PairAmplitude p φ) := by
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

theorem replacePair_cons_two_three {Q N : ℕ} (a : Configuration Q (N+2))
    (x y u v : Orbital Q) :
    replacePair (Fin.cons x (Fin.cons y a) : Configuration Q (N+4)) 2 3 u v =
      Fin.cons x (Fin.cons y (replacePair a 0 1 u v)) := by
  change Function.update (Function.update
    (Fin.cons x (Fin.cons y a) : Configuration Q (N+4))
    (0 : Fin (N+2)).succ.succ u) (1 : Fin (N+2)).succ.succ v = _
  simp only [← Fin.cons_update, replacePair]

theorem fourBody_sum_two_three_exchange {A B C D E R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    [AddCommMonoid R] (f : A → B → C → D → E → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ c, ∑ d, ∑ e, ∑ a, ∑ b, f a b c d e := by
  have h := Finset.sum_comm (s := (univ : Finset (A × B)))
    (t := (univ : Finset (C × D × E)))
    (f := fun x y => f x.1 x.2 y.1 y.2.1 y.2.2)
  simpa only [Fintype.sum_prod_type] using h

theorem v0PairAmplitude_pairApply_two_three {Q N : ℕ} (p : Fin (2*Q+1))
    (ψ : State Q (N+4)) :
    v0PairAmplitude p (pairApply 2 3 ψ) = pairApply 0 1 (v0PairAmplitude p ψ) := by
  funext a
  have hc2 (x y : Orbital Q) :
      (Fin.cons x (Fin.cons y a) : Configuration Q (N+4)) 2 = a 0 := by rfl
  have hc3 (x y : Orbital Q) :
      (Fin.cons x (Fin.cons y a) : Configuration Q (N+4)) 3 = a 1 := by rfl
  simp only [v0PairAmplitude, pairApply, replacePair_cons_two_three,
    hc2, hc3, Finset.mul_sum]
  rw [fourBody_sum_two_three_exchange]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem first_four_energy_identity {Q N : ℕ} (ψ : State Q (N+4)) :
    (inner ψ (pairApply 0 1 (pairApply 2 3 ψ))).re =
      ∑ p : Fin (2*Q+1), ∑ q : Fin (2*Q+1),
        normSq (v0PairAmplitude q (v0PairAmplitude p ψ)) := by
  rw [first_pair_inner_identity]
  simp only [Complex.re_sum, v0PairAmplitude_pairApply_two_three]
  apply Finset.sum_congr rfl
  intro p _
  rw [first_pair_energy_identity]
  simp only [normSq_eq_sum]

theorem v0PairAmplitude_smul {Q N : ℕ} (p : Fin (2*Q+1)) (c : ℂ)
    (ψ : State Q (N+2)) :
    v0PairAmplitude p (c • ψ) = c • v0PairAmplitude p ψ := by
  funext a
  simp only [v0PairAmplitude, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (pairVector Q p.val _ _ : ℂ) c, ← Finset.mul_sum]

theorem v0PairAnnihilate_composition_normSq {Q N : ℕ} (p q : Fin (2*Q+1))
    (ψ : State Q (N+4)) :
    normSq (v0PairAnnihilate q (v0PairAnnihilate p ψ)) =
      ((N+4).choose 2 : ℝ) * ((N+2).choose 2 : ℝ) *
        normSq (v0PairAmplitude q (v0PairAmplitude p ψ)) := by
  rw [v0PairAnnihilate_normSq]
  have he : v0PairAnnihilate p ψ =
      (Real.sqrt ((N+4).choose 2) : ℂ) • v0PairAmplitude p ψ := rfl
  rw [he, v0PairAmplitude_smul]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (show (0 : ℝ) ≤ ((N+4).choose 2 : ℝ) by positivity),
    normSq_eq_sum, ← Finset.mul_sum]
  ring

/-- Exact Fock normalization of two consecutive V₀ pair annihilators. -/
theorem sum_v0PairAnnihilate_composition_normSq {Q N : ℕ} (ψ : State Q (N+4)) :
    (∑ p : Fin (2*Q+1), ∑ q : Fin (2*Q+1),
      normSq (v0PairAnnihilate q (v0PairAnnihilate p ψ))) =
      ((N+4).choose 2 : ℝ) * ((N+2).choose 2 : ℝ) *
        (inner ψ (pairApply 0 1 (pairApply 2 3 ψ))).re := by
  simp_rw [v0PairAnnihilate_composition_normSq]
  rw [first_four_energy_identity]
  simp only [Finset.mul_sum]

theorem pairApply_product_permute_bosonic {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (i j k l : Fin N) (ψ : State Q N) (hψ : IsBosonic ψ) (a : Configuration Q N) :
    pairApply i j (pairApply k l ψ) (a ∘ σ) =
      pairApply (σ i) (σ j) (pairApply (σ k) (σ l) ψ) a := by
  rw [pairApply_permute]
  have he : (fun b => pairApply k l ψ (b ∘ σ)) = pairApply (σ k) (σ l) ψ :=
    funext (pairApply_permute_bosonic σ k l ψ hψ)
  rw [he]

theorem pair_product_energy_permute_bosonic {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (i j k l : Fin N) (ψ : State Q N) (hψ : IsBosonic ψ) :
    inner ψ (pairApply i j (pairApply k l ψ)) =
      inner ψ (pairApply (σ i) (σ j) (pairApply (σ k) (σ l) ψ)) := by
  unfold inner
  rw [← Equiv.sum_comp (configurationPermutation σ)
    (fun a => star (ψ a) * pairApply i j (pairApply k l ψ) a)]
  simp only [configurationPermutation, Equiv.coe_fn_mk,
    pairApply_product_permute_bosonic σ i j k l ψ hψ, hψ σ]

theorem exists_four_permutation (N : ℕ) (i j k l : Fin (N+4))
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ∃ σ : Equiv.Perm (Fin (N+4)), σ i = 0 ∧ σ j = 1 ∧ σ k = 2 ∧ σ l = 3 := by
  let f : Fin 4 → Fin (N+4) := ![i,j,k,l]
  let g : Fin 4 → Fin (N+4) := fun a => ⟨a.val, by omega⟩
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [f]
  have hg : Function.Injective g := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin (N+4) => x.val) h
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · simpa [f, g] using hσ 0
  · simpa [f, g] using hσ 1
  · apply Fin.ext
    have h := congrArg Fin.val (hσ 2)
    simpa [f, g, Fin.val_ofNat, Nat.mod_eq_of_lt (show 2 < N+4 by omega)] using h
  · apply Fin.ext
    have h := congrArg Fin.val (hσ 3)
    simpa [f, g, Fin.val_ofNat, Nat.mod_eq_of_lt (show 3 < N+4 by omega)] using h

theorem pair_product_energy_eq_first_bosonic {Q N : ℕ} (i j k l : Fin (N+4))
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (ψ : State Q (N+4)) (hψ : IsBosonic ψ) :
    inner ψ (pairApply i j (pairApply k l ψ)) =
      inner ψ (pairApply 0 1 (pairApply 2 3 ψ)) := by
  obtain ⟨σ, hi, hj, hk, hl⟩ := exists_four_permutation N i j k l hij hkl hik hil hjk hjl
  simpa only [hi, hj, hk, hl] using pair_product_energy_permute_bosonic σ i j k l ψ hψ

theorem selectedCount_exclude_pair (M : ℕ) (i j : Fin M) (hij : i ≠ j) :
    selectedCount (fun k => decide (k ≠ i ∧ k ≠ j)) = M-2 := by
  have hterm (k : Fin M) :
      (if k ≠ i ∧ k ≠ j then (1 : ℕ) else 0) +
        (if k = i then 1 else 0) + (if k = j then 1 else 0) = 1 := by
    by_cases hki : k=i
    · subst k; simp [hij]
    by_cases hkj : k=j
    · subst k; simp [hki]
    simp [hki, hkj]
  have hs := Finset.sum_congr (s₁ := (univ : Finset (Fin M))) rfl (fun k _ => hterm k)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hs
  simp only [selectedCount, decide_eq_true_eq]
  omega

theorem disjoint_unordered_pair_count (M : ℕ) (i j : Fin M) (hij : i ≠ j) :
    (∑ k : Fin M, ∑ l : Fin M,
      if k < l then if i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l then (1 : ℝ) else 0 else 0) =
        ((M-2).choose 2 : ℝ) := by
  have hn : (∑ k : Fin M, ∑ l : Fin M,
      if k < l then if i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l then (1 : ℕ) else 0 else 0) =
        (M-2).choose 2 := by
    rw [← selectedCount_exclude_pair M i j hij, ← selectedPairs_eq_choose]
    unfold selectedPairs
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    simp only [decide_eq_true_eq]
    by_cases hkl : k < l
    · simp only [hkl, ite_true, true_and]
      congr 1
      apply propext
      constructor
      · intro h
        exact ⟨⟨h.1.symm, h.2.2.1.symm⟩, h.2.1.symm, h.2.2.2.symm⟩
      · intro h
        exact ⟨h.1.1.symm, h.2.1.symm, h.1.2.symm, h.2.2.symm⟩
    · simp [hkl]
  exact_mod_cast hn

theorem normalFourBody_energy_eq_first_bosonic {Q N : ℕ}
    (ψ : State Q (N+4)) (hψ : IsBosonic ψ) :
    (inner ψ (normalFourBodyApply ψ)).re =
      ((N+4).choose 2 : ℝ) * ((N+2).choose 2 : ℝ) *
        (inner ψ (pairApply 0 1 (pairApply 2 3 ψ))).re := by
  rw [normalFourBody_energy]
  let e : ℝ := (inner ψ (pairApply 0 1 (pairApply 2 3 ψ))).re
  have hpair (i j : Fin (N+4)) (hij : i < j) :
      (∑ k : Fin (N+4), ∑ l : Fin (N+4), if k < l then
        if DisjointPairs i j k l then
          (inner ψ (pairApply i j (pairApply k l ψ))).re else 0 else 0) =
            ((N+2).choose 2 : ℝ) * e := by
    have he (k l : Fin (N+4)) :
        (if k < l then if DisjointPairs i j k l then
          (inner ψ (pairApply i j (pairApply k l ψ))).re else 0 else 0) =
            (if k < l then if DisjointPairs i j k l then (1 : ℝ) else 0 else 0) * e := by
      by_cases hkl : k < l
      · by_cases hd : DisjointPairs i j k l
        · simp only [hkl, hd, ite_true, one_mul]
          exact congrArg Complex.re (pair_product_energy_eq_first_bosonic i j k l
            (ne_of_lt hij) (ne_of_lt hkl) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 ψ hψ)
        · simp [hkl, hd]
      · simp [hkl]
    simp_rw [he, ← Finset.sum_mul]
    change (∑ k : Fin (N+4), ∑ l : Fin (N+4), if k < l then
      if i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l then (1 : ℝ) else 0 else 0) * e = _
    rw [disjoint_unordered_pair_count (N+4) i j (ne_of_lt hij)]
    congr 2
  have he (i j : Fin (N+4)) :
      (if i < j then ∑ k : Fin (N+4), ∑ l : Fin (N+4), if k < l then
        if DisjointPairs i j k l then
          (inner ψ (pairApply i j (pairApply k l ψ))).re else 0 else 0 else 0) =
            (if i < j then (1 : ℝ) else 0) * (((N+2).choose 2 : ℝ) * e) := by
    by_cases hij : i < j
    · simp only [hij, ite_true, one_mul, hpair i j hij]
    · simp [hij]
  simp_rw [he, ← Finset.sum_mul]
  rw [unordered_pair_count]
  exact (mul_assoc _ _ _).symm

/-- The actual disjoint-pair term is the positive Fock-space square sum. -/
theorem normalFourBody_eq_sum_v0PairAnnihilate_normSq {Q N : ℕ}
    (ψ : State Q (N+4)) (hψ : IsBosonic ψ) :
    (inner ψ (normalFourBodyApply ψ)).re =
      ∑ p : Fin (2*Q+1), ∑ q : Fin (2*Q+1),
        normSq (v0PairAnnihilate q (v0PairAnnihilate p ψ)) := by
  rw [normalFourBody_energy_eq_first_bosonic ψ hψ,
    sum_v0PairAnnihilate_composition_normSq]

/-- In Σp Bp† H Bp, H acts in the N+2 output sector. This is exactly S₄. -/
theorem normalFourBody_eq_sum_v0PairAnnihilate_energy {Q N : ℕ}
    (ψ : State Q (N+4)) (hψ : IsBosonic ψ) :
    (inner ψ (normalFourBodyApply ψ)).re =
      ∑ p : Fin (2*Q+1), energy (v0PairAnnihilate p ψ) := by
  rw [normalFourBody_eq_sum_v0PairAnnihilate_normSq ψ hψ]
  apply Finset.sum_congr rfl
  intro p _
  exact (energy_eq_sum_v0PairAnnihilate_normSq (v0PairAnnihilate p ψ)
    (v0PairAnnihilate_isBosonic p ψ hψ)).symm

/-- The same identity includes the two- and three-particle input sectors. -/
theorem normalFourBody_eq_sum_v0PairAnnihilate_energy_all_sectors {Q N : ℕ}
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    (inner ψ (normalFourBodyApply ψ)).re =
      ∑ p : Fin (2*Q+1), energy (v0PairAnnihilate p ψ) := by
  cases N with
  | zero =>
    rw [normalFourBody_small_sector (by omega)]
    simp [energy, hamiltonian_small_sector (N:=0) (by omega), inner]
  | succ N =>
    cases N with
    | zero =>
      rw [normalFourBody_small_sector (by omega)]
      simp [energy, hamiltonian_small_sector (N:=1) (by omega), inner]
    | succ N =>
      exact normalFourBody_eq_sum_v0PairAnnihilate_energy ψ hψ

/-- Exact H²=H+S₃+Σp,q (Bq Bp)†(Bq Bp) on every bosonic N+4 sector. -/
theorem normal_order_fock_quadratic_form {Q N : ℕ}
    (ψ : State Q (N+4)) (hψ : IsBosonic ψ) :
    normSq (hamiltonian ψ) = energy ψ + (inner ψ (normalThreeBodyApply ψ)).re +
      ∑ p : Fin (2*Q+1), ∑ q : Fin (2*Q+1),
        normSq (v0PairAnnihilate q (v0PairAnnihilate p ψ)) := by
  rw [normal_order_quadratic_form, normalFourBody_eq_sum_v0PairAnnihilate_normSq ψ hψ]

/-- Normal ordering in a form that remains typed for every N+2 input sector. -/
theorem normal_order_annihilator_energy {Q N : ℕ}
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    normSq (hamiltonian ψ) = energy ψ + (inner ψ (normalThreeBodyApply ψ)).re +
      ∑ p : Fin (2*Q+1), energy (v0PairAnnihilate p ψ) := by
  rw [normal_order_quadratic_form,
    normalFourBody_eq_sum_v0PairAnnihilate_energy_all_sectors ψ hψ]

/-- The occupation estimate summed over every physical V₀ annihilation channel,
with the right-hand side identified as S₄+H rather than an assumed error bound. -/
theorem coherent_occupation_v0_sum_lift {Q N : ℕ} (u v : ℂ)
    (hspinor : Complex.normSq u + Complex.normSq v = 1)
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    (∑ p : Fin (2*Q+1),
      modeOccupation (coherentOrbital Q u v) (v0PairAnnihilate p ψ)) ≤
        (inner ψ (normalFourBodyApply ψ)).re + energy ψ := by
  have h := Finset.sum_le_sum (s := (univ : Finset (Fin (2*Q+1))))
    (fun p _ => coherent_occupation_bound u v hspinor (v0PairAnnihilate p ψ))
  rw [Finset.sum_add_distrib,
    ← normalFourBody_eq_sum_v0PairAnnihilate_energy_all_sectors ψ hψ,
    ← energy_eq_sum_v0PairAnnihilate_normSq ψ hψ] at h
  exact h

end
end BosonicLaughlin

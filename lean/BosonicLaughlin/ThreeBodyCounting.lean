import BosonicLaughlin.FourBodyFock

/-! Permutation reduction and exact particle-slot counting for the three-body term. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem normalThreeBody_small_sector {Q N : ℕ} (hN : N ≤ 2) (ψ : State Q N) :
    normalThreeBodyApply ψ = 0 := by
  funext a
  simp only [normalThreeBodyApply, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with hij
  · apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    split_ifs with hkl ho
    · exfalso
      apply ho.1
      have hi := i.isLt
      have hj := j.isLt
      have hk := k.isLt
      have hl := l.isLt
      constructor <;> apply Fin.ext <;> omega
    · rfl
    · rfl
  · rfl

theorem normalThreeBody_inner {Q N : ℕ} (ψ φ : State Q N) :
    inner ψ (normalThreeBodyApply φ) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then
        ∑ k : Fin N, ∑ l : Fin N, if k < l then
          if ¬ (i = k ∧ j = l) ∧ ¬ DisjointPairs i j k l then
            inner ψ (pairApply i j (pairApply k l φ)) else 0
        else 0
      else 0 := by
  simp only [inner, normalThreeBodyApply, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> simp
  · simp [hij]

theorem pair_product_inner_permute_bosonic {Q N : ℕ} (σ : Equiv.Perm (Fin N))
    (i j k l : Fin N) (ψ φ : State Q N) (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner ψ (pairApply i j (pairApply k l φ)) =
      inner ψ (pairApply (σ i) (σ j) (pairApply (σ k) (σ l) φ)) := by
  unfold inner
  rw [← Equiv.sum_comp (configurationPermutation σ)
    (fun a => star (ψ a) * pairApply i j (pairApply k l φ) a)]
  simp only [configurationPermutation, Equiv.coe_fn_mk,
    pairApply_product_permute_bosonic σ i j k l φ hφ, hψ σ]

theorem exists_three_permutation (N : ℕ) (i j k : Fin (N+3))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ σ : Equiv.Perm (Fin (N+3)), σ i = 0 ∧ σ j = 1 ∧ σ k = 2 := by
  let f : Fin 3 → Fin (N+3) := ![i,j,k]
  let g : Fin 3 → Fin (N+3) := fun a => ⟨a.val, by omega⟩
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [f]
  have hg : Function.Injective g := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin (N+3) => x.val) h
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, ?_, ?_, ?_⟩
  · simpa [f, g] using hσ 0
  · simpa [f, g] using hσ 1
  · apply Fin.ext
    have h := congrArg Fin.val (hσ 2)
    simpa [f, g, Fin.val_ofNat, Nat.mod_eq_of_lt (show 2 < N+3 by omega)] using h

theorem overlap_pair_inner_eq_first_bosonic {Q N : ℕ} (i j k l : Fin (N+3))
    (hij : i < j) (hkl : k < l)
    (ho : ¬ (i = k ∧ j = l) ∧ ¬ DisjointPairs i j k l)
    (ψ φ : State Q (N+3)) (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner ψ (pairApply i j (pairApply k l φ)) =
      inner ψ (pairApply 0 1 (pairApply 0 2 φ)) := by
  have h20 : (2 : Fin (N+3)) ≠ 0 := by
    simp [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt (show 2 < N+3 by omega)]
  have h10 : (1 : Fin (N+3)) ≠ 0 := by
    simp [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt (show 1 < N+3 by omega)]
  have hd : i=k ∨ i=l ∨ j=k ∨ j=l := by
    by_contra h
    push Not at h
    exact ho.2 ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  rcases hd with hik | hil | hjk | hjl
  · subst k
    have hjl : j ≠ l := by intro he; exact ho.1 ⟨rfl, he⟩
    obtain ⟨σ, hi, hj, hl⟩ := exists_three_permutation N i j l
      (ne_of_lt hij) (ne_of_lt hkl) hjl
    simpa only [hi, hj, hl] using
      pair_product_inner_permute_bosonic σ i j i l ψ φ hψ hφ
  · subst l
    have hjk : j ≠ k := ne_of_gt (lt_trans hkl hij)
    obtain ⟨σ, hi, hj, hk⟩ := exists_three_permutation N i j k
      (ne_of_lt hij) (ne_of_gt hkl) hjk
    have he := pair_product_inner_permute_bosonic σ i j k i ψ φ hψ hφ
    simp only [hi, hj, hk] at he
    rw [pairApply_swap 2 0 h20] at he
    exact he
  · subst k
    obtain ⟨σ, hj, hi, hl⟩ := exists_three_permutation N j i l
      (ne_of_gt hij) (ne_of_lt hkl) (ne_of_lt (lt_trans hij hkl))
    have he := pair_product_inner_permute_bosonic σ i j j l ψ φ hψ hφ
    simp only [hi, hj, hl] at he
    rw [pairApply_swap 1 0 h10] at he
    exact he
  · subst l
    have hik : i ≠ k := by intro he; exact ho.1 ⟨he, rfl⟩
    obtain ⟨σ, hj, hi, hk⟩ := exists_three_permutation N j i k
      (ne_of_gt hij) (ne_of_gt hkl) hik
    have he := pair_product_inner_permute_bosonic σ i j k j ψ φ hψ hφ
    simp only [hi, hj, hk] at he
    rw [pairApply_swap 2 0 h20, pairApply_swap 1 0 h10] at he
    exact he

theorem overlap_unordered_pair_count (N : ℕ) (i j : Fin (N+3)) (hij : i < j) :
    (∑ k : Fin (N+3), ∑ l : Fin (N+3), if k < l then
      if ¬ (i=k ∧ j=l) ∧ ¬ DisjointPairs i j k l then (1 : ℝ) else 0 else 0) =
        2*(N+1) := by
  have hterm (k l : Fin (N+3)) :
      (if k<l then if ¬ (i=k ∧ j=l) ∧ ¬ DisjointPairs i j k l then (1:ℝ) else 0 else 0) +
      (if k<l then if DisjointPairs i j k l then (1:ℝ) else 0 else 0) +
      (if k<l then if i=k ∧ j=l then (1:ℝ) else 0 else 0) =
        (if k<l then (1:ℝ) else 0) := by
    by_cases hkl : k<l
    · by_cases heq : i=k ∧ j=l
      · obtain ⟨rfl, rfl⟩ := heq
        simp [DisjointPairs]
      · by_cases hd : DisjointPairs i j k l <;> simp [hkl, heq, hd]
    · simp [hkl]
  have hdiag : (∑ k : Fin (N+3), ∑ l : Fin (N+3),
      if k<l then if i=k ∧ j=l then (1:ℝ) else 0 else 0) = 1 := by
    have hd (k l : Fin (N+3)) :
        (if k<l then if i=k ∧ j=l then (1:ℝ) else 0 else 0) =
        (if i=k then if j=l then (1:ℝ) else 0 else 0) := by
      by_cases hik : i=k <;> by_cases hjl : j=l <;> simp_all
    simp_rw [hd]
    simp
  have hs := Finset.sum_congr (s₁ := (univ : Finset (Fin (N+3)))) rfl
    (fun k _ => Finset.sum_congr (s₁ := (univ : Finset (Fin (N+3)))) rfl
      (fun l _ => hterm k l))
  simp only [Finset.sum_add_distrib] at hs
  rw [hdiag, unordered_pair_count] at hs
  have hd : (∑ k : Fin (N+3), ∑ l : Fin (N+3),
      if k<l then if DisjointPairs i j k l then (1:ℝ) else 0 else 0) =
        ((N+1).choose 2 : ℝ) := by
    convert disjoint_unordered_pair_count (N+3) i j (ne_of_lt hij) using 1
    · rfl
    · congr 2
  rw [hd] at hs
  have hc : ((N+3).choose 2 : ℝ) = ((N+1).choose 2 : ℝ)+2*(N+1)+1 := by
    have ha := Nat.choose_succ_succ (N+2) 1
    have hb := Nat.choose_succ_succ (N+1) 1
    simp only [Nat.choose_one_right] at ha hb
    have haR : ((N+3).choose 2 : ℝ) = (N+2)+((N+2).choose 2 : ℝ) := by exact_mod_cast ha
    have hbR : ((N+2).choose 2 : ℝ) = (N+1)+((N+1).choose 2 : ℝ) := by exact_mod_cast hb
    linarith
  linarith

theorem overlapping_pair_count_factor (N : ℕ) :
    (N+3).choose 2 * (2*(N+1)) = 6*(N+3).choose 3 := by
  have h := Nat.choose_succ_right_eq (N+3) 2
  have he : N+3-2=N+1 := by omega
  rw [he] at h
  nlinarith

/-- Every ordered pair of unequal overlapping pairs has the same bosonic
matrix element. Its exact multiplicity is six per unordered particle triple. -/
theorem normalThreeBody_inner_eq_first_bosonic {Q N : ℕ}
    (ψ φ : State Q (N+3)) (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner ψ (normalThreeBodyApply φ) =
      ((6*(N+3).choose 3 : ℕ) : ℂ) * inner ψ (pairApply 0 1 (pairApply 0 2 φ)) := by
  rw [normalThreeBody_inner]
  let e : ℂ := inner ψ (pairApply 0 1 (pairApply 0 2 φ))
  have hpair (i j : Fin (N+3)) (hij : i<j) :
      (∑ k : Fin (N+3), ∑ l : Fin (N+3), if k<l then
        if ¬ (i=k ∧ j=l) ∧ ¬ DisjointPairs i j k l then
          inner ψ (pairApply i j (pairApply k l φ)) else 0 else 0) =
            ((2*(N+1) : ℕ) : ℂ) * e := by
    have he (k l : Fin (N+3)) :
        (if k<l then if ¬ (i=k ∧ j=l) ∧ ¬ DisjointPairs i j k l then
          inner ψ (pairApply i j (pairApply k l φ)) else 0 else 0) =
        (if k<l then if ¬ (i=k ∧ j=l) ∧ ¬ DisjointPairs i j k l then
          (1:ℂ) else 0 else 0) * e := by
      by_cases hkl : k<l
      · by_cases ho : ¬ (i=k ∧ j=l) ∧ ¬ DisjointPairs i j k l
        · rw [ite_eq_left hkl, ite_eq_left ho, ite_eq_left hkl, ite_eq_left ho, one_mul]
          exact overlap_pair_inner_eq_first_bosonic i j k l hij hkl ho ψ φ hψ hφ
        · rw [ite_eq_left hkl, ite_eq_right ho, ite_eq_left hkl, ite_eq_right ho, zero_mul]
      · simp [hkl]
    simp_rw [he, ← Finset.sum_mul]
    have hc : (∑ k : Fin (N+3), ∑ l : Fin (N+3), if k<l then
        if ¬ (i=k ∧ j=l) ∧ ¬ DisjointPairs i j k l then (1:ℂ) else 0 else 0) =
          ((2*(N+1) : ℕ) : ℂ) := by
      exact_mod_cast overlap_unordered_pair_count N i j hij
    rw [hc]
  have he (i j : Fin (N+3)) :
      (if i<j then ∑ k : Fin (N+3), ∑ l : Fin (N+3), if k<l then
        if ¬ (i=k ∧ j=l) ∧ ¬ DisjointPairs i j k l then
          inner ψ (pairApply i j (pairApply k l φ)) else 0 else 0 else 0) =
        (if i<j then (1:ℂ) else 0) * (((2*(N+1) : ℕ) : ℂ) * e) := by
    by_cases hij : i<j
    · simp only [hij, ite_true, one_mul, hpair i j hij]
    · simp [hij]
  simp_rw [he, ← Finset.sum_mul]
  have hc : (∑ i : Fin (N+3), ∑ j : Fin (N+3), if i<j then (1:ℂ) else 0) =
      ((N+3).choose 2 : ℂ) := by
    exact_mod_cast unordered_pair_count (N+3)
  rw [hc, ← mul_assoc, ← Nat.cast_mul, overlapping_pair_count_factor]

end
end BosonicLaughlin

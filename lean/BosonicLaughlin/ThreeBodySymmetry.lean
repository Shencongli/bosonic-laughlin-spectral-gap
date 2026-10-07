import BosonicLaughlin.NormalOrdering
import BosonicLaughlin.BosonicSymmetry

/-! Permutation covariance of the actual unequal-overlapping-pair three-body sum. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem unorderedPairSum_double {N : ℕ} (f : Fin N → Fin N → ℂ)
    (hf : ∀ i j, i ≠ j → f i j = f j i) :
    (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) =
        ∑ i, ∑ j, if i≠j then f i j else 0 := by
  have he : ∀ i j : Fin N, (if i≠j then f i j else 0) =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [ne_of_lt h, h, not_lt_of_ge (le_of_lt h)]
    · subst j
      simp
    · have hij : i≠j := (ne_of_lt h).symm
      simp [hij, h, not_lt_of_ge (le_of_lt h), hf i j hij]
  simp_rw [he, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

theorem unorderedPairSum_permute {N : ℕ} (f : Fin N → Fin N → ℂ)
    (hf : ∀ i j, i ≠ j → f i j = f j i) (σ : Equiv.Perm (Fin N)) :
    (∑ i, ∑ j, if i < j then f (σ i) (σ j) else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
  have hs : ∀ i j, i≠j → f (σ i) (σ j) = f (σ j) (σ i) := by
    intro i j hij
    exact hf (σ i) (σ j) (σ.injective.ne hij)
  have he : (∑ i, ∑ j, if i < j then f (σ i) (σ j) else 0) +
      (∑ i, ∑ j, if i < j then f (σ i) (σ j) else 0) =
      (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) := by
    rw [unorderedPairSum_double _ hs, unorderedPairSum_double f hf]
    have hi : ∀ i j : Fin N, i≠j ↔ σ i≠σ j := by
      intro i j
      exact σ.injective.ne_iff.symm
    calc
      _ = ∑ i, ∑ j, if σ i≠σ j then f (σ i) (σ j) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [← hi i j]
      _ = ∑ i, ∑ j, if σ i≠j then f (σ i) j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp σ (fun j => if σ i≠j then f (σ i) j else 0)
      _ = _ := Equiv.sum_comp σ (fun i => ∑ j, if i≠j then f i j else 0)
  apply mul_left_cancel₀ (by norm_num : (2:ℂ)≠0)
  simpa only [two_mul] using he

def overlapPairCondition {N : ℕ} (i j k l : Fin N) : Prop :=
  ¬ ((i=k ∧ j=l) ∨ (i=l ∧ j=k)) ∧ ¬ DisjointPairs i j k l

instance {N : ℕ} (i j k l : Fin N) : Decidable (overlapPairCondition i j k l) :=
  inferInstanceAs (Decidable (¬ ((i=k ∧ j=l) ∨ (i=l ∧ j=k)) ∧ ¬ DisjointPairs i j k l))

def overlappingPairTerm {Q N : ℕ} (ψ : State Q N) (a : Configuration Q N)
    (i j k l : Fin N) : ℂ :=
  if overlapPairCondition i j k l then pairApply i j (pairApply k l ψ) a else 0

theorem overlappingPairTerm_swap_left {Q N : ℕ} (ψ : State Q N)
    (a : Configuration Q N) (i j k l : Fin N) (hij : i≠j) :
    overlappingPairTerm ψ a i j k l = overlappingPairTerm ψ a j i k l := by
  have hc : overlapPairCondition i j k l ↔ overlapPairCondition j i k l := by
    unfold overlapPairCondition DisjointPairs
    tauto
  simp only [overlappingPairTerm, hc, pairApply_swap i j hij]

theorem overlappingPairTerm_swap_right {Q N : ℕ} (ψ : State Q N)
    (a : Configuration Q N) (i j k l : Fin N) (hkl : k≠l) :
    overlappingPairTerm ψ a i j k l = overlappingPairTerm ψ a i j l k := by
  have hc : overlapPairCondition i j k l ↔ overlapPairCondition i j l k := by
    unfold overlapPairCondition DisjointPairs
    tauto
  simp only [overlappingPairTerm, hc, pairApply_swap k l hkl]

theorem normalThreeBodyApply_overlap_sum {Q N : ℕ} (ψ : State Q N)
    (a : Configuration Q N) :
    normalThreeBodyApply ψ a =
      ∑ i, ∑ j, if i < j then ∑ k, ∑ l,
        if k < l then overlappingPairTerm ψ a i j k l else 0 else 0 := by
  unfold normalThreeBodyApply
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [hij, ite_true]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hkl : k < l
    · have hr : ¬ (i=l ∧ j=k) := by rintro ⟨rfl, rfl⟩; omega
      simp [hkl, overlappingPairTerm, overlapPairCondition, hr]
    · simp [hkl]
  · simp [hij]

theorem overlappingPairTerm_permute_bosonic {Q N : ℕ} (ψ : State Q N)
    (hψ : IsBosonic ψ) (σ : Equiv.Perm (Fin N)) (a : Configuration Q N)
    (i j k l : Fin N) :
    overlappingPairTerm ψ (a ∘ σ) i j k l =
      overlappingPairTerm ψ a (σ i) (σ j) (σ k) (σ l) := by
  have hc : overlapPairCondition (σ i) (σ j) (σ k) (σ l) ↔
      overlapPairCondition i j k l := by
    simp only [overlapPairCondition, DisjointPairs, ne_eq, σ.injective.eq_iff]
  simp only [overlappingPairTerm, hc]
  split_ifs
  · rw [pairApply_permute]
    have hp : (fun b => pairApply k l ψ (b ∘ σ)) = pairApply (σ k) (σ l) ψ := by
      funext b
      exact pairApply_permute_bosonic σ k l ψ hψ b
    rw [hp]
  · rfl

/-- The existing normal-order three-body operator preserves the bosonic sector. -/
theorem normalThreeBodyApply_isBosonic {Q N : ℕ} (ψ : State Q N)
    (hψ : IsBosonic ψ) : IsBosonic (normalThreeBodyApply ψ) := by
  intro σ a
  simp only [normalThreeBodyApply_overlap_sum]
  simp_rw [overlappingPairTerm_permute_bosonic ψ hψ σ a]
  have hi (i j : Fin N) :
      (∑ k, ∑ l, if k < l then overlappingPairTerm ψ a (σ i) (σ j) (σ k) (σ l) else 0) =
        ∑ k, ∑ l, if k < l then overlappingPairTerm ψ a (σ i) (σ j) k l else 0 := by
    apply unorderedPairSum_permute
    intro k l hkl
    exact overlappingPairTerm_swap_right ψ a (σ i) (σ j) k l hkl
  simp_rw [hi]
  apply unorderedPairSum_permute
    (fun i j => ∑ k, ∑ l, if k < l then overlappingPairTerm ψ a i j k l else 0) _ σ
  intro i j hij
  simp_rw [overlappingPairTerm_swap_left ψ a i j _ _ hij]

end
end BosonicLaughlin

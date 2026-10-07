import BosonicLaughlin.PairTensor
import BosonicLaughlin.HamiltonianForms
import BosonicLaughlin.FourBody

/-!
The exact expansion of H² by the support of two unordered particle pairs.
The three-body term contains unequal overlapping pairs; the four-body term
contains disjoint pairs. Both are defined independently of the expansion.
All identities hold on the ambient tensor space, hence on its bosonic subspace.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

/-- The complex-linear pair projector on specified tensor slots. -/
def pairApplyLinear (Q N : ℕ) (i j : Fin N) : State Q N →ₗ[ℂ] State Q N where
  toFun := pairApply i j
  map_add' := pairApply_add i j
  map_smul' := pairApply_smul i j

/-- The two pairs share no particle slot. -/
def DisjointPairs {N : ℕ} (i j k l : Fin N) : Prop :=
  i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l

instance {N : ℕ} (i j k l : Fin N) : Decidable (DisjointPairs i j k l) :=
  inferInstanceAs (Decidable (i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l))

/-- Sum of products of unequal, overlapping unordered pair projectors. -/
def normalThreeBodyApply {Q N : ℕ} (ψ : State Q N) : State Q N := by
  classical
  exact fun a => ∑ i : Fin N, ∑ j : Fin N, if i < j then
    ∑ k : Fin N, ∑ l : Fin N, if k < l then
      if ¬ (i = k ∧ j = l) ∧ ¬ DisjointPairs i j k l then
        pairApply i j (pairApply k l ψ) a else 0
    else 0
  else 0

/-- Sum over ordered choices of two disjoint unordered particle pairs. -/
def normalFourBodyApply {Q N : ℕ} (ψ : State Q N) : State Q N := by
  classical
  exact fun a => ∑ i : Fin N, ∑ j : Fin N, if i < j then
    ∑ k : Fin N, ∑ l : Fin N, if k < l then
      if DisjointPairs i j k l then pairApply i j (pairApply k l ψ) a else 0
    else 0
  else 0

theorem pairApply_hamiltonian {Q N : ℕ} (i j : Fin N) (ψ : State Q N)
    (a : Configuration Q N) :
    pairApply i j (hamiltonian ψ) a =
      ∑ k : Fin N, ∑ l : Fin N, if k < l then
        pairApply i j (pairApply k l ψ) a else 0 := by
  classical
  have h : hamiltonian ψ = ∑ k : Fin N, ∑ l : Fin N,
      if k < l then pairApply k l ψ else 0 := by
    funext b
    simp only [hamiltonian, Finset.sum_apply]
    congr 1
    ext k
    congr 1
    ext l
    split_ifs <;> rfl
  change (pairApplyLinear Q N i j) (hamiltonian ψ) a = _
  rw [h]
  simp only [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp [pairApplyLinear, pairApply]

/-- Exact support classification of H², with coefficient one for each pair. -/
theorem hamiltonian_normal_order {Q N : ℕ} (ψ : State Q N) :
    hamiltonian (hamiltonian ψ) =
      hamiltonian ψ + normalThreeBodyApply ψ + normalFourBodyApply ψ := by
  classical
  have diag (i j : Fin N) (hij : i < j) (a : Configuration Q N) :
      (∑ k : Fin N, ∑ l : Fin N, if k < l then
        if i = k ∧ j = l then pairApply i j (pairApply k l ψ) a else 0
        else 0) = pairApply i j ψ a := by
    have hterm (k l : Fin N) :
        (if k < l then if i = k ∧ j = l then
          pairApply i j (pairApply k l ψ) a else 0 else 0) =
        (if i = k then if j = l then pairApply i j (pairApply i j ψ) a
          else 0 else 0) := by
      by_cases hik : i = k <;> by_cases hjl : j = l <;> simp_all
    simp_rw [hterm]
    simpa using congrFun (pairApply_idempotent i j (ne_of_lt hij) ψ) a
  funext a
  simp only [hamiltonian, pairApply_hamiltonian, normalThreeBodyApply,
    normalFourBodyApply, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    rw [← diag i j hij a]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hkl : k < l
    · simp only [ite_eq_left hkl]
      by_cases heq : i = k ∧ j = l
      · have hd : ¬ DisjointPairs i j k l := by
          intro hd
          exact hd.1 heq.1
        have ho : ¬ (¬ (i = k ∧ j = l) ∧ ¬ DisjointPairs i j k l) := by
          exact fun h => h.1 heq
        simp only [ite_eq_left heq, ite_eq_right ho, ite_eq_right hd, add_zero]
      · by_cases hd : DisjointPairs i j k l <;> simp [heq, hd]
    · simp [hkl]
  · simp [hij]

theorem normal_order_quadratic_form {Q N : ℕ} (ψ : State Q N) :
    normSq (hamiltonian ψ) = energy ψ +
      (inner ψ (normalThreeBodyApply ψ)).re +
      (inner ψ (normalFourBodyApply ψ)).re := by
  rw [normSq, ← hamiltonian_hermitian, hamiltonian_normal_order]
  simp [inner, energy, mul_add, Finset.sum_add_distrib]

theorem normalFourBody_inner {Q N : ℕ} (ψ φ : State Q N) :
    inner ψ (normalFourBodyApply φ) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then
        ∑ k : Fin N, ∑ l : Fin N, if k < l then
          if DisjointPairs i j k l then inner ψ (pairApply i j (pairApply k l φ))
          else 0
        else 0
      else 0 := by
  classical
  simp only [inner, normalFourBodyApply, Finset.mul_sum, mul_ite, mul_zero]
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

theorem normalFourBody_energy {Q N : ℕ} (ψ : State Q N) :
    (inner ψ (normalFourBodyApply ψ)).re =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then
        ∑ k : Fin N, ∑ l : Fin N, if k < l then
          if DisjointPairs i j k l then
            (inner ψ (pairApply i j (pairApply k l ψ))).re else 0
        else 0
      else 0 := by
  classical
  rw [normalFourBody_inner]
  simp only [Complex.re_sum, apply_ite, Complex.zero_re]

/-- Positivity follows from the product of commuting orthogonal projectors. -/
theorem normalFourBody_nonneg {Q N : ℕ} (ψ : State Q N) :
    0 ≤ (inner ψ (normalFourBodyApply ψ)).re := by
  classical
  rw [normalFourBody_energy]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs with hij
  · apply Finset.sum_nonneg
    intro k _
    apply Finset.sum_nonneg
    intro l _
    split_ifs with hkl hd
    · exact pairApply_product_energy_nonneg i j k l (ne_of_lt hij) (ne_of_lt hkl)
        hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 ψ
    · exact le_rfl
    · exact le_rfl
  · exact le_rfl

theorem normalFourBody_hermitian {Q N : ℕ} (ψ φ : State Q N) :
    inner ψ (normalFourBodyApply φ) = inner (normalFourBodyApply ψ) φ := by
  classical
  conv_rhs => rw [← inner_star]
  rw [normalFourBody_inner, normalFourBody_inner]
  simp only [Complex.star_def, map_sum, apply_ite, map_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    split_ifs with hkl hd
    · rw [pairApply_hermitian i j (ne_of_lt hij),
        pairApply_hermitian k l (ne_of_lt hkl),
        pairApply_commute_disjoint k l i j hd.1.symm hd.2.2.1.symm
          hd.2.1.symm hd.2.2.2.symm, ← Complex.star_def, inner_star]
    · rfl
    · rfl
  · rfl

/-- The three-body contribution is Hermitian; no positivity is asserted. -/
theorem normalThreeBody_hermitian {Q N : ℕ} (ψ φ : State Q N) :
    inner ψ (normalThreeBodyApply φ) = inner (normalThreeBodyApply ψ) φ := by
  have h : inner ψ (hamiltonian (hamiltonian φ)) =
      inner (hamiltonian (hamiltonian ψ)) φ := by
    rw [hamiltonian_hermitian, hamiltonian_hermitian]
  rw [hamiltonian_normal_order, hamiltonian_normal_order] at h
  simp only [inner, Pi.add_apply, mul_add, add_mul, star_add,
    Finset.sum_add_distrib] at h
  have hH := hamiltonian_hermitian ψ φ
  have h4 := normalFourBody_hermitian ψ φ
  simp only [inner] at hH h4 ⊢
  linear_combination h - hH - h4

theorem normalFourBody_small_sector {Q N : ℕ} (hN : N ≤ 3) (ψ : State Q N) :
    normalFourBodyApply ψ = 0 := by
  classical
  funext a
  simp only [normalFourBodyApply, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with hij
  · apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    split_ifs with hkl hd
    · have hi := i.isLt
      have hj := j.isLt
      have hk := k.isLt
      have hl := l.isLt
      rcases hd with ⟨hik, hil, hjk, hjl⟩
      omega
    · rfl
    · rfl
  · rfl

theorem three_particle_square {Q : ℕ} (ψ : State Q 3) :
    hamiltonian (hamiltonian ψ) = hamiltonian ψ + normalThreeBodyApply ψ := by
  rw [hamiltonian_normal_order, normalFourBody_small_sector (by omega), add_zero]

end
end BosonicLaughlin

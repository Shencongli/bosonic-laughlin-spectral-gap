import BosonicLaughlin.Model
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linarith

namespace BosonicLaughlin
noncomputable section
open Finset

/-- Number of occupied slots selected by a Boolean predicate. -/
def selectedCount {N : ℕ} (f : Fin N → Bool) : ℕ :=
  ∑ i, if f i then 1 else 0

/-- Number of unordered pairs of selected slots. -/
def selectedPairs {N : ℕ} (f : Fin N → Bool) : ℕ :=
  ∑ i, ∑ j, if i < j ∧ f i = true ∧ f j = true then 1 else 0

theorem selectedCount_succ {N : ℕ} (f : Fin (N+1) → Bool) :
    selectedCount f = (if f 0 then 1 else 0) + selectedCount (fun i => f i.succ) := by
  simp only [selectedCount, Fin.sum_univ_succ]

theorem selectedPairs_succ {N : ℕ} (f : Fin (N+1) → Bool) :
    selectedPairs f = (if f 0 then selectedCount (fun i => f i.succ) else 0) +
      selectedPairs (fun i => f i.succ) := by
  unfold selectedPairs selectedCount
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, Fin.not_lt_zero, false_and, ite_eq_right,
    not_false_eq_true, Fin.succ_pos, true_and, Fin.succ_lt_succ_iff, zero_add]
  cases f 0 <;> simp

theorem selectedPairs_eq_choose {N : ℕ} (f : Fin N → Bool) :
    selectedPairs f = (selectedCount f).choose 2 := by
  induction N with
  | zero => simp [selectedPairs, selectedCount]
  | succ N ih =>
    rw [selectedPairs_succ, selectedCount_succ, ih]
    cases h : f 0
    · simp
    · simp only [ite_true]
      rw [Nat.add_comm 1 _, Nat.choose_succ_succ]
      simp

theorem occupation_scalar_bound (n : ℕ) : n ≤ n.choose 2 + 1 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    omega

def orbitalCount {Q N : ℕ} (k : Orbital Q) (a : Configuration Q N) : ℕ :=
  selectedCount (fun i => decide (a i = k))

/-- Quadratic form of the number operator in a specified basis orbital. -/
def orbitalOccupation {Q N : ℕ} (k : Orbital Q) (ψ : State Q N) : ℝ :=
  ∑ a, (orbitalCount k a : ℝ) * Complex.normSq (ψ a)

/-- Quadratic form of n_k(n_k-1)/2, in tensor coordinates. -/
def orbitalPairOccupation {Q N : ℕ} (k : Orbital Q) (ψ : State Q N) : ℝ :=
  ∑ a, ((orbitalCount k a).choose 2 : ℝ) * Complex.normSq (ψ a)

theorem normSq_eq_sum {Q N : ℕ} (ψ : State Q N) :
    normSq ψ = ∑ a, Complex.normSq (ψ a) := by
  unfold normSq inner
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (starRingEnd ℂ (ψ a) * ψ a).re = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem orbitalPairOccupation_eq_pair_sum {Q N : ℕ} (k : Orbital Q) (ψ : State Q N) :
    orbitalPairOccupation k ψ =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then
        ∑ a : Configuration Q N, if a i = k ∧ a j = k then Complex.normSq (ψ a) else 0
      else 0 := by
  unfold orbitalPairOccupation orbitalCount
  simp_rw [← selectedPairs_eq_choose]
  unfold selectedPairs
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [hij, true_and, decide_eq_true_eq, ite_true]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  · simp [hij]

/-- The discrete occupation bound on every tensor sector, with no N-dependent constant. -/
theorem orbitalOccupation_le_pairs_add_norm {Q N : ℕ} (k : Orbital Q) (ψ : State Q N) :
    orbitalOccupation k ψ ≤ orbitalPairOccupation k ψ + normSq ψ := by
  rw [normSq_eq_sum]
  unfold orbitalOccupation orbitalPairOccupation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have h : (orbitalCount k a : ℝ) ≤ ((orbitalCount k a).choose 2 : ℝ) + 1 := by
    exact_mod_cast occupation_scalar_bound (orbitalCount k a)
  have hmul := mul_le_mul_of_nonneg_right h (Complex.normSq_nonneg (ψ a))
  simpa only [add_mul, one_mul] using hmul

end
end BosonicLaughlin

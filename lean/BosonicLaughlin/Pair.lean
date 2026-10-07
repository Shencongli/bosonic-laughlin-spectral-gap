import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Field

/-!
The spherical V₀ pair coefficient in the orthonormal orbital basis.
Q is the integer flux. The integer p is the sum of the two orbital labels.
Using a block indexed by Fin (p+1) includes zero entries when either label
exceeds Q; these entries vanish by the definition of Nat.choose.
-/
namespace BosonicLaughlin

noncomputable section
open Finset

def pairWeight (Q p i : ℕ) : ℝ :=
  (Q.choose i : ℝ) * (Q.choose (p-i) : ℝ)

def pairCoefficient (Q p i : ℕ) : ℝ :=
  Real.sqrt (pairWeight Q p i / ((2*Q).choose p : ℝ))

theorem pairWeight_nonneg (Q p i : ℕ) : 0 ≤ pairWeight Q p i := by
  unfold pairWeight
  positivity

theorem pairCoefficient_nonneg (Q p i : ℕ) : 0 ≤ pairCoefficient Q p i :=
  Real.sqrt_nonneg _

theorem pairCoefficient_sq (Q p i : ℕ) :
    pairCoefficient Q p i ^ 2 = pairWeight Q p i / ((2*Q).choose p : ℝ) := by
  unfold pairCoefficient
  exact Real.sq_sqrt (div_nonneg (pairWeight_nonneg Q p i) (by positivity))

theorem pairWeight_sum (Q p : ℕ) :
    ∑ i ∈ range (p+1), pairWeight Q p i = ((2*Q).choose p : ℝ) := by
  have h := Nat.add_choose_eq Q Q p
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [two_mul, Nat.succ_eq_add_one] at *
  simp only [pairWeight]
  exact_mod_cast h.symm

/-- Exact normalization, valid for every allowed pair block, with no flux threshold. -/
theorem pairCoefficient_normalized (Q p : ℕ) (hp : p ≤ 2*Q) :
    ∑ i ∈ range (p+1), pairCoefficient Q p i ^ 2 = 1 := by
  simp_rw [pairCoefficient_sq]
  rw [← Finset.sum_div, pairWeight_sum]
  exact div_self (by exact_mod_cast (Nat.choose_pos hp).ne')

theorem pairCoefficient_exchange (Q p i : ℕ) (hi : i ≤ p) :
    pairCoefficient Q p (p-i) = pairCoefficient Q p i := by
  unfold pairCoefficient pairWeight
  rw [Nat.sub_sub_self hi, mul_comm]

theorem pairCoefficient_zero_left (Q p i : ℕ) (hi : Q < i) :
    pairCoefficient Q p i = 0 := by
  simp [pairCoefficient, pairWeight, Nat.choose_eq_zero_of_lt hi]

theorem pairCoefficient_zero_right (Q p i : ℕ) (hi : Q < p-i) :
    pairCoefficient Q p i = 0 := by
  simp [pairCoefficient, pairWeight, Nat.choose_eq_zero_of_lt hi]

end
end BosonicLaughlin

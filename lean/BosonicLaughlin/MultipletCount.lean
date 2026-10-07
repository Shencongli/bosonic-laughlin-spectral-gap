import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! The exact dimension count for the pair-spin and spectator multiplets. -/
namespace BosonicLaughlin
open Finset

theorem multiplet_dimension_sum (Q : ℕ) :
    (∑ z : Fin (Q+1), (3*Q-2*z.val+1)) = (2*Q+1)*(Q+1) := by
  have hp : ∀ z : Fin (Q+1), (3*Q-2*z.val+1)+2*z.val=3*Q+1 := by
    intro z
    omega
  have hs : (∑ z : Fin (Q+1), (3*Q-2*z.val+1)) +
      2*(∑ z : Fin (Q+1), z.val) = (Q+1)*(3*Q+1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_cast
  have hz : (∑ z : Fin (Q+1), z.val)*2 = (Q+1)*Q := by
    rw [Fin.sum_univ_eq_sum_range (fun z => z)]
    simpa using Finset.sum_range_id_mul_two (Q+1)
  nlinarith

end BosonicLaughlin

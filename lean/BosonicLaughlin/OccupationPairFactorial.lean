import BosonicLaughlin.PolynomialCoordinates
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Sym.Basic

/-! Exact occupation multiplicities for polynomial coefficient coordinates. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def multisetOccupationFactorial {α : Type*} [Fintype α] [DecidableEq α]
    (A : Multiset α) : ℕ := ∏ j : α, (A.count j).factorial

theorem multisetOccupationFactorial_pos {α : Type*} [Fintype α] [DecidableEq α]
    (A : Multiset α) : 0 < multisetOccupationFactorial A := by
  exact Finset.prod_pos (fun j _ => Nat.factorial_pos _)

theorem multisetOccupationFactorial_cons {α : Type*} [Fintype α] [DecidableEq α]
    (x : α) (A : Multiset α) :
    multisetOccupationFactorial (x ::ₘ A) =
      (A.count x + 1) * multisetOccupationFactorial A := by
  unfold multisetOccupationFactorial
  rw [← Finset.mul_prod_erase univ (fun j => ((x ::ₘ A).count j).factorial) (mem_univ x),
    ← Finset.mul_prod_erase univ (fun j => (A.count j).factorial) (mem_univ x)]
  have hp : (∏ j ∈ univ.erase x, ((x ::ₘ A).count j).factorial) =
      ∏ j ∈ univ.erase x, (A.count j).factorial := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hp, Multiset.count_cons_self, Nat.factorial_succ]
  exact mul_assoc _ _ _

theorem multisetOccupationFactorial_cons_twice {α : Type*} [Fintype α] [DecidableEq α]
    (x y : α) (A : Multiset α) :
    multisetOccupationFactorial (x ::ₘ y ::ₘ A) =
      ((x ::ₘ y ::ₘ A).count x * (y ::ₘ A).count y) * multisetOccupationFactorial A := by
  rw [multisetOccupationFactorial_cons x, multisetOccupationFactorial_cons y]
  simp only [Multiset.count_cons_self]
  exact (mul_assoc _ _ _).symm

end
end BosonicLaughlin

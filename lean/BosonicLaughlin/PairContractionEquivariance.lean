import BosonicLaughlin.PairEquivariance

/-! Equivariance of contraction with the concrete normalized pair vectors. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def pairInsert {Q : ℕ} (v : Fin (2*Q+1) → ℂ) (x y : Orbital Q) : ℂ :=
  ∑ p, (pairVector Q p.val x y : ℂ) * v p

def pairContract {Q : ℕ} (ψ : Orbital Q → Orbital Q → ℂ) (p : Fin (2*Q+1)) : ℂ :=
  ∑ x, ∑ y, (pairVector Q p.val x y : ℂ) * ψ x y

theorem pairInsert_lower {Q : ℕ} (v : Fin (2*Q+1) → ℂ) (x y : Orbital Q) :
    pairInsert (spinLower v) x y =
      spinLower (fun a => pairInsert v a y) x + spinLower (pairInsert v x) y := by
  exact threeBodyInsertion_pair_lower (fun p _ => v p) x y 0

theorem pairInsert_raise {Q : ℕ} (v : Fin (2*Q+1) → ℂ) (x y : Orbital Q) :
    pairInsert (spinRaise v) x y =
      spinRaise (fun a => pairInsert v a y) x + spinRaise (pairInsert v x) y := by
  exact threeBodyInsertion_pair_raise (fun p _ => v p) x y 0

theorem pairInsert_bilinear {Q : ℕ} (v : Fin (2*Q+1) → ℂ)
    (ψ : Orbital Q → Orbital Q → ℂ) :
    (∑ x, ∑ y, pairInsert v x y * ψ x y) =
      ∑ p, v p * pairContract ψ p := by
  simp only [pairInsert, pairContract, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem pairContract_raise_bilinear {Q : ℕ} (v : Fin (2*Q+1) → ℂ)
    (ψ : Orbital Q → Orbital Q → ℂ) :
    (∑ p, v p * pairContract
      (fun x y => spinRaise (fun a => ψ a y) x + spinRaise (ψ x) y) p) =
      ∑ p, v p * spinRaise (pairContract ψ) p := by
  rw [← pairInsert_bilinear, spinRaise_bilinear, ← pairInsert_bilinear]
  simp only [pairInsert_lower, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm, Finset.sum_comm
        (f := fun x y => spinLower (fun a => pairInsert v a y) x * ψ x y)]
    apply Finset.sum_congr rfl
    intro y _
    exact spinRaise_bilinear (fun x => pairInsert v x y) (fun x => ψ x y)
  · apply Finset.sum_congr rfl
    intro x _
    exact spinRaise_bilinear (pairInsert v x) (ψ x)

theorem pairContract_raise {Q : ℕ} (ψ : Orbital Q → Orbital Q → ℂ) :
    pairContract (fun x y => spinRaise (fun a => ψ a y) x + spinRaise (ψ x) y) =
      spinRaise (pairContract ψ) := by
  funext p
  have h := pairContract_raise_bilinear (fun q => if q=p then 1 else 0) ψ
  simpa using h

theorem pairContract_lower_bilinear {Q : ℕ} (v : Fin (2*Q+1) → ℂ)
    (ψ : Orbital Q → Orbital Q → ℂ) :
    (∑ p, v p * pairContract
      (fun x y => spinLower (fun a => ψ a y) x + spinLower (ψ x) y) p) =
      ∑ p, v p * spinLower (pairContract ψ) p := by
  rw [← pairInsert_bilinear, spinLower_bilinear, ← pairInsert_bilinear]
  simp only [pairInsert_raise, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm, Finset.sum_comm
        (f := fun x y => spinRaise (fun a => pairInsert v a y) x * ψ x y)]
    apply Finset.sum_congr rfl
    intro y _
    exact spinLower_bilinear (fun x => pairInsert v x y) (fun x => ψ x y)
  · apply Finset.sum_congr rfl
    intro x _
    exact spinLower_bilinear (pairInsert v x) (ψ x)

theorem pairContract_lower {Q : ℕ} (ψ : Orbital Q → Orbital Q → ℂ) :
    pairContract (fun x y => spinLower (fun a => ψ a y) x + spinLower (ψ x) y) =
      spinLower (pairContract ψ) := by
  funext p
  have h := pairContract_lower_bilinear (fun q => if q=p then 1 else 0) ψ
  simpa using h

end
end BosonicLaughlin

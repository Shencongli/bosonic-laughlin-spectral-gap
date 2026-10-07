import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

namespace BosonicLaughlin
noncomputable section
open Finset Matrix
open scoped ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

def projectionNumber {N : ℕ} (P : Fin N → Matrix d d ℂ) : Matrix d d ℂ := ∑ i, P i

def projectionPairs {N : ℕ} (P : Fin N → Matrix d d ℂ) : Matrix d d ℂ :=
  ∑ i, ∑ j, if i < j then P i * P j else 0

omit [Fintype d] [DecidableEq d] in
theorem projectionNumber_succ {N : ℕ} (P : Fin (N+1) → Matrix d d ℂ) :
    projectionNumber P = P 0 + projectionNumber (fun i => P i.succ) := by
  simp only [projectionNumber, Fin.sum_univ_succ]

omit [DecidableEq d] in
theorem projectionPairs_succ {N : ℕ} (P : Fin (N+1) → Matrix d d ℂ) :
    projectionPairs P = P 0 * projectionNumber (fun i => P i.succ) +
      projectionPairs (fun i => P i.succ) := by
  unfold projectionPairs projectionNumber
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, Fin.not_lt_zero, ite_eq_right, not_false_eq_true,
    Fin.succ_pos, ite_true, Fin.succ_lt_succ_iff, zero_add, Matrix.mul_sum]

omit [DecidableEq d] in
theorem commute_projectionNumber {N : ℕ} (A : Matrix d d ℂ)
    (P : Fin N → Matrix d d ℂ) (h : ∀ i, Commute A (P i)) :
    Commute A (projectionNumber P) := by
  unfold Commute SemiconjBy projectionNumber
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => (h i).eq)

theorem commute_projectionPairs {N : ℕ} (A : Matrix d d ℂ)
    (P : Fin N → Matrix d d ℂ) (h : ∀ i, Commute A (P i)) :
    Commute A (projectionPairs P) := by
  unfold Commute SemiconjBy projectionPairs
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · exact ((h i).mul_right (h j)).eq
  · simp

omit [DecidableEq d] in
theorem projection_posSemidef (P : Matrix d d ℂ)
    (hstar : P.IsHermitian) (hsq : P*P=P) : P.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  simpa only [hstar.eq, hsq] using h

omit [DecidableEq d] in
theorem projection_sandwich (P A : Matrix d d ℂ) (hsq : P*P=P)
    (hcomm : Commute P A) : P*A*P=P*A := by
  rw [hcomm.eq, Matrix.mul_assoc, hsq, ← hcomm.eq]

theorem projection_occupation_decomposition (P A C : Matrix d d ℂ)
    (hsq : P*P=P) (hA : Commute P A) (hC : Commute P C) :
    (1-P)*(1-A+C)*(1-P)+P*C*P = 1-(P+A)+(P*A+C) := by
  have hPA := projection_sandwich P A hsq hA
  have hPC := projection_sandwich P C hsq hC
  noncomm_ring [hsq, hPA, hPC, hA.eq, hC.eq]

/-- Simultaneous positivity of the number, pair-count, and occupation-defect operators.
The third component is n ≤ I + sum_{i<j} P_i P_j for commuting orthogonal
projections, with no dependence of the coefficient on the number of slots. -/
theorem projection_occupation_positive {N : ℕ} (P : Fin N → Matrix d d ℂ)
    (hstar : ∀ i, (P i).IsHermitian) (hsq : ∀ i, P i*P i=P i)
    (hcomm : ∀ i j, Commute (P i) (P j)) :
    (projectionNumber P).PosSemidef ∧ (projectionPairs P).PosSemidef ∧
      (1-projectionNumber P+projectionPairs P).PosSemidef := by
  induction N with
  | zero =>
    simp only [projectionNumber, projectionPairs, Finset.univ_eq_empty,
      Finset.sum_empty, sub_zero, add_zero]
    exact ⟨Matrix.PosSemidef.zero, Matrix.PosSemidef.zero, Matrix.PosSemidef.one⟩
  | succ N ih =>
    let T : Fin N → Matrix d d ℂ := fun i => P i.succ
    have ht := ih T (fun i => hstar i.succ) (fun i => hsq i.succ)
      (fun i j => hcomm i.succ j.succ)
    have hp := projection_posSemidef (P 0) (hstar 0) (hsq 0)
    have hpa := commute_projectionNumber (P 0) T (fun i => hcomm 0 i.succ)
    have hpc := commute_projectionPairs (P 0) T (fun i => hcomm 0 i.succ)
    have hprod : (P 0 * projectionNumber T).PosSemidef := by
      have hh := ht.1.conjTranspose_mul_mul_same (P 0)
      simpa only [(hstar 0).eq, projection_sandwich _ _ (hsq 0) hpa] using hh
    rw [projectionNumber_succ, projectionPairs_succ]
    refine ⟨hp.add ht.1, hprod.add ht.2.1, ?_⟩
    have h1 := ht.2.2.conjTranspose_mul_mul_same (1-P 0)
    have h2 := ht.2.1.conjTranspose_mul_mul_same (P 0)
    have hh := h1.add h2
    simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (hstar 0).eq,
      projection_occupation_decomposition _ _ _ (hsq 0) hpa hpc] using hh

/-- Real quadratic form in the finite orthonormal coordinate basis. -/
def matrixQuadratic (A : Matrix d d ℂ) (ψ : d → ℂ) : ℝ :=
  (star ψ ⬝ᵥ (A *ᵥ ψ)).re

theorem projection_occupation_form {N : ℕ} (P : Fin N → Matrix d d ℂ)
    (hstar : ∀ i, (P i).IsHermitian) (hsq : ∀ i, P i*P i=P i)
    (hcomm : ∀ i j, Commute (P i) (P j)) (ψ : d → ℂ) :
    matrixQuadratic (projectionNumber P) ψ ≤ matrixQuadratic (1 : Matrix d d ℂ) ψ +
      matrixQuadratic (projectionPairs P) ψ := by
  have h := (projection_occupation_positive P hstar hsq hcomm).2.2.dotProduct_mulVec_nonneg ψ
  have hr := (Complex.nonneg_iff.mp h).1
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub,
    Complex.add_re, Complex.sub_re] at hr
  unfold matrixQuadratic
  linarith

/-- The pair count is the second factorial moment of the number operator. -/
theorem projection_factorial_moment {N : ℕ} (P : Fin N → Matrix d d ℂ)
    (hsq : ∀ i, P i*P i=P i) (hcomm : ∀ i j, Commute (P i) (P j)) :
    projectionNumber P * projectionNumber P - projectionNumber P =
      projectionPairs P + projectionPairs P := by
  induction N with
  | zero => simp [projectionNumber, projectionPairs]
  | succ N ih =>
    let T : Fin N → Matrix d d ℂ := fun i => P i.succ
    have ht := ih T (fun i => hsq i.succ) (fun i j => hcomm i.succ j.succ)
    have hc := commute_projectionNumber (P 0) T (fun i => hcomm 0 i.succ)
    rw [projectionNumber_succ, projectionPairs_succ]
    change (P 0+projectionNumber T)*(P 0+projectionNumber T)-(P 0+projectionNumber T) = _
    calc
      _ = (P 0*P 0-P 0) + (P 0*projectionNumber T+projectionNumber T*P 0) +
        (projectionNumber T*projectionNumber T-projectionNumber T) := by noncomm_ring
      _ = _ := by rw [hsq 0, sub_self, ht, ← hc.eq]; abel

end
end BosonicLaughlin

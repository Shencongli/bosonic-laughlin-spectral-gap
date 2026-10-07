import BosonicLaughlin.Pair
import BosonicLaughlin.ThreeBodyGram
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-!
Exact coefficient identities used in the three-body recoupling calculation,
and one explicit nonzero deficit-one kernel vector of the physical creation map.
The full spectral decomposition of the compressed transposition still requires
equivariance and a complete family of eigenvectors.
The highest-weight recurrence is represented by its finite product, normalized
to have first coefficient one.
-/
namespace BosonicLaughlin

noncomputable section
open Finset

/-- The positive falling-factorial ratio appearing in the proposed spin blocks. -/
def recouplingRatio (Q z : ℕ) : ℝ :=
  (Q.descFactorial z : ℝ) / ((2 * Q).descFactorial z : ℝ)

theorem recouplingRatio_zero (Q : ℕ) : recouplingRatio Q 0 = 1 := by
  simp [recouplingRatio]

theorem recouplingRatio_pos (Q z : ℕ) (hz : z ≤ Q) :
    0 < recouplingRatio Q z := by
  unfold recouplingRatio
  exact div_pos (by exact_mod_cast Nat.descFactorial_pos.mpr hz)
    (by exact_mod_cast Nat.descFactorial_pos.mpr (show z ≤ 2 * Q by omega))

theorem recouplingRatio_succ (Q z : ℕ) :
    recouplingRatio Q (z + 1) =
      ((Q - z : ℕ) : ℝ) / ((2 * Q - z : ℕ) : ℝ) * recouplingRatio Q z := by
  simp only [recouplingRatio, Nat.descFactorial_succ, Nat.cast_mul]
  ring

theorem recouplingRatio_one (Q : ℕ) (hQ : 0 < Q) :
    recouplingRatio Q 1 = 1 / 2 := by
  simp only [recouplingRatio, Nat.descFactorial_one, Nat.cast_mul, Nat.cast_ofNat]
  have h : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  field_simp

theorem recouplingRatio_eq_choose_ratio (Q z : ℕ) :
    recouplingRatio Q z = (Q.choose z : ℝ) / ((2 * Q).choose z : ℝ) := by
  simp only [recouplingRatio, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast z.factorial_ne_zero)

theorem recouplingRatio_le_half_pow (Q z : ℕ) (hz : z ≤ Q) :
    recouplingRatio Q z ≤ (1 / 2 : ℝ) ^ z := by
  induction z with
  | zero => simp [recouplingRatio_zero]
  | succ z ih =>
    have hzQ : z ≤ Q := by omega
    have hden : (0 : ℝ) < ((2 * Q - z : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < 2 * Q - z by omega)
    have hstep : ((Q - z : ℕ) : ℝ) / ((2 * Q - z : ℕ) : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hden]
      have hnat : 2 * (Q - z) ≤ 2 * Q - z := by omega
      have hreal : 2 * ((Q - z : ℕ) : ℝ) ≤ ((2 * Q - z : ℕ) : ℝ) := by
        exact_mod_cast hnat
      linarith
    rw [recouplingRatio_succ, pow_succ]
    calc
      _ ≤ (1 / 2) * recouplingRatio Q z :=
        mul_le_mul_of_nonneg_right hstep (le_of_lt (recouplingRatio_pos Q z hzQ))
      _ ≤ (1 / 2) * (1 / 2 : ℝ) ^ z := by gcongr; exact ih hzQ
      _ = _ := mul_comm _ _

/-- The actual pair-vector endpoint in the manuscript's coefficient extraction. -/
theorem pairCoefficient_endpoint_recoupling (Q z : ℕ) :
    pairCoefficient Q z 0 = Real.sqrt (recouplingRatio Q z) := by
  simp [pairCoefficient, pairWeight, recouplingRatio_eq_choose_ratio]

/-- Squared ratio of consecutive highest-weight coefficients, with natural
subtraction; its intended range is `p < z ≤ Q`. -/
def highestWeightStepSq (Q z p : ℕ) : ℝ :=
  (((z - p : ℕ) : ℝ) * ((Q - z + p + 1 : ℕ) : ℝ)) /
    (((p + 1 : ℕ) : ℝ) * ((2 * Q - p : ℕ) : ℝ))

def highestWeightCoefficient (Q z p : ℕ) : ℝ :=
  ∏ k ∈ range p, -Real.sqrt (highestWeightStepSq Q z k)

theorem highestWeightCoefficient_zero (Q z : ℕ) :
    highestWeightCoefficient Q z 0 = 1 := by
  simp [highestWeightCoefficient]

theorem highestWeightCoefficient_succ (Q z p : ℕ) :
    highestWeightCoefficient Q z (p + 1) =
      -Real.sqrt (highestWeightStepSq Q z p) * highestWeightCoefficient Q z p := by
  simp only [highestWeightCoefficient, prod_range_succ]
  ring

theorem highestWeightStepSq_nonneg (Q z p : ℕ) :
    0 ≤ highestWeightStepSq Q z p := by
  unfold highestWeightStepSq
  positivity

theorem highestWeightStepSq_pos (Q z p : ℕ) (hp : p < z) (hz : z ≤ Q) :
    0 < highestWeightStepSq Q z p := by
  unfold highestWeightStepSq
  apply div_pos
  · apply mul_pos
    · exact_mod_cast Nat.sub_pos_of_lt hp
    · positivity
  · apply mul_pos (by positivity)
    exact_mod_cast (show 0 < 2 * Q - p by omega)

theorem highestWeightCoefficient_ne_zero (Q z p : ℕ) (hp : p ≤ z) (hz : z ≤ Q) :
    highestWeightCoefficient Q z p ≠ 0 := by
  unfold highestWeightCoefficient
  apply prod_ne_zero_iff.mpr
  intro k hk
  exact neg_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr
    (highestWeightStepSq_pos Q z k (by have := mem_range.mp hk; omega) hz)))

theorem highestWeightCoefficient_ratio (Q z p : ℕ) (hp : p < z) (hz : z ≤ Q) :
    highestWeightCoefficient Q z (p + 1) / highestWeightCoefficient Q z p =
      -Real.sqrt (highestWeightStepSq Q z p) := by
  rw [highestWeightCoefficient_succ,
    mul_div_cancel_right₀ _ (highestWeightCoefficient_ne_zero Q z p (by omega) hz)]

/-- Cancellation of the two ladder contributions at every interior weight.
The two square roots are the spin-Q and spin-Q/2 raising coefficients in
the orthonormal basis used in the manuscript. -/
theorem highestWeightCoefficient_ladder_cancel (Q z p : ℕ)
    (hp : p < z) (hz : z ≤ Q) :
    Real.sqrt (((p + 1 : ℕ) : ℝ) * ((2 * Q - p : ℕ) : ℝ)) *
      highestWeightCoefficient Q z (p + 1) +
    Real.sqrt (((z - p : ℕ) : ℝ) * ((Q - z + p + 1 : ℕ) : ℝ)) *
      highestWeightCoefficient Q z p = 0 := by
  have hden : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) * ((2 * Q - p : ℕ) : ℝ) := by
    apply mul_pos (by positivity)
    exact_mod_cast (show 0 < 2 * Q - p by omega)
  have hsqrt : Real.sqrt (((p + 1 : ℕ) : ℝ) * ((2 * Q - p : ℕ) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hden)
  rw [highestWeightCoefficient_succ, highestWeightStepSq,
    Real.sqrt_div (by positivity)]
  field_simp
  ring

theorem highestWeightStepSq_product (Q z p : ℕ) :
    (∏ k ∈ range p, highestWeightStepSq Q z k) =
      (z.descFactorial p : ℝ) * ((Q - z + 1).ascFactorial p : ℝ) /
        ((p.factorial : ℝ) * ((2 * Q).descFactorial p : ℝ)) := by
  simp only [highestWeightStepSq, prod_div_distrib, prod_mul_distrib,
    Nat.descFactorial_eq_prod_range, Nat.ascFactorial_eq_prod_range,
    Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
  congr 3
  funext k
  congr 1
  omega

theorem highestWeightStepSq_endpoint_product (Q z : ℕ) (hz : z ≤ Q) :
    (∏ k ∈ range z, highestWeightStepSq Q z k) = recouplingRatio Q z := by
  rw [highestWeightStepSq_product, Nat.descFactorial_self,
    ← Nat.add_descFactorial_eq_ascFactorial, Nat.sub_add_cancel hz]
  unfold recouplingRatio
  exact mul_div_mul_left _ _ (by exact_mod_cast z.factorial_ne_zero)

/-- Telescoping the displayed highest-weight recurrence gives its endpoint.
This proves the coefficient identity, independently of whether the recurrence
has yet been realized as an SU(2) highest-weight vector. -/
theorem highestWeightCoefficient_endpoint (Q z : ℕ) (hz : z ≤ Q) :
    highestWeightCoefficient Q z z =
      (-1 : ℝ) ^ z * Real.sqrt (recouplingRatio Q z) := by
  unfold highestWeightCoefficient
  rw [prod_neg, card_range, ← Real.sqrt_prod (range z)
    (fun k _ => highestWeightStepSq_nonneg Q z k),
    highestWeightStepSq_endpoint_product Q z hz]

/-- The scalar extracted from the endpoint is exactly the signed ratio. -/
theorem recoupling_endpoint_coefficient (Q z : ℕ) (hz : z ≤ Q) :
    highestWeightCoefficient Q z z * pairCoefficient Q z 0 =
      (-1 : ℝ) ^ z * recouplingRatio Q z := by
  rw [highestWeightCoefficient_endpoint Q z hz, pairCoefficient_endpoint_recoupling,
    mul_assoc, Real.mul_self_sqrt (le_of_lt (recouplingRatio_pos Q z hz))]

theorem recoupling_one_gram_scalar (Q : ℕ) (hQ : 0 < Q) :
    1 + 2 * (-1 : ℝ) ^ 1 * recouplingRatio Q 1 = 0 := by
  rw [recouplingRatio_one Q hQ]
  norm_num

theorem pairVector_one (Q : ℕ) (hQ : 0 < Q) (x y : Orbital Q) :
    pairVector Q 1 x y =
      if (x.val = 0 ∧ y.val = 1) ∨ (x.val = 1 ∧ y.val = 0)
      then Real.sqrt (1 / 2) else 0 := by
  have hc : pairCoefficient Q 1 0 = Real.sqrt (1 / 2) := by
    rw [pairCoefficient_endpoint_recoupling, recouplingRatio_one Q hQ]
  have hc1 : pairCoefficient Q 1 1 = Real.sqrt (1 / 2) := by
    simpa using (pairCoefficient_exchange Q 1 0 (by omega)).trans hc
  unfold pairVector
  split_ifs with hsum hxy hxy
  · rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> simp [hx, hc, hc1]
  · omega
  · omega
  · rfl

/-- A concrete nonzero vector in the deficit-one auxiliary sector, normalized
to have coefficient one at pair label zero and spectator label one. -/
def threeBodyDeficitOne (Q : ℕ) (hQ : 0 < Q) : ThreeBodyAux Q := fun p k =>
  (if p = ⟨0, by omega⟩ then (if k.val = 1 then 1 else 0) else 0) -
  (if p = ⟨1, by omega⟩ then
    (Real.sqrt (1 / 2) : ℂ) * (if k.val = 0 then 1 else 0) else 0)

theorem threeBodyDeficitOne_nonzero (Q : ℕ) (hQ : 0 < Q) :
    threeBodyDeficitOne Q hQ ≠ 0 := by
  intro h
  have he := congrFun (congrFun h ⟨0, by omega⟩) ⟨1, by omega⟩
  simp [threeBodyDeficitOne] at he

theorem threeBodyDeficitOne_insertion (Q : ℕ) (hQ : 0 < Q) (x y z : Orbital Q) :
    threeBodyInsertion (threeBodyDeficitOne Q hQ) x y z =
      (if x.val = 0 ∧ y.val = 0 ∧ z.val = 1 then 1 else 0) -
      (1 / 2 : ℂ) *
        (if ((x.val = 0 ∧ y.val = 1) ∨ (x.val = 1 ∧ y.val = 0)) ∧ z.val = 0
          then 1 else 0) := by
  have hs : (Real.sqrt (1 / 2) : ℂ) * (Real.sqrt (1 / 2) : ℂ) = (1 / 2 : ℂ) := by
    have h := congrArg Complex.ofReal (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2))
    norm_num only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] at h
    exact h
  simp only [threeBodyInsertion, threeBodyDeficitOne, mul_sub, Finset.sum_sub_distrib,
    mul_ite, mul_zero, Finset.sum_ite_eq', mem_univ, ite_true]
  rw [pairVector_zero, pairVector_one Q hQ]
  simp only [Fin.ext_iff, Fin.val_zero, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero]
  split_ifs <;> simp_all
  all_goals tauto

/-- An actual kernel vector of W₃, not merely cancellation of a proposed eigenvalue. -/
theorem threeBodyDeficitOne_kernel (Q : ℕ) (hQ : 0 < Q) :
    threeBodyMap (threeBodyDeficitOne Q hQ) = 0 := by
  funext a
  simp only [threeBodyMap, threeBodyDeficitOne_insertion, Pi.zero_apply]
  split_ifs <;> simp_all
  all_goals try ring
  all_goals tauto

/-- The same nonzero vector is an exact eigenvector of the actual compressed
transposition with eigenvalue -1/2. -/
theorem threeBodyDeficitOne_swap (Q : ℕ) (hQ : 0 < Q) :
    compressedSwap (threeBodyDeficitOne Q hQ) =
      (-1 / 2 : ℂ) • threeBodyDeficitOne Q hQ := by
  have h := threeBody_gram (threeBodyDeficitOne Q hQ)
  rw [threeBodyDeficitOne_kernel Q hQ] at h
  funext p k
  have he := congrFun (congrFun h p) k
  simp only [threeBodyAdjoint, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] at he ⊢
  linear_combination (1 / 2 : ℂ) * -he

end
end BosonicLaughlin

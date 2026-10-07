import BosonicLaughlin.PolynomialMetric

/-! Exact finite-sphere factors used in the rational certificate coordinates.
All formulas refer to positive integer flux; the products are not truncated
asymptotic expansions. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def sphereFactor (Q j : ℕ) : ℝ :=
  ∏ s ∈ Finset.range j, (1 - (s : ℝ) / (Q : ℝ))

theorem sphereFactor_zero (Q : ℕ) : sphereFactor Q 0 = 1 := by
  simp [sphereFactor]

theorem sphereFactor_succ (Q j : ℕ) :
    sphereFactor Q (j+1) = sphereFactor Q j * (1 - (j : ℝ) / (Q : ℝ)) := by
  exact Finset.prod_range_succ _ _

theorem sphereFactor_pos {Q j : ℕ} (hQ : 0 < Q) (hj : j ≤ Q) :
    0 < sphereFactor Q j := by
  apply Finset.prod_pos
  intro s hs
  have hsQ : (s : ℝ) < (Q : ℝ) := by exact_mod_cast (lt_of_lt_of_le (Finset.mem_range.mp hs) hj)
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  exact sub_pos.mpr ((div_lt_one hQr).mpr hsQ)

theorem factorial_mul_choose_eq_sphereFactor {Q j : ℕ} (hQ : 0 < Q) (hj : j ≤ Q) :
    (j.factorial : ℝ) * (Q.choose j : ℝ) = (Q : ℝ)^j * sphereFactor Q j := by
  induction j with
  | zero => simp [sphereFactor_zero]
  | succ j ih =>
    have hjQ : j ≤ Q := by omega
    have he : (Q.choose (j+1) : ℝ) * (j+1 : ℝ) =
        (Q.choose j : ℝ) * ((Q-j : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq Q j
    rw [Nat.cast_sub hjQ] at he
    have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
    calc
      ((j+1).factorial : ℝ) * (Q.choose (j+1) : ℝ) =
          (j.factorial : ℝ) * ((Q.choose (j+1) : ℝ) * (j+1 : ℝ)) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      _ = (j.factorial : ℝ) * ((Q.choose j : ℝ) * ((Q : ℝ) - j)) := by rw [he]
      _ = (Q : ℝ)^j * sphereFactor Q j * ((Q : ℝ) - j) := by rw [← mul_assoc, ih hjQ]
      _ = (Q : ℝ)^(j+1) * sphereFactor Q (j+1) := by
        rw [sphereFactor_succ, pow_succ]
        field_simp
        <;> ring

theorem sphereFactor_eq_factorial_choose {Q j : ℕ} (hQ : 0 < Q) (hj : j ≤ Q) :
    sphereFactor Q j = (j.factorial : ℝ) * (Q.choose j : ℝ) / (Q : ℝ)^j := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [factorial_mul_choose_eq_sphereFactor hQ hj]
  field_simp

/-- The coefficient of the unweighted pair derivative in the planar metric. -/
def planarPairFactor (p : ℕ) : ℝ := (p.factorial : ℝ) / 2^(p+1)

/-- Exact squared pair coefficient after the sector normalization: the finite
sphere correction is E_p(Q)=P_p(2Q), with no series approximation. -/
theorem sphere_pair_factor {Q p : ℕ} (hQ : 0 < Q) (hp : p ≤ 2*Q) :
    (Q : ℝ)^p / (2 * ((2*Q).choose p : ℝ)) =
      planarPairFactor p / sphereFactor (2*Q) p := by
  have h2Q : 0 < 2*Q := by omega
  have hE := (sphereFactor_pos h2Q hp).ne'
  have hC : (((2*Q).choose p : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hp).ne'
  have he := factorial_mul_choose_eq_sphereFactor h2Q hp
  simp only [Nat.cast_mul, Nat.cast_ofNat, mul_pow] at he
  unfold planarPairFactor
  rw [pow_succ, div_div]
  apply (div_eq_div_iff (mul_ne_zero (by norm_num) hC)
    (mul_ne_zero (by positivity) hE)).mpr
  nlinarith [he]

end
end BosonicLaughlin

import BosonicLaughlin.ThreeBodyGram

/-! Binomial square-root identities for the actual spherical pair kernel. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def binomialRoot (D i : ℕ) : ℝ := Real.sqrt (D.choose i : ℝ)

theorem binomialRoot_nonneg (D i : ℕ) : 0 ≤ binomialRoot D i :=
  Real.sqrt_nonneg _

theorem binomialRoot_sq (D i : ℕ) : binomialRoot D i ^ 2 = (D.choose i : ℝ) :=
  Real.sq_sqrt (by positivity)

theorem binomialRoot_pos (D i : ℕ) (hi : i ≤ D) : 0 < binomialRoot D i := by
  exact Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos hi)

theorem binomialRoot_zero (D i : ℕ) (hi : D < i) : binomialRoot D i = 0 := by
  simp [binomialRoot, Nat.choose_eq_zero_of_lt hi]

theorem binomialRoot_ladder_left (D i : ℕ) :
    Real.sqrt (((i+1 : ℕ) : ℝ) * ((D-i : ℕ) : ℝ)) * binomialRoot D (i+1) =
      ((D-i : ℕ) : ℝ) * binomialRoot D i := by
  have hr : (D.choose (i+1) : ℝ) * ((i+1 : ℕ) : ℝ) =
      (D.choose i : ℝ) * ((D-i : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq D i
  have hs : Real.sqrt (((i+1 : ℕ) : ℝ) * ((D-i : ℕ) : ℝ)) ^ 2 =
      ((i+1 : ℕ) : ℝ) * ((D-i : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have h1 := binomialRoot_sq D (i+1)
  have h0 := binomialRoot_sq D i
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (binomialRoot_nonneg _ _))
    (mul_nonneg (Nat.cast_nonneg _) (binomialRoot_nonneg _ _))).mp
  rw [mul_pow, mul_pow, hs, h1, h0]
  nlinarith [hr]

theorem binomialRoot_ladder_right (D i : ℕ) :
    Real.sqrt (((i+1 : ℕ) : ℝ) * ((D-i : ℕ) : ℝ)) * binomialRoot D i =
      ((i+1 : ℕ) : ℝ) * binomialRoot D (i+1) := by
  have hr : (D.choose (i+1) : ℝ) * ((i+1 : ℕ) : ℝ) =
      (D.choose i : ℝ) * ((D-i : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq D i
  have hs : Real.sqrt (((i+1 : ℕ) : ℝ) * ((D-i : ℕ) : ℝ)) ^ 2 =
      ((i+1 : ℕ) : ℝ) * ((D-i : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have h1 := binomialRoot_sq D (i+1)
  have h0 := binomialRoot_sq D i
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (binomialRoot_nonneg _ _))
    (mul_nonneg (Nat.cast_nonneg _) (binomialRoot_nonneg _ _))).mp
  rw [mul_pow, mul_pow, hs, h1, h0]
  nlinarith [hr]

theorem pairVector_binomialRoot (Q p : ℕ) (x y : Orbital Q) :
    pairVector Q p x y = if x.val+y.val=p then
      binomialRoot Q x.val * binomialRoot Q y.val / binomialRoot (2*Q) p else 0 := by
  by_cases h : x.val+y.val=p
  · have hp : p-x.val=y.val := by omega
    simp only [pairVector, h, ite_true, pairCoefficient, pairWeight, hp, binomialRoot]
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
  · simp [pairVector, h]

theorem pair_roots_raise (Q i j : ℕ) (hi : i ≤ Q) (hj : j ≤ Q)
    (hp : i+j < 2*Q) :
    Real.sqrt (((i+1 : ℕ) : ℝ) * ((Q-i : ℕ) : ℝ)) *
        (binomialRoot Q (i+1) * binomialRoot Q j / binomialRoot (2*Q) (i+j+1)) +
      Real.sqrt (((j+1 : ℕ) : ℝ) * ((Q-j : ℕ) : ℝ)) *
        (binomialRoot Q i * binomialRoot Q (j+1) / binomialRoot (2*Q) (i+j+1)) =
      Real.sqrt (((i+j+1 : ℕ) : ℝ) * ((2*Q-(i+j) : ℕ) : ℝ)) *
        (binomialRoot Q i * binomialRoot Q j / binomialRoot (2*Q) (i+j)) := by
  have h0 := (binomialRoot_pos (2*Q) (i+j) (by omega)).ne'
  have h1 := (binomialRoot_pos (2*Q) (i+j+1) (by omega)).ne'
  have ha := binomialRoot_ladder_left Q i
  have hb := binomialRoot_ladder_left Q j
  have hc := binomialRoot_ladder_left (2*Q) (i+j)
  have hd : ((Q-i : ℕ) : ℝ) + ((Q-j : ℕ) : ℝ) = ((2*Q-(i+j) : ℕ) : ℝ) := by
    exact_mod_cast (show (Q-i)+(Q-j)=2*Q-(i+j) by omega)
  field_simp
  linear_combination
    binomialRoot Q j * binomialRoot (2*Q) (i+j) * ha +
    binomialRoot Q i * binomialRoot (2*Q) (i+j) * hb -
    binomialRoot Q i * binomialRoot Q j * hc +
    binomialRoot Q i * binomialRoot Q j * binomialRoot (2*Q) (i+j) * hd

theorem threeBodyInsertion_single {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) :
    threeBodyInsertion φ x y z =
      (binomialRoot Q x.val * binomialRoot Q y.val / binomialRoot (2*Q) (x.val+y.val) : ℝ) *
        φ ⟨x.val+y.val, by omega⟩ z := by
  simp only [threeBodyInsertion, pairVector_binomialRoot]
  rw [Finset.sum_eq_single (⟨x.val+y.val, by omega⟩ : Fin (2*Q+1))]
  · simp
  · intro p _ hp
    have he : x.val+y.val ≠ p.val := by
      intro he
      exact hp (Fin.ext he.symm)
    simp [he]
  · simp

theorem binomialRoot_lower_ratio (D s : ℕ) (hs : 0 < s) (hD : s ≤ D) :
    (s : ℝ) / binomialRoot D (s-1) =
      Real.sqrt (((s : ℕ) : ℝ) * ((D-(s-1) : ℕ) : ℝ)) / binomialRoot D s := by
  have h0 := (binomialRoot_pos D (s-1) (by omega)).ne'
  have h1 := (binomialRoot_pos D s hD).ne'
  have h := binomialRoot_ladder_right D (s-1)
  rw [show s-1+1=s by omega] at h
  apply (div_eq_div_iff h0 h1).mpr
  exact h.symm

end
end BosonicLaughlin

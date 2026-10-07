import BosonicLaughlin.Pair
import Mathlib.Basic.Complex.BigOperators

namespace BosonicLaughlin
noncomputable section
open Finset

abbrev PairBlockState (p : ℕ) := Fin (p+1) → ℂ

def pairBlockAmplitude (Q p : ℕ) (ψ : PairBlockState p) : ℂ :=
  ∑ i : Fin (p+1), (pairCoefficient Q p i.val : ℂ) * ψ i

def pairBlockApply (Q p : ℕ) (ψ : PairBlockState p) : PairBlockState p :=
  fun i => (pairCoefficient Q p i.val : ℂ) * pairBlockAmplitude Q p ψ

theorem pairCoefficient_normalized_fin (Q p : ℕ) (hp : p ≤ 2*Q) :
    ∑ i : Fin (p+1), pairCoefficient Q p i.val ^ 2 = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => pairCoefficient Q p i ^ 2)]
  exact pairCoefficient_normalized Q p hp

theorem pairCoefficient_normalized_complex (Q p : ℕ) (hp : p ≤ 2*Q) :
    ∑ i : Fin (p+1), (pairCoefficient Q p i.val : ℂ)^2 = 1 := by
  simpa only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_one] using
    congrArg Complex.ofReal (pairCoefficient_normalized_fin Q p hp)

theorem pairBlockAmplitude_apply (Q p : ℕ) (hp : p ≤ 2*Q)
    (ψ : PairBlockState p) :
    pairBlockAmplitude Q p (pairBlockApply Q p ψ) = pairBlockAmplitude Q p ψ := by
  change (∑ i : Fin (p+1), (pairCoefficient Q p i.val : ℂ) *
    ((pairCoefficient Q p i.val : ℂ) * pairBlockAmplitude Q p ψ)) = _
  simp_rw [← mul_assoc, ← pow_two, ← Finset.sum_mul]
  rw [pairCoefficient_normalized_complex Q p hp, one_mul]

/-- Every allowed pair block is idempotent, at arbitrary flux. -/
theorem pairBlockApply_idempotent (Q p : ℕ) (hp : p ≤ 2*Q)
    (ψ : PairBlockState p) :
    pairBlockApply Q p (pairBlockApply Q p ψ) = pairBlockApply Q p ψ := by
  funext i
  change (pairCoefficient Q p i.val : ℂ) *
    pairBlockAmplitude Q p (pairBlockApply Q p ψ) = _
  rw [pairBlockAmplitude_apply Q p hp]
  rfl

/-- The rank-one block has a real symmetric matrix, hence a Hermitian matrix. -/
theorem pairBlock_kernel_hermitian (Q p : ℕ) (i j : Fin (p+1)) :
    star ((pairCoefficient Q p j.val : ℂ) * (pairCoefficient Q p i.val : ℂ)) =
      (pairCoefficient Q p i.val : ℂ) * (pairCoefficient Q p j.val : ℂ) := by
  simp [mul_comm]

theorem pairBlock_energy_identity (Q p : ℕ) (ψ : PairBlockState p) :
    (∑ i, star (ψ i) * pairBlockApply Q p ψ i) =
      star (pairBlockAmplitude Q p ψ) * pairBlockAmplitude Q p ψ := by
  simp only [pairBlockApply, ← mul_assoc, ← Finset.sum_mul]
  congr 1
  simp [pairBlockAmplitude, mul_comm]

theorem pairBlock_energy_nonneg (Q p : ℕ) (ψ : PairBlockState p) :
    0 ≤ (∑ i, star (ψ i) * pairBlockApply Q p ψ i).re := by
  rw [pairBlock_energy_identity]
  change 0 ≤ (starRingEnd ℂ (pairBlockAmplitude Q p ψ) * pairBlockAmplitude Q p ψ).re
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end
end BosonicLaughlin

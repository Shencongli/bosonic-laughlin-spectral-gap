import BosonicLaughlin.SparseKernelFrame
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! Exact positivity witnesses using integer Gram decompositions.  The checker
verifies S M = R^T diag(w) R with S>0 and w>=0; the soundness theorem proves
positive semidefiniteness after scalar extension to complex amplitudes. -/
namespace BosonicLaughlin
open Finset
open scoped Matrix ComplexOrder

def SparseGramCheck {n r : ℕ} (S : ℤ) (M : SparseIntMatrix n n)
    (R : SparseIntMatrix r n) (T : SparseIntMatrix n r) (w : Fin r → ℤ) : Prop :=
  (∀ i j, sparseIntRowEval (T i) j=sparseIntRowEval (R j) i) ∧
  (∀ i, sparseIntRowAdd
    (sparseIntMulRow (T i) (fun j => sparseIntRowScale (w j) (R j)))
    (sparseIntRowScale (-S) (M i))=[])

theorem sparseGramCheck_integer {n r : ℕ} {S : ℤ} {M : SparseIntMatrix n n}
    {R : SparseIntMatrix r n} {T : SparseIntMatrix n r} {w : Fin r → ℤ}
    (h : SparseGramCheck S M R T w) :
    S • sparseIntToMatrix M = (sparseIntToMatrix R)ᵀ * Matrix.diagonal w * sparseIntToMatrix R := by
  have ht : sparseIntToMatrix T=(sparseIntToMatrix R)ᵀ := by ext i j; exact h.1 i j
  have hw : sparseIntToMatrix (fun j => sparseIntRowScale (w j) (R j)) =
      Matrix.diagonal w * sparseIntToMatrix R := by
    ext i j
    simp [sparseIntToMatrix, sparseIntRowScale_eval, Matrix.diagonal_mul]
  ext i j
  have he := congrArg (fun a => sparseIntRowEval a j) (h.2 i)
  rw [sparseIntRowAdd_eval, sparseIntRowScale_eval, sparseIntMulRow_matrix, ht, hw] at he
  change _ + -S * sparseIntToMatrix M i j=0 at he
  simp only [Matrix.mul_assoc]
  change S * sparseIntToMatrix M i j = _
  linear_combination -he

def sparseComplexMatrix {m n : ℕ} (M : SparseIntMatrix m n) : Matrix (Fin m) (Fin n) ℂ :=
  (sparseIntToMatrix M).map (Int.castRingHom ℂ)

theorem sparseGramCheck_complex {n r : ℕ} {S : ℤ} {M : SparseIntMatrix n n}
    {R : SparseIntMatrix r n} {T : SparseIntMatrix n r} {w : Fin r → ℤ}
    (h : SparseGramCheck S M R T w) :
    (S : ℂ) • sparseComplexMatrix M =
      (sparseComplexMatrix R)ᴴ * Matrix.diagonal (fun i => (w i : ℂ)) * sparseComplexMatrix R := by
  have he := congrArg (fun A => A.map (Int.castRingHom ℂ)) (sparseGramCheck_integer h)
  have ht : ((sparseIntToMatrix R)ᵀ.map (Int.castRingHom ℂ))=(sparseComplexMatrix R)ᴴ := by
    ext i j
    simp [sparseComplexMatrix, Matrix.conjTranspose_apply]
  have hs : (S • sparseIntToMatrix M).map (Int.castRingHom ℂ) = (S : ℂ) • sparseComplexMatrix M := by
    ext i j
    change ((S * sparseIntToMatrix M i j : ℤ) : ℂ) = (S : ℂ) * (sparseIntToMatrix M i j : ℂ)
    push_cast
    rfl
  have hd : (Matrix.diagonal w).map (Int.castRingHom ℂ)=Matrix.diagonal (fun i => (w i : ℂ)) := by
    ext i j
    simp [Matrix.diagonal_apply]
  rw [hs, Matrix.map_mul, Matrix.map_mul, ht, hd] at he
  exact he


theorem sparseGramCheck_posSemidef {n r : ℕ} {S : ℤ} {M : SparseIntMatrix n n}
    {R : SparseIntMatrix r n} {T : SparseIntMatrix n r} {w : Fin r → ℤ}
    (hS : 0<S) (hw : ∀ i, 0≤w i) (h : SparseGramCheck S M R T w) :
    (sparseComplexMatrix M).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => (w i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by change (0 : ℂ)≤(w i : ℂ); exact_mod_cast hw i)
  have hg := hd.conjTranspose_mul_mul_same (sparseComplexMatrix R)
  rw [← sparseGramCheck_complex h] at hg
  have hs : (S : ℂ)≠0 := by exact_mod_cast hS.ne'
  have hi : (0 : ℂ)≤(S : ℂ)⁻¹ := by
    simpa only [RCLike.ofReal_inv, RCLike.ofReal_intCast] using
      (RCLike.ofReal_nonneg (K := ℂ)).2 (inv_nonneg.mpr (show (0 : ℝ)≤S by exact_mod_cast hS.le))
  simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using hg.smul hi

theorem sparseGramCheck_scaled_posSemidef {n r : ℕ} {S D : ℤ} {M : SparseIntMatrix n n}
    {R : SparseIntMatrix r n} {T : SparseIntMatrix n r} {w : Fin r → ℤ}
    (hD : 0<D) (hS : 0<S) (hw : ∀ i, 0≤w i) (h : SparseGramCheck S M R T w) :
    ((sparseRatScaledMatrix D M).map (Rat.castHom ℂ)).PosSemidef := by
  have hi : (0 : ℂ)≤(D : ℂ)⁻¹ := by
    simpa only [RCLike.ofReal_inv, RCLike.ofReal_intCast] using
      (RCLike.ofReal_nonneg (K := ℂ)).2 (inv_nonneg.mpr (show (0 : ℝ)≤D by exact_mod_cast hD.le))
  have hp := (sparseGramCheck_posSemidef hS hw h).smul hi
  convert hp using 1
  ext i j
  simp [sparseRatScaledMatrix, sparseRatMatrix, sparseComplexMatrix]

end BosonicLaughlin

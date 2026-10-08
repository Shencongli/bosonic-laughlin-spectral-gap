import BosonicLaughlin.DescendantSchur
import BosonicLaughlin.CertificateRowNormalOrder
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Basis covariance of the spin partial trace, with arbitrary left and
right multiplicity vectors. Finite weighted conjugations preserve this
trace. Relating a physical SU(2) action to these spin matrices is separate. -/
namespace BosonicLaughlin
noncomputable section
open Finset
open scoped Matrix

def spinCrossForm {Q N s : ℕ} (P R : Fin s → State Q N)
    (A : State Q N →ₗ[ℂ] State Q N) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => inner (P i) (A (R j))

/-- A change of spin basis, using columns of U as coefficients. -/
def mixSpinFrame {Q N s : ℕ} (P : Fin s → State Q N)
    (U : Matrix (Fin s) (Fin s) ℂ) (i : Fin s) : State Q N :=
  ∑ j, U j i • P j

theorem spinCrossForm_mix {Q N s : ℕ} (P R : Fin s → State Q N)
    (A : State Q N →ₗ[ℂ] State Q N) (U : Matrix (Fin s) (Fin s) ℂ) :
    spinCrossForm (mixSpinFrame P U) (mixSpinFrame R U) A=
      Uᴴ * spinCrossForm P R A * U := by
  ext i j
  simp only [spinCrossForm, mixSpinFrame, map_sum, map_smul,
    stateInner_sum_left, stateInner_sum_right, stateInner_smul_left, stateInner_smul_right,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem spinTrace_unitary_conjugate {s : ℕ} (K U : Matrix (Fin s) (Fin s) ℂ)
    (hU : U * Uᴴ=1) : Matrix.trace (Uᴴ * K * U)=Matrix.trace K := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

theorem spinCrossForm_trace_mix {Q N s : ℕ} (P R : Fin s → State Q N)
    (A : State Q N →ₗ[ℂ] State Q N) (U : Matrix (Fin s) (Fin s) ℂ)
    (hU : U * Uᴴ=1) :
    Matrix.trace (spinCrossForm (mixSpinFrame P U) (mixSpinFrame R U) A)=
      Matrix.trace (spinCrossForm P R A) := by
  rw [spinCrossForm_mix, spinTrace_unitary_conjugate _ _ hU]

theorem descendantPartialTrace_eq_trace {Q N : ℕ} (m : ℕ)
    (A : State Q N →ₗ[ℂ] State Q N) (ψ φ : State Q N) :
    descendantPartialTrace m A ψ φ=Matrix.trace (spinCrossForm
      (fun n : Fin (m+1) => normalizedTensorDescendant ψ m n.val)
      (fun n : Fin (m+1) => normalizedTensorDescendant φ m n.val) A) := rfl

theorem spinTrace_finite_conjugate_average {s : ℕ} {ι : Type*} [Fintype ι]
    (K : Matrix (Fin s) (Fin s) ℂ) (U : ι → Matrix (Fin s) (Fin s) ℂ)
    (w : ι → ℂ) (hw : ∑ g, w g=1) (hU : ∀ g, U g * (U g)ᴴ=1) :
    Matrix.trace (∑ g, w g • ((U g)ᴴ * K * U g))=Matrix.trace K := by
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_smul, spinTrace_unitary_conjugate _ _ (hU _)]
  change (∑ g, w g * Matrix.trace K)=_
  rw [← Finset.sum_mul, hw, one_mul]

/-- Physical pullback under a map whose action on both descendant ladders
is the same unitary spin matrix. No orthonormality of multiplicity vectors
or of their frame is assumed. -/
theorem descendantPartialTrace_of_spin_covariance {Q N : ℕ} (m : ℕ)
    (A B T : State Q N →ₗ[ℂ] State Q N) (ψ φ : State Q N)
    (U : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (hU : U * Uᴴ=1)
    (hB : ∀ v w, inner v (B w)=inner (T v) (A (T w)))
    (hψ : ∀ n : Fin (m+1), T (normalizedTensorDescendant ψ m n.val)=
      mixSpinFrame (fun j : Fin (m+1) => normalizedTensorDescendant ψ m j.val) U n)
    (hφ : ∀ n : Fin (m+1), T (normalizedTensorDescendant φ m n.val)=
      mixSpinFrame (fun j : Fin (m+1) => normalizedTensorDescendant φ m j.val) U n) :
    descendantPartialTrace m B ψ φ=descendantPartialTrace m A ψ φ := by
  rw [descendantPartialTrace_eq_trace, descendantPartialTrace_eq_trace]
  have hmatrix : spinCrossForm
      (fun n : Fin (m+1) => normalizedTensorDescendant ψ m n.val)
      (fun n : Fin (m+1) => normalizedTensorDescendant φ m n.val) B=
      spinCrossForm
        (mixSpinFrame (fun n : Fin (m+1) => normalizedTensorDescendant ψ m n.val) U)
        (mixSpinFrame (fun n : Fin (m+1) => normalizedTensorDescendant φ m n.val) U) A := by
    ext i j
    simp only [spinCrossForm, hB, hψ, hφ]
  rw [hmatrix, spinCrossForm_trace_mix _ _ _ _ hU]

end
end BosonicLaughlin

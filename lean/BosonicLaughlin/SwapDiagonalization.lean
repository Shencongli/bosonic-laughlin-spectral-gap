import BosonicLaughlin.SwapStructure
import Mathlib.Analysis.Matrix.Spectrum

/-!
Finite-dimensional spectral completeness for the actual compressed exchange.
The Euclidean matrix coordinates carry the tensor Hilbert-space inner product;
the explicit linear equivalence below only curries the two finite indices.
No spin-multiplet multiplicity is assumed in this diagonalization.
-/
namespace BosonicLaughlin
noncomputable section
open Module

def auxEuclideanEquiv (Q : ℕ) :
    EuclideanSpace ℂ (ThreeBodyIndex Q) ≃ₗ[ℂ] ThreeBodyAux Q where
  toFun v := fun p k => v (p, k)
  invFun φ := WithLp.toLp 2 (fun a => φ a.1 a.2)
  left_inv v := by ext a; rfl
  right_inv φ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- An orthonormal eigenbasis in the tensor Hilbert-space coordinates. -/
def compressedSwapOrthonormalBasis (Q : ℕ) :
    OrthonormalBasis (ThreeBodyIndex Q) ℂ (EuclideanSpace ℂ (ThreeBodyIndex Q)) :=
  (compressedSwapMatrix_hermitian Q).eigenvectorBasis

/-- The same complete eigenbasis, curried into the actual auxiliary type. -/
def compressedSwapEigenbasis (Q : ℕ) : Basis (ThreeBodyIndex Q) ℂ (ThreeBodyAux Q) :=
  (compressedSwapOrthonormalBasis Q).toBasis.map (auxEuclideanEquiv Q)

def compressedSwapEigenvalues (Q : ℕ) : ThreeBodyIndex Q → ℝ :=
  (compressedSwapMatrix_hermitian Q).eigenvalues

theorem compressedSwapEigenbasis_apply (Q : ℕ) (j : ThreeBodyIndex Q)
    (p : Fin (2 * Q + 1)) (k : Orbital Q) :
    compressedSwapEigenbasis Q j p k = compressedSwapOrthonormalBasis Q j (p, k) := rfl

theorem compressedSwapEigenbasis_eigenvector (Q : ℕ) (j : ThreeBodyIndex Q) :
    compressedSwap (compressedSwapEigenbasis Q j) =
      (compressedSwapEigenvalues Q j : ℂ) • compressedSwapEigenbasis Q j := by
  have h := (compressedSwapMatrix_hermitian Q).mulVec_eigenvectorBasis j
  have hb := compressedSwapMatrix_mulVec (compressedSwapEigenbasis Q j)
  funext p k
  have he := congrFun h (p, k)
  have he' := congrFun hb (p, k)
  change (compressedSwapMatrix Q).mulVec
    (fun a => compressedSwapOrthonormalBasis Q j a) (p, k) = _ at he
  change (compressedSwapMatrix Q).mulVec
    (fun a => compressedSwapOrthonormalBasis Q j a) (p, k) =
      compressedSwap (compressedSwapEigenbasis Q j) p k at he'
  rw [← he']
  exact he

theorem compressedSwapEigenbasis_nonzero (Q : ℕ) (j : ThreeBodyIndex Q) :
    compressedSwapEigenbasis Q j ≠ 0 := (compressedSwapEigenbasis Q).ne_zero j

/-- Every auxiliary vector has an exact finite expansion in actual eigenvectors. -/
theorem compressedSwapEigenbasis_complete (Q : ℕ) (φ : ThreeBodyAux Q) :
    (∑ j, (compressedSwapEigenbasis Q).repr φ j • compressedSwapEigenbasis Q j) = φ :=
  (compressedSwapEigenbasis Q).sum_repr φ

theorem compressedSwap_mem_spectrum_iff (Q : ℕ) (μ : ℂ) :
    μ ∈ spectrum ℂ (compressedSwapMatrix Q) ↔
      ∃ φ : ThreeBodyAux Q, φ ≠ 0 ∧ compressedSwap φ = μ • φ := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    refine ⟨fun p k => v (p, k), ?_, ?_⟩
    · intro hzero
      apply hv.2
      funext a
      exact congrFun (congrFun hzero a.1) a.2
    · have he := hv.apply_eq_smul
      rw [Matrix.toLin'_apply] at he
      have hb := compressedSwapMatrix_mulVec (fun p k => v (p, k))
      funext p k
      have he' := congrFun he (p, k)
      have hb' := congrFun hb (p, k)
      simpa only [Pi.smul_apply, smul_eq_mul] using hb'.symm.trans he'
  · rintro ⟨φ, hφ, he⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector
      (x := fun a : ThreeBodyIndex Q => φ a.1 a.2)
    constructor
    · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply,
        compressedSwapMatrix_mulVec, he]
      rfl
    · intro hzero
      apply hφ
      funext p k
      exact congrFun hzero (p, k)

theorem compressedSwap_spectrum_exists_eigenvector {Q : ℕ} {μ : ℂ}
    (h : μ ∈ spectrum ℂ (compressedSwapMatrix Q)) :
    ∃ φ : ThreeBodyAux Q, φ ≠ 0 ∧ compressedSwap φ = μ • φ :=
  (compressedSwap_mem_spectrum_iff Q μ).mp h

theorem compressedSwap_eigenvector_mem_spectrum {Q : ℕ} {μ : ℂ}
    (φ : ThreeBodyAux Q) (hφ : φ ≠ 0) (he : compressedSwap φ = μ • φ) :
    μ ∈ spectrum ℂ (compressedSwapMatrix Q) :=
  (compressedSwap_mem_spectrum_iff Q μ).mpr ⟨φ, hφ, he⟩

end
end BosonicLaughlin


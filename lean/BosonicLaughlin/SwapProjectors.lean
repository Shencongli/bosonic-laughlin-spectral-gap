import BosonicLaughlin.SwapSpectrum
import BosonicLaughlin.SpectralPartition

/-!
An exact orthogonal spectral resolution of the actual compressed exchange.
The labels are the recoupling deficits `z=0,...,Q`; construction proceeds in
the complete orthonormal eigenbasis, then returns to physical pair/spectator
coordinates by unitary conjugation. No block rank is postulated.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def compressedSwapSpectralLabel (Q : ℕ) (j : ThreeBodyIndex Q) : Fin (Q+1) :=
  Classical.choose (compressedSwapEigenvalues_label Q j)

theorem compressedSwapSpectralLabel_spec (Q : ℕ) (j : ThreeBodyIndex Q) :
    compressedSwapEigenvalues Q j = recouplingEigenvalue Q
      (compressedSwapSpectralLabel Q j).val :=
  Classical.choose_spec (compressedSwapEigenvalues_label Q j)

def compressedSwapConjugation (Q : ℕ) :
    Matrix (ThreeBodyIndex Q) (ThreeBodyIndex Q) ℂ ≃⋆ₐ[ℂ]
      Matrix (ThreeBodyIndex Q) (ThreeBodyIndex Q) ℂ :=
  Unitary.conjStarAlgAut ℂ _ (compressedSwapMatrix_hermitian Q).eigenvectorUnitary

def compressedSwapProjector (Q : ℕ) (z : Fin (Q+1)) :
    Matrix (ThreeBodyIndex Q) (ThreeBodyIndex Q) ℂ :=
  spectralPartitionProjector (compressedSwapConjugation Q) (compressedSwapSpectralLabel Q) z

theorem compressedSwapProjector_sum (Q : ℕ) :
    ∑ z, compressedSwapProjector Q z = 1 :=
  spectralPartition_sum (compressedSwapConjugation Q) (compressedSwapSpectralLabel Q)

theorem compressedSwapProjector_mul (Q : ℕ) (z w : Fin (Q+1)) :
    compressedSwapProjector Q z * compressedSwapProjector Q w =
      if z=w then compressedSwapProjector Q z else 0 :=
  spectralPartition_mul (compressedSwapConjugation Q) (compressedSwapSpectralLabel Q) z w

theorem compressedSwapProjector_idempotent (Q : ℕ) (z : Fin (Q+1)) :
    compressedSwapProjector Q z * compressedSwapProjector Q z = compressedSwapProjector Q z := by
  simp only [compressedSwapProjector_mul, ite_true]

theorem compressedSwapProjector_hermitian (Q : ℕ) (z : Fin (Q+1)) :
    (compressedSwapProjector Q z).IsHermitian :=
  spectralPartition_hermitian (compressedSwapConjugation Q) (compressedSwapSpectralLabel Q) z

/-- The full finite operator resolution with the explicit recoupling eigenvalues. -/
theorem compressedSwap_projector_resolution (Q : ℕ) :
    compressedSwapMatrix Q =
      ∑ z : Fin (Q+1), (recouplingEigenvalue Q z.val : ℂ) • compressedSwapProjector Q z := by
  rw [show (∑ z : Fin (Q+1), (recouplingEigenvalue Q z.val : ℂ) • compressedSwapProjector Q z) =
      compressedSwapConjugation Q (Matrix.diagonal
        (fun j => (recouplingEigenvalue Q (compressedSwapSpectralLabel Q j).val : ℂ))) from
    spectralPartition_resolution (compressedSwapConjugation Q) (compressedSwapSpectralLabel Q)
      (fun z => (recouplingEigenvalue Q z.val : ℂ))]
  simp_rw [← compressedSwapSpectralLabel_spec]
  exact (compressedSwapMatrix_hermitian Q).spectral_theorem

theorem compressedSwapProjector_eigen (Q : ℕ) (z : Fin (Q+1)) :
    compressedSwapMatrix Q * compressedSwapProjector Q z =
      (recouplingEigenvalue Q z.val : ℂ) • compressedSwapProjector Q z := by
  rw [compressedSwap_projector_resolution, Finset.sum_mul]
  simp only [Matrix.smul_mul, compressedSwapProjector_mul]
  simp

end
end BosonicLaughlin

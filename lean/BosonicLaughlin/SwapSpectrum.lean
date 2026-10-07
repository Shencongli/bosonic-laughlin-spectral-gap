import BosonicLaughlin.SwapEigenvalues
import BosonicLaughlin.CompressedSwapEquivariance
import BosonicLaughlin.SwapDiagonalization

/-! The exact spectrum of the physical compressed exchange, for every flux.
No equivariance or completeness hypothesis remains in these statements.
Spin-multiplet ranks are a separate identification, not asserted here. -/
namespace BosonicLaughlin
noncomputable section

theorem compressedSwap_highestWeight (Q z : ℕ) (hz : z ≤ Q) :
    compressedSwap (auxHighestWeight Q z) =
      (recouplingEigenvalue Q z : ℂ) • auxHighestWeight Q z :=
  auxHighestWeight_swap_of_raise_commutes Q z hz (compressedSwap_auxRaise _).symm

/-- Every actual nonzero eigenvector has one of the stated eigenvalues. -/
theorem compressedSwap_eigenvalue {Q : ℕ} (φ : ThreeBodyAux Q) (hφ : φ ≠ 0)
    (μ : ℂ) (he : compressedSwap φ = μ • φ) :
    ∃ z ≤ Q, μ = (recouplingEigenvalue Q z : ℂ) :=
  compressedSwap_eigenvalue_of_commutation compressedSwap_auxRaise φ hφ μ he

/-- Equality of spectra as sets; includes existence and absence of extra eigenvalues. -/
theorem compressedSwap_spectrum (Q : ℕ) :
    spectrum ℂ (compressedSwapMatrix Q) =
      {μ : ℂ | ∃ z ≤ Q, μ = (recouplingEigenvalue Q z : ℂ)} := by
  ext μ
  constructor
  · intro h
    obtain ⟨φ, hn, he⟩ := compressedSwap_spectrum_exists_eigenvector h
    exact compressedSwap_eigenvalue φ hn μ he
  · rintro ⟨z, hz, rfl⟩
    exact compressedSwap_eigenvector_mem_spectrum (auxHighestWeight Q z)
      (auxHighestWeight_nonzero Q z hz) (compressedSwap_highestWeight Q z hz)

theorem compressedSwapEigenvalues_label (Q : ℕ) (j : ThreeBodyIndex Q) :
    ∃ z : Fin (Q+1), compressedSwapEigenvalues Q j = recouplingEigenvalue Q z.val := by
  obtain ⟨z, hz, he⟩ := compressedSwap_eigenvalue (compressedSwapEigenbasis Q j)
    (compressedSwapEigenbasis_nonzero Q j) _ (compressedSwapEigenbasis_eigenvector Q j)
  exact ⟨⟨z, by omega⟩, Complex.ofReal_injective he⟩

/-- A complete basis of actual eigenvectors, with each eigenvalue given explicitly. -/
theorem compressedSwap_complete_labeled_basis (Q : ℕ) :
    ∃ label : ThreeBodyIndex Q → Fin (Q+1),
      (∀ j, compressedSwap (compressedSwapEigenbasis Q j) =
        (recouplingEigenvalue Q (label j).val : ℂ) • compressedSwapEigenbasis Q j) ∧
      (∀ φ : ThreeBodyAux Q,
        (∑ j, (compressedSwapEigenbasis Q).repr φ j • compressedSwapEigenbasis Q j) = φ) := by
  choose label hlabel using compressedSwapEigenvalues_label Q
  refine ⟨label, ?_, compressedSwapEigenbasis_complete Q⟩
  intro j
  rw [compressedSwapEigenbasis_eigenvector, hlabel j]

end
end BosonicLaughlin

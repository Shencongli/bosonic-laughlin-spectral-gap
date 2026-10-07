import BosonicLaughlin.HighestWeight

/-! Highest-weight reduction of every eigenvector. The commutation assumption
in these assembly lemmas is discharged for the physical map in SwapSpectrum. -/
namespace BosonicLaughlin
noncomputable section

def recouplingEigenvalue (Q z : ℕ) : ℝ := (-1 : ℝ)^z * recouplingRatio Q z

theorem compressedSwap_highest_eigenvalue_of_commutation {Q z : ℕ}
    (hcomm : ∀ χ : ThreeBodyAux Q,
      compressedSwap (auxRaise χ) = auxRaise (compressedSwap χ))
    (φ : ThreeBodyAux Q) (hs : AuxSupported z φ) (hφ : φ ≠ 0)
    (hE : auxRaise φ = 0) (μ : ℂ) (hμ : compressedSwap φ = μ • φ) :
    z ≤ Q ∧ μ = (recouplingEigenvalue Q z : ℂ) := by
  have hz := auxRaise_kernel_deficit_le φ hs hE hφ
  have hu := auxHighestWeight_unique hz φ hs hE
  have ht := auxHighestWeight_swap_of_raise_commutes Q z hz (hcomm _).symm
  change compressedSwap (auxHighestWeight Q z) =
    (recouplingEigenvalue Q z : ℂ) • auxHighestWeight Q z at ht
  have htφ : compressedSwap φ = (recouplingEigenvalue Q z : ℂ) • φ := by
    have hscaled : compressedSwap (φ ⟨0, by omega⟩ ⟨z, by omega⟩ • auxHighestWeight Q z) =
        (recouplingEigenvalue Q z : ℂ) •
          (φ ⟨0, by omega⟩ ⟨z, by omega⟩ • auxHighestWeight Q z) := by
      rw [compressedSwap_smul, ht]
      exact smul_comm _ _ _
    rw [← hu] at hscaled
    exact hscaled
  exact ⟨hz, smul_left_injective ℂ hφ (hμ.symm.trans htφ)⟩

/-- Every eigenvalue is detected on one of the concrete highest-weight lines.
The proof descends the deficit of an actual nonzero eigenvector. -/
theorem compressedSwap_eigenvalue_of_commutation {Q : ℕ}
    (hcomm : ∀ χ : ThreeBodyAux Q,
      compressedSwap (auxRaise χ) = auxRaise (compressedSwap χ))
    (φ : ThreeBodyAux Q) (hφ : φ ≠ 0) (μ : ℂ)
    (hμ : compressedSwap φ = μ • φ) :
    ∃ z ≤ Q, μ = (recouplingEigenvalue Q z : ℂ) := by
  have hblock : ∀ z : ℕ, ∀ χ : ThreeBodyAux Q,
      AuxSupported z χ → χ ≠ 0 → compressedSwap χ = μ • χ →
        ∃ r ≤ Q, μ = (recouplingEigenvalue Q r : ℂ) := by
    intro z
    induction z with
    | zero =>
      intro χ hs hn he
      exact ⟨0, compressedSwap_highest_eigenvalue_of_commutation hcomm χ hs hn
        (auxRaise_supported_zero χ hs) μ he⟩
    | succ z ih =>
      intro χ hs hn he
      by_cases hE : auxRaise χ = 0
      · exact ⟨z+1, compressedSwap_highest_eigenvalue_of_commutation hcomm χ hs hn hE μ he⟩
      · apply ih (auxRaise χ) (auxRaise_supported_pred χ hs) hE
        rw [hcomm χ, he, auxRaise_smul]
  obtain ⟨z, _, hn⟩ := auxDeficitProject_exists_nonzero φ hφ
  apply hblock z (auxDeficitProject z φ) (auxDeficitProject_supported z φ) hn
  rw [compressedSwap_deficit_project, hμ, auxDeficitProject_smul]

end
end BosonicLaughlin

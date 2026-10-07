import BosonicLaughlin.NormalOrdering
import BosonicLaughlin.ThreeBodyGram

/-! The three-particle normal-order coefficient in the physical bosonic sector.
This identifies the operator coefficient before any SU(2) diagonalization. -/
namespace BosonicLaughlin
noncomputable section

/-- S₃ on three particles is exactly W₃ (2T) W₃†. -/
theorem threeBody_normal_coefficient {Q : ℕ} (ψ : State Q 3)
    (hψ : IsBosonic ψ) :
    normalThreeBodyApply ψ =
      (2 : ℂ) • threeBodyMap (compressedSwap (threeBodyAdjoint ψ)) := by
  have h : hamiltonian (hamiltonian ψ) = hamiltonian ψ +
      (2 : ℂ) • threeBodyMap (compressedSwap (threeBodyAdjoint ψ)) := by
    calc
      _ = threeBodyMap (threeBodyAdjoint (hamiltonian ψ)) :=
        (threeBody_hamiltonian _ (hamiltonian_isBosonic ψ hψ)).symm
      _ = threeBodyMap (threeBodyAdjoint (threeBodyMap (threeBodyAdjoint ψ))) := by
        rw [threeBody_hamiltonian ψ hψ]
      _ = _ := by
        rw [threeBody_gram, threeBodyMap_add, threeBodyMap_smul,
          threeBody_hamiltonian ψ hψ]
  rw [three_particle_square] at h
  exact add_left_cancel h

end
end BosonicLaughlin

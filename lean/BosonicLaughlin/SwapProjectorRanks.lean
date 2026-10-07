import BosonicLaughlin.SwapProjectorEigenspaces
import BosonicLaughlin.MultipletDimensions

/-! Exact ranks of the physical auxiliary spectral projectors. -/
namespace BosonicLaughlin
noncomputable section

/-- Rank means the complex dimension of the image of the actual projector. -/
theorem compressedSwapProjector_rank (Q : ℕ) (z : Fin (Q+1)) :
    Module.finrank ℂ (LinearMap.range (compressedSwapProjectorLinear Q z)) =
      3*Q - 2*z.val + 1 := by
  rw [compressedSwapProjector_range]
  exact compressedSwap_eigenspace_dimension Q z.val (by omega)

theorem compressedSwapProjectorLinear_nonzero (Q : ℕ) (z : Fin (Q+1)) :
    compressedSwapProjectorLinear Q z ≠ 0 := by
  intro hzero
  have hr := compressedSwapProjector_rank Q z
  rw [hzero] at hr
  rw [LinearMap.range_zero] at hr
  have hz : Module.finrank ℂ (⊥ : Submodule ℂ (ThreeBodyAux Q)) = 0 :=
    finrank_bot ℂ (ThreeBodyAux Q)
  rw [hz] at hr
  omega

end
end BosonicLaughlin

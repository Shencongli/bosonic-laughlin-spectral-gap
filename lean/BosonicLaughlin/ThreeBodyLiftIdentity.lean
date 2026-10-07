import BosonicLaughlin.ThreeBodyLift
import BosonicLaughlin.ThreeBodyCounting
import BosonicLaughlin.ThreeBodySymmetry

/-! The actual overlapping-pair term is the normalized lift of its three-particle coefficient. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem normalThreeBody_inner_eq_slice_sum {Q N : ℕ} (ψ φ : State Q (N+3))
    (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner ψ (normalThreeBodyApply φ) = ((N+3).choose 3 : ℂ) *
      ∑ a : Configuration Q N,
        inner (threeBodySlice ψ a) (normalThreeBodyApply (threeBodySlice φ a)) := by
  have hs (a : Configuration Q N) :
      inner (threeBodySlice ψ a) (normalThreeBodyApply (threeBodySlice φ a)) =
        (6 : ℂ) * inner (threeBodySlice ψ a)
          (pairApply 0 1 (pairApply 0 2 (threeBodySlice φ a))) := by
    simpa using normalThreeBody_inner_eq_first_bosonic (N := 0)
      (threeBodySlice ψ a) (threeBodySlice φ a)
      (threeBodySlice_isBosonic ψ hψ a) (threeBodySlice_isBosonic φ hφ a)
  rw [normalThreeBody_inner_eq_first_bosonic ψ φ hψ hφ,
    inner_firstThree_pairProduct]
  simp_rw [hs, ← Finset.mul_sum]
  push_cast
  ring

theorem normalThreeBody_eq_lift_above {Q N : ℕ} (ψ : State Q (N+3))
    (hψ : IsBosonic ψ) :
    normalThreeBodyApply ψ = threeBodyLiftAbove Q N (normalThreeBodyLinear Q 3) ψ := by
  apply bosonic_stateInner_ext _ _ (normalThreeBodyApply_isBosonic ψ hψ)
    (threeBodyLiftAbove_isBosonic Q N _ ψ)
  intro φ hφ
  rw [threeBodyLiftAbove_inner_bosonic Q N _ φ ψ hφ hψ]
  exact normalThreeBody_inner_eq_slice_sum φ ψ hφ hψ

/-- Every finite particle sector, including the zero one-, two-, and vacuum-sector terms. -/
theorem normalThreeBody_eq_lift {Q M : ℕ} (ψ : State Q M) (hψ : IsBosonic ψ) :
    normalThreeBodyApply ψ = threeBodyLift Q M (normalThreeBodyLinear Q 3) ψ := by
  rcases M with _ | (_ | (_ | N))
  · rw [normalThreeBody_small_sector (by omega)]
    rfl
  · rw [normalThreeBody_small_sector (by omega)]
    rfl
  · rw [normalThreeBody_small_sector (by omega)]
    rfl
  · exact normalThreeBody_eq_lift_above ψ hψ

end
end BosonicLaughlin

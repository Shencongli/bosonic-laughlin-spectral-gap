import BosonicLaughlin.RetainedCMFrames
import BosonicLaughlin.OccupationCMBlocks
import BosonicLaughlin.OccupationSortedCoordinates

/-!
The script has no degree-minus-one rows at degree zero. The physical CM map
instead has a degree-zero target, and is zero. Its one-dimensional source and
the retained column [1] therefore give the full physical highest-weight block.
-/
namespace BosonicLaughlin
noncomputable section
open scoped Matrix

theorem sortedDegreeTuple_zero_eq {N : ℕ} (a : SortedDegreeTuple N 0) :
    a.val = fun _ => 0 := by
  funext i
  have h := sortedDegreeTuple_entry_le a i
  omega

def zeroDegreeTupleEquiv (N : ℕ) : Fin 1 ≃ SortedDegreeTuple N 0 where
  toFun _ := ⟨fun _ => 0, (by intro _ _ _; rfl), by simp⟩
  invFun _ := 0
  left_inv i := Subsingleton.elim _ _
  right_inv a := by
    apply Subtype.ext
    exact (sortedDegreeTuple_zero_eq a).symm

def zeroDegreeOccupationEquiv (Q N : ℕ) : Fin 1 ≃ WeightOccupation Q N 0 :=
  (zeroDegreeTupleEquiv N).trans (sortedDegreeOccupationEquiv (Nat.zero_le Q))

def zeroDegreeOccupationCoordinates (Q N : ℕ) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] WeightOccupationState Q N 0 where
  toFun c := c ∘ (zeroDegreeOccupationEquiv Q N).symm
  invFun c := c ∘ zeroDegreeOccupationEquiv Q N
  left_inv c := by funext i; simp only [Function.comp_apply, Equiv.symm_apply_apply]
  right_inv c := by funext i; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem occupationCMBlock_zero_degree (Q N : ℕ) : occupationCMBlock Q N 0=0 := by
  apply LinearMap.ext
  intro c
  change occupationCMBlock Q N 0 c=0
  apply (polynomialWeightOccupationInclude_CMBlock_zero_iff c).mp
  apply (weightPolynomialCM_zero_iff _).mpr
  exact polynomialCM_zero_weight _ (weightInclude_supported _)

def zeroDegreeCMKernelEquiv (Q N : ℕ) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] LinearMap.ker (occupationCMBlock Q N 0) where
  toFun c := ⟨zeroDegreeOccupationCoordinates Q N c, by
    rw [LinearMap.mem_ker, occupationCMBlock_zero_degree]; rfl⟩
  invFun c := (zeroDegreeOccupationCoordinates Q N).symm c.val
  left_inv c := (zeroDegreeOccupationCoordinates Q N).symm_apply_apply c
  right_inv c := by
    apply Subtype.ext
    exact (zeroDegreeOccupationCoordinates Q N).apply_symm_apply c.val
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

def zeroDegreePhysicalHighestEquiv (Q N : ℕ) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N 0 :=
  (zeroDegreeCMKernelEquiv Q N).trans (occupationHighestWeightEquiv Q N 0)

theorem zeroDegreePhysicalHighestEquiv_apply (Q N : ℕ) (c : Fin 1 → ℂ) :
    (zeroDegreePhysicalHighestEquiv Q N c).val =
      (polynomialWeightCoordinates Q N 0).symm
        (polynomialWeightOccupationInclude (c ∘ (zeroDegreeOccupationEquiv Q N).symm)) := rfl

theorem physicalHighestWeight_zero_degree_finrank (Q N : ℕ) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q N 0)=1 := by
  rw [← (zeroDegreePhysicalHighestEquiv Q N).finrank_eq]
  simp

theorem retainedCM_3_0_U_identity : retainedCM_3_0U=1 := by decide +kernel

theorem retainedCM_4_0_U_identity : retainedCM_4_0U=1 := by decide +kernel

theorem retainedCM_3_0_columns_complete (Q : ℕ) :
    Function.Bijective (fun c : Fin 1 → ℂ => zeroDegreePhysicalHighestEquiv Q 3
      ((retainedCM_3_0U.map (Rat.castHom ℂ)) *ᵥ c)) := by
  simpa [retainedCM_3_0_U_identity] using (zeroDegreePhysicalHighestEquiv Q 3).bijective

theorem retainedCM_4_0_columns_complete (Q : ℕ) :
    Function.Bijective (fun c : Fin 1 → ℂ => zeroDegreePhysicalHighestEquiv Q 4
      ((retainedCM_4_0U.map (Rat.castHom ℂ)) *ᵥ c)) := by
  simpa [retainedCM_4_0_U_identity] using (zeroDegreePhysicalHighestEquiv Q 4).bijective

end
end BosonicLaughlin

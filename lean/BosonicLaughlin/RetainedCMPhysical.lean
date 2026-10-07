import BosonicLaughlin.RetainedCMCoordinates
import BosonicLaughlin.RetainedCMZeroDegree
import BosonicLaughlin.KernelFramePhysical

/-! The retained rational columns give complete (nonorthonormal)
coordinates on the actual spherical physical highest-weight spaces.
Positive degrees require Q >= d; the degree-zero result holds for all Q. -/
namespace BosonicLaughlin
noncomputable section
open scoped Matrix

theorem retainedCM_3_0_physical_finrank (Q : ℕ) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 0)=1 :=
  physicalHighestWeight_zero_degree_finrank Q 3

def retainedCM_3_1_physicalEquiv (Q : ℕ) (hd : 1≤Q) :
    (Fin 0 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 3 1 :=
  indexedKernelFramePhysicalEquiv retainedCM_3_1_frame hd retainedEnum_3_1 retainedEnum_3_0
    (retainedCM_3_1_physical_matrix Q hd)

theorem retainedCM_3_1_physical_apply (Q : ℕ) (hd : 1≤Q) (c : Fin 0 → ℂ) :
    (retainedCM_3_1_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 3 1).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_3_1U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_3_1.occupationEquiv hd).symm)) := rfl

theorem retainedCM_3_1_columns_complete (Q : ℕ) (hd : 1≤Q) :
    Function.Bijective (retainedCM_3_1_physicalEquiv Q hd) :=
  (retainedCM_3_1_physicalEquiv Q hd).bijective

theorem retainedCM_3_1_physical_finrank (Q : ℕ) (hd : 1≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 1)=0 := by
  rw [← (retainedCM_3_1_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_3_2_physicalEquiv (Q : ℕ) (hd : 2≤Q) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 3 2 :=
  indexedKernelFramePhysicalEquiv retainedCM_3_2_frame hd retainedEnum_3_2 retainedEnum_3_1
    (retainedCM_3_2_physical_matrix Q hd)

theorem retainedCM_3_2_physical_apply (Q : ℕ) (hd : 2≤Q) (c : Fin 1 → ℂ) :
    (retainedCM_3_2_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 3 2).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_3_2U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_3_2.occupationEquiv hd).symm)) := rfl

theorem retainedCM_3_2_columns_complete (Q : ℕ) (hd : 2≤Q) :
    Function.Bijective (retainedCM_3_2_physicalEquiv Q hd) :=
  (retainedCM_3_2_physicalEquiv Q hd).bijective

theorem retainedCM_3_2_physical_finrank (Q : ℕ) (hd : 2≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 2)=1 := by
  rw [← (retainedCM_3_2_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_3_3_physicalEquiv (Q : ℕ) (hd : 3≤Q) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 3 3 :=
  indexedKernelFramePhysicalEquiv retainedCM_3_3_frame hd retainedEnum_3_3 retainedEnum_3_2
    (retainedCM_3_3_physical_matrix Q hd)

theorem retainedCM_3_3_physical_apply (Q : ℕ) (hd : 3≤Q) (c : Fin 1 → ℂ) :
    (retainedCM_3_3_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 3 3).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_3_3U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_3_3.occupationEquiv hd).symm)) := rfl

theorem retainedCM_3_3_columns_complete (Q : ℕ) (hd : 3≤Q) :
    Function.Bijective (retainedCM_3_3_physicalEquiv Q hd) :=
  (retainedCM_3_3_physicalEquiv Q hd).bijective

theorem retainedCM_3_3_physical_finrank (Q : ℕ) (hd : 3≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 3)=1 := by
  rw [← (retainedCM_3_3_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_3_4_physicalEquiv (Q : ℕ) (hd : 4≤Q) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 3 4 :=
  indexedKernelFramePhysicalEquiv retainedCM_3_4_frame hd retainedEnum_3_4 retainedEnum_3_3
    (retainedCM_3_4_physical_matrix Q hd)

theorem retainedCM_3_4_physical_apply (Q : ℕ) (hd : 4≤Q) (c : Fin 1 → ℂ) :
    (retainedCM_3_4_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 3 4).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_3_4U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_3_4.occupationEquiv hd).symm)) := rfl

theorem retainedCM_3_4_columns_complete (Q : ℕ) (hd : 4≤Q) :
    Function.Bijective (retainedCM_3_4_physicalEquiv Q hd) :=
  (retainedCM_3_4_physicalEquiv Q hd).bijective

theorem retainedCM_3_4_physical_finrank (Q : ℕ) (hd : 4≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 4)=1 := by
  rw [← (retainedCM_3_4_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_3_5_physicalEquiv (Q : ℕ) (hd : 5≤Q) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 3 5 :=
  indexedKernelFramePhysicalEquiv retainedCM_3_5_frame hd retainedEnum_3_5 retainedEnum_3_4
    (retainedCM_3_5_physical_matrix Q hd)

theorem retainedCM_3_5_physical_apply (Q : ℕ) (hd : 5≤Q) (c : Fin 1 → ℂ) :
    (retainedCM_3_5_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 3 5).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_3_5U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_3_5.occupationEquiv hd).symm)) := rfl

theorem retainedCM_3_5_columns_complete (Q : ℕ) (hd : 5≤Q) :
    Function.Bijective (retainedCM_3_5_physicalEquiv Q hd) :=
  (retainedCM_3_5_physicalEquiv Q hd).bijective

theorem retainedCM_3_5_physical_finrank (Q : ℕ) (hd : 5≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 5)=1 := by
  rw [← (retainedCM_3_5_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_3_6_physicalEquiv (Q : ℕ) (hd : 6≤Q) :
    (Fin 2 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 3 6 :=
  indexedKernelFramePhysicalEquiv retainedCM_3_6_frame hd retainedEnum_3_6 retainedEnum_3_5
    (retainedCM_3_6_physical_matrix Q hd)

theorem retainedCM_3_6_physical_apply (Q : ℕ) (hd : 6≤Q) (c : Fin 2 → ℂ) :
    (retainedCM_3_6_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 3 6).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_3_6U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_3_6.occupationEquiv hd).symm)) := rfl

theorem retainedCM_3_6_columns_complete (Q : ℕ) (hd : 6≤Q) :
    Function.Bijective (retainedCM_3_6_physicalEquiv Q hd) :=
  (retainedCM_3_6_physicalEquiv Q hd).bijective

theorem retainedCM_3_6_physical_finrank (Q : ℕ) (hd : 6≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 6)=2 := by
  rw [← (retainedCM_3_6_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_3_7_physicalEquiv (Q : ℕ) (hd : 7≤Q) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 3 7 :=
  indexedKernelFramePhysicalEquiv retainedCM_3_7_frame hd retainedEnum_3_7 retainedEnum_3_6
    (retainedCM_3_7_physical_matrix Q hd)

theorem retainedCM_3_7_physical_apply (Q : ℕ) (hd : 7≤Q) (c : Fin 1 → ℂ) :
    (retainedCM_3_7_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 3 7).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_3_7U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_3_7.occupationEquiv hd).symm)) := rfl

theorem retainedCM_3_7_columns_complete (Q : ℕ) (hd : 7≤Q) :
    Function.Bijective (retainedCM_3_7_physicalEquiv Q hd) :=
  (retainedCM_3_7_physicalEquiv Q hd).bijective

theorem retainedCM_3_7_physical_finrank (Q : ℕ) (hd : 7≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 7)=1 := by
  rw [← (retainedCM_3_7_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_3_8_physicalEquiv (Q : ℕ) (hd : 8≤Q) :
    (Fin 2 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 3 8 :=
  indexedKernelFramePhysicalEquiv retainedCM_3_8_frame hd retainedEnum_3_8 retainedEnum_3_7
    (retainedCM_3_8_physical_matrix Q hd)

theorem retainedCM_3_8_physical_apply (Q : ℕ) (hd : 8≤Q) (c : Fin 2 → ℂ) :
    (retainedCM_3_8_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 3 8).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_3_8U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_3_8.occupationEquiv hd).symm)) := rfl

theorem retainedCM_3_8_columns_complete (Q : ℕ) (hd : 8≤Q) :
    Function.Bijective (retainedCM_3_8_physicalEquiv Q hd) :=
  (retainedCM_3_8_physicalEquiv Q hd).bijective

theorem retainedCM_3_8_physical_finrank (Q : ℕ) (hd : 8≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 8)=2 := by
  rw [← (retainedCM_3_8_physicalEquiv Q hd).finrank_eq]
  simp

theorem retainedCM_4_0_physical_finrank (Q : ℕ) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 0)=1 :=
  physicalHighestWeight_zero_degree_finrank Q 4

def retainedCM_4_1_physicalEquiv (Q : ℕ) (hd : 1≤Q) :
    (Fin 0 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 1 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_1_frame hd retainedEnum_4_1 retainedEnum_4_0
    (retainedCM_4_1_physical_matrix Q hd)

theorem retainedCM_4_1_physical_apply (Q : ℕ) (hd : 1≤Q) (c : Fin 0 → ℂ) :
    (retainedCM_4_1_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 1).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_1U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_1.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_1_columns_complete (Q : ℕ) (hd : 1≤Q) :
    Function.Bijective (retainedCM_4_1_physicalEquiv Q hd) :=
  (retainedCM_4_1_physicalEquiv Q hd).bijective

theorem retainedCM_4_1_physical_finrank (Q : ℕ) (hd : 1≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 1)=0 := by
  rw [← (retainedCM_4_1_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_2_physicalEquiv (Q : ℕ) (hd : 2≤Q) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 2 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_2_frame hd retainedEnum_4_2 retainedEnum_4_1
    (retainedCM_4_2_physical_matrix Q hd)

theorem retainedCM_4_2_physical_apply (Q : ℕ) (hd : 2≤Q) (c : Fin 1 → ℂ) :
    (retainedCM_4_2_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 2).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_2U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_2.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_2_columns_complete (Q : ℕ) (hd : 2≤Q) :
    Function.Bijective (retainedCM_4_2_physicalEquiv Q hd) :=
  (retainedCM_4_2_physicalEquiv Q hd).bijective

theorem retainedCM_4_2_physical_finrank (Q : ℕ) (hd : 2≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 2)=1 := by
  rw [← (retainedCM_4_2_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_3_physicalEquiv (Q : ℕ) (hd : 3≤Q) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 3 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_3_frame hd retainedEnum_4_3 retainedEnum_4_2
    (retainedCM_4_3_physical_matrix Q hd)

theorem retainedCM_4_3_physical_apply (Q : ℕ) (hd : 3≤Q) (c : Fin 1 → ℂ) :
    (retainedCM_4_3_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 3).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_3U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_3.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_3_columns_complete (Q : ℕ) (hd : 3≤Q) :
    Function.Bijective (retainedCM_4_3_physicalEquiv Q hd) :=
  (retainedCM_4_3_physicalEquiv Q hd).bijective

theorem retainedCM_4_3_physical_finrank (Q : ℕ) (hd : 3≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 3)=1 := by
  rw [← (retainedCM_4_3_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_4_physicalEquiv (Q : ℕ) (hd : 4≤Q) :
    (Fin 2 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 4 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_4_frame hd retainedEnum_4_4 retainedEnum_4_3
    (retainedCM_4_4_physical_matrix Q hd)

theorem retainedCM_4_4_physical_apply (Q : ℕ) (hd : 4≤Q) (c : Fin 2 → ℂ) :
    (retainedCM_4_4_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 4).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_4U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_4.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_4_columns_complete (Q : ℕ) (hd : 4≤Q) :
    Function.Bijective (retainedCM_4_4_physicalEquiv Q hd) :=
  (retainedCM_4_4_physicalEquiv Q hd).bijective

theorem retainedCM_4_4_physical_finrank (Q : ℕ) (hd : 4≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 4)=2 := by
  rw [← (retainedCM_4_4_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_5_physicalEquiv (Q : ℕ) (hd : 5≤Q) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 5 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_5_frame hd retainedEnum_4_5 retainedEnum_4_4
    (retainedCM_4_5_physical_matrix Q hd)

theorem retainedCM_4_5_physical_apply (Q : ℕ) (hd : 5≤Q) (c : Fin 1 → ℂ) :
    (retainedCM_4_5_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 5).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_5U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_5.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_5_columns_complete (Q : ℕ) (hd : 5≤Q) :
    Function.Bijective (retainedCM_4_5_physicalEquiv Q hd) :=
  (retainedCM_4_5_physicalEquiv Q hd).bijective

theorem retainedCM_4_5_physical_finrank (Q : ℕ) (hd : 5≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 5)=1 := by
  rw [← (retainedCM_4_5_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_6_physicalEquiv (Q : ℕ) (hd : 6≤Q) :
    (Fin 3 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 6 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_6_frame hd retainedEnum_4_6 retainedEnum_4_5
    (retainedCM_4_6_physical_matrix Q hd)

theorem retainedCM_4_6_physical_apply (Q : ℕ) (hd : 6≤Q) (c : Fin 3 → ℂ) :
    (retainedCM_4_6_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 6).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_6U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_6.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_6_columns_complete (Q : ℕ) (hd : 6≤Q) :
    Function.Bijective (retainedCM_4_6_physicalEquiv Q hd) :=
  (retainedCM_4_6_physicalEquiv Q hd).bijective

theorem retainedCM_4_6_physical_finrank (Q : ℕ) (hd : 6≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 6)=3 := by
  rw [← (retainedCM_4_6_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_7_physicalEquiv (Q : ℕ) (hd : 7≤Q) :
    (Fin 2 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 7 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_7_frame hd retainedEnum_4_7 retainedEnum_4_6
    (retainedCM_4_7_physical_matrix Q hd)

theorem retainedCM_4_7_physical_apply (Q : ℕ) (hd : 7≤Q) (c : Fin 2 → ℂ) :
    (retainedCM_4_7_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 7).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_7U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_7.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_7_columns_complete (Q : ℕ) (hd : 7≤Q) :
    Function.Bijective (retainedCM_4_7_physicalEquiv Q hd) :=
  (retainedCM_4_7_physicalEquiv Q hd).bijective

theorem retainedCM_4_7_physical_finrank (Q : ℕ) (hd : 7≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 7)=2 := by
  rw [← (retainedCM_4_7_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_8_physicalEquiv (Q : ℕ) (hd : 8≤Q) :
    (Fin 4 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 8 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_8_frame hd retainedEnum_4_8 retainedEnum_4_7
    (retainedCM_4_8_physical_matrix Q hd)

theorem retainedCM_4_8_physical_apply (Q : ℕ) (hd : 8≤Q) (c : Fin 4 → ℂ) :
    (retainedCM_4_8_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 8).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_8U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_8.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_8_columns_complete (Q : ℕ) (hd : 8≤Q) :
    Function.Bijective (retainedCM_4_8_physicalEquiv Q hd) :=
  (retainedCM_4_8_physicalEquiv Q hd).bijective

theorem retainedCM_4_8_physical_finrank (Q : ℕ) (hd : 8≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 8)=4 := by
  rw [← (retainedCM_4_8_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_9_physicalEquiv (Q : ℕ) (hd : 9≤Q) :
    (Fin 3 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 9 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_9_frame hd retainedEnum_4_9 retainedEnum_4_8
    (retainedCM_4_9_physical_matrix Q hd)

theorem retainedCM_4_9_physical_apply (Q : ℕ) (hd : 9≤Q) (c : Fin 3 → ℂ) :
    (retainedCM_4_9_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 9).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_9U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_9.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_9_columns_complete (Q : ℕ) (hd : 9≤Q) :
    Function.Bijective (retainedCM_4_9_physicalEquiv Q hd) :=
  (retainedCM_4_9_physicalEquiv Q hd).bijective

theorem retainedCM_4_9_physical_finrank (Q : ℕ) (hd : 9≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 9)=3 := by
  rw [← (retainedCM_4_9_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_10_physicalEquiv (Q : ℕ) (hd : 10≤Q) :
    (Fin 5 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 10 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_10_frame hd retainedEnum_4_10 retainedEnum_4_9
    (retainedCM_4_10_physical_matrix Q hd)

theorem retainedCM_4_10_physical_apply (Q : ℕ) (hd : 10≤Q) (c : Fin 5 → ℂ) :
    (retainedCM_4_10_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 10).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_10U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_10.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_10_columns_complete (Q : ℕ) (hd : 10≤Q) :
    Function.Bijective (retainedCM_4_10_physicalEquiv Q hd) :=
  (retainedCM_4_10_physicalEquiv Q hd).bijective

theorem retainedCM_4_10_physical_finrank (Q : ℕ) (hd : 10≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 10)=5 := by
  rw [← (retainedCM_4_10_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_11_physicalEquiv (Q : ℕ) (hd : 11≤Q) :
    (Fin 4 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 11 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_11_frame hd retainedEnum_4_11 retainedEnum_4_10
    (retainedCM_4_11_physical_matrix Q hd)

theorem retainedCM_4_11_physical_apply (Q : ℕ) (hd : 11≤Q) (c : Fin 4 → ℂ) :
    (retainedCM_4_11_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 11).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_11U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_11.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_11_columns_complete (Q : ℕ) (hd : 11≤Q) :
    Function.Bijective (retainedCM_4_11_physicalEquiv Q hd) :=
  (retainedCM_4_11_physicalEquiv Q hd).bijective

theorem retainedCM_4_11_physical_finrank (Q : ℕ) (hd : 11≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 11)=4 := by
  rw [← (retainedCM_4_11_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_12_physicalEquiv (Q : ℕ) (hd : 12≤Q) :
    (Fin 7 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 12 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_12_frame hd retainedEnum_4_12 retainedEnum_4_11
    (retainedCM_4_12_physical_matrix Q hd)

theorem retainedCM_4_12_physical_apply (Q : ℕ) (hd : 12≤Q) (c : Fin 7 → ℂ) :
    (retainedCM_4_12_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 12).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_12U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_12.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_12_columns_complete (Q : ℕ) (hd : 12≤Q) :
    Function.Bijective (retainedCM_4_12_physicalEquiv Q hd) :=
  (retainedCM_4_12_physicalEquiv Q hd).bijective

theorem retainedCM_4_12_physical_finrank (Q : ℕ) (hd : 12≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 12)=7 := by
  rw [← (retainedCM_4_12_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_13_physicalEquiv (Q : ℕ) (hd : 13≤Q) :
    (Fin 5 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 13 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_13_frame hd retainedEnum_4_13 retainedEnum_4_12
    (retainedCM_4_13_physical_matrix Q hd)

theorem retainedCM_4_13_physical_apply (Q : ℕ) (hd : 13≤Q) (c : Fin 5 → ℂ) :
    (retainedCM_4_13_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 13).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_13U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_13.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_13_columns_complete (Q : ℕ) (hd : 13≤Q) :
    Function.Bijective (retainedCM_4_13_physicalEquiv Q hd) :=
  (retainedCM_4_13_physicalEquiv Q hd).bijective

theorem retainedCM_4_13_physical_finrank (Q : ℕ) (hd : 13≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 13)=5 := by
  rw [← (retainedCM_4_13_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_14_physicalEquiv (Q : ℕ) (hd : 14≤Q) :
    (Fin 8 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 14 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_14_frame hd retainedEnum_4_14 retainedEnum_4_13
    (retainedCM_4_14_physical_matrix Q hd)

theorem retainedCM_4_14_physical_apply (Q : ℕ) (hd : 14≤Q) (c : Fin 8 → ℂ) :
    (retainedCM_4_14_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 14).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_14U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_14.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_14_columns_complete (Q : ℕ) (hd : 14≤Q) :
    Function.Bijective (retainedCM_4_14_physicalEquiv Q hd) :=
  (retainedCM_4_14_physicalEquiv Q hd).bijective

theorem retainedCM_4_14_physical_finrank (Q : ℕ) (hd : 14≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 14)=8 := by
  rw [← (retainedCM_4_14_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_15_physicalEquiv (Q : ℕ) (hd : 15≤Q) :
    (Fin 7 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 15 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_15_frame hd retainedEnum_4_15 retainedEnum_4_14
    (retainedCM_4_15_physical_matrix Q hd)

theorem retainedCM_4_15_physical_apply (Q : ℕ) (hd : 15≤Q) (c : Fin 7 → ℂ) :
    (retainedCM_4_15_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 15).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_15U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_15.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_15_columns_complete (Q : ℕ) (hd : 15≤Q) :
    Function.Bijective (retainedCM_4_15_physicalEquiv Q hd) :=
  (retainedCM_4_15_physicalEquiv Q hd).bijective

theorem retainedCM_4_15_physical_finrank (Q : ℕ) (hd : 15≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 15)=7 := by
  rw [← (retainedCM_4_15_physicalEquiv Q hd).finrank_eq]
  simp

def retainedCM_4_16_physicalEquiv (Q : ℕ) (hd : 16≤Q) :
    (Fin 10 → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q 4 16 :=
  indexedKernelFramePhysicalEquiv retainedCM_4_16_frame hd retainedEnum_4_16 retainedEnum_4_15
    (retainedCM_4_16_physical_matrix Q hd)

theorem retainedCM_4_16_physical_apply (Q : ℕ) (hd : 16≤Q) (c : Fin 10 → ℂ) :
    (retainedCM_4_16_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 16).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_16U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_16.occupationEquiv hd).symm)) := rfl

theorem retainedCM_4_16_columns_complete (Q : ℕ) (hd : 16≤Q) :
    Function.Bijective (retainedCM_4_16_physicalEquiv Q hd) :=
  (retainedCM_4_16_physicalEquiv Q hd).bijective

theorem retainedCM_4_16_physical_finrank (Q : ℕ) (hd : 16≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 16)=10 := by
  rw [← (retainedCM_4_16_physicalEquiv Q hd).finrank_eq]
  simp

end
end BosonicLaughlin

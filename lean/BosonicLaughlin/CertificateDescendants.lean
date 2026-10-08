import BosonicLaughlin.TensorDescendants
import BosonicLaughlin.CertificateHighestWeight
import BosonicLaughlin.PhysicalComparisonForms

/-! Descendant Gram identities in the actual certificate coordinates and in
any complete physical highest-weight frame. The frame metric is preserved;
the occupation or highest-weight frame is not silently assumed orthonormal. -/
namespace BosonicLaughlin
noncomputable section

theorem certificateHighest_weight {Q N d : ℕ} (hQ : 0<Q) (hd : 2*d≤N*Q)
    (c : WeightOccupationState Q N d) :
    tensorWeight (certificateWeightCoordinates Q N d c)=
      ((N*Q-2*d : ℕ) : ℂ) • certificateWeightCoordinates Q N d c := by
  rw [tensorWeight_of_supported _ (certificateWeightCoordinates_weightSupported hQ N d c)]
  simp only [Nat.cast_sub hd, Nat.cast_mul, Nat.cast_ofNat]

theorem certificateDescendant_inner {Q N d : ℕ} (hQ : 0<Q) (hd : 2*d≤N*Q)
    (c e : WeightOccupationState Q N d)
    (he : (occupationCMBlockMatrix Q N d).mulVec e=0)
    (n : ℕ) (hn : n≤N*Q-2*d) :
    inner (tensorDescendant (certificateWeightCoordinates Q N d c) n)
      (tensorDescendant (certificateWeightCoordinates Q N d e) n)=
      (descendantFactor (N*Q-2*d) n : ℂ)*certificateInner c e := by
  rw [tensorDescendant_inner _ _ (N*Q-2*d)
      ((tensorRaise_certificateWeightCoordinates_zero_iff hQ e).mpr he)
      (certificateHighest_weight hQ hd e) n hn,
    certificateWeightCoordinates_inner hQ]

theorem normalizedCertificateDescendant_inner {Q N d : ℕ} (hQ : 0<Q) (hd : 2*d≤N*Q)
    (c e : WeightOccupationState Q N d)
    (he : (occupationCMBlockMatrix Q N d).mulVec e=0)
    (n : ℕ) (hn : n≤N*Q-2*d) :
    inner (normalizedTensorDescendant (certificateWeightCoordinates Q N d c) (N*Q-2*d) n)
      (normalizedTensorDescendant (certificateWeightCoordinates Q N d e) (N*Q-2*d) n)=
      certificateInner c e := by
  rw [normalizedTensorDescendant_inner _ _ (N*Q-2*d)
      ((tensorRaise_certificateWeightCoordinates_zero_iff hQ e).mpr he)
      (certificateHighest_weight hQ hd e) n hn,
    certificateWeightCoordinates_inner hQ]

theorem highestWeightPhysicalFrame_raise {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d) (c : Fin k → ℂ) :
    tensorRaise (highestWeightPhysicalFrame E c)=0 :=
  ((mem_physicalHighestWeightSubspace (E c).val).mp (E c).property).2

theorem highestWeightPhysicalFrame_supported {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d) (c : Fin k → ℂ) :
    WeightSupported d (highestWeightPhysicalFrame E c) := weightInclude_supported (E c).val

theorem highestWeightPhysicalFrame_isBosonic {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d) (c : Fin k → ℂ) :
    IsBosonic (highestWeightPhysicalFrame E c) :=
  ((mem_physicalHighestWeightSubspace (E c).val).mp (E c).property).1

def normalizedDescendantFrame {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d) (n : ℕ) :
    (Fin k → ℂ) →ₗ[ℂ] State Q N :=
  (((Real.sqrt (descendantFactor (N*Q-2*d) n : ℝ))⁻¹ : ℝ) : ℂ) •
    ((tensorLowerLinear Q N ^ n).comp (highestWeightPhysicalFrame E))

theorem normalizedDescendantFrame_apply {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d) (n : ℕ) (c : Fin k → ℂ) :
    normalizedDescendantFrame E n c=
      normalizedTensorDescendant (highestWeightPhysicalFrame E c) (N*Q-2*d) n := rfl

theorem normalizedDescendantFrame_inner {Q N d k : ℕ} (hd : 2*d≤N*Q)
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d)
    (n : ℕ) (hn : n≤N*Q-2*d) (c e : Fin k → ℂ) :
    inner (normalizedDescendantFrame E n c) (normalizedDescendantFrame E n e)=
      inner (highestWeightPhysicalFrame E c) (highestWeightPhysicalFrame E e) := by
  have hw := tensorWeight_of_supported _ (highestWeightPhysicalFrame_supported E e)
  have hw' : tensorWeight (highestWeightPhysicalFrame E e)=
      ((N*Q-2*d : ℕ) : ℂ) • highestWeightPhysicalFrame E e := by
    simpa only [Nat.cast_sub hd, Nat.cast_mul, Nat.cast_ofNat] using hw
  exact normalizedTensorDescendant_inner _ _ _ (highestWeightPhysicalFrame_raise E e) hw' n hn

theorem normalizedDescendantFrame_orthogonal {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d)
    (n l : ℕ) (hnl : n≠l) (c e : Fin k → ℂ) :
    inner (normalizedDescendantFrame E n c) (normalizedDescendantFrame E l e)=0 :=
  normalizedTensorDescendant_orthogonal _ _ (highestWeightPhysicalFrame_supported E c)
    (highestWeightPhysicalFrame_supported E e) _ n l hnl

theorem normalizedDescendantFrame_gram {Q N d k : ℕ} (hd : 2*d≤N*Q)
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d)
    (n : ℕ) (hn : n≤N*Q-2*d) :
    physicalFormMatrix (normalizedDescendantFrame E n) (LinearMap.id : State Q N →ₗ[ℂ] State Q N)=
      physicalFormMatrix (highestWeightPhysicalFrame E) (LinearMap.id : State Q N →ₗ[ℂ] State Q N) := by
  ext i j
  simp only [physicalFormMatrix_apply, LinearMap.id_apply]
  exact normalizedDescendantFrame_inner hd E n hn _ _

theorem normalizedDescendantFrame_isBosonic {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d) (n : ℕ) (c : Fin k → ℂ) :
    IsBosonic (normalizedDescendantFrame E n c) :=
  (bosonicSubspace Q N).smul_mem _
    (tensorDescendant_isBosonic _ (highestWeightPhysicalFrame_isBosonic E c) n)

theorem normalizedDescendantFrame_supported {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d) (n : ℕ) (c : Fin k → ℂ) :
    WeightSupported (d+n) (normalizedDescendantFrame E n c) := by
  intro a ha
  change _ * tensorDescendant (highestWeightPhysicalFrame E c) n a=0
  rw [tensorDescendant_supported _ (highestWeightPhysicalFrame_supported E c) n a ha, mul_zero]

theorem normalizedDescendantFrame_finite_gram {Q N d k : ℕ} (hd : 2*d≤N*Q)
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d)
    (n l : Fin (N*Q-2*d+1)) (c e : Fin k → ℂ) :
    inner (normalizedDescendantFrame E n.val c) (normalizedDescendantFrame E l.val e)=
      if n=l then inner (highestWeightPhysicalFrame E c) (highestWeightPhysicalFrame E e) else 0 := by
  by_cases h : n=l
  · subst l
    simp only [ite_true]
    exact normalizedDescendantFrame_inner hd E n.val (by omega) c e
  · rw [ite_eq_right h]
    exact normalizedDescendantFrame_orthogonal E n.val l.val (fun he => h (Fin.ext he)) c e

end
end BosonicLaughlin

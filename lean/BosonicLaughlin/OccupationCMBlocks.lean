import BosonicLaughlin.OccupationHighestWeight
import BosonicLaughlin.OccupationPairBlocks

/-! Fixed-degree integer occupation CM matrices and the actual spherical
highest-weight condition. These are exact coordinate maps; no particular
enumeration or nullspace frame is built into their definitions. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem occupationWeight_replace {Q N : ℕ} (A : Occupation Q N)
    (x y : Orbital Q) (hx : x ∈ A.val) :
    occupationWeight (occupationReplace A x y hx) + x.val = occupationWeight A + y.val := by
  have he : A.val=x ::ₘ A.val.erase x := (Multiset.cons_erase hx).symm
  have hw := congrArg (fun B : Multiset (Orbital Q) => (B.map Fin.val).sum) he
  simp only [Multiset.map_cons, Multiset.sum_cons] at hw
  change ((y ::ₘ A.val.erase x).map Fin.val).sum + x.val = (A.val.map Fin.val).sum + y.val
  simp only [Multiset.map_cons, Multiset.sum_cons]
  omega

theorem occupationCM_weightSupported {Q N : ℕ} (d : ℕ) (c : OccupationState Q N)
    (hc : OccupationWeightSupported d c) : OccupationWeightSupported (d-1) (occupationCM c) := by
  intro B hB
  unfold occupationCM
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi hm
  · have hw := occupationWeight_replace B i (⟨i.val+1, by omega⟩ : Orbital Q) hm
    have hz : occupationWeight (occupationReplace B i ⟨i.val+1, by omega⟩ hm)≠d := by
      change _ + i.val = _ + (i.val+1) at hw
      omega
    simp only [hc _ hz, mul_zero]
  · rfl
  · rfl

def occupationCMBlock (Q N d : ℕ) :
    WeightOccupationState Q N d →ₗ[ℂ] WeightOccupationState Q N (d-1) :=
  (occupationWeightRestrictLinear Q N (d-1)).comp
    ((occupationCMLinear Q N).comp (occupationWeightExtendLinear Q N d))

theorem occupationCMBlock_apply {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    occupationCMBlock Q N d c =
      occupationWeightRestrict (d-1) (occupationCM (occupationWeightExtend d c)) := rfl

theorem occupationCMBlock_extend {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    occupationWeightExtend (d-1) (occupationCMBlock Q N d c) =
      occupationCM (occupationWeightExtend d c) := by
  rw [occupationCMBlock_apply, occupationWeightExtend_restrict_supported]
  exact occupationCM_weightSupported d _ (occupationWeightExtend_supported c)

theorem occupationCMBlock_zero_iff {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    occupationCMBlock Q N d c=0 ↔ occupationCM (occupationWeightExtend d c)=0 := by
  constructor
  · intro h
    rw [← occupationCMBlock_extend, h]
    exact (occupationWeightExtendLinear Q N (d-1)).map_zero
  · intro h
    rw [occupationCMBlock_apply, h]
    rfl

def occupationCMBlockMatrix (Q N d : ℕ) :
    Matrix (WeightOccupation Q N (d-1)) (WeightOccupation Q N d) ℂ :=
  LinearMap.toMatrix' (occupationCMBlock Q N d)

theorem occupationCMBlockMatrix_mulVec {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    (occupationCMBlockMatrix Q N d).mulVec c = occupationCMBlock Q N d c :=
  LinearMap.toMatrix'_mulVec _ _

theorem occupationCMBlockMatrix_apply (Q N d : ℕ)
    (B : WeightOccupation Q N (d-1)) (A : WeightOccupation Q N d) :
    occupationCMBlockMatrix Q N d B A = ∑ i : Orbital Q,
      if hi : i.val < Q then if hm : i ∈ B.val.val then
        let j : Orbital Q := ⟨i.val+1, by omega⟩
        if occupationReplace B.val i j hm=A.val then ((j.val * A.val.val.count j : ℕ) : ℂ) else 0
      else 0 else 0 := by
  rw [occupationCMBlockMatrix, LinearMap.toMatrix'_apply]
  change occupationCM (occupationWeightExtend d (Pi.single A 1)) B.val = _
  rw [occupationWeightExtend_single]
  exact occupationCMMatrix_apply Q N B.val A.val

theorem polynomialWeightOccupationInclude_CMBlock {Q N d : ℕ}
    (c : WeightOccupationState Q N d) :
    weightPolynomialCM Q N d (polynomialWeightOccupationInclude c) =
      polynomialWeightOccupationInclude (occupationCMBlock Q N d c) := by
  apply weightInclude_injective Q N (d-1)
  rw [weightPolynomialCM_include, polynomialWeightOccupationInclude_include,
    polynomialOccupationInclude_CM, polynomialWeightOccupationInclude_include,
    occupationCMBlock_extend]

theorem polynomialWeightOccupationInclude_CMBlock_zero_iff {Q N d : ℕ}
    (c : WeightOccupationState Q N d) :
    weightPolynomialCM Q N d (polynomialWeightOccupationInclude c)=0 ↔
      occupationCMBlock Q N d c=0 := by
  rw [polynomialWeightOccupationInclude_CMBlock]
  constructor
  · intro h
    apply polynomialWeightOccupationInclude_injective Q N (d-1)
    rw [h]
    exact ((polynomialWeightOccupationIncludeLinear Q N (d-1)).map_zero).symm
  · intro h
    rw [h]
    exact (polynomialWeightOccupationIncludeLinear Q N (d-1)).map_zero

theorem tensorRaise_weightOccupation_zero_iff {Q N d : ℕ}
    (c : WeightOccupationState Q N d) :
    tensorRaise ((polynomialCoordinates Q N).symm
      (weightInclude d (polynomialWeightOccupationInclude c)))=0 ↔
      (occupationCMBlockMatrix Q N d).mulVec c=0 := by
  rw [polynomialWeightOccupationInclude_include, tensorRaise_polynomialOccupation_zero_iff,
    occupationCMMatrix_mulVec, occupationCMBlockMatrix_mulVec, occupationCMBlock_zero_iff]

theorem weightTensorRaise_occupation_zero_iff {Q N d : ℕ}
    (c : WeightOccupationState Q N d) :
    weightTensorRaise Q N d ((polynomialWeightCoordinates Q N d).symm
      (polynomialWeightOccupationInclude c))=0 ↔ occupationCMBlock Q N d c=0 := by
  rw [← (polynomialWeightCoordinates Q N (d-1)).map_eq_zero_iff,
    polynomialWeightCoordinates_tensorRaise, LinearEquiv.apply_symm_apply,
    polynomialWeightOccupationInclude_CMBlock_zero_iff]

theorem occupationHighestWeight_mem_iff {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    (polynomialWeightCoordinates Q N d).symm (polynomialWeightOccupationInclude c) ∈
      physicalHighestWeightSubspace Q N d ↔ occupationCMBlock Q N d c=0 := by
  change (WeightIsBosonic ((polynomialWeightCoordinates Q N d).symm
      (polynomialWeightOccupationInclude c)) ∧
      weightTensorRaise Q N d ((polynomialWeightCoordinates Q N d).symm
        (polynomialWeightOccupationInclude c))=0) ↔ _
  have hb : WeightIsBosonic ((polynomialWeightCoordinates Q N d).symm
      (polynomialWeightOccupationInclude c)) := by
    apply (polynomialWeightCoordinates_bosonic_iff _).mp
    simpa only [LinearEquiv.apply_symm_apply] using polynomialWeightOccupationInclude_isBosonic c
  rw [weightTensorRaise_occupation_zero_iff]
  simp only [hb, true_and]

theorem occupationHighestWeight_surjective {Q N d : ℕ} (φ : WeightState Q N d)
    (hφ : φ ∈ physicalHighestWeightSubspace Q N d) :
    ∃ c : WeightOccupationState Q N d, occupationCMBlock Q N d c=0 ∧
      (polynomialWeightCoordinates Q N d).symm (polynomialWeightOccupationInclude c)=φ := by
  have hb : WeightIsBosonic φ := hφ.1
  have hp : WeightIsBosonic (polynomialWeightCoordinates Q N d φ) :=
    (polynomialWeightCoordinates_bosonic_iff φ).mpr hb
  obtain ⟨c,hc⟩ := polynomialWeightOccupationInclude_surjective_bosonic
    (polynomialWeightCoordinates Q N d φ) hp
  have he : (polynomialWeightCoordinates Q N d).symm (polynomialWeightOccupationInclude c)=φ := by
    rw [hc, LinearEquiv.symm_apply_apply]
  refine ⟨c, (occupationHighestWeight_mem_iff c).mp ?_, he⟩
  rw [he]
  exact hφ

/-- All physical highest-weight vectors are represented, not only vectors in
the image of a proposed numerical nullspace frame. -/
def occupationHighestWeightEquiv (Q N d : ℕ) :
    LinearMap.ker (occupationCMBlock Q N d) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d := by
  let F := (polynomialWeightCoordinates Q N d).symm.toLinearMap.comp
    (polynomialWeightOccupationIncludeLinear Q N d)
  let G : LinearMap.ker (occupationCMBlock Q N d) →ₗ[ℂ] physicalHighestWeightSubspace Q N d :=
    { toFun := fun c => ⟨F c.val, (occupationHighestWeight_mem_iff c.val).mpr c.property⟩
      map_add' := by intro c e; apply Subtype.ext; exact F.map_add c.val e.val
      map_smul' := by intro z c; apply Subtype.ext; exact F.map_smul z c.val }
  apply LinearEquiv.ofBijective G
  constructor
  · intro c e h
    apply Subtype.ext
    apply polynomialWeightOccupationInclude_injective Q N d
    apply (polynomialWeightCoordinates Q N d).symm.injective
    exact congrArg Subtype.val h
  · intro φ
    obtain ⟨c,hc,he⟩ := occupationHighestWeight_surjective φ.val φ.property
    exact ⟨⟨c,hc⟩, Subtype.ext he⟩

end
end BosonicLaughlin

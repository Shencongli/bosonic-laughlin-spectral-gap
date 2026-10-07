import BosonicLaughlin.OccupationCoordinates

/-! Restriction and zero extension for the actual total-degree occupation sector. -/
namespace BosonicLaughlin
noncomputable section

abbrev WeightOccupationState (Q N d : ℕ) := WeightOccupation Q N d → ℂ

theorem occupationWeight_cons {Q N : ℕ} (x : Orbital Q) (A : Occupation Q N) :
    occupationWeight (Sym.cons x A)=x.val+occupationWeight A := by
  change ((x ::ₘ A.val).map Fin.val).sum = _
  simp [occupationWeight]

def OccupationWeightSupported {Q N : ℕ} (d : ℕ) (c : OccupationState Q N) : Prop :=
  ∀ A, occupationWeight A≠d → c A=0

def occupationWeightExtend {Q N : ℕ} (d : ℕ) (c : WeightOccupationState Q N d) :
    OccupationState Q N := fun A => if h : occupationWeight A=d then c ⟨A,h⟩ else 0

def occupationWeightRestrict {Q N : ℕ} (d : ℕ) (c : OccupationState Q N) :
    WeightOccupationState Q N d := fun A => c A.val

theorem occupationWeightExtend_supported {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    OccupationWeightSupported d (occupationWeightExtend d c) := by
  intro A hA
  simp [occupationWeightExtend, hA]

theorem occupationWeightRestrict_extend {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    occupationWeightRestrict d (occupationWeightExtend d c)=c := by
  funext A
  simp [occupationWeightRestrict, occupationWeightExtend, A.property]

theorem occupationWeightExtend_restrict_supported {Q N : ℕ} (d : ℕ)
    (c : OccupationState Q N) (hc : OccupationWeightSupported d c) :
    occupationWeightExtend d (occupationWeightRestrict d c)=c := by
  funext A
  by_cases hA : occupationWeight A=d
  · simp [occupationWeightExtend, occupationWeightRestrict, hA]
  · simp [occupationWeightExtend, hA, hc A hA]

def occupationWeightExtendLinear (Q N d : ℕ) :
    WeightOccupationState Q N d →ₗ[ℂ] OccupationState Q N where
  toFun := occupationWeightExtend d
  map_add' c e := by
    funext A
    simp only [occupationWeightExtend, Pi.add_apply]
    split_ifs <;> simp
  map_smul' r c := by
    funext A
    simp only [occupationWeightExtend, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp

def occupationWeightRestrictLinear (Q N d : ℕ) :
    OccupationState Q N →ₗ[ℂ] WeightOccupationState Q N d where
  toFun := occupationWeightRestrict d
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def weightOccupationOfConfiguration {Q N d : ℕ} (a : WeightConfiguration Q N d) :
    WeightOccupation Q N d :=
  ⟨occupationOfConfiguration a.val, (occupationOfConfiguration_weight a.val).trans a.property⟩

theorem weightOccupationOfConfiguration_surjective (Q N d : ℕ) :
    Function.Surjective (@weightOccupationOfConfiguration Q N d) := by
  intro A
  refine ⟨⟨occupationRepresentative A.val, ?_⟩, ?_⟩
  · rw [← occupationOfConfiguration_weight, occupationOfConfiguration_representative]
    exact A.property
  · apply Subtype.ext
    exact occupationOfConfiguration_representative A.val

def weightOccupationInclude {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    WeightState Q N d := fun a => c (weightOccupationOfConfiguration a)

def weightOccupationIncludeLinear (Q N d : ℕ) :
    WeightOccupationState Q N d →ₗ[ℂ] WeightState Q N d where
  toFun := weightOccupationInclude
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem weightOccupationInclude_injective (Q N d : ℕ) :
    Function.Injective (@weightOccupationInclude Q N d) := by
  intro c e h
  funext A
  obtain ⟨a,ha⟩ := weightOccupationOfConfiguration_surjective Q N d A
  exact ha ▸ congrFun h a

theorem occupationInclude_weightSupported {Q N : ℕ} (d : ℕ)
    (c : OccupationState Q N) (hc : OccupationWeightSupported d c) :
    WeightSupported d (occupationInclude c) := by
  intro a ha
  exact hc _ (by simpa only [occupationOfConfiguration_weight] using ha)

theorem weightOccupationInclude_include {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    weightInclude d (weightOccupationInclude c) =
      occupationInclude (occupationWeightExtend d c) := by
  funext a
  simp only [weightInclude, occupationInclude, occupationWeightExtend,
    occupationOfConfiguration_weight]
  split_ifs <;> rfl

theorem weightOccupationInclude_isBosonic {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    WeightIsBosonic (weightOccupationInclude c) := by
  unfold WeightIsBosonic
  rw [weightOccupationInclude_include]
  exact occupationInclude_isBosonic _

theorem weightOccupationInclude_surjective_bosonic {Q N d : ℕ}
    (φ : WeightState Q N d) (hφ : WeightIsBosonic φ) :
    ∃ c : WeightOccupationState Q N d, weightOccupationInclude c=φ := by
  let c : WeightOccupationState Q N d := fun A =>
    weightInclude d φ (occupationRepresentative A.val)
  refine ⟨c, ?_⟩
  funext a
  change weightInclude d φ (occupationRepresentative (occupationOfConfiguration a.val))=φ a
  rw [isBosonic_eq_of_occupation_eq _ hφ _ a.val
    (occupationOfConfiguration_representative _)]
  simp [weightInclude, a.property]

end
end BosonicLaughlin

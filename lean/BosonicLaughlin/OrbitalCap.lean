import BosonicLaughlin.WeightCoordinates

/-!
Exact orbital-cap independence of an ordered-tensor block of total deficit d.
Every label in such a configuration is at most d. For d ≤ Q the coordinate
sets at orbital caps Q and d are therefore explicitly equivalent. Bose
symmetry is preserved by this coordinate identification.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem orbital_le_configurationWeight {Q N : ℕ} (a : Configuration Q N)
    (i : Fin N) : (a i).val ≤ configurationWeight a :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (a j).val) (Finset.mem_univ i)

/-- The coordinatewise inclusion of orbitals at cap d into those at cap Q. -/
def capConfiguration {Q d N : ℕ} (hd : d ≤ Q) (a : Configuration d N) :
    Configuration Q N := fun i => ⟨(a i).val, by have h := (a i).isLt; omega⟩

theorem capConfiguration_weight {Q d N : ℕ} (hd : d ≤ Q) (a : Configuration d N) :
    configurationWeight (capConfiguration hd a) = configurationWeight a := rfl

theorem capConfiguration_permute {Q d N : ℕ} (hd : d ≤ Q)
    (a : Configuration d N) (σ : Equiv.Perm (Fin N)) :
    capConfiguration hd (a ∘ σ) = capConfiguration hd a ∘ σ := rfl

theorem capConfiguration_injective {Q d N : ℕ} (hd : d ≤ Q) :
    Function.Injective (@capConfiguration Q d N hd) := by
  intro a b hab
  funext i
  apply Fin.ext
  exact congrArg (fun c : Configuration Q N => (c i).val) hab

/-- Truncation is defined on the exact total-deficit block, not on all states. -/
def lowerWeightConfiguration {Q N d : ℕ} (a : WeightConfiguration Q N d) :
    WeightConfiguration d N d :=
  ⟨fun i => ⟨(a.val i).val, by
      have h := orbital_le_configurationWeight a.val i
      rw [a.property] at h
      omega⟩, a.property⟩

def includeWeightConfiguration {Q N d : ℕ} (hd : d ≤ Q)
    (a : WeightConfiguration d N d) : WeightConfiguration Q N d :=
  ⟨capConfiguration hd a.val, a.property⟩

theorem lower_includeWeightConfiguration {Q N d : ℕ} (hd : d ≤ Q)
    (a : WeightConfiguration d N d) :
    lowerWeightConfiguration (includeWeightConfiguration hd a) = a := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rfl

theorem include_lowerWeightConfiguration {Q N d : ℕ} (hd : d ≤ Q)
    (a : WeightConfiguration Q N d) :
    includeWeightConfiguration hd (lowerWeightConfiguration a) = a := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rfl

def capConfigurationEquiv {Q N d : ℕ} (hd : d ≤ Q) :
    WeightConfiguration Q N d ≃ WeightConfiguration d N d where
  toFun := lowerWeightConfiguration
  invFun := includeWeightConfiguration hd
  left_inv := include_lowerWeightConfiguration hd
  right_inv := lower_includeWeightConfiguration hd

/-- Restriction of coefficients; the inverse is canonical zero extension in
the supported-state realization supplied by weightInclude. -/
def capWeightStateEquiv {Q N d : ℕ} (hd : d ≤ Q) :
    WeightState Q N d ≃ₗ[ℂ] WeightState d N d where
  toFun φ := fun a => φ (includeWeightConfiguration hd a)
  invFun χ := fun a => χ (lowerWeightConfiguration a)
  left_inv φ := by funext a; dsimp only; rw [include_lowerWeightConfiguration]
  right_inv χ := by funext a; dsimp only; rw [lower_includeWeightConfiguration]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem capWeightStateEquiv_apply {Q N d : ℕ} (hd : d ≤ Q)
    (φ : WeightState Q N d) (a : WeightConfiguration d N d) :
    capWeightStateEquiv hd φ a = φ (includeWeightConfiguration hd a) := rfl

theorem capWeightStateEquiv_symm_apply {Q N d : ℕ} (hd : d ≤ Q)
    (χ : WeightState d N d) (a : WeightConfiguration Q N d) :
    (capWeightStateEquiv hd).symm χ a = χ (lowerWeightConfiguration a) := rfl

theorem capWeightStateEquiv_include {Q N d : ℕ} (hd : d ≤ Q)
    (φ : WeightState Q N d) (a : Configuration d N) :
    weightInclude d (capWeightStateEquiv hd φ) a =
      weightInclude d φ (capConfiguration hd a) := by
  by_cases ha : configurationWeight a=d
  · simp only [weightInclude, capConfiguration_weight, ha, dite_true,
      capWeightStateEquiv_apply, includeWeightConfiguration]
  · simp [weightInclude, capConfiguration_weight, ha]

theorem weightIsBosonic_iff_permute {Q N d : ℕ} (φ : WeightState Q N d) :
    WeightIsBosonic φ ↔ ∀ (σ : Equiv.Perm (Fin N)) (a : WeightConfiguration Q N d),
      φ ⟨a.val ∘ σ, (configurationWeight_permute a.val σ).trans a.property⟩ = φ a := by
  constructor
  · intro h σ a
    have he := h σ a.val
    simpa only [weightInclude, configurationWeight_permute, a.property, dite_true] using he
  · intro h σ a
    by_cases ha : configurationWeight a=d
    · exact (show weightInclude d φ (a ∘ σ) = weightInclude d φ a from by
        simpa only [weightInclude, configurationWeight_permute, ha, dite_true]
          using h σ ⟨a,ha⟩)
    · simp [weightInclude, configurationWeight_permute, ha]

theorem capWeightStateEquiv_bosonic_iff {Q N d : ℕ} (hd : d ≤ Q)
    (φ : WeightState Q N d) :
    WeightIsBosonic (capWeightStateEquiv hd φ) ↔ WeightIsBosonic φ := by
  rw [weightIsBosonic_iff_permute, weightIsBosonic_iff_permute]
  constructor
  · intro h σ a
    have he := h σ (lowerWeightConfiguration a)
    change φ (includeWeightConfiguration hd (lowerWeightConfiguration
        ⟨a.val ∘ σ, (configurationWeight_permute a.val σ).trans a.property⟩)) =
      φ (includeWeightConfiguration hd (lowerWeightConfiguration a)) at he
    simpa only [include_lowerWeightConfiguration] using he
  · intro h σ a
    exact h σ (includeWeightConfiguration hd a)

end
end BosonicLaughlin

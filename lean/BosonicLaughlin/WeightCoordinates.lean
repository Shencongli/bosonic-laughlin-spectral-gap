import BosonicLaughlin.WeightBlocks

/-!
Coordinates for an exact orbital-deficit block. WeightState is an ambient
ordered-tensor block; WeightIsBosonic separately imposes Bose symmetry.
Restriction and zero extension identify it with the supported subspace.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

abbrev WeightConfiguration (Q N d : ℕ) :=
  {a : Configuration Q N // configurationWeight a = d}

abbrev WeightState (Q N d : ℕ) := WeightConfiguration Q N d → ℂ

def weightRestrict {Q N : ℕ} (d : ℕ) (ψ : State Q N) : WeightState Q N d :=
  fun a => ψ a.val

def weightInclude {Q N : ℕ} (d : ℕ) (φ : WeightState Q N d) : State Q N := fun a =>
  if h : configurationWeight a=d then φ ⟨a,h⟩ else 0

def WeightIsBosonic {Q N d : ℕ} (φ : WeightState Q N d) : Prop :=
  IsBosonic (weightInclude d φ)

theorem weightRestrict_include {Q N d : ℕ} (φ : WeightState Q N d) :
    weightRestrict d (weightInclude d φ) = φ := by
  funext a
  simp [weightRestrict, weightInclude, a.property]

theorem weightInclude_restrict {Q N : ℕ} (d : ℕ) (ψ : State Q N) :
    weightInclude d (weightRestrict d ψ) = weightProjection d ψ := by
  funext a
  simp only [weightInclude, weightRestrict, weightProjection]
  split_ifs <;> rfl

theorem weightInclude_supported {Q N d : ℕ} (φ : WeightState Q N d) :
    WeightSupported d (weightInclude d φ) := by
  intro a ha
  simp [weightInclude, ha]

theorem weightInclude_restrict_supported {Q N : ℕ} (d : ℕ) (ψ : State Q N)
    (hψ : WeightSupported d ψ) : weightInclude d (weightRestrict d ψ) = ψ := by
  rw [weightInclude_restrict, weightProjection_eq_self d ψ hψ]

theorem weightRestrict_projection {Q N : ℕ} (d : ℕ) (ψ : State Q N) :
    weightRestrict d (weightProjection d ψ) = weightRestrict d ψ := by
  funext a
  simp [weightRestrict, weightProjection, a.property]

theorem weightInclude_injective (Q N d : ℕ) :
    Function.Injective (@weightInclude Q N d) := by
  intro φ χ h
  have he := congrArg (weightRestrict d) h
  simpa only [weightRestrict_include] using he

def weightRestrictLinear (Q N d : ℕ) : State Q N →ₗ[ℂ] WeightState Q N d where
  toFun := weightRestrict d
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem weightInclude_add {Q N d : ℕ} (φ χ : WeightState Q N d) :
    weightInclude d (φ+χ) = weightInclude d φ + weightInclude d χ := by
  funext a
  simp only [weightInclude, Pi.add_apply]
  split_ifs <;> simp

theorem weightInclude_smul {Q N d : ℕ} (c : ℂ) (φ : WeightState Q N d) :
    weightInclude d (c • φ) = c • weightInclude d φ := by
  funext a
  simp only [weightInclude, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def weightIncludeLinear (Q N d : ℕ) : WeightState Q N d →ₗ[ℂ] State Q N where
  toFun := weightInclude d
  map_add' := weightInclude_add
  map_smul' := weightInclude_smul

def weightSubspace (Q N d : ℕ) : Submodule ℂ (State Q N) where
  carrier := {ψ | WeightSupported d ψ}
  zero_mem' := by intro a _; rfl
  add_mem' := by intro φ χ hφ hχ a ha; simp [hφ a ha, hχ a ha]
  smul_mem' := by intro c φ hφ a ha; simp [hφ a ha]

def weightCoordinateEquiv (Q N d : ℕ) :
    WeightState Q N d ≃ₗ[ℂ] weightSubspace Q N d where
  toFun φ := ⟨weightInclude d φ, weightInclude_supported φ⟩
  invFun ψ := weightRestrict d ψ.val
  left_inv := weightRestrict_include
  right_inv ψ := by
    apply Subtype.ext
    exact weightInclude_restrict_supported d ψ.val ψ.property
  map_add' φ χ := by
    apply Subtype.ext
    exact weightInclude_add φ χ
  map_smul' c φ := by
    apply Subtype.ext
    exact weightInclude_smul c φ

theorem weightRestrict_isBosonic {Q N : ℕ} (d : ℕ) (ψ : State Q N)
    (hψ : IsBosonic ψ) : WeightIsBosonic (weightRestrict d ψ) := by
  unfold WeightIsBosonic
  rw [weightInclude_restrict]
  exact weightProjection_isBosonic d ψ hψ

def weightHamiltonian (Q N d : ℕ) : WeightState Q N d →ₗ[ℂ] WeightState Q N d :=
  (weightRestrictLinear Q N d).comp
    ((hamiltonianLinear Q N).comp (weightIncludeLinear Q N d))

theorem weightHamiltonian_apply (Q N d : ℕ) (φ : WeightState Q N d) :
    weightHamiltonian Q N d φ = weightRestrict d (hamiltonian (weightInclude d φ)) := rfl

/-- Actual zero extension intertwines the block operator with the original Hamiltonian. -/
theorem weightHamiltonian_include (Q N d : ℕ) (φ : WeightState Q N d) :
    weightInclude d (weightHamiltonian Q N d φ) = hamiltonian (weightInclude d φ) := by
  rw [weightHamiltonian_apply, weightInclude_restrict_supported]
  exact hamiltonian_weightSupported d _ (weightInclude_supported φ)

/-- Restriction intertwines on every ambient vector, since the sectors do not mix. -/
theorem weightHamiltonian_restrict (Q N d : ℕ) (ψ : State Q N) :
    weightHamiltonian Q N d (weightRestrict d ψ) = weightRestrict d (hamiltonian ψ) := by
  rw [weightHamiltonian_apply, weightInclude_restrict, hamiltonian_weightProjection,
    weightRestrict_projection]

theorem weightHamiltonian_isBosonic (Q N d : ℕ) (φ : WeightState Q N d)
    (hφ : WeightIsBosonic φ) : WeightIsBosonic (weightHamiltonian Q N d φ) := by
  unfold WeightIsBosonic
  rw [weightHamiltonian_include]
  exact hamiltonian_isBosonic _ hφ

end
end BosonicLaughlin

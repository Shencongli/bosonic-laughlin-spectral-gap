import BosonicLaughlin.WeightCoordinates
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-!
The ordered-coordinate weight block has its inherited orthonormal coordinate
inner product. Zero extension preserves it exactly. The block Hamiltonian
matrix represents the actual restricted Hamiltonian; Bose symmetry is imposed
by a separate orthogonal projection within this block.
-/
namespace BosonicLaughlin
noncomputable section
open Finset
open scoped Matrix
open scoped ComplexOrder

def weightInner {Q N d : ℕ} (φ χ : WeightState Q N d) : ℂ :=
  ∑ a : WeightConfiguration Q N d, star (φ a) * χ a

theorem weightInclude_inner {Q N d : ℕ} (φ χ : WeightState Q N d) :
    inner (weightInclude d φ) (weightInclude d χ) = weightInner φ χ := by
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun a : Configuration Q N => configurationWeight a=d)
    (fun a => star (weightInclude d φ a) * weightInclude d χ a)
  have hp : (∑ a : WeightConfiguration Q N d,
      star (weightInclude d φ a.val) * weightInclude d χ a.val) = weightInner φ χ := by
    apply Finset.sum_congr rfl
    intro a _
    simp [weightInclude, a.property]
  have hn : (∑ a : {a : Configuration Q N // ¬ configurationWeight a=d},
      star (weightInclude d φ a.val) * weightInclude d χ a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    simp [weightInclude, a.property]
  rw [hp, hn, add_zero] at h
  exact h.symm

theorem weightHamiltonian_hermitian {Q N d : ℕ} (φ χ : WeightState Q N d) :
    weightInner φ (weightHamiltonian Q N d χ) =
      weightInner (weightHamiltonian Q N d φ) χ := by
  rw [← weightInclude_inner, ← weightInclude_inner,
    weightHamiltonian_include, weightHamiltonian_include]
  exact hamiltonian_hermitian _ _

theorem weightHamiltonian_nonneg {Q N d : ℕ} (φ : WeightState Q N d) :
    0 ≤ (weightInner φ (weightHamiltonian Q N d φ)).re := by
  rw [← weightInclude_inner, weightHamiltonian_include]
  exact energy_nonneg _

def weightBosonicProjection (Q N d : ℕ) : WeightState Q N d →ₗ[ℂ] WeightState Q N d :=
  (weightRestrictLinear Q N d).comp
    ((bosonicProjectionLinear Q N).comp (weightIncludeLinear Q N d))

theorem weightBosonicProjection_include {Q N d : ℕ} (φ : WeightState Q N d) :
    weightInclude d (weightBosonicProjection Q N d φ) =
      bosonicProjection (weightInclude d φ) := by
  change weightInclude d (weightRestrict d (bosonicProjection (weightInclude d φ))) = _
  rw [weightInclude_restrict, weightProjection_bosonicProjection,
    weightProjection_eq_self d _ (weightInclude_supported φ)]

theorem weightBosonicProjection_isBosonic {Q N d : ℕ} (φ : WeightState Q N d) :
    WeightIsBosonic (weightBosonicProjection Q N d φ) := by
  unfold WeightIsBosonic
  rw [weightBosonicProjection_include]
  exact bosonicProjection_isBosonic _

theorem weightBosonicProjection_eq_self {Q N d : ℕ} (φ : WeightState Q N d)
    (hφ : WeightIsBosonic φ) : weightBosonicProjection Q N d φ = φ := by
  apply weightInclude_injective Q N d
  rw [weightBosonicProjection_include]
  exact bosonicProjection_eq_self _ hφ

theorem weightBosonicProjection_fixed_iff {Q N d : ℕ} (φ : WeightState Q N d) :
    weightBosonicProjection Q N d φ = φ ↔ WeightIsBosonic φ := by
  constructor
  · intro h
    rw [← h]
    exact weightBosonicProjection_isBosonic φ
  · exact weightBosonicProjection_eq_self φ

theorem weightBosonicProjection_idempotent {Q N d : ℕ} (φ : WeightState Q N d) :
    weightBosonicProjection Q N d (weightBosonicProjection Q N d φ) =
      weightBosonicProjection Q N d φ :=
  weightBosonicProjection_eq_self _ (weightBosonicProjection_isBosonic φ)

theorem weightBosonicProjection_hermitian {Q N d : ℕ} (φ χ : WeightState Q N d) :
    weightInner φ (weightBosonicProjection Q N d χ) =
      weightInner (weightBosonicProjection Q N d φ) χ := by
  rw [← weightInclude_inner, ← weightInclude_inner,
    weightBosonicProjection_include, weightBosonicProjection_include]
  exact bosonicProjection_hermitian _ _

/-- Matrix in the standard delta basis of ordered weight configurations. -/
def weightHamiltonianMatrix (Q N d : ℕ) :
    Matrix (WeightConfiguration Q N d) (WeightConfiguration Q N d) ℂ :=
  LinearMap.toMatrix' (weightHamiltonian Q N d)

theorem weightHamiltonianMatrix_mulVec {Q N d : ℕ} (φ : WeightState Q N d) :
    weightHamiltonianMatrix Q N d *ᵥ φ = weightHamiltonian Q N d φ :=
  LinearMap.toMatrix'_mulVec _ _

theorem weightInner_single_left {Q N d : ℕ} (a : WeightConfiguration Q N d)
    (φ : WeightState Q N d) : weightInner (Pi.single a 1) φ = φ a := by
  simp [weightInner, Pi.single_apply]

theorem weightInner_single_right {Q N d : ℕ} (a : WeightConfiguration Q N d)
    (φ : WeightState Q N d) : weightInner φ (Pi.single a 1) = star (φ a) := by
  simp [weightInner, Pi.single_apply]

theorem weightHamiltonianMatrix_hermitian (Q N d : ℕ) :
    (weightHamiltonianMatrix Q N d).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  have h := weightHamiltonian_hermitian (Pi.single a 1) (Pi.single b 1)
  rw [weightInner_single_left, weightInner_single_right] at h
  exact h.symm

theorem weightHamiltonianMatrix_nonneg {Q N d : ℕ} (φ : WeightState Q N d) :
    0 ≤ (∑ a, star (φ a) * (weightHamiltonianMatrix Q N d *ᵥ φ) a).re := by
  rw [weightHamiltonianMatrix_mulVec]
  exact weightHamiltonian_nonneg φ

theorem weightHamiltonianMatrix_posSemidef (Q N d : ℕ) :
    (weightHamiltonianMatrix Q N d).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (weightHamiltonianMatrix_hermitian Q N d)
  intro φ
  apply Complex.nonneg_iff.mpr
  constructor
  · exact weightHamiltonianMatrix_nonneg φ
  · have h := congrArg Complex.im
      ((weightHamiltonianMatrix_hermitian Q N d).star_dotProduct_mulVec_comm φ φ)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith

end
end BosonicLaughlin

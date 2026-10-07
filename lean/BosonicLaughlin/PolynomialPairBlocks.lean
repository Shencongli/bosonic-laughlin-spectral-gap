import BosonicLaughlin.PolynomialMetric
import BosonicLaughlin.WeightCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Finite ordered-tensor weight matrices of the unweighted polynomial pair channels.
These coordinates retain the orbital cap and do not quotient by Bose symmetry or
restrict to highest-weight vectors. The symmetry condition is stated separately.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem configurationWeight_cons {Q N : ℕ} (x : Orbital Q) (a : Configuration Q N) :
    configurationWeight (Fin.cons x a) = x.val + configurationWeight a := by
  simp only [configurationWeight, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem polynomialPairChannel_weightSupported {Q N : ℕ} (d p : ℕ)
    (χ : State Q (N+2)) (hχ : WeightSupported d χ) :
    WeightSupported (d-p) (polynomialPairChannel p χ) := by
  intro a ha
  unfold polynomialPairChannel
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with hxy
  · apply hχ
    simp only [configurationWeight_cons]
    omega
  · rfl

theorem polynomialPairChannel_above_weight {Q N : ℕ} (d p : ℕ) (hp : d < p)
    (χ : State Q (N+2)) (hχ : WeightSupported d χ) :
    polynomialPairChannel p χ = 0 := by
  funext a
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with hxy
  · apply hχ
    simp only [configurationWeight_cons]
    omega
  · rfl

/-- The exact channel from total deficit d to spectator deficit d-p. -/
def polynomialPairBlock (Q N d p : ℕ) :
    WeightState Q (N+2) d →ₗ[ℂ] WeightState Q N (d-p) :=
  (weightRestrictLinear Q N (d-p)).comp
    ((polynomialPairChannelLinear Q N p).comp (weightIncludeLinear Q (N+2) d))

theorem polynomialPairBlock_apply (Q N d p : ℕ) (χ : WeightState Q (N+2) d) :
    polynomialPairBlock Q N d p χ =
      weightRestrict (d-p) (polynomialPairChannel p (weightInclude d χ)) := rfl

theorem polynomialPairBlock_include (Q N d p : ℕ) (χ : WeightState Q (N+2) d) :
    weightInclude (d-p) (polynomialPairBlock Q N d p χ) =
      polynomialPairChannel p (weightInclude d χ) := by
  rw [polynomialPairBlock_apply, weightInclude_restrict_supported]
  exact polynomialPairChannel_weightSupported d p _ (weightInclude_supported χ)

theorem polynomialPairBlock_above_weight (Q N d p : ℕ) (hp : d < p) :
    polynomialPairBlock Q N d p = 0 := by
  apply LinearMap.ext
  intro χ
  rw [polynomialPairBlock_apply,
    polynomialPairChannel_above_weight d p hp _ (weightInclude_supported χ)]
  rfl

theorem polynomialPairBlock_zero_iff (Q N d p : ℕ) (χ : WeightState Q (N+2) d) :
    polynomialPairBlock Q N d p χ = 0 ↔
      polynomialPairChannel p (weightInclude d χ) = 0 := by
  constructor
  · intro h
    rw [← polynomialPairBlock_include, h]
    exact (weightIncludeLinear Q N (d-p)).map_zero
  · intro h
    rw [polynomialPairBlock_apply, h]
    rfl

def polynomialPairMatrix (Q N d p : ℕ) :
    Matrix (WeightConfiguration Q N (d-p)) (WeightConfiguration Q (N+2) d) ℂ :=
  LinearMap.toMatrix' (polynomialPairBlock Q N d p)

theorem polynomialPairMatrix_mulVec (Q N d p : ℕ) (χ : WeightState Q (N+2) d) :
    (polynomialPairMatrix Q N d p).mulVec χ = polynomialPairBlock Q N d p χ :=
  LinearMap.toMatrix'_mulVec _ _

theorem polynomialPairMatrix_zero_iff (Q N d p : ℕ) (χ : WeightState Q (N+2) d) :
    (polynomialPairMatrix Q N d p).mulVec χ = 0 ↔
      polynomialPairChannel p (weightInclude d χ) = 0 := by
  rw [polynomialPairMatrix_mulVec, polynomialPairBlock_zero_iff]

/-- The finite tensor-weight channel matrices detect the actual transformed
Hamiltonian kernel once Bose symmetry is imposed. -/
theorem polynomialHamiltonian_weight_kernel {Q N d : ℕ}
    (χ : WeightState Q (N+2) d) (hχ : WeightIsBosonic χ) :
    polynomialHamiltonian Q (N+2) (weightInclude d χ) = 0 ↔
      ∀ p : Fin (2*Q+1), polynomialPairBlock Q N d p.val χ = 0 := by
  rw [polynomialHamiltonian_kernel _ hχ]
  exact forall_congr' (fun p => (polynomialPairBlock_zero_iff Q N d p.val χ).symm)

theorem polynomialHamiltonian_weight_matrix_kernel {Q N d : ℕ}
    (χ : WeightState Q (N+2) d) (hχ : WeightIsBosonic χ) :
    polynomialHamiltonian Q (N+2) (weightInclude d χ) = 0 ↔
      ∀ p : Fin (2*Q+1), (polynomialPairMatrix Q N d p.val).mulVec χ = 0 := by
  rw [polynomialHamiltonian_weight_kernel χ hχ]
  simp only [polynomialPairMatrix_mulVec]

end
end BosonicLaughlin

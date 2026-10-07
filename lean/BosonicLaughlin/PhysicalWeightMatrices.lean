import BosonicLaughlin.PolynomialWeightCoordinates
import BosonicLaughlin.PolynomialPairBlocks
import BosonicLaughlin.WeightBlockForms

/-!
The actual physical V0 weight-block kernel in finite polynomial pair matrices.
The vector on the left is in physical orthonormal ordered-tensor coordinates;
the pair matrices act on its explicitly rescaled polynomial coordinates.
Bose symmetry remains a separate condition, with no occupation or highest-weight
basis identification assumed.
-/
namespace BosonicLaughlin
noncomputable section

theorem weightHamiltonian_zero_iff_polynomialPairBlocks {Q N d : ℕ}
    (φ : WeightState Q (N+2) d) (hφ : WeightIsBosonic φ) :
    weightHamiltonian Q (N+2) d φ = 0 ↔ ∀ p : Fin (2*Q+1),
      polynomialPairBlock Q N d p.val (polynomialWeightCoordinates Q (N+2) d φ) = 0 := by
  rw [weightHamiltonian_zero_iff_polynomialChannels φ hφ]
  exact forall_congr' (fun p =>
    (polynomialPairBlock_zero_iff Q N d p.val (polynomialWeightCoordinates Q (N+2) d φ)).symm)

theorem weightHamiltonian_zero_iff_polynomialPairMatrices {Q N d : ℕ}
    (φ : WeightState Q (N+2) d) (hφ : WeightIsBosonic φ) :
    weightHamiltonian Q (N+2) d φ = 0 ↔ ∀ p : Fin (2*Q+1),
      (polynomialPairMatrix Q N d p.val).mulVec
        (polynomialWeightCoordinates Q (N+2) d φ) = 0 := by
  rw [weightHamiltonian_zero_iff_polynomialPairBlocks φ hφ]
  simp only [polynomialPairMatrix_mulVec]

/-- Equality of the actual physical matrix kernel and the pulled-back common
polynomial pair-matrix kernel, on the bosonic part of the weight sector. -/
theorem weightHamiltonianMatrix_zero_iff_polynomialPairMatrices {Q N d : ℕ}
    (φ : WeightState Q (N+2) d) (hφ : WeightIsBosonic φ) :
    (weightHamiltonianMatrix Q (N+2) d).mulVec φ = 0 ↔ ∀ p : Fin (2*Q+1),
      (polynomialPairMatrix Q N d p.val).mulVec
        (polynomialWeightCoordinates Q (N+2) d φ) = 0 := by
  rw [weightHamiltonianMatrix_mulVec]
  exact weightHamiltonian_zero_iff_polynomialPairMatrices φ hφ

theorem hamiltonian_weight_zero_iff_polynomialPairMatrices {Q N d : ℕ}
    (φ : WeightState Q (N+2) d) (hφ : WeightIsBosonic φ) :
    hamiltonian (weightInclude d φ) = 0 ↔ ∀ p : Fin (2*Q+1),
      (polynomialPairMatrix Q N d p.val).mulVec
        (polynomialWeightCoordinates Q (N+2) d φ) = 0 := by
  rw [← weightHamiltonian_zero_iff_include]
  exact weightHamiltonian_zero_iff_polynomialPairMatrices φ hφ

end
end BosonicLaughlin

import BosonicLaughlin.OccupationWeightCoordinates
import BosonicLaughlin.OccupationPairChannels
import BosonicLaughlin.PolynomialOccupationCoordinates
import BosonicLaughlin.PolynomialPairBlocks

/-!
Fixed-deficit occupation matrices for the actual polynomial pair channels.
Their entries are the integer sequential-removal multiplicities. The orbital
cap is retained; no assertion about a chosen script enumeration is built in.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem occupationPairChannel_weightSupported {Q N : ℕ} (d p : ℕ)
    (c : OccupationState Q (N+2)) (hc : OccupationWeightSupported d c) :
    OccupationWeightSupported (d-p) (occupationPairChannel p c) := by
  intro B hB
  unfold occupationPairChannel
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with hxy
  · have hs : occupationWeight (Sym.cons x (Sym.cons y B)) ≠ d := by
      simp only [occupationWeight_cons]
      omega
    simp [occupationAnnihilate, hc _ hs]
  · rfl

theorem occupationPairChannel_above_weight {Q N : ℕ} (d p : ℕ) (hp : d<p)
    (c : OccupationState Q (N+2)) (hc : OccupationWeightSupported d c) :
    occupationPairChannel p c = 0 := by
  funext B
  unfold occupationPairChannel
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with hxy
  · have hs : occupationWeight (Sym.cons x (Sym.cons y B)) ≠ d := by
      simp only [occupationWeight_cons]
      omega
    simp [occupationAnnihilate, hc _ hs]
  · rfl

def occupationPairBlock (Q N d p : ℕ) :
    WeightOccupationState Q (N+2) d →ₗ[ℂ] WeightOccupationState Q N (d-p) :=
  (occupationWeightRestrictLinear Q N (d-p)).comp
    ((occupationPairChannelLinear Q N p).comp (occupationWeightExtendLinear Q (N+2) d))

theorem occupationPairBlock_apply (Q N d p : ℕ) (c : WeightOccupationState Q (N+2) d) :
    occupationPairBlock Q N d p c =
      occupationWeightRestrict (d-p) (occupationPairChannel p (occupationWeightExtend d c)) := rfl

theorem occupationPairBlock_extend (Q N d p : ℕ) (c : WeightOccupationState Q (N+2) d) :
    occupationWeightExtend (d-p) (occupationPairBlock Q N d p c) =
      occupationPairChannel p (occupationWeightExtend d c) := by
  rw [occupationPairBlock_apply, occupationWeightExtend_restrict_supported]
  exact occupationPairChannel_weightSupported d p _ (occupationWeightExtend_supported c)

theorem occupationPairBlock_zero_iff (Q N d p : ℕ) (c : WeightOccupationState Q (N+2) d) :
    occupationPairBlock Q N d p c = 0 ↔ occupationPairChannel p (occupationWeightExtend d c) = 0 := by
  constructor
  · intro h
    rw [← occupationPairBlock_extend, h]
    funext B
    simp [occupationWeightExtend]
  · intro h
    rw [occupationPairBlock_apply, h]
    rfl

def occupationPairBlockMatrix (Q N d p : ℕ) :
    Matrix (WeightOccupation Q N (d-p)) (WeightOccupation Q (N+2) d) ℂ :=
  LinearMap.toMatrix' (occupationPairBlock Q N d p)

theorem occupationPairBlockMatrix_mulVec (Q N d p : ℕ) (c : WeightOccupationState Q (N+2) d) :
    (occupationPairBlockMatrix Q N d p).mulVec c = occupationPairBlock Q N d p c :=
  LinearMap.toMatrix'_mulVec _ _

theorem occupationWeightExtend_single {Q N d : ℕ} (A : WeightOccupation Q N d) :
    occupationWeightExtend d (Pi.single A (1 : ℂ)) = Pi.single A.val 1 := by
  funext B
  by_cases h : B=A.val
  · subst B
    simp [occupationWeightExtend, A.property]
  · simp [occupationWeightExtend, Pi.single_apply, Subtype.ext_iff, h, Ne.symm h]

theorem occupationPairBlockMatrix_apply (Q N d p : ℕ)
    (B : WeightOccupation Q N (d-p)) (A : WeightOccupation Q (N+2) d) :
    occupationPairBlockMatrix Q N d p B A =
      ∑ x : Orbital Q, ∑ y : Orbital Q,
        if x.val+y.val=p then
          if Sym.cons x (Sym.cons y B.val) = A.val then
            ((A.val.val.count x * (A.val.val.erase x).count y : ℕ) : ℂ) else 0
        else 0 := by
  rw [occupationPairBlockMatrix, LinearMap.toMatrix'_apply]
  change occupationPairChannel p (occupationWeightExtend d (Pi.single A 1)) B.val = _
  rw [occupationWeightExtend_single]
  exact occupationPairMatrix_apply Q N p B.val A.val

theorem polynomialWeightOccupationInclude_pairBlock (Q N d p : ℕ)
    (c : WeightOccupationState Q (N+2) d) :
    polynomialPairBlock Q N d p (polynomialWeightOccupationInclude c) =
      polynomialWeightOccupationInclude (occupationPairBlock Q N d p c) := by
  apply weightInclude_injective Q N (d-p)
  rw [polynomialPairBlock_include, polynomialWeightOccupationInclude_include,
    polynomialOccupationInclude_pairChannel, polynomialWeightOccupationInclude_include,
    occupationPairBlock_extend]

theorem polynomialWeightOccupationInclude_pairMatrix (Q N d p : ℕ)
    (c : WeightOccupationState Q (N+2) d) :
    (polynomialPairMatrix Q N d p).mulVec (polynomialWeightOccupationInclude c) =
      polynomialWeightOccupationInclude ((occupationPairBlockMatrix Q N d p).mulVec c) := by
  rw [polynomialPairMatrix_mulVec, occupationPairBlockMatrix_mulVec,
    polynomialWeightOccupationInclude_pairBlock]

theorem polynomialHamiltonian_occupation_kernel {Q N : ℕ}
    (c : OccupationState Q (N+2)) :
    polynomialHamiltonian Q (N+2) (polynomialOccupationInclude c) = 0 ↔
      ∀ p : Fin (2*Q+1), (occupationPairMatrix Q N p.val).mulVec c = 0 := by
  rw [polynomialHamiltonian_kernel _ (polynomialOccupationInclude_isBosonic c)]
  simp only [occupationPairMatrix_mulVec]
  exact forall_congr' (fun p => polynomialOccupationInclude_pairChannel_zero_iff p.val c)

theorem polynomialHamiltonian_weightOccupation_kernel {Q N d : ℕ}
    (c : WeightOccupationState Q (N+2) d) :
    polynomialHamiltonian Q (N+2) (weightInclude d (polynomialWeightOccupationInclude c)) = 0 ↔
      ∀ p : Fin (2*Q+1), (occupationPairBlockMatrix Q N d p.val).mulVec c = 0 := by
  rw [polynomialWeightOccupationInclude_include,
    polynomialHamiltonian_occupation_kernel]
  simp only [occupationPairMatrix_mulVec, occupationPairBlockMatrix_mulVec]
  exact forall_congr' (fun p => (occupationPairBlock_zero_iff Q N d p.val c).symm)

end
end BosonicLaughlin

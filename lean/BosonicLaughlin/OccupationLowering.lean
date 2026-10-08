import BosonicLaughlin.PolynomialLowering
import BosonicLaughlin.CertificateHighestWeight

/-! Actual occupation lowering, with source multiplicities. The rescaled
block R=Q^{-1}L is the verifier's j -> j+1 rule with coefficient 1-j/Q. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def occupationLower {Q N : ℕ} (c : OccupationState Q N) : OccupationState Q N := fun B =>
  ∑ i : Orbital Q, if hi : 0 < i.val then if hm : i ∈ B.val then
    let j : Orbital Q := ⟨i.val-1, by omega⟩
    let A := occupationReplace B i j hm
    (((Q-j.val)*A.val.count j : ℕ) : ℂ)*c A
  else 0 else 0

theorem occupationLower_add {Q N : ℕ} (c e : OccupationState Q N) :
    occupationLower (c+e)=occupationLower c+occupationLower e := by
  funext B
  simp only [occupationLower, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [mul_add]

theorem occupationLower_smul {Q N : ℕ} (z : ℂ) (c : OccupationState Q N) :
    occupationLower (z • c)=z • occupationLower c := by
  funext B
  simp only [occupationLower, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

def occupationLowerLinear (Q N : ℕ) : OccupationState Q N →ₗ[ℂ] OccupationState Q N where
  toFun := occupationLower
  map_add' := occupationLower_add
  map_smul' := occupationLower_smul

theorem polynomialOccupationInclude_lower {Q N : ℕ} (c : OccupationState Q N) :
    polynomialLower (polynomialOccupationInclude c)=polynomialOccupationInclude (occupationLower c) := by
  funext a
  let B := occupationOfConfiguration a
  let f : Orbital Q → ℂ := fun i => if hi : 0 < i.val then if hm : i ∈ B.val then
    let j : Orbital Q := ⟨i.val-1, by omega⟩
    let A := occupationReplace B i j hm
    ((Q-j.val : ℕ) : ℂ)*(occupationFactorial A : ℂ)*c A else 0 else 0
  have hs : polynomialLower (polynomialOccupationInclude c) a=∑ k : Fin N, f (a k) := by
    apply Finset.sum_congr rfl
    intro k _
    have hm : a k ∈ B.val := occupationOfConfiguration_mem a k
    simp only [polynomialOccupationInclude, occupationOfConfiguration_update, f, hm, dite_true]
    split_ifs <;> ring
  rw [hs, sum_slots_occupation_count]
  change (∑ i : Orbital Q, (B.val.count i : ℂ)*f i)=(occupationFactorial B : ℂ)*occupationLower c B
  simp only [occupationLower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [f]
  split_ifs with hi hm
  · have he := occupationReplace_factorial B i (⟨i.val-1, by omega⟩ : Orbital Q) hm
    have hc : (B.val.count i : ℂ)*
        (occupationFactorial (occupationReplace B i ⟨i.val-1, by omega⟩ hm) : ℂ)=
      ((occupationReplace B i ⟨i.val-1, by omega⟩ hm).val.count ⟨i.val-1, by omega⟩ : ℂ)*
        (occupationFactorial B : ℂ) := by exact_mod_cast he
    simp only [Nat.cast_mul]
    linear_combination (((Q-(i.val-1) : ℕ) : ℂ)*c (occupationReplace B i ⟨i.val-1, by omega⟩ hm))*hc
  · simp
  · simp

theorem occupationLower_weightSupported {Q N : ℕ} (d : ℕ) (c : OccupationState Q N)
    (hc : OccupationWeightSupported d c) : OccupationWeightSupported (d+1) (occupationLower c) := by
  intro B hB
  unfold occupationLower
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi hm
  · have hw := occupationWeight_replace B i (⟨i.val-1, by omega⟩ : Orbital Q) hm
    have hz : occupationWeight (occupationReplace B i ⟨i.val-1, by omega⟩ hm)≠d := by
      change _+i.val=_+(i.val-1) at hw
      omega
    simp only [hc _ hz, mul_zero]
  · rfl
  · rfl

def occupationLowerBlock (Q N d : ℕ) :
    WeightOccupationState Q N d →ₗ[ℂ] WeightOccupationState Q N (d+1) :=
  (occupationWeightRestrictLinear Q N (d+1)).comp
    ((occupationLowerLinear Q N).comp (occupationWeightExtendLinear Q N d))

theorem occupationLowerBlock_extend {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    occupationWeightExtend (d+1) (occupationLowerBlock Q N d c)=occupationLower (occupationWeightExtend d c) := by
  change occupationWeightExtend (d+1) (occupationWeightRestrict (d+1) (occupationLower (occupationWeightExtend d c)))=_
  rw [occupationWeightExtend_restrict_supported]
  exact occupationLower_weightSupported d _ (occupationWeightExtend_supported c)

def verifierRaiseBlock (Q N d : ℕ) :
    WeightOccupationState Q N d →ₗ[ℂ] WeightOccupationState Q N (d+1) :=
  (Q : ℂ)⁻¹ • occupationLowerBlock Q N d

def verifierRaiseMatrix (Q N d : ℕ) :
    Matrix (WeightOccupation Q N (d+1)) (WeightOccupation Q N d) ℂ :=
  LinearMap.toMatrix' (verifierRaiseBlock Q N d)

theorem verifierRaiseMatrix_mulVec {Q N d : ℕ} (c : WeightOccupationState Q N d) :
    (verifierRaiseMatrix Q N d).mulVec c=verifierRaiseBlock Q N d c := LinearMap.toMatrix'_mulVec _ _

theorem verifierRaiseMatrix_apply (Q N d : ℕ)
    (B : WeightOccupation Q N (d+1)) (A : WeightOccupation Q N d) :
    verifierRaiseMatrix Q N d B A=(Q : ℂ)⁻¹ * ∑ i : Orbital Q,
      if hi : 0 < i.val then if hm : i ∈ B.val.val then
        let j : Orbital Q := ⟨i.val-1, by omega⟩
        if occupationReplace B.val i j hm=A.val then (((Q-j.val)*A.val.val.count j : ℕ) : ℂ) else 0
      else 0 else 0 := by
  rw [verifierRaiseMatrix, LinearMap.toMatrix'_apply]
  change (Q : ℂ)⁻¹ * occupationLower (occupationWeightExtend d (Pi.single A 1)) B.val=_
  rw [occupationWeightExtend_single]
  congr 1
  unfold occupationLower
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi hm
  · dsimp only
    by_cases he : occupationReplace B.val i ⟨i.val-1, by omega⟩ hm=A.val
    · rw [he]; simp
    · simp [he]
  · rfl
  · rfl

theorem tensorLower_certificateCoordinates (Q N d : ℕ) (c : OccupationState Q N) :
    tensorLower (certificateCoordinates Q N d c)=certificateCoordinates Q N d (occupationLower c) := by
  apply (polynomialCoordinates Q N).injective
  rw [polynomialCoordinates_tensorLower, certificateCoordinates_polynomial,
    polynomialLower_smul, polynomialOccupationInclude_lower, certificateCoordinates_polynomial]

theorem tensorLower_certificateWeightCoordinates {Q N d : ℕ} (hQ : 0<Q)
    (c : WeightOccupationState Q N d) :
    tensorLower (certificateWeightCoordinates Q N d c)=
      (Real.sqrt Q : ℂ) • certificateWeightCoordinates Q N (d+1) (verifierRaiseBlock Q N d c) := by
  have hq : (Q : ℂ)≠0 := by exact_mod_cast hQ.ne'
  have hs : (Real.sqrt Q : ℂ)*(Real.sqrt Q : ℂ)=(Q : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg Q : (0 : ℝ)≤Q)
  rw [certificateWeightCoordinates_apply, tensorLower_certificateCoordinates,
    ← occupationLowerBlock_extend,
    verifierRaiseBlock, LinearMap.smul_apply, map_smul]
  rw [certificateWeightCoordinates_apply, certificateCoordinates_apply,
    certificateCoordinates_apply,
    certificateSectorScale_succ, Complex.ofReal_mul]
  simp only [smul_smul]
  congr 1
  calc
    (certificateSectorScale Q N d : ℂ) =
        (Q : ℂ)*(Q : ℂ)⁻¹*(certificateSectorScale Q N d : ℂ) := by rw [mul_inv_cancel₀ hq, one_mul]
    _ = _ := by rw [← hs]; ring

end
end BosonicLaughlin

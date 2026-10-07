import BosonicLaughlin.CertificateGram

/-! Exact physical pair annihilation in normalized occupation coordinates.
The coefficient is independent of particle number and input degree. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def certificatePairCoefficient (Q p : ℕ) : ℝ :=
  Real.sqrt (planarPairFactor p / sphereFactor (2*Q) p)

theorem certificatePairCoefficient_sq {Q p : ℕ} (hQ : 0<Q) (hp : p≤2*Q) :
    certificatePairCoefficient Q p ^ 2=planarPairFactor p / sphereFactor (2*Q) p := by
  apply Real.sq_sqrt
  exact div_nonneg (by unfold planarPairFactor; positivity) (sphereFactor_pos (by omega) hp).le

theorem certificatePairCoefficient_pos {Q p : ℕ} (hQ : 0<Q) (hp : p≤2*Q) :
    0<certificatePairCoefficient Q p := by
  apply Real.sqrt_pos.mpr
  exact div_pos (by unfold planarPairFactor; positivity) (sphereFactor_pos (by omega) hp)

theorem certificate_pair_scale {Q N d p : ℕ} (hQ : 0<Q) (hp : p≤d) (hpQ : p≤2*Q) :
    certificateSectorScale Q (N+2) d *
      (Real.sqrt ((N+2).choose 2) / binomialRoot (2*Q) p) =
        certificatePairCoefficient Q p * certificateSectorScale Q N (d-p) := by
  have hsq : (certificateSectorScale Q (N+2) d *
      (Real.sqrt ((N+2).choose 2) / binomialRoot (2*Q) p))^2 =
        (certificatePairCoefficient Q p * certificateSectorScale Q N (d-p))^2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), binomialRoot_sq,
      mul_pow, certificatePairCoefficient_sq hQ hpQ]
    exact certificate_pair_gram_factor hQ hp hpQ
  have hl : 0 ≤ certificateSectorScale Q (N+2) d *
      (Real.sqrt ((N+2).choose 2) / binomialRoot (2*Q) p) :=
    mul_nonneg (certificateSectorScale_pos hQ _ _).le
      (div_nonneg (Real.sqrt_nonneg _) (binomialRoot_pos _ _ hpQ).le)
  have hr : 0 ≤ certificatePairCoefficient Q p * certificateSectorScale Q N (d-p) :=
    mul_nonneg (certificatePairCoefficient_pos hQ hpQ).le (certificateSectorScale_pos hQ _ _).le
  nlinarith

theorem v0PairAnnihilate_certificateWeightCoordinates {Q N d : ℕ} (hQ : 0<Q)
    (p : Fin (2*Q+1)) (c : WeightOccupationState Q (N+2) d) :
    v0PairAnnihilate p (certificateWeightCoordinates Q (N+2) d c) =
      (certificatePairCoefficient Q p.val : ℂ) •
        certificateWeightCoordinates Q N (d-p.val) (occupationPairBlock Q N d p.val c) := by
  rw [certificateWeightCoordinates_apply, certificateCoordinates_apply,
    show v0PairAnnihilate p ((certificateSectorScale Q (N+2) d : ℂ) •
      (polynomialCoordinates Q (N+2)).symm (polynomialOccupationInclude (occupationWeightExtend d c))) =
      (certificateSectorScale Q (N+2) d : ℂ) • v0PairAnnihilate p
        ((polynomialCoordinates Q (N+2)).symm (polynomialOccupationInclude (occupationWeightExtend d c)))
      from (v0PairAnnihilateLinear Q N p).map_smul _ _,
    v0PairAnnihilate_polynomial_inverse, polynomialOccupationInclude_pairChannel,
    ← occupationPairBlock_extend, certificateWeightCoordinates_apply,
    certificateCoordinates_apply, smul_smul, smul_smul]
  by_cases hp : p.val≤d
  · rw [← Complex.ofReal_mul, certificate_pair_scale hQ hp (by omega), Complex.ofReal_mul]
  · have hz : occupationPairBlock Q N d p.val c=0 := by
      apply (occupationPairBlock_zero_iff Q N d p.val c).mpr
      exact occupationPairChannel_above_weight d p.val (by omega) _ (occupationWeightExtend_supported c)
    rw [hz, show occupationWeightExtend (d-p.val) (0 : WeightOccupationState Q N (d-p.val))=0
      from (occupationWeightExtendLinear Q N (d-p.val)).map_zero,
      show polynomialOccupationInclude (0 : OccupationState Q N)=0
      from (polynomialOccupationIncludeLinear Q N).map_zero, map_zero, smul_zero, smul_zero]

theorem v0PairAnnihilate_twice_certificateWeightCoordinates {Q N d : ℕ} (hQ : 0<Q)
    (p q : Fin (2*Q+1)) (c : WeightOccupationState Q (N+4) d) :
    v0PairAnnihilate q (v0PairAnnihilate p (certificateWeightCoordinates Q (N+4) d c)) =
      ((certificatePairCoefficient Q q.val * certificatePairCoefficient Q p.val : ℝ) : ℂ) •
        certificateWeightCoordinates Q N (d-p.val-q.val)
          (occupationPairBlock Q N (d-p.val) q.val (occupationPairBlock Q (N+2) d p.val c)) := by
  rw [v0PairAnnihilate_certificateWeightCoordinates hQ p]
  change (v0PairAnnihilateLinear Q N q) (_ • _)=_
  rw [map_smul]
  change _ • v0PairAnnihilate q _=_
  rw [v0PairAnnihilate_certificateWeightCoordinates hQ q, smul_smul, Complex.ofReal_mul, mul_comm]

end
end BosonicLaughlin

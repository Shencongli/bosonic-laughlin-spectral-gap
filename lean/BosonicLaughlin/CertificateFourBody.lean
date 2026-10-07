import BosonicLaughlin.CertificatePairIntertwiner
import BosonicLaughlin.NonorthogonalHamiltonian

/-! The exact double-pair Gram matrix of the physical four-body target.
All output degree sectors and finite orbital caps are retained. -/
namespace BosonicLaughlin
noncomputable section
open Finset
open scoped Matrix ComplexOrder

theorem certificateInner_matrix {Q N d : ℕ} (c e : WeightOccupationState Q N d) :
    star c ⬝ᵥ (certificateMetricMatrix Q N d *ᵥ e)=certificateInner c e := by
  simp only [certificateMetricMatrix, Matrix.mulVec_diagonal, dotProduct, certificateInner, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro A _
  ring

def certificateDoublePairMatrix (Q N d p q : ℕ) :
    Matrix (WeightOccupation Q N (d-p-q)) (WeightOccupation Q (N+4) d) ℂ :=
  occupationPairBlockMatrix Q N (d-p) q * occupationPairBlockMatrix Q (N+2) d p

theorem certificateDoublePairMatrix_mulVec (Q N d p q : ℕ)
    (c : WeightOccupationState Q (N+4) d) :
    certificateDoublePairMatrix Q N d p q *ᵥ c=
      occupationPairBlock Q N (d-p) q (occupationPairBlock Q (N+2) d p c) := by
  rw [certificateDoublePairMatrix, ← Matrix.mulVec_mulVec,
    occupationPairBlockMatrix_mulVec, occupationPairBlockMatrix_mulVec]

def certificateDoublePairFormMatrix (Q N d p q : ℕ) :
    Matrix (WeightOccupation Q (N+4) d) (WeightOccupation Q (N+4) d) ℂ :=
  (certificateDoublePairMatrix Q N d p q)ᴴ * certificateMetricMatrix Q N (d-p-q) *
    certificateDoublePairMatrix Q N d p q

theorem certificateDoublePairFormMatrix_form (Q N d p q : ℕ)
    (c e : WeightOccupationState Q (N+4) d) :
    star c ⬝ᵥ (certificateDoublePairFormMatrix Q N d p q *ᵥ e)=
      certificateInner
        (occupationPairBlock Q N (d-p) q (occupationPairBlock Q (N+2) d p c))
        (occupationPairBlock Q N (d-p) q (occupationPairBlock Q (N+2) d p e)) := by
  rw [certificateDoublePairFormMatrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, certificateInner_matrix,
    certificateDoublePairMatrix_mulVec, certificateDoublePairMatrix_mulVec]

theorem v0DoublePair_certificate_inner {Q N d : ℕ} (hQ : 0<Q)
    (p q : Fin (2*Q+1)) (c e : WeightOccupationState Q (N+4) d) :
    inner
      (v0PairAnnihilate q (v0PairAnnihilate p (certificateWeightCoordinates Q (N+4) d c)))
      (v0PairAnnihilate q (v0PairAnnihilate p (certificateWeightCoordinates Q (N+4) d e))) =
      ((planarPairFactor p.val / sphereFactor (2*Q) p.val *
        (planarPairFactor q.val / sphereFactor (2*Q) q.val) : ℝ) : ℂ) *
          (star c ⬝ᵥ (certificateDoublePairFormMatrix Q N d p.val q.val *ᵥ e)) := by
  rw [v0PairAnnihilate_twice_certificateWeightCoordinates hQ,
    v0PairAnnihilate_twice_certificateWeightCoordinates hQ, stateInner_real_smul_both,
    mul_pow, certificatePairCoefficient_sq hQ (by omega),
    certificatePairCoefficient_sq hQ (by omega), certificateWeightCoordinates_inner hQ,
    certificateDoublePairFormMatrix_form, mul_comm (planarPairFactor q.val / _)]

def certificateFourBodyFormMatrix (Q N d : ℕ) :
    Matrix (WeightOccupation Q (N+4) d) (WeightOccupation Q (N+4) d) ℂ :=
  ∑ p : Fin (2*Q+1), ∑ q : Fin (2*Q+1),
    ((planarPairFactor p.val / sphereFactor (2*Q) p.val *
      (planarPairFactor q.val / sphereFactor (2*Q) q.val) : ℝ) : ℂ) •
        certificateDoublePairFormMatrix Q N d p.val q.val

theorem certificateFourBodyFormMatrix_gram {Q N d : ℕ} (hQ : 0<Q)
    (c e : WeightOccupationState Q (N+4) d) :
    star c ⬝ᵥ (certificateFourBodyFormMatrix Q N d *ᵥ e)=
      ∑ p : Fin (2*Q+1), ∑ q : Fin (2*Q+1),
        inner
          (v0PairAnnihilate q (v0PairAnnihilate p (certificateWeightCoordinates Q (N+4) d c)))
          (v0PairAnnihilate q (v0PairAnnihilate p (certificateWeightCoordinates Q (N+4) d e))) := by
  simp only [certificateFourBodyFormMatrix, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl
    (fun q _ => (v0DoublePair_certificate_inner hQ p q c e).symm))

theorem certificateFourBody_target_quadratic {Q N d : ℕ} (hQ : 0<Q)
    (c : WeightOccupationState Q (N+4) d) :
    (inner (certificateWeightCoordinates Q (N+4) d c)
      (normalFourBodyApply (certificateWeightCoordinates Q (N+4) d c))).re =
        (star c ⬝ᵥ (certificateFourBodyFormMatrix Q N d *ᵥ c)).re := by
  rw [normalFourBody_eq_sum_v0PairAnnihilate_normSq _
    (certificateWeightCoordinates_isBosonic Q (N+4) d c), certificateFourBodyFormMatrix_gram hQ]
  simp only [Complex.re_sum, normSq]

theorem certificateMetricMatrix_posSemidef {Q N d : ℕ} (hQ : 0<Q) :
    (certificateMetricMatrix Q N d).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro A
  change (0 : ℂ)≤(certificateMetricWeight A.val : ℂ)
  exact_mod_cast (certificateMetricWeight_pos hQ A.val).le

theorem certificateFourBodyFormMatrix_posSemidef {Q N d : ℕ} (hQ : 0<Q) :
    (certificateFourBodyFormMatrix Q N d).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro p _
  apply Matrix.posSemidef_sum
  intro q _
  apply ((certificateMetricMatrix_posSemidef hQ).conjTranspose_mul_mul_same
    (certificateDoublePairMatrix Q N d p.val q.val)).smul
  have hp := (certificatePairCoefficient_sq (p:=p.val) hQ (by omega))
  have hq := (certificatePairCoefficient_sq (p:=q.val) hQ (by omega))
  rw [← hp, ← hq]
  exact_mod_cast mul_nonneg (sq_nonneg (certificatePairCoefficient Q p.val))
    (sq_nonneg (certificatePairCoefficient Q q.val))

end
end BosonicLaughlin

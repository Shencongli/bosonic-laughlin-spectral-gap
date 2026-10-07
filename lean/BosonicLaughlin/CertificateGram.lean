import BosonicLaughlin.CertificateCoordinates
import BosonicLaughlin.OccupationPolynomialMetric
import BosonicLaughlin.PolynomialGram

/-! The certificate metric and Hamiltonian quadratic matrix, derived from the
actual physical coordinate map. Matrix entries use occupation multisets. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def certificateMetricWeight {Q N : ℕ} (A : Occupation Q N) : ℝ :=
  (occupationFactorial A : ℝ) * occupationOrbitalFactorial A / occupationSphereProduct A

def certificateInner {Q N d : ℕ} (c e : WeightOccupationState Q N d) : ℂ :=
  ∑ A : WeightOccupation Q N d, (certificateMetricWeight A.val : ℂ) * star (c A) * e A

theorem certificateMetricWeight_pos {Q N : ℕ} (hQ : 0<Q) (A : Occupation Q N) :
    0 < certificateMetricWeight A := by
  rw [certificateMetricWeight, ← occupation_metric_factor hQ A]
  exact div_pos (mul_pos (pow_pos (by exact_mod_cast hQ) _)
    (by exact_mod_cast occupationFactorial_pos A)) (occupationBinomialProduct_pos A)

theorem certificateWeightCoordinates_inner {Q N d : ℕ} (hQ : 0<Q)
    (c e : WeightOccupationState Q N d) :
    inner (certificateWeightCoordinates Q N d c) (certificateWeightCoordinates Q N d e) =
      certificateInner c e := by
  rw [certificateWeightCoordinates_apply, certificateWeightCoordinates_apply,
    certificateCoordinates_apply, certificateCoordinates_apply, stateInner_real_smul_both]
  change ((certificateSectorScale Q N d)^2 : ℝ) *
    polynomialInner (polynomialOccupationInclude (occupationWeightExtend d c))
      (polynomialOccupationInclude (occupationWeightExtend d e)) = _
  rw [polynomialOccupationInclude_weight_inner, ← mul_assoc]
  have hs : ((certificateSectorScale Q N d)^2 : ℝ) * (N.factorial : ℂ) = (Q : ℂ)^d := by
    rw [certificateSectorScale_sq]
    have hn : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
    push_cast
    field_simp
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  have hm : (Q : ℂ)^d * ((occupationFactorial A.val : ℂ) /
      (occupationBinomialProduct A.val : ℂ)) = (certificateMetricWeight A.val : ℂ) := by
    have h := occupation_metric_factor hQ A.val
    rw [A.property] at h
    unfold certificateMetricWeight
    rw [← mul_div_assoc]
    exact_mod_cast h
  change (Q : ℂ)^d * (((occupationFactorial A.val : ℂ) /
    (occupationBinomialProduct A.val : ℂ)) * star (c A) * e A) = _
  rw [← mul_assoc, ← mul_assoc, hm]

/-- Exact Hamiltonian form in the same metric and pair matrices as the
certificate, including its finite-sphere pair coefficient. -/
theorem certificateWeightCoordinates_hamiltonian_inner {Q N d : ℕ} (hQ : 0<Q)
    (c e : WeightOccupationState Q (N+2) d) :
    inner (certificateWeightCoordinates Q (N+2) d c)
      (hamiltonian (certificateWeightCoordinates Q (N+2) d e)) =
      ∑ p : Fin (2*Q+1), (planarPairFactor p.val / sphereFactor (2*Q) p.val : ℝ) *
        certificateInner (occupationPairBlock Q N d p.val c) (occupationPairBlock Q N d p.val e) := by
  rw [certificateWeightCoordinates_apply, certificateWeightCoordinates_apply,
    certificateCoordinates_apply, certificateCoordinates_apply, hamiltonian_smul,
    stateInner_real_smul_both, ← polynomialHamiltonian_inner,
    polynomialHamiltonian_gram _ _ (polynomialOccupationInclude_isBosonic _)
      (polynomialOccupationInclude_isBosonic _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [polynomialOccupationInclude_pairChannel, polynomialOccupationInclude_pairChannel,
    ← occupationPairBlock_extend, ← occupationPairBlock_extend]
  rw [← certificateWeightCoordinates_inner hQ,
    certificateWeightCoordinates_apply, certificateWeightCoordinates_apply,
    certificateCoordinates_apply, certificateCoordinates_apply, stateInner_real_smul_both]
  by_cases hp : p.val ≤ d
  · have hf := certificate_pair_gram_factor (N := N) hQ hp (Nat.le_of_lt_succ p.isLt)
    have hf' : ((certificateSectorScale Q (N+2) d)^2 : ℝ) *
        ((((N+2).choose 2 : ℝ) / ((2*Q).choose p.val : ℝ) : ℝ) : ℂ) =
      ((planarPairFactor p.val / sphereFactor (2*Q) p.val : ℝ) : ℂ) *
        (((certificateSectorScale Q N (d-p.val))^2 : ℝ) : ℂ) := by exact_mod_cast hf
    rw [← mul_assoc, hf', mul_assoc]
    rfl
  · have hz : occupationPairBlock Q N d p.val c = 0 := by
      apply (occupationPairBlock_zero_iff Q N d p.val c).mpr
      exact occupationPairChannel_above_weight d p.val (by omega) _ (occupationWeightExtend_supported c)
    rw [hz]
    simp [occupationWeightExtend, polynomialOccupationInclude, polynomialInner,
      polynomialCoordinates_symm_apply, inner]

def certificateHamiltonianFormMatrix (Q N d : ℕ) :
    Matrix (WeightOccupation Q N d) (WeightOccupation Q N d) ℂ := fun A B =>
  inner (certificateWeightCoordinates Q N d (Pi.single A 1))
    (hamiltonian (certificateWeightCoordinates Q N d (Pi.single B 1)))

theorem certificateHamiltonianFormMatrix_apply {Q N d : ℕ} (hQ : 0<Q)
    (A B : WeightOccupation Q (N+2) d) :
    certificateHamiltonianFormMatrix Q (N+2) d A B =
      ∑ p : Fin (2*Q+1), (planarPairFactor p.val / sphereFactor (2*Q) p.val : ℝ) *
        ∑ C : WeightOccupation Q N (d-p.val), (certificateMetricWeight C.val : ℂ) *
          star (occupationPairBlockMatrix Q N d p.val C A) *
            occupationPairBlockMatrix Q N d p.val C B := by
  unfold certificateHamiltonianFormMatrix
  rw [certificateWeightCoordinates_hamiltonian_inner hQ]
  rfl

end
end BosonicLaughlin

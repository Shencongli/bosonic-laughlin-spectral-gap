import BosonicLaughlin.OccupationCMBlocks
import BosonicLaughlin.CertificateCoordinates

/-! The exact highest-weight correspondence in the certificate's normalized
physical coordinates. The degree-dependent normalization contributes sqrt Q
to the raising intertwiner. Kernel equivalence requires Q>0. -/
namespace BosonicLaughlin
noncomputable section

theorem certificateSectorScale_succ (Q N d : ℕ) :
    certificateSectorScale Q N (d+1) = Real.sqrt Q * certificateSectorScale Q N d := by
  unfold certificateSectorScale
  have hp : (Q : ℝ)^(d+1) / (N.factorial : ℝ) =
      (Q : ℝ) * ((Q : ℝ)^d / (N.factorial : ℝ)) := by rw [pow_succ]; ring
  rw [hp, Real.sqrt_mul (Nat.cast_nonneg Q)]

theorem certificateSectorScale_pred (Q N d : ℕ) (hd : 0<d) :
    certificateSectorScale Q N d = Real.sqrt Q * certificateSectorScale Q N (d-1) := by
  simpa only [Nat.sub_add_cancel (show 1≤d by omega)] using certificateSectorScale_succ Q N (d-1)

theorem tensorRaise_certificateCoordinates (Q N d : ℕ) (c : OccupationState Q N) :
    tensorRaise (certificateCoordinates Q N d c) = certificateCoordinates Q N d (occupationCM c) := by
  apply (polynomialCoordinates Q N).injective
  rw [polynomialCoordinates_tensorRaise, certificateCoordinates_polynomial,
    polynomialCM_smul, polynomialOccupationInclude_CM, certificateCoordinates_polynomial]

/-- J+ Φ_d = sqrt(Q) Φ_(d-1) C_d, with the certificate's actual degree normalization. -/
theorem tensorRaise_certificateWeightCoordinates {Q N d : ℕ} (hd : 0<d)
    (c : WeightOccupationState Q N d) :
    tensorRaise (certificateWeightCoordinates Q N d c) =
      (Real.sqrt Q : ℂ) • certificateWeightCoordinates Q N (d-1) (occupationCMBlock Q N d c) := by
  rw [certificateWeightCoordinates_apply, tensorRaise_certificateCoordinates,
    ← occupationCMBlock_extend, certificateWeightCoordinates_apply,
    certificateCoordinates_apply, certificateCoordinates_apply,
    certificateSectorScale_pred Q N d hd, Complex.ofReal_mul, smul_smul]

theorem tensorRaise_certificateWeightCoordinates_zero_iff {Q N d : ℕ} (hQ : 0<Q)
    (c : WeightOccupationState Q N d) :
    tensorRaise (certificateWeightCoordinates Q N d c)=0 ↔
      (occupationCMBlockMatrix Q N d).mulVec c=0 := by
  rw [certificateWeightCoordinates_apply, certificateCoordinates_apply,
    tensorRaise_scaledPolynomialOccupation_zero_iff _ (certificateSectorScale_complex_ne_zero hQ),
    occupationCMMatrix_mulVec, occupationCMBlockMatrix_mulVec, occupationCMBlock_zero_iff]

/-- Every physical bosonic highest-weight vector of degree d has certificate
coordinates in the integer CM kernel. This is independent of a chosen frame. -/
theorem certificateWeightCoordinates_highest_surjective {Q N d : ℕ} (hQ : 0<Q)
    (ψ : State Q N) (hψ : IsBosonic ψ) (hw : WeightSupported d ψ)
    (hE : tensorRaise ψ=0) :
    ∃ c : WeightOccupationState Q N d,
      (occupationCMBlockMatrix Q N d).mulVec c=0 ∧ certificateWeightCoordinates Q N d c=ψ := by
  obtain ⟨c,hc⟩ := certificateWeightCoordinates_surjective_bosonic_weight hQ N d ψ hψ hw
  refine ⟨c, (tensorRaise_certificateWeightCoordinates_zero_iff hQ c).mp ?_, hc⟩
  rw [hc]
  exact hE

end
end BosonicLaughlin

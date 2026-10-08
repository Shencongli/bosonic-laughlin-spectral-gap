import BosonicLaughlin.OccupationLowering
import BosonicLaughlin.CertificateDescendants

/-! The verifier's iterated affine raising rule is the physical lowering
descendant, with sqrt(Q) per step in the certificate normalization.
Its norm recurrence is derived from the physical factorial ladder factor. -/
namespace BosonicLaughlin
noncomputable section

def verifierDescendant (Q N d : ℕ) : (n : ℕ) →
    WeightOccupationState Q N d →ₗ[ℂ] WeightOccupationState Q N (d+n)
  | 0 => LinearMap.id
  | n+1 => (verifierRaiseBlock Q N (d+n)).comp (verifierDescendant Q N d n)

theorem verifierDescendant_zero (Q N d : ℕ) (c : WeightOccupationState Q N d) :
    verifierDescendant Q N d 0 c=c := rfl

theorem verifierDescendant_succ (Q N d n : ℕ) (c : WeightOccupationState Q N d) :
    verifierDescendant Q N d (n+1) c=verifierRaiseBlock Q N (d+n) (verifierDescendant Q N d n c) := rfl

theorem tensorDescendant_certificateCoordinates {Q N d : ℕ} (hQ : 0 < Q)
    (c : WeightOccupationState Q N d) (n : ℕ) :
    tensorDescendant (certificateWeightCoordinates Q N d c) n=
      ((Real.sqrt Q : ℂ)^n) • certificateWeightCoordinates Q N (d+n) (verifierDescendant Q N d n c) := by
  induction n with
  | zero => simp [tensorDescendant_zero, verifierDescendant_zero]
  | succ n ih =>
    rw [tensorDescendant_succ, ih]
    change tensorLowerLinear Q N (_ • _) = _
    rw [map_smul]
    change _ • tensorLower _ = _
    rw [tensorLower_certificateWeightCoordinates hQ, smul_smul, ← pow_succ]
    rfl

def verifierDescendantNorm (Q N d : ℕ) : ℕ → ℝ
  | 0 => 1
  | n+1 => verifierDescendantNorm Q N d n *
      (((n+1 : ℕ) : ℝ)*((N : ℝ)-((2*d+n : ℕ) : ℝ)/(Q : ℝ)))

theorem verifierDescendantNorm_eq_factor {Q N d : ℕ} (hQ : 0 < Q) (hd : 2*d≤N*Q)
    (n : ℕ) (hn : n≤N*Q-2*d) :
    verifierDescendantNorm Q N d n=(descendantFactor (N*Q-2*d) n : ℝ)/(Q : ℝ)^n := by
  have hq : (Q : ℝ)≠0 := by exact_mod_cast hQ.ne'
  induction n with
  | zero => simp [verifierDescendantNorm, descendantFactor_zero]
  | succ n ih =>
    rw [verifierDescendantNorm, ih (by omega), descendantFactor_succ]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : n≤N*Q-2*d), Nat.cast_sub hd]
    push_cast
    rw [pow_succ]
    field_simp
    ring

theorem verifierDescendantNorm_pos {Q N d : ℕ} (hQ : 0 < Q) (hd : 2*d≤N*Q)
    (n : ℕ) (hn : n≤N*Q-2*d) : 0 < verifierDescendantNorm Q N d n := by
  rw [verifierDescendantNorm_eq_factor hQ hd n hn]
  exact div_pos (by exact_mod_cast descendantFactor_pos hn) (pow_pos (by exact_mod_cast hQ) n)

theorem certificateDescendant_inner_scale {Q N d : ℕ} (hQ : 0 < Q)
    (c e : WeightOccupationState Q N d) (n : ℕ) :
    inner (tensorDescendant (certificateWeightCoordinates Q N d c) n)
      (tensorDescendant (certificateWeightCoordinates Q N d e) n)=
      ((Q : ℂ)^n)*certificateInner (verifierDescendant Q N d n c) (verifierDescendant Q N d n e) := by
  rw [tensorDescendant_certificateCoordinates hQ, tensorDescendant_certificateCoordinates hQ]
  simp only [← Complex.ofReal_pow]
  rw [stateInner_real_smul_both, certificateWeightCoordinates_inner hQ]
  have hs : ((Real.sqrt (Q : ℝ))^n)^2=(Q : ℝ)^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt (Nat.cast_nonneg Q)]
  rw [hs]
  push_cast
  rfl

theorem verifierDescendant_inner {Q N d : ℕ} (hQ : 0 < Q) (hd : 2*d≤N*Q)
    (c e : WeightOccupationState Q N d) (he : (occupationCMBlockMatrix Q N d).mulVec e=0)
    (n : ℕ) (hn : n≤N*Q-2*d) :
    certificateInner (verifierDescendant Q N d n c) (verifierDescendant Q N d n e)=
      (verifierDescendantNorm Q N d n : ℂ)*certificateInner c e := by
  have h := certificateDescendant_inner hQ hd c e he n hn
  rw [certificateDescendant_inner_scale hQ] at h
  rw [verifierDescendantNorm_eq_factor hQ hd n hn]
  push_cast
  have hq : (Q : ℂ)^n≠0 := pow_ne_zero n (by exact_mod_cast hQ.ne')
  apply (mul_left_cancel₀ hq)
  rw [h]
  field_simp

theorem verifierDescendant_normalized_form {Q N d : ℕ} (hQ : 0 < Q) (hd : 2*d≤N*Q)
    (c e : WeightOccupationState Q N d) (n : ℕ) (hn : n≤N*Q-2*d)
    (A : State Q N →ₗ[ℂ] State Q N) :
    inner (normalizedTensorDescendant (certificateWeightCoordinates Q N d c) (N*Q-2*d) n)
      (A (normalizedTensorDescendant (certificateWeightCoordinates Q N d e) (N*Q-2*d) n))=
      ((verifierDescendantNorm Q N d n : ℂ)⁻¹)*
        inner (certificateWeightCoordinates Q N (d+n) (verifierDescendant Q N d n c))
          (A (certificateWeightCoordinates Q N (d+n) (verifierDescendant Q N d n e))) := by
  rw [normalizedTensorDescendant, normalizedTensorDescendant, map_smul, stateInner_real_smul_both,
    tensorDescendant_certificateCoordinates hQ, tensorDescendant_certificateCoordinates hQ, map_smul]
  simp only [← Complex.ofReal_pow]
  rw [stateInner_real_smul_both]
  have hp : (0 : ℝ)<descendantFactor (N*Q-2*d) n := by exact_mod_cast descendantFactor_pos hn
  have hs : ((Real.sqrt (Q : ℝ))^n)^2=(Q : ℝ)^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt (Nat.cast_nonneg Q)]
  rw [inv_pow, Real.sq_sqrt hp.le, hs, verifierDescendantNorm_eq_factor hQ hd n hn]
  push_cast
  rw [inv_div, div_eq_mul_inv]
  ring

end
end BosonicLaughlin

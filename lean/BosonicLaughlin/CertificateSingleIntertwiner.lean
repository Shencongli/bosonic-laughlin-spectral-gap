import BosonicLaughlin.CertificatePairIntertwiner

/-! Single-orbital annihilation in the same normalized polynomial coordinates.
This supplies the spectator factors in the three- and four-body row forms. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def certificateSingleCoefficient (Q j : ℕ) : ℝ :=
  Real.sqrt ((j.factorial : ℝ) / sphereFactor Q j)

theorem certificateSingleCoefficient_sq {Q j : ℕ} (hQ : 0<Q) (hj : j≤Q) :
    certificateSingleCoefficient Q j ^ 2=(j.factorial : ℝ) / sphereFactor Q j := by
  apply Real.sq_sqrt
  exact div_nonneg (Nat.cast_nonneg _) (sphereFactor_pos hQ hj).le

theorem certificate_single_scale {Q N d j : ℕ} (hQ : 0<Q) (hj : j≤d) (hjQ : j≤Q) :
    certificateSectorScale Q (N+1) d * (Real.sqrt (N+1) / binomialRoot Q j) =
      certificateSingleCoefficient Q j * certificateSectorScale Q N (d-j) := by
  have hfactor : (Q : ℝ)^j / (Q.choose j : ℝ) = (j.factorial : ℝ) / sphereFactor Q j := by
    apply (div_eq_div_iff (by exact_mod_cast (Nat.choose_pos hjQ).ne') (sphereFactor_pos hQ hjQ).ne').mpr
    exact (factorial_mul_choose_eq_sphereFactor hQ hjQ).symm
  have hsq : (certificateSectorScale Q (N+1) d * (Real.sqrt (N+1) / binomialRoot Q j))^2 =
      (certificateSingleCoefficient Q j * certificateSectorScale Q N (d-j))^2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), binomialRoot_sq, mul_pow,
      certificateSingleCoefficient_sq hQ hjQ, ← hfactor, certificateSectorScale_sq, certificateSectorScale_sq]
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hpw : (Q : ℝ)^d=(Q : ℝ)^j*(Q : ℝ)^(d-j) := by rw [← pow_add, Nat.add_sub_of_le hj]
    rw [hpw]
    have hn : ((N+1 : ℕ) : ℝ)≠0 := by positivity
    field_simp
    push_cast
    rfl
  have hl : 0≤certificateSectorScale Q (N+1) d * (Real.sqrt (N+1) / binomialRoot Q j) :=
    mul_nonneg (certificateSectorScale_pos hQ _ _).le
      (div_nonneg (Real.sqrt_nonneg _) (binomialRoot_pos _ _ hjQ).le)
  have hr : 0≤certificateSingleCoefficient Q j * certificateSectorScale Q N (d-j) :=
    mul_nonneg (Real.sqrt_nonneg _) (certificateSectorScale_pos hQ _ _).le
  nlinarith

theorem annihilate_single_apply {Q N : ℕ} (j : Orbital Q) (ψ : State Q (N+1))
    (a : Configuration Q N) :
    annihilate (Pi.single j 1) ψ a=(Real.sqrt (N+1) : ℂ)*ψ (Fin.cons j a) := by
  simp [annihilate, Pi.single_apply, ite_mul]

theorem polynomialOccupationInclude_single {Q N : ℕ} (j : Orbital Q)
    (c : OccupationState Q (N+1)) (a : Configuration Q N) :
    polynomialOccupationInclude c (Fin.cons j a)=
      polynomialOccupationInclude (occupationAnnihilate j c) a := by
  simp only [polynomialOccupationInclude, occupationOfConfiguration_cons,
    occupationFactorial_cons, occupationAnnihilate, occupation_cons_val,
    Multiset.count_cons_self, Nat.cast_mul]
  ring

theorem annihilate_single_polynomial_inverse {Q N : ℕ} (j : Orbital Q)
    (c : OccupationState Q (N+1)) :
    annihilate (Pi.single j 1) ((polynomialCoordinates Q (N+1)).symm (polynomialOccupationInclude c)) =
      ((Real.sqrt (N+1) / binomialRoot Q j.val : ℝ) : ℂ) •
        (polynomialCoordinates Q N).symm (polynomialOccupationInclude (occupationAnnihilate j c)) := by
  funext a
  rw [annihilate_single_apply, polynomialCoordinates_symm_apply, polynomialScale_cons,
    polynomialOccupationInclude_single]
  simp only [Pi.smul_apply, smul_eq_mul, polynomialCoordinates_symm_apply,
    Complex.ofReal_mul, Complex.ofReal_inv, mul_inv_rev, div_eq_mul_inv]
  ring

theorem annihilate_single_certificateCoordinates {Q N d : ℕ} (hQ : 0<Q)
    (j : Orbital Q) (hj : j.val≤d) (c : OccupationState Q (N+1)) :
    annihilate (Pi.single j 1) (certificateCoordinates Q (N+1) d c) =
      (certificateSingleCoefficient Q j.val : ℂ) •
        certificateCoordinates Q N (d-j.val) (occupationAnnihilate j c) := by
  rw [certificateCoordinates_apply]
  change (annihilateLinear Q N (Pi.single j 1)) (_ • _)=_
  rw [map_smul]
  change _ • annihilate (Pi.single j 1) _=_
  rw [annihilate_single_polynomial_inverse, certificateCoordinates_apply,
    smul_smul, smul_smul, ← Complex.ofReal_mul,
    certificate_single_scale hQ hj (by omega), Complex.ofReal_mul]

theorem v0PairAnnihilate_certificateCoordinates {Q N d : ℕ} (hQ : 0<Q)
    (p : Fin (2*Q+1)) (hp : p.val≤d) (c : OccupationState Q (N+2)) :
    v0PairAnnihilate p (certificateCoordinates Q (N+2) d c) =
      (certificatePairCoefficient Q p.val : ℂ) •
        certificateCoordinates Q N (d-p.val) (occupationPairChannel p.val c) := by
  rw [certificateCoordinates_apply]
  change (v0PairAnnihilateLinear Q N p) (_ • _)=_
  rw [map_smul]
  change _ • v0PairAnnihilate p _=_
  rw [v0PairAnnihilate_polynomial_inverse, polynomialOccupationInclude_pairChannel,
    certificateCoordinates_apply, smul_smul, smul_smul, ← Complex.ofReal_mul,
    certificate_pair_scale hQ hp (by omega), Complex.ofReal_mul]

theorem single_pair_certificateCoordinates {Q N d : ℕ} (hQ : 0<Q)
    (p : Fin (2*Q+1)) (j : Orbital Q) (hpj : p.val+j.val≤d)
    (c : OccupationState Q (N+3)) :
    annihilate (Pi.single j 1) (v0PairAnnihilate p (certificateCoordinates Q (N+3) d c)) =
      ((certificatePairCoefficient Q p.val * certificateSingleCoefficient Q j.val : ℝ) : ℂ) •
        certificateCoordinates Q N (d-p.val-j.val)
          (occupationAnnihilate j (occupationPairChannel p.val c)) := by
  rw [v0PairAnnihilate_certificateCoordinates hQ p (by omega)]
  change (annihilateLinear Q N (Pi.single j 1)) (_ • _)=_
  rw [map_smul]
  change _ • annihilate (Pi.single j 1) _=_
  rw [annihilate_single_certificateCoordinates hQ j (by omega), smul_smul, Complex.ofReal_mul]

theorem double_single_pair_certificateCoordinates {Q N d : ℕ} (hQ : 0<Q)
    (p : Fin (2*Q+1)) (i j : Orbital Q) (hpij : p.val+i.val+j.val≤d)
    (c : OccupationState Q (N+4)) :
    annihilate (Pi.single i 1) (annihilate (Pi.single j 1)
      (v0PairAnnihilate p (certificateCoordinates Q (N+4) d c))) =
      ((certificatePairCoefficient Q p.val * certificateSingleCoefficient Q j.val *
        certificateSingleCoefficient Q i.val : ℝ) : ℂ) •
        certificateCoordinates Q N (d-p.val-j.val-i.val)
          (occupationAnnihilate i (occupationAnnihilate j (occupationPairChannel p.val c))) := by
  rw [single_pair_certificateCoordinates hQ p j (by omega)]
  change (annihilateLinear Q N (Pi.single i 1)) (_ • _)=_
  rw [map_smul]
  change _ • annihilate (Pi.single i 1) _=_
  rw [annihilate_single_certificateCoordinates hQ i (by omega), smul_smul]
  simp only [Complex.ofReal_mul]

end
end BosonicLaughlin

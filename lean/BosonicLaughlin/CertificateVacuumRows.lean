import BosonicLaughlin.CertificateRowNormalOrder

/-! Vacuum functionals obtained by the verifier's integer derivatives.
The physical coefficients are derived from the actual annihilation maps. -/
namespace BosonicLaughlin
noncomputable section

def vacuumOccupation (Q : ℕ) : Occupation Q 0 :=
  occupationOfConfiguration (vacuumConfiguration Q)

theorem certificateCoordinates_vacuum (Q : ℕ) (c : OccupationState Q 0) :
    certificateCoordinates Q 0 0 c (vacuumConfiguration Q)=c (vacuumOccupation Q) := by
  simp [certificateCoordinates_apply, certificateSectorScale, polynomialCoordinates_symm_apply,
    polynomialScale, polynomialOccupationInclude, occupationFactorial, occupationOfConfiguration,
    multisetOccupationFactorial, vacuumOccupation, vacuumConfiguration]

/-- Vacuum coefficient of d_j Bhat_p, acting on three-particle occupation amplitudes. -/
def occupationThreeFunctional {Q : ℕ} (p : ℕ) (j : Orbital Q)
    (c : OccupationState Q 3) : ℂ :=
  occupationAnnihilate j (occupationPairChannel p c) (vacuumOccupation Q)

/-- Vacuum coefficient of d_i d_j Bhat_p, including coinciding-label multiplicities. -/
def occupationFourFunctional {Q : ℕ} (p : ℕ) (i j : Orbital Q)
    (c : OccupationState Q 4) : ℂ :=
  occupationAnnihilate i (occupationAnnihilate j (occupationPairChannel p c)) (vacuumOccupation Q)

theorem single_pair_vacuum_coordinates {Q : ℕ} (hQ : 0<Q)
    (p : Fin (2*Q+1)) (j : Orbital Q) (c : OccupationState Q 3) :
    annihilate (Pi.single j 1) (v0PairAnnihilate p
      (certificateCoordinates Q 3 (p.val+j.val) c)) (vacuumConfiguration Q) =
        ((certificatePairCoefficient Q p.val * certificateSingleCoefficient Q j.val : ℝ) : ℂ) *
          occupationThreeFunctional p.val j c := by
  rw [single_pair_certificateCoordinates hQ p j (by omega)]
  simp only [Pi.smul_apply, smul_eq_mul, Nat.add_sub_cancel_left, Nat.sub_self,
    certificateCoordinates_vacuum]
  rfl

theorem double_single_pair_vacuum_coordinates {Q : ℕ} (hQ : 0<Q)
    (p : Fin (2*Q+1)) (i j : Orbital Q) (c : OccupationState Q 4) :
    annihilate (Pi.single i 1) (annihilate (Pi.single j 1) (v0PairAnnihilate p
      (certificateCoordinates Q 4 (p.val+i.val+j.val) c))) (vacuumConfiguration Q) =
        ((certificatePairCoefficient Q p.val * certificateSingleCoefficient Q j.val *
          certificateSingleCoefficient Q i.val : ℝ) : ℂ) * occupationFourFunctional p.val i j c := by
  rw [double_single_pair_certificateCoordinates hQ p i j (by omega)]
  have hz : p.val+i.val+j.val-p.val-j.val-i.val=0 := by omega
  simp only [Pi.smul_apply, smul_eq_mul, hz, certificateCoordinates_vacuum]
  rfl

theorem three_functional_cross_coordinates {Q : ℕ} (hQ : 0<Q)
    (p t : Fin (2*Q+1)) (i j : Orbital Q) (hdegree : t.val+i.val=p.val+j.val)
    (c e : OccupationState Q 3) :
    inner
      (annihilate (Pi.single i 1) (v0PairAnnihilate t (certificateCoordinates Q 3 (p.val+j.val) c)))
      (annihilate (Pi.single j 1) (v0PairAnnihilate p (certificateCoordinates Q 3 (p.val+j.val) e))) =
      ((certificatePairCoefficient Q t.val * certificateSingleCoefficient Q i.val *
        certificatePairCoefficient Q p.val * certificateSingleCoefficient Q j.val : ℝ) : ℂ) *
          star (occupationThreeFunctional t.val i c) * occupationThreeFunctional p.val j e := by
  rw [stateInner_vacuum]
  have hc := single_pair_vacuum_coordinates hQ t i c
  rw [hdegree] at hc
  rw [hc, single_pair_vacuum_coordinates hQ p j e, star_mul]
  simp only [Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem four_functional_cross_coordinates {Q : ℕ} (hQ : 0<Q)
    (p q : Fin (2*Q+1)) (i j k l : Orbital Q)
    (hdegree : p.val+k.val+j.val=q.val+i.val+l.val) (c e : OccupationState Q 4) :
    inner
      (annihilate (Pi.single k 1) (annihilate (Pi.single j 1) (v0PairAnnihilate p
        (certificateCoordinates Q 4 (p.val+k.val+j.val) c))))
      (annihilate (Pi.single i 1) (annihilate (Pi.single l 1) (v0PairAnnihilate q
        (certificateCoordinates Q 4 (p.val+k.val+j.val) e)))) =
      ((certificatePairCoefficient Q p.val * certificateSingleCoefficient Q j.val *
        certificateSingleCoefficient Q k.val * certificatePairCoefficient Q q.val *
        certificateSingleCoefficient Q l.val * certificateSingleCoefficient Q i.val : ℝ) : ℂ) *
          star (occupationFourFunctional p.val k j c) * occupationFourFunctional q.val i l e := by
  rw [stateInner_vacuum, double_single_pair_vacuum_coordinates hQ p k j c]
  have he := double_single_pair_vacuum_coordinates hQ q i l e
  rw [← hdegree] at he
  rw [he, star_mul]
  simp only [Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

end
end BosonicLaughlin

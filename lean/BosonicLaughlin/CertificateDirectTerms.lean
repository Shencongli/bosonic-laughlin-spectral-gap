import BosonicLaughlin.CertificateVacuumRows
import BosonicLaughlin.CertificateRowFactors

/-! Term-by-term physical pullbacks of the direct K3 and K4 formulas.
The degree hypotheses specify the blocks in which the vacuum rows live. -/
namespace BosonicLaughlin
noncomputable section

theorem physical_direct_three_cross {Q : ℕ} (hQ : 0<Q)
    (t p : Fin (2*Q+1)) (i j : Orbital Q) (hd : t.val+i.val=p.val+j.val)
    (y0 y : ℝ) (c e : OccupationState Q 3) :
    (frozenRowLeading t.val y0 : ℂ)*(frozenRowTransfer p.val i.val j.val y : ℂ)*
      inner
        (annihilate (Pi.single i 1) (v0PairAnnihilate t
          (certificateCoordinates Q 3 (p.val+j.val) c)))
        (annihilate (Pi.single j 1) (v0PairAnnihilate p
          (certificateCoordinates Q 3 (p.val+j.val) e))) =
      ((y0*y*directRowFactor Q p.val i.val j.val / spherePairRoot Q t.val : ℝ) : ℂ) *
        star (occupationThreeFunctional t.val i c)*occupationThreeFunctional p.val j e := by
  rw [three_functional_cross_coordinates hQ p t i j hd]
  have hs := congrArg Complex.ofReal (directRow_three_cross_factor Q t.val p.val i.val j.val y0 y)
  push_cast at hs ⊢
  linear_combination (star (occupationThreeFunctional t.val i c)*occupationThreeFunctional p.val j e)*hs

theorem physical_direct_three_contraction {Q : ℕ} (hQ : 0<Q)
    (p q : Fin (2*Q+1)) (i j l : Orbital Q) (hd : p.val+j.val=q.val+l.val)
    (y z : ℝ) (c e : OccupationState Q 3) :
    (frozenRowTransfer p.val i.val j.val y : ℂ)*(frozenRowTransfer q.val i.val l.val z : ℂ)*
      inner
        (annihilate (Pi.single j 1) (v0PairAnnihilate p
          (certificateCoordinates Q 3 (p.val+j.val) c)))
        (annihilate (Pi.single l 1) (v0PairAnnihilate q
          (certificateCoordinates Q 3 (p.val+j.val) e))) =
      ((y*z*(i.val.factorial : ℝ) /
        (spherePairRoot Q p.val*spherePairRoot Q q.val*sphereOrbitalRoot Q j.val*sphereOrbitalRoot Q l.val) : ℝ) : ℂ) *
        star (occupationThreeFunctional p.val j c)*occupationThreeFunctional q.val l e := by
  have hc := three_functional_cross_coordinates hQ q p j l hd c e
  rw [← hd] at hc
  rw [hc]
  have hs := congrArg Complex.ofReal (directRow_three_contraction_factor Q p.val q.val i.val j.val l.val y z)
  push_cast at hs ⊢
  linear_combination (star (occupationThreeFunctional p.val j c)*occupationThreeFunctional q.val l e)*hs

theorem physical_direct_four {Q : ℕ} (hQ : 0<Q)
    (p q : Fin (2*Q+1)) (i j k l : Orbital Q)
    (hd : p.val+k.val+j.val=q.val+i.val+l.val) (y z : ℝ) (c e : OccupationState Q 4) :
    (frozenRowTransfer p.val i.val j.val y : ℂ)*(frozenRowTransfer q.val k.val l.val z : ℂ)*
      inner
        (annihilate (Pi.single k 1) (annihilate (Pi.single j 1) (v0PairAnnihilate p
          (certificateCoordinates Q 4 (p.val+k.val+j.val) c))))
        (annihilate (Pi.single i 1) (annihilate (Pi.single l 1) (v0PairAnnihilate q
          (certificateCoordinates Q 4 (p.val+k.val+j.val) e)))) =
      ((y*z*directRowFactor Q p.val i.val j.val*directRowFactor Q q.val k.val l.val : ℝ) : ℂ) *
        star (occupationFourFunctional p.val k j c)*occupationFourFunctional q.val i l e := by
  rw [four_functional_cross_coordinates hQ p q i j k l hd]
  have hs := congrArg Complex.ofReal (directRow_four_factor Q p.val q.val i.val j.val k.val l.val y z)
  push_cast at hs ⊢
  linear_combination (star (occupationFourFunctional p.val k j c)*occupationFourFunctional q.val i l e)*hs

end
end BosonicLaughlin

import BosonicLaughlin.SphereFactors

/-! Sector normalization for the fixed polynomial certificate coordinates. -/
namespace BosonicLaughlin
noncomputable section

/-- The scalar multiplying factorial-weighted polynomial occupation amplitudes.
Its square is Q^d/N!, where d is the total orbital degree. -/
def certificateSectorScale (Q N d : ℕ) : ℝ :=
  Real.sqrt ((Q : ℝ)^d / (N.factorial : ℝ))

theorem certificateSectorScale_sq (Q N d : ℕ) :
    certificateSectorScale Q N d ^ 2 = (Q : ℝ)^d / (N.factorial : ℝ) :=
  Real.sq_sqrt (by positivity)

theorem certificateSectorScale_pos {Q : ℕ} (hQ : 0 < Q) (N d : ℕ) :
    0 < certificateSectorScale Q N d := by
  apply Real.sqrt_pos.mpr
  apply div_pos
  · exact pow_pos (by exact_mod_cast hQ) _
  · exact_mod_cast Nat.factorial_pos N

theorem pair_choose_factorial (N : ℕ) :
    ((N+2).choose 2 : ℝ) * 2 * (N.factorial : ℝ) = ((N+2).factorial : ℝ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show 2 ≤ N+2 by omega)
  norm_num at h
  exact_mod_cast h

/-- Cancellation of the pair-count and particle factorials, with the output
degree d-p explicitly required to be nonnegative. -/
theorem certificate_sector_pair_ratio {Q N d p : ℕ} (hQ : 0 < Q) (hp : p ≤ d) :
    certificateSectorScale Q (N+2) d ^ 2 * ((N+2).choose 2 : ℝ) =
      (Q : ℝ)^p / 2 * certificateSectorScale Q N (d-p) ^ 2 := by
  rw [certificateSectorScale_sq, certificateSectorScale_sq]
  have hf : ((N+2).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (N+2)).ne'
  have hn : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  have hc := pair_choose_factorial N
  have hpw : (Q : ℝ)^d = (Q : ℝ)^p * (Q : ℝ)^(d-p) := by
    rw [← pow_add, Nat.add_sub_of_le hp]
  rw [hpw]
  field_simp
  nlinarith [hc]

theorem certificate_pair_gram_factor {Q N d p : ℕ}
    (hQ : 0 < Q) (hp : p ≤ d) (hpQ : p ≤ 2*Q) :
    certificateSectorScale Q (N+2) d ^ 2 *
        (((N+2).choose 2 : ℝ) / ((2*Q).choose p : ℝ)) =
      (planarPairFactor p / sphereFactor (2*Q) p) *
        certificateSectorScale Q N (d-p) ^ 2 := by
  rw [← mul_div_assoc, certificate_sector_pair_ratio hQ hp, ← sphere_pair_factor hQ hpQ]
  ring

end
end BosonicLaughlin

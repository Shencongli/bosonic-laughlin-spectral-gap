import BosonicLaughlin.CertificateSingleIntertwiner

/-! Exact cancellation of the frozen row normalization factors.
The real row entries may have either sign; no expansion in 1/Q is used. -/
namespace BosonicLaughlin
noncomputable section

def frozenRowLeading (t : ℕ) (y : ℝ) : ℝ := y / Real.sqrt (planarPairFactor t)
def frozenRowTransfer (p i j : ℕ) (y : ℝ) : ℝ :=
  y * Real.sqrt ((i.factorial : ℝ) / (planarPairFactor p * (j.factorial : ℝ)))
def sphereOrbitalRoot (Q j : ℕ) : ℝ := Real.sqrt (sphereFactor Q j)
def spherePairRoot (Q p : ℕ) : ℝ := Real.sqrt (sphereFactor (2*Q) p)
def directRowFactor (Q p i j : ℕ) : ℝ :=
  (i.factorial : ℝ) / (spherePairRoot Q p * sphereOrbitalRoot Q i * sphereOrbitalRoot Q j)

theorem planarPairFactor_pos (p : ℕ) : 0<planarPairFactor p := by
  unfold planarPairFactor
  positivity

theorem certificatePairCoefficient_eq_roots (Q p : ℕ) :
    certificatePairCoefficient Q p=Real.sqrt (planarPairFactor p)/spherePairRoot Q p := by
  exact Real.sqrt_div (planarPairFactor_pos p).le _

theorem certificateSingleCoefficient_eq_roots (Q j : ℕ) :
    certificateSingleCoefficient Q j=Real.sqrt (j.factorial : ℝ)/sphereOrbitalRoot Q j := by
  exact Real.sqrt_div (Nat.cast_nonneg _) _

theorem frozenRowTransfer_eq_roots (p i j : ℕ) (y : ℝ) :
    frozenRowTransfer p i j y=
      y*Real.sqrt (i.factorial : ℝ)/(Real.sqrt (planarPairFactor p)*Real.sqrt (j.factorial : ℝ)) := by
  rw [frozenRowTransfer, Real.sqrt_div (Nat.cast_nonneg _) _, Real.sqrt_mul (planarPairFactor_pos p).le]
  ring

theorem frozenRowLeading_pair_single (Q t i : ℕ) (y : ℝ) :
    frozenRowLeading t y * certificatePairCoefficient Q t * certificateSingleCoefficient Q i =
      y*Real.sqrt (i.factorial : ℝ)/(spherePairRoot Q t*sphereOrbitalRoot Q i) := by
  rw [frozenRowLeading, certificatePairCoefficient_eq_roots, certificateSingleCoefficient_eq_roots]
  have hp : Real.sqrt (planarPairFactor t)≠0 := (Real.sqrt_pos.mpr (planarPairFactor_pos t)).ne'
  field_simp

theorem frozenRowTransfer_pair_single (Q p i j : ℕ) (y : ℝ) :
    frozenRowTransfer p i j y * certificatePairCoefficient Q p * certificateSingleCoefficient Q j =
      y*Real.sqrt (i.factorial : ℝ)/(spherePairRoot Q p*sphereOrbitalRoot Q j) := by
  rw [frozenRowTransfer_eq_roots, certificatePairCoefficient_eq_roots, certificateSingleCoefficient_eq_roots]
  have hp : Real.sqrt (planarPairFactor p)≠0 := (Real.sqrt_pos.mpr (planarPairFactor_pos p)).ne'
  have hj : Real.sqrt (j.factorial : ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos j)).ne'
  field_simp

theorem directRow_three_cross_factor (Q t p i j : ℕ) (y0 y : ℝ) :
    (frozenRowLeading t y0 * certificatePairCoefficient Q t * certificateSingleCoefficient Q i) *
      (frozenRowTransfer p i j y * certificatePairCoefficient Q p * certificateSingleCoefficient Q j) =
        y0*y*directRowFactor Q p i j / spherePairRoot Q t := by
  rw [frozenRowLeading_pair_single, frozenRowTransfer_pair_single]
  have hs : Real.sqrt (i.factorial : ℝ)^2=(i.factorial : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  calc
    _ = y0*y*(Real.sqrt (i.factorial : ℝ)^2) /
      (spherePairRoot Q p*sphereOrbitalRoot Q i*sphereOrbitalRoot Q j*spherePairRoot Q t) := by ring
    _ = _ := by rw [hs]; unfold directRowFactor; ring

theorem directRow_three_contraction_factor (Q p q i j l : ℕ) (y z : ℝ) :
    (frozenRowTransfer p i j y * certificatePairCoefficient Q p * certificateSingleCoefficient Q j) *
      (frozenRowTransfer q i l z * certificatePairCoefficient Q q * certificateSingleCoefficient Q l) =
        y*z*(i.factorial : ℝ) /
          (spherePairRoot Q p*spherePairRoot Q q*sphereOrbitalRoot Q j*sphereOrbitalRoot Q l) := by
  rw [frozenRowTransfer_pair_single, frozenRowTransfer_pair_single]
  have hs : Real.sqrt (i.factorial : ℝ)^2=(i.factorial : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  calc
    _ = y*z*(Real.sqrt (i.factorial : ℝ)^2) /
      (spherePairRoot Q p*spherePairRoot Q q*sphereOrbitalRoot Q j*sphereOrbitalRoot Q l) := by ring
    _ = _ := by rw [hs]

theorem directRow_four_factor (Q p q i j k l : ℕ) (y z : ℝ) :
    (frozenRowTransfer p i j y * certificatePairCoefficient Q p *
      certificateSingleCoefficient Q j * certificateSingleCoefficient Q k) *
    (frozenRowTransfer q k l z * certificatePairCoefficient Q q *
      certificateSingleCoefficient Q l * certificateSingleCoefficient Q i) =
        y*z*directRowFactor Q p i j*directRowFactor Q q k l := by
  rw [frozenRowTransfer_pair_single, frozenRowTransfer_pair_single,
    certificateSingleCoefficient_eq_roots, certificateSingleCoefficient_eq_roots]
  have hi : Real.sqrt (i.factorial : ℝ)^2=(i.factorial : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hk : Real.sqrt (k.factorial : ℝ)^2=(k.factorial : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  calc
    _ = y*z*(Real.sqrt (i.factorial : ℝ)^2)*(Real.sqrt (k.factorial : ℝ)^2) /
      (spherePairRoot Q p*sphereOrbitalRoot Q i*sphereOrbitalRoot Q j *
       spherePairRoot Q q*sphereOrbitalRoot Q k*sphereOrbitalRoot Q l) := by ring
    _ = _ := by rw [hi,hk]; unfold directRowFactor; ring

end
end BosonicLaughlin

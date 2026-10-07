import BosonicLaughlin.OccupationMetric
import BosonicLaughlin.OccupationWeightCoordinates
import BosonicLaughlin.OccupationSphereMetric
import BosonicLaughlin.PolynomialMetric

/-! The exact inherited metric of factorial-scaled occupation coefficients. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem polynomialOccupationInclude_inner {Q N : ℕ} (c e : OccupationState Q N) :
    polynomialInner (polynomialOccupationInclude c) (polynomialOccupationInclude e) =
      (N.factorial : ℂ) * ∑ A : Occupation Q N,
        ((occupationFactorial A : ℂ) / (occupationBinomialProduct A : ℂ)) * star (c A) * e A := by
  rw [polynomialInner_diagonal]
  have ht (a : Configuration Q N) :
      star (polynomialOccupationInclude c a) * polynomialOccupationInclude e a /
        (polynomialScale a : ℂ)^2 =
      (((occupationFactorial (occupationOfConfiguration a) : ℂ)^2 /
        (occupationBinomialProduct (occupationOfConfiguration a) : ℂ)) *
        star (c (occupationOfConfiguration a)) * e (occupationOfConfiguration a)) := by
    rw [← Complex.ofReal_pow, polynomialScale_sq_eq_occupationBinomialProduct]
    simp only [polynomialOccupationInclude, star_mul, star_natCast]
    ring
  simp_rw [ht]
  rw [← Fintype.sum_fiberwise' (@occupationOfConfiguration Q N)
    (fun A => ((occupationFactorial A : ℂ)^2 / (occupationBinomialProduct A : ℂ)) *
      star (c A) * e A)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  have hc : (occupationOrbitMultiplicity A : ℂ) * (occupationFactorial A : ℂ) =
      (N.factorial : ℂ) := by
    exact_mod_cast occupationOrbitMultiplicity_mul_factorial A
  change (occupationOrbitMultiplicity A : ℂ) * _ = _
  calc
    _ = ((occupationOrbitMultiplicity A : ℂ) * (occupationFactorial A : ℂ)) *
        ((occupationFactorial A : ℂ) / (occupationBinomialProduct A : ℂ)) * star (c A) * e A := by ring
    _ = _ := by rw [hc]; ring

theorem occupationWeightExtend_sum {Q N d : ℕ} (f : Occupation Q N → ℂ)
    (c e : WeightOccupationState Q N d) :
    (∑ A : Occupation Q N, f A * star (occupationWeightExtend d c A) *
      occupationWeightExtend d e A) =
      ∑ A : WeightOccupation Q N d, f A.val * star (c A) * e A := by
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun A : Occupation Q N => occupationWeight A=d)
    (fun A => f A * star (occupationWeightExtend d c A) * occupationWeightExtend d e A)
  have hp : (∑ A : WeightOccupation Q N d,
      f A.val * star (occupationWeightExtend d c A.val) * occupationWeightExtend d e A.val) =
      ∑ A : WeightOccupation Q N d, f A.val * star (c A) * e A := by
    apply Finset.sum_congr rfl
    intro A _
    simp [occupationWeightExtend, A.property]
  have hn : (∑ A : {A : Occupation Q N // ¬ occupationWeight A=d},
      f A.val * star (occupationWeightExtend d c A.val) * occupationWeightExtend d e A.val) = 0 := by
    apply Finset.sum_eq_zero
    intro A _
    simp [occupationWeightExtend, A.property]
  rw [hp, hn, add_zero] at h
  exact h.symm

theorem polynomialOccupationInclude_weight_inner {Q N d : ℕ}
    (c e : WeightOccupationState Q N d) :
    polynomialInner (polynomialOccupationInclude (occupationWeightExtend d c))
      (polynomialOccupationInclude (occupationWeightExtend d e)) =
      (N.factorial : ℂ) * ∑ A : WeightOccupation Q N d,
        ((occupationFactorial A.val : ℂ) / (occupationBinomialProduct A.val : ℂ)) *
          star (c A) * e A := by
  rw [polynomialOccupationInclude_inner, occupationWeightExtend_sum]

end
end BosonicLaughlin

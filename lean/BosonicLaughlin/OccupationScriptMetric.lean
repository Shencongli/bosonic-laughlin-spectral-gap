import BosonicLaughlin.OccupationSphereMetric

/-! Count-powered formulas for the script's metric, derived from the actual
occupation multiset products. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem occupation_product_count {Q N : ℕ} (A : Occupation Q N)
    {M : Type*} [CommMonoid M] (f : Orbital Q → M) :
    (A.val.map f).prod = ∏ j : Orbital Q, f j ^ A.val.count j := by
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro j _ hj
  rw [Multiset.count_eq_zero.mpr (by simpa only [Multiset.mem_toFinset] using hj)]
  exact pow_zero _

theorem occupationOrbitalFactorial_count {Q N : ℕ} (A : Occupation Q N) :
    occupationOrbitalFactorial A =
      ∏ j : Orbital Q, (j.val.factorial : ℝ) ^ A.val.count j :=
  occupation_product_count A _

theorem occupationSphereProduct_count {Q N : ℕ} (A : Occupation Q N) :
    occupationSphereProduct A =
      ∏ j : Orbital Q, sphereFactor Q j.val ^ A.val.count j :=
  occupation_product_count A _

/-- The uncorrected metric g_A = product_j n_j! (j!)^n_j in the script. -/
def occupationPlanarMetric {Q N : ℕ} (A : Occupation Q N) : ℝ :=
  ∏ j : Orbital Q, ((A.val.count j).factorial : ℝ) * (j.val.factorial : ℝ)^A.val.count j

theorem occupationPlanarMetric_eq {Q N : ℕ} (A : Occupation Q N) :
    occupationPlanarMetric A = (occupationFactorial A : ℝ) * occupationOrbitalFactorial A := by
  rw [occupationPlanarMetric, Finset.prod_mul_distrib, ← occupationOrbitalFactorial_count]
  simp [occupationFactorial, multisetOccupationFactorial]

theorem occupation_metric_script_factor {Q N : ℕ} (hQ : 0<Q) (A : Occupation Q N) :
    (Q : ℝ)^(occupationWeight A) * (occupationFactorial A : ℝ) /
      occupationBinomialProduct A =
      occupationPlanarMetric A / occupationSphereProduct A := by
  rw [occupationPlanarMetric_eq]
  exact occupation_metric_factor hQ A

end
end BosonicLaughlin

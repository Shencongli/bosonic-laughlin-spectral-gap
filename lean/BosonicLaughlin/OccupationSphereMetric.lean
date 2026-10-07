import BosonicLaughlin.OccupationPairChannels
import BosonicLaughlin.CertificateNormalization

/-! Exact diagonal factors of the spherical occupation-coordinate metric. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def occupationBinomialProduct {Q N : ℕ} (A : Occupation Q N) : ℝ :=
  (A.val.map (fun j => (Q.choose j.val : ℝ))).prod

def occupationOrbitalFactorial {Q N : ℕ} (A : Occupation Q N) : ℝ :=
  (A.val.map (fun j => (j.val.factorial : ℝ))).prod

def occupationSphereProduct {Q N : ℕ} (A : Occupation Q N) : ℝ :=
  (A.val.map (fun j => sphereFactor Q j.val)).prod

theorem occupationBinomialProduct_pos {Q N : ℕ} (A : Occupation Q N) :
    0 < occupationBinomialProduct A := by
  apply Multiset.prod_pos
  intro r hr
  obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hr
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ j.isLt)

theorem occupationSphereProduct_pos {Q N : ℕ} (hQ : 0 < Q) (A : Occupation Q N) :
    0 < occupationSphereProduct A := by
  apply Multiset.prod_pos
  intro r hr
  obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hr
  exact sphereFactor_pos hQ (Nat.le_of_lt_succ j.isLt)

theorem multiset_factorial_choose_product {Q : ℕ} (hQ : 0 < Q)
    (A : Multiset (Orbital Q)) :
    (A.map (fun j => (j.val.factorial : ℝ))).prod *
        (A.map (fun j => (Q.choose j.val : ℝ))).prod =
      (Q : ℝ)^(A.map Fin.val).sum * (A.map (fun j => sphereFactor Q j.val)).prod := by
  induction A using Multiset.induction_on with
  | empty => simp
  | @cons j A ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, pow_add]
    have hj := factorial_mul_choose_eq_sphereFactor hQ (Nat.le_of_lt_succ j.isLt)
    calc
      _ = ((j.val.factorial : ℝ) * (Q.choose j.val : ℝ)) *
          ((A.map (fun k => (k.val.factorial : ℝ))).prod *
            (A.map (fun k => (Q.choose k.val : ℝ))).prod) := by ring
      _ = _ := by rw [hj, ih]; ring

theorem occupation_factorial_choose_product {Q N : ℕ} (hQ : 0 < Q)
    (A : Occupation Q N) :
    occupationOrbitalFactorial A * occupationBinomialProduct A =
      (Q : ℝ)^(occupationWeight A) * occupationSphereProduct A :=
  multiset_factorial_choose_product hQ A.val

theorem polynomialScale_sq_eq_occupationBinomialProduct {Q N : ℕ}
    (a : Configuration Q N) :
    polynomialScale a ^ 2 = occupationBinomialProduct (occupationOfConfiguration a) := by
  simp [polynomialScale, occupationBinomialProduct, occupationOfConfiguration,
    List.map_ofFn, List.prod_ofFn, ← Finset.prod_pow, binomialRoot_sq]

theorem occupation_metric_factor {Q N : ℕ} (hQ : 0 < Q) (A : Occupation Q N) :
    (Q : ℝ)^(occupationWeight A) * (occupationFactorial A : ℝ) /
        occupationBinomialProduct A =
      (occupationFactorial A : ℝ) * occupationOrbitalFactorial A /
        occupationSphereProduct A := by
  apply (div_eq_div_iff (occupationBinomialProduct_pos A).ne'
    (occupationSphereProduct_pos hQ A).ne').mpr
  have h := occupation_factorial_choose_product hQ A
  linear_combination -(occupationFactorial A : ℝ) * h

end
end BosonicLaughlin

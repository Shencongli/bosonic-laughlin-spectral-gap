import BosonicLaughlin.FockInner
import BosonicLaughlin.PolynomialMetric

/-! Exact Hamiltonian matrix elements in the nonorthonormal polynomial metric. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem v0PairAnnihilate_polynomial_inverse {Q N : ℕ} (p : Fin (2*Q+1))
    (χ : State Q (N+2)) :
    v0PairAnnihilate p ((polynomialCoordinates Q (N+2)).symm χ) =
      ((Real.sqrt ((N+2).choose 2) / binomialRoot (2*Q) p.val : ℝ) : ℂ) •
        (polynomialCoordinates Q N).symm (polynomialPairChannel p.val χ) := by
  have hr : (binomialRoot (2*Q) p.val : ℂ) ≠ 0 := by
    exact_mod_cast (binomialRoot_pos (2*Q) p.val (by omega)).ne'
  have he := polynomialPairChannel_annihilate p ((polynomialCoordinates Q (N+2)).symm χ)
  rw [LinearEquiv.apply_symm_apply] at he
  apply (polynomialCoordinates Q N).injective
  rw [map_smul, LinearEquiv.apply_symm_apply]
  funext a
  have ha := congrFun he a
  simp only [Pi.smul_apply, smul_eq_mul] at ha ⊢
  push_cast
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hr).mpr
  simpa only [mul_comm] using ha.symm

theorem stateInner_real_smul_both {Q N : ℕ} (c : ℝ) (ψ φ : State Q N) :
    inner ((c : ℂ) • ψ) ((c : ℂ) • φ) = (c^2 : ℝ) * inner ψ φ := by
  rw [stateInner_smul_left, stateInner_smul_right, ← mul_assoc]
  simp [pow_two]

theorem v0PairAnnihilate_polynomial_inner {Q N : ℕ} (p : Fin (2*Q+1))
    (χ η : State Q (N+2)) :
    inner (v0PairAnnihilate p ((polynomialCoordinates Q (N+2)).symm χ))
      (v0PairAnnihilate p ((polynomialCoordinates Q (N+2)).symm η)) =
      (((N+2).choose 2 : ℝ) / ((2*Q).choose p.val : ℝ) : ℝ) *
        polynomialInner (polynomialPairChannel p.val χ) (polynomialPairChannel p.val η) := by
  rw [v0PairAnnihilate_polynomial_inverse, v0PairAnnihilate_polynomial_inverse,
    stateInner_real_smul_both]
  rw [div_pow, Real.sq_sqrt (by positivity), binomialRoot_sq]
  rfl

theorem polynomialHamiltonian_gram {Q N : ℕ} (χ η : State Q (N+2))
    (hχ : IsBosonic χ) (hη : IsBosonic η) :
    polynomialInner χ (polynomialHamiltonian Q (N+2) η) =
      ∑ p : Fin (2*Q+1),
        (((N+2).choose 2 : ℝ) / ((2*Q).choose p.val : ℝ) : ℝ) *
          polynomialInner (polynomialPairChannel p.val χ) (polynomialPairChannel p.val η) := by
  have hχ' : IsBosonic ((polynomialCoordinates Q (N+2)).symm χ) := by
    apply (polynomialCoordinates_bosonic_iff _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hχ
  have hη' : IsBosonic ((polynomialCoordinates Q (N+2)).symm η) := by
    apply (polynomialCoordinates_bosonic_iff _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hη
  rw [polynomialHamiltonian_inner,
    hamiltonian_inner_eq_sum_pair_inner _ _ hχ' hη']
  exact Finset.sum_congr rfl (fun p _ => v0PairAnnihilate_polynomial_inner p χ η)

end
end BosonicLaughlin

import BosonicLaughlin.PairLadder
import BosonicLaughlin.FockCorrespondence
import BosonicLaughlin.PhysicalKernel

/-!
Polynomial coefficient coordinates on the full finite spherical tensor space.
The diagonal change of coordinates is invertible but is not declared unitary.
In these coordinates the common pair kernel is given by unweighted sums
over orbital pairs with fixed total label.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def polynomialScale {Q N : ℕ} (a : Configuration Q N) : ℝ :=
  ∏ i : Fin N, binomialRoot Q (a i).val

theorem polynomialScale_pos {Q N : ℕ} (a : Configuration Q N) :
    0 < polynomialScale a := by
  apply Finset.prod_pos
  intro i _
  exact binomialRoot_pos Q (a i).val (by omega)

theorem polynomialScale_ne_zero {Q N : ℕ} (a : Configuration Q N) :
    (polynomialScale a : ℂ) ≠ 0 := by
  exact_mod_cast (polynomialScale_pos a).ne'

theorem polynomialScale_cons {Q N : ℕ} (x : Orbital Q) (a : Configuration Q N) :
    polynomialScale (Fin.cons x a) = binomialRoot Q x.val * polynomialScale a := by
  simp only [polynomialScale, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem polynomialScale_permute {Q N : ℕ} (a : Configuration Q N)
    (σ : Equiv.Perm (Fin N)) : polynomialScale (a ∘ σ) = polynomialScale a :=
  Equiv.prod_comp σ (fun i => binomialRoot Q (a i).val)

/-- Multiplication by the spherical monomial normalization in every tensor slot. -/
def polynomialCoordinates (Q N : ℕ) : State Q N ≃ₗ[ℂ] State Q N where
  toFun ψ := fun a => (polynomialScale a : ℂ) * ψ a
  invFun χ := fun a => (polynomialScale a : ℂ)⁻¹ * χ a
  left_inv ψ := by
    funext a
    simp [← mul_assoc, polynomialScale_ne_zero a]
  right_inv χ := by
    funext a
    simp [← mul_assoc, polynomialScale_ne_zero a]
  map_add' ψ φ := by funext a; simp [mul_add]
  map_smul' c ψ := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem polynomialCoordinates_apply {Q N : ℕ} (ψ : State Q N) (a : Configuration Q N) :
    polynomialCoordinates Q N ψ a = (polynomialScale a : ℂ) * ψ a := rfl

theorem polynomialCoordinates_bosonic_iff {Q N : ℕ} (ψ : State Q N) :
    IsBosonic (polynomialCoordinates Q N ψ) ↔ IsBosonic ψ := by
  constructor
  · intro h σ a
    have ha := h σ a
    simp only [polynomialCoordinates_apply, polynomialScale_permute] at ha
    exact mul_left_cancel₀ (polynomialScale_ne_zero a) ha
  · intro h σ a
    simp only [polynomialCoordinates_apply, polynomialScale_permute, h σ a]

/-- Polynomial pair-coincidence coefficient, before any occupation-basis quotient. -/
def polynomialPairChannel {Q N : ℕ} (p : ℕ) (χ : State Q (N+2)) : State Q N :=
  fun a => ∑ x : Orbital Q, ∑ y : Orbital Q,
    if x.val + y.val = p then χ (Fin.cons x (Fin.cons y a)) else 0

theorem polynomialPairChannel_add {Q N : ℕ} (p : ℕ) (χ η : State Q (N+2)) :
    polynomialPairChannel p (χ+η) = polynomialPairChannel p χ + polynomialPairChannel p η := by
  funext a
  simp [polynomialPairChannel, ite_add_zero, Finset.sum_add_distrib]

theorem polynomialPairChannel_smul {Q N : ℕ} (p : ℕ) (c : ℂ) (χ : State Q (N+2)) :
    polynomialPairChannel p (c • χ) = c • polynomialPairChannel p χ := by
  funext a
  simp [polynomialPairChannel, Finset.mul_sum, mul_ite]

def polynomialPairChannelLinear (Q N p : ℕ) : State Q (N+2) →ₗ[ℂ] State Q N where
  toFun := polynomialPairChannel p
  map_add' := polynomialPairChannel_add p
  map_smul' := polynomialPairChannel_smul p

theorem pairVector_polynomial_scale (Q : ℕ) (p : Fin (2*Q+1)) (x y : Orbital Q) :
    (binomialRoot (2*Q) p.val : ℂ) * (pairVector Q p.val x y : ℂ) =
      if x.val + y.val = p.val then
        (binomialRoot Q x.val : ℂ) * (binomialRoot Q y.val : ℂ) else 0 := by
  have hd : (binomialRoot (2*Q) p.val : ℂ) ≠ 0 := by
    exact_mod_cast (binomialRoot_pos (2*Q) p.val (by omega)).ne'
  rw [pairVector_binomialRoot]
  split_ifs with h
  · push_cast
    field_simp
  · simp

theorem polynomialPairChannel_amplitude {Q N : ℕ} (p : Fin (2*Q+1))
    (ψ : State Q (N+2)) :
    polynomialPairChannel p.val (polynomialCoordinates Q (N+2) ψ) =
      (binomialRoot (2*Q) p.val : ℂ) •
        polynomialCoordinates Q N (v0PairAmplitude p ψ) := by
  funext a
  simp only [polynomialPairChannel, polynomialCoordinates_apply, Pi.smul_apply, smul_eq_mul,
    v0PairAmplitude, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [show (binomialRoot (2*Q) p.val : ℂ) *
      ((polynomialScale a : ℂ) * ((pairVector Q p.val x y : ℂ) *
        ψ (Fin.cons x (Fin.cons y a)))) =
      ((binomialRoot (2*Q) p.val : ℂ) * (pairVector Q p.val x y : ℂ)) *
        (polynomialScale a : ℂ) * ψ (Fin.cons x (Fin.cons y a)) by ring,
    pairVector_polynomial_scale]
  split_ifs with h
  · simp only [polynomialScale_cons, Complex.ofReal_mul]
    ring
  · simp

theorem polynomialPairChannel_annihilate {Q N : ℕ} (p : Fin (2*Q+1))
    (ψ : State Q (N+2)) :
    (Real.sqrt ((N+2).choose 2) : ℂ) •
        polynomialPairChannel p.val (polynomialCoordinates Q (N+2) ψ) =
      (binomialRoot (2*Q) p.val : ℂ) •
        polynomialCoordinates Q N (v0PairAnnihilate p ψ) := by
  rw [polynomialPairChannel_amplitude]
  have hb : v0PairAnnihilate p ψ =
      (Real.sqrt ((N+2).choose 2) : ℂ) • v0PairAmplitude p ψ := rfl
  rw [hb, map_smul]
  exact smul_comm _ _ _

theorem polynomialPairChannel_zero_iff {Q N : ℕ} (p : Fin (2*Q+1))
    (ψ : State Q (N+2)) :
    polynomialPairChannel p.val (polynomialCoordinates Q (N+2) ψ) = 0 ↔
      v0PairAnnihilate p ψ = 0 := by
  have hd : (binomialRoot (2*Q) p.val : ℂ) ≠ 0 := by
    exact_mod_cast (binomialRoot_pos (2*Q) p.val (by omega)).ne'
  have hn : (Real.sqrt ((N+2).choose 2) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply (Real.sqrt_pos.mpr _).ne'
    exact_mod_cast Nat.choose_pos (show 2 ≤ N+2 by omega)
  have he := polynomialPairChannel_annihilate p ψ
  constructor
  · intro h
    rw [h, smul_zero] at he
    have hc : polynomialCoordinates Q N (v0PairAnnihilate p ψ) = 0 :=
      (smul_eq_zero.mp he.symm).resolve_left hd
    exact (polynomialCoordinates Q N).injective (by simpa using hc)
  · intro h
    rw [h, map_zero, smul_zero] at he
    exact (smul_eq_zero.mp he).resolve_left hn

/-- Actual physical zero modes are exactly the common unweighted polynomial pair kernel. -/
theorem hamiltonian_zero_iff_polynomialPairChannels {Q N : ℕ}
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    hamiltonian ψ = 0 ↔ ∀ p : Fin (2*Q+1),
      polynomialPairChannel p.val (polynomialCoordinates Q (N+2) ψ) = 0 := by
  rw [hamiltonian_zero_iff_v0PairAnnihilate_zero ψ hψ]
  exact forall_congr' (fun p => (polynomialPairChannel_zero_iff p ψ).symm)

end
end BosonicLaughlin

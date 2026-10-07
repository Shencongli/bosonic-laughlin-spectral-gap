import BosonicLaughlin.PairLadder
import BosonicLaughlin.AngularMomentum

/-! Equivariance of the concrete normalized V₀ pair insertion. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem insertion_raise_first {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) (hp : x.val+y.val < 2*Q) :
    spinRaise (fun a => threeBodyInsertion φ a y z) x =
      ((spinRaiseCoeff Q x.val *
        (binomialRoot Q (x.val+1) * binomialRoot Q y.val /
          binomialRoot (2*Q) (x.val+y.val+1)) : ℝ) : ℂ) *
        φ ⟨x.val+y.val+1, by omega⟩ z := by
  unfold spinRaise
  split_ifs with hx
  · dsimp only
    rw [threeBodyInsertion_single]
    simp only [Fin.val_mk, Nat.add_assoc, Nat.add_left_comm 1 y.val,
      Complex.ofReal_mul, Complex.ofReal_div]
    ring
  · have hxe : x.val=Q := by omega
    simp [spinRaiseCoeff, hxe]

theorem insertion_raise_second {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) (hp : x.val+y.val < 2*Q) :
    spinRaise (fun a => threeBodyInsertion φ x a z) y =
      ((spinRaiseCoeff Q y.val *
        (binomialRoot Q x.val * binomialRoot Q (y.val+1) /
          binomialRoot (2*Q) (x.val+y.val+1)) : ℝ) : ℂ) *
        φ ⟨x.val+y.val+1, by omega⟩ z := by
  simp_rw [threeBodyInsertion_exchange φ x]
  simpa only [Nat.add_comm y.val x.val,
    mul_comm (binomialRoot Q (y.val+1)) (binomialRoot Q x.val)] using
    insertion_raise_first φ y x z (by omega)

theorem threeBodyInsertion_pair_raise {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) :
    threeBodyInsertion (fun p k => spinRaise (fun q => φ q k) p) x y z =
      spinRaise (fun a => threeBodyInsertion φ a y z) x +
      spinRaise (fun a => threeBodyInsertion φ x a z) y := by
  by_cases hp : x.val+y.val < 2*Q
  · rw [insertion_raise_first φ x y z hp, insertion_raise_second φ x y z hp]
    rw [threeBodyInsertion_single]
    simp only [spinRaise, Fin.val_mk, hp, dite_true]
    rw [← add_mul, ← Complex.ofReal_add]
    have he := pair_roots_raise Q x.val y.val (by omega) (by omega) hp
    unfold spinRaiseCoeff
    rw [he]
    simp only [Complex.ofReal_mul]
    ring
  · have hx : x.val=Q := by omega
    have hy : y.val=Q := by omega
    rw [threeBodyInsertion_single]
    simp only [spinRaise, Fin.val_mk, hx, hy, lt_self_iff_false, dite_false, add_zero]
    simp [show ¬Q+Q<2*Q by omega]

theorem insertion_lower_first {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) (hp : 0 < x.val+y.val) :
    spinLower (fun a => threeBodyInsertion φ a y z) x =
      ((x.val : ℂ) *
        ((binomialRoot Q x.val * binomialRoot Q y.val /
          binomialRoot (2*Q) (x.val+y.val-1) : ℝ) : ℂ)) *
        φ ⟨x.val+y.val-1, by omega⟩ z := by
  unfold spinLower
  split_ifs with hx
  · dsimp only
    rw [threeBodyInsertion_single]
    have he : x.val-1+y.val=x.val+y.val-1 := by omega
    simp only [Fin.val_mk, he, Complex.ofReal_mul, Complex.ofReal_div]
    have ha := binomialRoot_ladder_right Q (x.val-1)
    rw [show x.val-1+1=x.val by omega] at ha
    have haC : (spinRaiseCoeff Q (x.val-1) : ℂ) * (binomialRoot Q (x.val-1) : ℂ) =
        (x.val : ℂ) * (binomialRoot Q x.val : ℂ) := by
      unfold spinRaiseCoeff
      rw [show x.val-1+1=x.val by omega]
      exact_mod_cast ha
    linear_combination
      (binomialRoot Q y.val : ℂ) / (binomialRoot (2*Q) (x.val+y.val-1) : ℂ) *
        φ ⟨x.val+y.val-1, by omega⟩ z * haC
  · have hx0 : x.val=0 := by omega
    simp [hx0]

theorem insertion_lower_second {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) (hp : 0 < x.val+y.val) :
    spinLower (fun a => threeBodyInsertion φ x a z) y =
      ((y.val : ℂ) *
        ((binomialRoot Q x.val * binomialRoot Q y.val /
          binomialRoot (2*Q) (x.val+y.val-1) : ℝ) : ℂ)) *
        φ ⟨x.val+y.val-1, by omega⟩ z := by
  simp_rw [threeBodyInsertion_exchange φ x]
  simpa only [Nat.add_comm y.val x.val,
    mul_comm (binomialRoot Q y.val) (binomialRoot Q x.val)] using
    insertion_lower_first φ y x z (by omega)

theorem threeBodyInsertion_pair_lower {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) :
    threeBodyInsertion (fun p k => spinLower (fun q => φ q k) p) x y z =
      spinLower (fun a => threeBodyInsertion φ a y z) x +
      spinLower (fun a => threeBodyInsertion φ x a z) y := by
  by_cases hp : 0 < x.val+y.val
  · rw [insertion_lower_first φ x y z hp, insertion_lower_second φ x y z hp]
    rw [threeBodyInsertion_single]
    simp only [spinLower, Fin.val_mk, hp, dite_true]
    have he := binomialRoot_lower_ratio (2*Q) (x.val+y.val) hp (by omega)
    have heC : ((x.val+y.val : ℕ) : ℂ) / (binomialRoot (2*Q) (x.val+y.val-1) : ℂ) =
        (spinRaiseCoeff (2*Q) (x.val+y.val-1) : ℂ) /
          (binomialRoot (2*Q) (x.val+y.val) : ℂ) := by
      unfold spinRaiseCoeff
      rw [show x.val+y.val-1+1=x.val+y.val by omega]
      exact_mod_cast he
    simp only [Nat.cast_add] at heC
    simp only [Complex.ofReal_div, Complex.ofReal_mul]
    linear_combination
      -(binomialRoot Q x.val : ℂ) * (binomialRoot Q y.val : ℂ) *
        φ ⟨x.val+y.val-1, by omega⟩ z * heC
  · have hx : x.val=0 := by omega
    have hy : y.val=0 := by omega
    rw [threeBodyInsertion_single]
    simp [spinLower, hx, hy]

/-- Total raising operator on the full three-slot tensor space. -/
def tensorRaiseThree {Q : ℕ} (ψ : Orbital Q → Orbital Q → Orbital Q → ℂ)
    (x y z : Orbital Q) : ℂ :=
  spinRaise (fun a => ψ a y z) x + spinRaise (fun a => ψ x a z) y +
    spinRaise (ψ x y) z

theorem threeBodyInsertion_spectator_raise {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) :
    threeBodyInsertion (fun p k => spinRaise (φ p) k) x y z =
      spinRaise (threeBodyInsertion φ x y) z := by
  rw [threeBodyInsertion_single]
  unfold spinRaise
  split_ifs with hz
  · rw [threeBodyInsertion_single]
    ring
  · ring

theorem threeBodyInsertion_auxRaise {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) :
    threeBodyInsertion (auxRaise φ) x y z =
      tensorRaiseThree (threeBodyInsertion φ) x y z := by
  have hadd : threeBodyInsertion (auxRaise φ) x y z =
      threeBodyInsertion (fun p k => spinRaise (fun q => φ q k) p) x y z +
      threeBodyInsertion (fun p k => spinRaise (φ p) k) x y z := by
    simp only [auxRaise, threeBodyInsertion, mul_add, Finset.sum_add_distrib]
  rw [hadd, threeBodyInsertion_pair_raise, threeBodyInsertion_spectator_raise]
  rfl

theorem tensorRaiseThree_swap23 {Q : ℕ}
    (ψ : Orbital Q → Orbital Q → Orbital Q → ℂ) (x y z : Orbital Q) :
    tensorRaiseThree (fun a b c => ψ a c b) x y z = tensorRaiseThree ψ x z y := by
  simp only [tensorRaiseThree]
  ring

end
end BosonicLaughlin

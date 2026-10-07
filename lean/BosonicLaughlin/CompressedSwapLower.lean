import BosonicLaughlin.CompressedSwapEquivariance
import BosonicLaughlin.AngularCommutators
import BosonicLaughlin.SwapStructure

/-! Exact lowering equivariance of the concrete compressed exchange. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def tensorLowerThree {Q : ℕ} (ψ : Orbital Q → Orbital Q → Orbital Q → ℂ)
    (x y z : Orbital Q) : ℂ :=
  spinLower (fun a => ψ a y z) x + spinLower (fun a => ψ x a z) y +
    spinLower (ψ x y) z

theorem threeBodyInsertion_spectator_lower {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) :
    threeBodyInsertion (fun p k => spinLower (φ p) k) x y z =
      spinLower (threeBodyInsertion φ x y) z := by
  rw [threeBodyInsertion_single]
  unfold spinLower
  split_ifs with hz
  · rw [threeBodyInsertion_single]
    ring
  · ring

theorem threeBodyInsertion_auxLower {Q : ℕ} (φ : ThreeBodyAux Q)
    (x y z : Orbital Q) :
    threeBodyInsertion (auxLower φ) x y z =
      tensorLowerThree (threeBodyInsertion φ) x y z := by
  have hadd : threeBodyInsertion (auxLower φ) x y z =
      threeBodyInsertion (fun p k => spinLower (fun q => φ q k) p) x y z +
      threeBodyInsertion (fun p k => spinLower (φ p) k) x y z := by
    simp only [auxLower, threeBodyInsertion, mul_add, Finset.sum_add_distrib]
  rw [hadd, threeBodyInsertion_pair_lower, threeBodyInsertion_spectator_lower]
  rfl

theorem tensorLowerThree_swap23 {Q : ℕ}
    (ψ : Orbital Q → Orbital Q → Orbital Q → ℂ) (x y z : Orbital Q) :
    tensorLowerThree (fun a b c => ψ a c b) x y z = tensorLowerThree ψ x z y := by
  simp only [tensorLowerThree]
  ring

theorem threeBodyContract_spectator_lower {Q : ℕ}
    (ψ : Orbital Q → Orbital Q → Orbital Q → ℂ) (p : Fin (2*Q+1)) (k : Orbital Q) :
    pairContract (fun x y => spinLower (ψ x y) k) p =
      spinLower (threeBodyContract ψ p) k := by
  unfold spinLower
  split_ifs with hk
  · simp only [pairContract, threeBodyContract]
    simp_rw [mul_left_comm (pairVector Q p.val _ _ : ℂ) (spinRaiseCoeff Q (k.val-1) : ℂ),
      ← Finset.mul_sum]
  · simp [pairContract]

theorem threeBodyContract_lower {Q : ℕ}
    (ψ : Orbital Q → Orbital Q → Orbital Q → ℂ) :
    threeBodyContract (tensorLowerThree ψ) = auxLower (threeBodyContract ψ) := by
  funext p k
  have hpair := congrFun (pairContract_lower (fun x y => ψ x y k)) p
  have hsplit : threeBodyContract (tensorLowerThree ψ) p k =
      pairContract (fun x y => spinLower (fun a => ψ a y k) x +
        spinLower (fun a => ψ x a k) y) p +
      pairContract (fun x y => spinLower (ψ x y) k) p := by
    simp only [threeBodyContract, tensorLowerThree, pairContract, mul_add,
      Finset.sum_add_distrib]
  rw [hsplit, hpair, threeBodyContract_spectator_lower]
  rfl

theorem compressedSwap_auxLower {Q : ℕ} (φ : ThreeBodyAux Q) :
    compressedSwap (auxLower φ) = auxLower (compressedSwap φ) := by
  rw [compressedSwap_as_contraction, compressedSwap_as_contraction φ]
  have he : (fun x y z => threeBodyInsertion (auxLower φ) x z y) =
      tensorLowerThree (fun x y z => threeBodyInsertion φ x z y) := by
    funext x y z
    rw [threeBodyInsertion_auxLower, tensorLowerThree_swap23]
  rw [he, threeBodyContract_lower]

theorem compressedSwap_auxWeight {Q : ℕ} (φ : ThreeBodyAux Q) :
    compressedSwap (auxWeight φ) = auxWeight (compressedSwap φ) := by
  have hs : compressedSwap (auxRaise (auxLower φ) - auxLower (auxRaise φ)) =
      compressedSwap (auxRaise (auxLower φ)) - compressedSwap (auxLower (auxRaise φ)) :=
    (compressedSwapLinear Q).map_sub _ _
  rw [← auxRaise_lower_commutator φ, hs]
  rw [compressedSwap_auxRaise, compressedSwap_auxLower,
    compressedSwap_auxLower, compressedSwap_auxRaise, auxRaise_lower_commutator]

end
end BosonicLaughlin

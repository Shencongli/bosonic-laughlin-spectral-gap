import BosonicLaughlin.PairContractionEquivariance

/-! The actual compressed exchange commutes with total angular momentum raising. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def threeBodyContract {Q : ℕ} (ψ : Orbital Q → Orbital Q → Orbital Q → ℂ) :
    ThreeBodyAux Q := fun p k => pairContract (fun x y => ψ x y k) p

theorem threeBodyContract_spectator_raise {Q : ℕ}
    (ψ : Orbital Q → Orbital Q → Orbital Q → ℂ) (p : Fin (2*Q+1)) (k : Orbital Q) :
    pairContract (fun x y => spinRaise (ψ x y) k) p =
      spinRaise (threeBodyContract ψ p) k := by
  unfold spinRaise
  split_ifs with hk
  · simp only [pairContract, threeBodyContract]
    simp_rw [mul_left_comm (pairVector Q p.val _ _ : ℂ) (spinRaiseCoeff Q k.val : ℂ),
      ← Finset.mul_sum]
  · simp [pairContract]

theorem threeBodyContract_raise {Q : ℕ}
    (ψ : Orbital Q → Orbital Q → Orbital Q → ℂ) :
    threeBodyContract (tensorRaiseThree ψ) = auxRaise (threeBodyContract ψ) := by
  funext p k
  have hpair := congrFun (pairContract_raise (fun x y => ψ x y k)) p
  have hsplit : threeBodyContract (tensorRaiseThree ψ) p k =
      pairContract (fun x y => spinRaise (fun a => ψ a y k) x +
        spinRaise (fun a => ψ x a k) y) p +
      pairContract (fun x y => spinRaise (ψ x y) k) p := by
    simp only [threeBodyContract, tensorRaiseThree, pairContract, mul_add,
      Finset.sum_add_distrib]
  rw [hsplit, hpair, threeBodyContract_spectator_raise]
  rfl

theorem compressedSwap_as_contraction {Q : ℕ} (φ : ThreeBodyAux Q) :
    compressedSwap φ =
      threeBodyContract (fun x y z => threeBodyInsertion φ x z y) := by
  funext p k
  simp only [compressedSwap, threeBodyContract, pairContract, threeBodyInsertion,
    Finset.mul_sum, mul_assoc]

/-- Exact equivariance for the concrete binomial-kernel compressed swap. -/
theorem compressedSwap_auxRaise {Q : ℕ} (φ : ThreeBodyAux Q) :
    compressedSwap (auxRaise φ) = auxRaise (compressedSwap φ) := by
  rw [compressedSwap_as_contraction, compressedSwap_as_contraction φ]
  have he : (fun x y z => threeBodyInsertion (auxRaise φ) x z y) =
      tensorRaiseThree (fun x y z => threeBodyInsertion φ x z y) := by
    funext x y z
    rw [threeBodyInsertion_auxRaise, tensorRaiseThree_swap23]
  rw [he, threeBodyContract_raise]

end
end BosonicLaughlin

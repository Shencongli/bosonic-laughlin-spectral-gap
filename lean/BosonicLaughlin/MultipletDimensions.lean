import BosonicLaughlin.AngularMultiplets
import BosonicLaughlin.SwapSpectrum
import BosonicLaughlin.CompressedSwapLower
import BosonicLaughlin.RecouplingValues
import BosonicLaughlin.MultipletCount
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Concrete lowering descendants and their dimensions in the actual exchange eigenspaces. -/
namespace BosonicLaughlin
noncomputable section
open Module

theorem auxLower_power_nonzero {Q : ℕ} (φ : ThreeBodyAux Q) (m : ℕ)
    (hφ : φ ≠ 0) (he : auxRaise φ = 0) (hw : auxWeight φ = (m : ℂ) • φ)
    (n : ℕ) (hn : n ≤ m) : (auxLowerLinear Q ^ n) φ ≠ 0 := by
  induction n with
  | zero => simpa using hφ
  | succ n ih =>
    intro hzero
    have h := auxRaise_lower_power φ (m : ℂ) he hw n
    rw [hzero, auxRaise_zero] at h
    have hc : (((n + 1 : ℕ) : ℂ) * ((m : ℂ) - (n : ℂ))) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast (Nat.succ_ne_zero n)
      · apply sub_ne_zero.mpr
        exact_mod_cast (show m ≠ n by omega)
    exact (smul_ne_zero hc (ih (by omega))) h.symm

def auxDescendant (Q z n : ℕ) : ThreeBodyAux Q :=
  (auxLowerLinear Q ^ n) (auxHighestWeight Q z)

theorem auxHighestWeight_weight_nat (Q z : ℕ) (hz : z ≤ Q) :
    auxWeight (auxHighestWeight Q z) =
      ((3 * Q - 2 * z : ℕ) : ℂ) • auxHighestWeight Q z := by
  rw [Nat.cast_sub (by omega : 2 * z ≤ 3 * Q)]
  exact auxHighestWeight_weight Q z

theorem auxDescendant_nonzero (Q z n : ℕ) (hz : z ≤ Q) (hn : n ≤ 3 * Q - 2 * z) :
    auxDescendant Q z n ≠ 0 :=
  auxLower_power_nonzero (auxHighestWeight Q z) (3 * Q - 2 * z)
    (auxHighestWeight_nonzero Q z hz) (auxHighestWeight_raise Q z hz)
    (auxHighestWeight_weight_nat Q z hz) n hn

theorem auxDescendant_weight (Q z n : ℕ) (hz : z ≤ Q) :
    auxWeight (auxDescendant Q z n) =
      (((3 * Q - 2 * z : ℕ) : ℂ) - 2 * (n : ℂ)) • auxDescendant Q z n :=
  auxWeight_lower_power (auxHighestWeight Q z) ((3 * Q - 2 * z : ℕ) : ℂ)
    (auxHighestWeight_weight_nat Q z hz) n

theorem auxDescendant_linearIndependent (Q z : ℕ) (hz : z ≤ Q) :
    LinearIndependent ℂ (fun n : Fin (3 * Q - 2 * z + 1) => auxDescendant Q z n.val) := by
  apply Module.End.eigenvectors_linearIndependent' (auxWeightLinear Q)
    (fun n : Fin (3 * Q - 2 * z + 1) =>
      (((3 * Q - 2 * z : ℕ) : ℂ) - 2 * (n.val : ℂ)))
  · intro i j hij
    apply Fin.ext
    have hmul : (2 : ℂ) * (i.val : ℂ) = 2 * (j.val : ℂ) := sub_right_inj.mp hij
    have hc : (i.val : ℂ) = (j.val : ℂ) := mul_left_cancel₀ (by norm_num) hmul
    exact_mod_cast hc
  · intro n
    exact ⟨Module.End.mem_eigenspace_iff.mpr (auxDescendant_weight Q z n.val hz),
      auxDescendant_nonzero Q z n.val hz (by omega)⟩

theorem compressedSwap_descendant (Q z n : ℕ) (hz : z ≤ Q) :
    compressedSwap (auxDescendant Q z n) =
      (recouplingEigenvalue Q z : ℂ) • auxDescendant Q z n := by
  induction n with
  | zero => simpa [auxDescendant] using compressedSwap_highestWeight Q z hz
  | succ n ih =>
    change compressedSwap ((auxLowerLinear Q ^ (n+1)) (auxHighestWeight Q z)) = _
    rw [auxLower_power_succ, compressedSwap_auxLower]
    change auxLower (compressedSwap (auxDescendant Q z n)) = _
    rw [ih, auxLower_smul]
    simp only [auxDescendant, auxLower_power_succ]

theorem compressedSwap_eigenspace_dimension_lower (Q z : ℕ) (hz : z ≤ Q) :
    3 * Q - 2 * z + 1 ≤ Module.finrank ℂ
      (Module.End.eigenspace (compressedSwapLinear Q) (recouplingEigenvalue Q z : ℂ)) := by
  let V := Module.End.eigenspace (compressedSwapLinear Q) (recouplingEigenvalue Q z : ℂ)
  let v : Fin (3 * Q - 2 * z + 1) → V := fun n =>
    ⟨auxDescendant Q z n.val, Module.End.mem_eigenspace_iff.mpr
      (compressedSwap_descendant Q z n.val hz)⟩
  have hli : LinearIndependent ℂ v := by
    apply LinearIndependent.of_comp V.subtype
    exact auxDescendant_linearIndependent Q z hz
  simpa using hli.fintype_card_le_finrank

theorem threeBodyAux_finrank (Q : ℕ) :
    Module.finrank ℂ (ThreeBodyAux Q) = (2 * Q + 1) * (Q + 1) := by
  simp [ThreeBodyAux, Orbital, Module.finrank_pi_fintype]

theorem compressedSwap_eigenspace_dimensions_upper (Q : ℕ) :
    (∑ z : Fin (Q + 1), Module.finrank ℂ
      (Module.End.eigenspace (compressedSwapLinear Q)
        (recouplingEigenvalue Q z.val : ℂ))) ≤ (2 * Q + 1) * (Q + 1) := by
  let E : Fin (Q + 1) → Submodule ℂ (ThreeBodyAux Q) := fun z =>
    Module.End.eigenspace (compressedSwapLinear Q) (recouplingEigenvalue Q z.val : ℂ)
  have hinj : Function.Injective
      (fun z : Fin (Q + 1) => (recouplingEigenvalue Q z.val : ℂ)) := by
    intro a b he
    exact recouplingEigenvalue_injective Q (Complex.ofReal_injective he)
  have hind : iSupIndep E :=
    (Module.End.eigenspaces_iSupIndep (compressedSwapLinear Q)).comp hinj
  have hdim := LinearMap.finrank_le_finrank_of_injective hind.dfinsupp_lsum_injective
  have hsrc : Module.finrank ℂ (Π₀ z, E z) = ∑ z, Module.finrank ℂ (E z) :=
    Module.finrank_directSum (R := ℂ) (fun z => E z)
  rw [hsrc, threeBodyAux_finrank Q] at hdim
  exact hdim

/-- Every signed recoupling eigenvalue has exactly one spin-multiplet dimension. -/
theorem compressedSwap_eigenspace_dimension (Q z : ℕ) (hz : z ≤ Q) :
    Module.finrank ℂ
      (Module.End.eigenspace (compressedSwapLinear Q) (recouplingEigenvalue Q z : ℂ)) =
        3 * Q - 2 * z + 1 := by
  have hl : ∀ i : Fin (Q + 1), 3 * Q - 2 * i.val + 1 ≤ Module.finrank ℂ
      (Module.End.eigenspace (compressedSwapLinear Q) (recouplingEigenvalue Q i.val : ℂ)) :=
    fun i => compressedSwap_eigenspace_dimension_lower Q i.val (by omega)
  have hs : (∑ i : Fin (Q + 1), (3 * Q - 2 * i.val + 1)) =
      ∑ i : Fin (Q + 1), Module.finrank ℂ
        (Module.End.eigenspace (compressedSwapLinear Q) (recouplingEigenvalue Q i.val : ℂ)) := by
    apply le_antisymm
    · exact Finset.sum_le_sum (fun i _ => hl i)
    · rw [multiplet_dimension_sum Q]
      exact compressedSwap_eigenspace_dimensions_upper Q
  exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => hl i)).mp hs
    (⟨z, by omega⟩ : Fin (Q + 1)) (Finset.mem_univ _)).symm

end
end BosonicLaughlin

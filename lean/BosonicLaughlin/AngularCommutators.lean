import BosonicLaughlin.AngularMomentum

/-! The normalized spin algebra and adjoint relations on the auxiliary tensor product. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem spinWeight_raise_commutator {D : ℕ} (ψ : Fin (D+1) → ℂ) :
    spinWeight (spinRaise ψ) - spinRaise (spinWeight ψ) = (2 : ℂ) • spinRaise ψ := by
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, spinWeight, spinRaise]
  split_ifs with hi
  · simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]
    ring
  · ring

theorem spinWeight_lower_commutator {D : ℕ} (ψ : Fin (D+1) → ℂ) :
    spinWeight (spinLower ψ) - spinLower (spinWeight ψ) = (-2 : ℂ) • spinLower ψ := by
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, spinWeight, spinLower]
  split_ifs with hi
  · rw [Nat.cast_sub (by omega : 1 ≤ i.val), Nat.cast_one]
    ring
  · ring

theorem auxLower_add {Q : ℕ} (φ χ : ThreeBodyAux Q) :
    auxLower (φ+χ) = auxLower φ + auxLower χ := by
  funext p k
  change spinLower ((fun q => φ q k) + (fun q => χ q k)) p +
      spinLower (φ p + χ p) k = _
  simp only [spinLower_add, auxLower, Pi.add_apply]
  ring

theorem auxLower_smul {Q : ℕ} (c : ℂ) (φ : ThreeBodyAux Q) :
    auxLower (c • φ) = c • auxLower φ := by
  funext p k
  change spinLower (c • (fun q => φ q k)) p + spinLower (c • φ p) k = _
  simp only [spinLower_smul, auxLower, Pi.smul_apply, smul_eq_mul]
  ring

def auxLowerLinear (Q : ℕ) : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q where
  toFun := auxLower
  map_add' := auxLower_add
  map_smul' := auxLower_smul

theorem auxWeight_apply {Q : ℕ} (φ : ThreeBodyAux Q)
    (p : Fin (2*Q+1)) (k : Orbital Q) :
    auxWeight φ p k = ((3*Q : ℕ) - 2*(p.val+k.val) : ℂ) * φ p k := by
  simp only [auxWeight, spinWeight, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem auxRaise_bilinear {Q : ℕ} (φ χ : ThreeBodyAux Q) :
    (∑ p, ∑ k, φ p k * auxRaise χ p k) =
      ∑ p, ∑ k, auxLower φ p k * χ p k := by
  simp only [auxRaise, auxLower, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm, Finset.sum_comm (f := fun p k => _ * χ p k)]
    apply Finset.sum_congr rfl
    intro k _
    exact spinRaise_bilinear (fun p => φ p k) (fun p => χ p k)
  · apply Finset.sum_congr rfl
    intro p _
    exact spinRaise_bilinear (φ p) (χ p)

theorem auxLower_star {Q : ℕ} (φ : ThreeBodyAux Q) :
    auxLower (fun p k => star (φ p k)) = fun p k => star (auxLower φ p k) := by
  funext p k
  simp only [auxLower, spinLower_star, star_add]

theorem auxRaise_adjoint {Q : ℕ} (φ χ : ThreeBodyAux Q) :
    (∑ p, ∑ k, star (φ p k) * auxRaise χ p k) =
      ∑ p, ∑ k, star (auxLower φ p k) * χ p k := by
  simpa only [auxLower_star] using auxRaise_bilinear (fun p k => star (φ p k)) χ

theorem spinRaise_spinLower_separate {D S : ℕ} (φ : Fin (D+1) → Fin (S+1) → ℂ)
    (p : Fin (D+1)) (k : Fin (S+1)) :
    spinRaise (fun q => spinLower (φ q) k) p =
      spinLower (fun l => spinRaise (fun q => φ q l) p) k := by
  unfold spinRaise spinLower
  split_ifs <;> ring

theorem auxRaise_lower_commutator {Q : ℕ} (φ : ThreeBodyAux Q) :
    auxRaise (auxLower φ) - auxLower (auxRaise φ) = auxWeight φ := by
  funext p k
  change
    (spinRaise ((fun q => spinLower (fun r => φ r k) q) +
      (fun q => spinLower (φ q) k)) p +
     spinRaise ((fun l => spinLower (fun r => φ r l) p) + spinLower (φ p)) k) -
    (spinLower ((fun q => spinRaise (fun r => φ r k) q) +
      (fun q => spinRaise (φ q) k)) p +
     spinLower ((fun l => spinRaise (fun r => φ r l) p) + spinRaise (φ p)) k) = _
  simp only [spinRaise_add, spinLower_add, Pi.add_apply]
  have hpk := spinRaise_spinLower_separate φ p k
  have hkp := spinRaise_spinLower_separate (fun l q => φ q l) k p
  have hp := congrFun (spinRaise_lower_commutator (fun q => φ q k)) p
  have hk := congrFun (spinRaise_lower_commutator (φ p)) k
  simp only [Pi.sub_apply] at hp hk
  change _ = spinWeight (fun q => φ q k) p + spinWeight (φ p) k
  rw [← hp, ← hk, hpk, hkp]
  ring

theorem auxWeight_raise_commutator {Q : ℕ} (φ : ThreeBodyAux Q) :
    auxWeight (auxRaise φ) - auxRaise (auxWeight φ) = (2 : ℂ) • auxRaise φ := by
  funext p k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, auxWeight_apply, auxRaise, spinRaise]
  split_ifs
  all_goals try simp only [auxWeight_apply, Fin.val_mk, Nat.cast_add, Nat.cast_one]
  all_goals ring

theorem auxWeight_lower_commutator {Q : ℕ} (φ : ThreeBodyAux Q) :
    auxWeight (auxLower φ) - auxLower (auxWeight φ) = (-2 : ℂ) • auxLower φ := by
  funext p k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, auxWeight_apply, auxLower, spinLower]
  split_ifs
  all_goals try simp only [auxWeight_apply, Fin.val_mk]
  all_goals try rw [Nat.cast_sub (by omega : 1 ≤ p.val), Nat.cast_one]
  all_goals try rw [Nat.cast_sub (by omega : 1 ≤ k.val), Nat.cast_one]
  all_goals ring

theorem auxWeight_add {Q : ℕ} (φ χ : ThreeBodyAux Q) :
    auxWeight (φ+χ) = auxWeight φ + auxWeight χ := by
  funext p k
  simp only [auxWeight_apply, Pi.add_apply, mul_add]

theorem auxWeight_smul {Q : ℕ} (c : ℂ) (φ : ThreeBodyAux Q) :
    auxWeight (c • φ) = c • auxWeight φ := by
  funext p k
  simp only [auxWeight_apply, Pi.smul_apply, smul_eq_mul]
  ring

def auxWeightLinear (Q : ℕ) : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q where
  toFun := auxWeight
  map_add' := auxWeight_add
  map_smul' := auxWeight_smul

theorem aux_sl2_EF (Q : ℕ) :
    auxRaiseLinear Q * auxLowerLinear Q - auxLowerLinear Q * auxRaiseLinear Q =
      auxWeightLinear Q := by
  apply LinearMap.ext
  exact auxRaise_lower_commutator

theorem aux_sl2_HE (Q : ℕ) :
    auxWeightLinear Q * auxRaiseLinear Q - auxRaiseLinear Q * auxWeightLinear Q =
      (2 : ℂ) • auxRaiseLinear Q := by
  apply LinearMap.ext
  exact auxWeight_raise_commutator

theorem aux_sl2_HF (Q : ℕ) :
    auxWeightLinear Q * auxLowerLinear Q - auxLowerLinear Q * auxWeightLinear Q =
      (-2 : ℂ) • auxLowerLinear Q := by
  apply LinearMap.ext
  exact auxWeight_lower_commutator

end
end BosonicLaughlin

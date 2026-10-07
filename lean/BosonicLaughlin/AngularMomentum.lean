import BosonicLaughlin.ThreeBodyGram
import Mathlib.Tactic

/-!
Normalized spin ladders in the deficit basis and their tensor-sum action on
the actual three-body auxiliary space. The weight convention is twice the
usual magnetic quantum number, so the raising commutator is `[H,E]=2E`.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def spinRaiseCoeff (D i : ℕ) : ℝ :=
  Real.sqrt (((i + 1 : ℕ) : ℝ) * ((D - i : ℕ) : ℝ))

theorem spinRaiseCoeff_pos (D i : ℕ) (hi : i < D) :
    0 < spinRaiseCoeff D i := by
  unfold spinRaiseCoeff
  apply Real.sqrt_pos.mpr
  exact mul_pos (by positivity) (by exact_mod_cast (Nat.sub_pos_of_lt hi))

theorem spinRaiseCoeff_sq (D i : ℕ) :
    spinRaiseCoeff D i ^ 2 = ((i+1 : ℕ) : ℝ) * ((D-i : ℕ) : ℝ) := by
  unfold spinRaiseCoeff
  exact Real.sq_sqrt (by positivity)

def spinRaise {D : ℕ} (ψ : Fin (D+1) → ℂ) : Fin (D+1) → ℂ := fun i =>
  if h : i.val < D then (spinRaiseCoeff D i.val : ℂ) * ψ ⟨i.val+1, by omega⟩ else 0

def spinLower {D : ℕ} (ψ : Fin (D+1) → ℂ) : Fin (D+1) → ℂ := fun i =>
  if h : 0 < i.val then (spinRaiseCoeff D (i.val-1) : ℂ) * ψ ⟨i.val-1, by omega⟩ else 0

def spinWeight {D : ℕ} (ψ : Fin (D+1) → ℂ) : Fin (D+1) → ℂ := fun i =>
  ((D : ℂ) - 2 * (i.val : ℂ)) * ψ i

theorem spinRaise_add {D : ℕ} (ψ χ : Fin (D+1) → ℂ) :
    spinRaise (ψ+χ) = spinRaise ψ + spinRaise χ := by
  funext i
  simp only [spinRaise, Pi.add_apply]
  split_ifs <;> simp [mul_add]

theorem spinRaise_smul {D : ℕ} (c : ℂ) (ψ : Fin (D+1) → ℂ) :
    spinRaise (c • ψ) = c • spinRaise ψ := by
  funext i
  simp only [spinRaise, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

def spinRaiseLinear (D : ℕ) : (Fin (D+1) → ℂ) →ₗ[ℂ] (Fin (D+1) → ℂ) where
  toFun := spinRaise
  map_add' := spinRaise_add
  map_smul' := spinRaise_smul

theorem spinLower_add {D : ℕ} (ψ χ : Fin (D+1) → ℂ) :
    spinLower (ψ+χ) = spinLower ψ + spinLower χ := by
  funext i
  simp only [spinLower, Pi.add_apply]
  split_ifs <;> simp [mul_add]

theorem spinLower_smul {D : ℕ} (c : ℂ) (ψ : Fin (D+1) → ℂ) :
    spinLower (c • ψ) = c • spinLower ψ := by
  funext i
  simp only [spinLower, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

def spinLowerLinear (D : ℕ) : (Fin (D+1) → ℂ) →ₗ[ℂ] (Fin (D+1) → ℂ) where
  toFun := spinLower
  map_add' := spinLower_add
  map_smul' := spinLower_smul

def auxRaise {Q : ℕ} (φ : ThreeBodyAux Q) : ThreeBodyAux Q := fun p k =>
  spinRaise (fun q => φ q k) p + spinRaise (φ p) k

def auxLower {Q : ℕ} (φ : ThreeBodyAux Q) : ThreeBodyAux Q := fun p k =>
  spinLower (fun q => φ q k) p + spinLower (φ p) k

def auxWeight {Q : ℕ} (φ : ThreeBodyAux Q) : ThreeBodyAux Q := fun p k =>
  spinWeight (fun q => φ q k) p + spinWeight (φ p) k

theorem auxRaise_add {Q : ℕ} (φ χ : ThreeBodyAux Q) :
    auxRaise (φ+χ) = auxRaise φ + auxRaise χ := by
  funext p k
  simp only [auxRaise, Pi.add_apply]
  rw [show (fun q => φ q k + χ q k) = (fun q => φ q k) + (fun q => χ q k) from rfl]
  simp only [spinRaise_add, Pi.add_apply]
  ring

theorem auxRaise_smul {Q : ℕ} (c : ℂ) (φ : ThreeBodyAux Q) :
    auxRaise (c • φ) = c • auxRaise φ := by
  funext p k
  change spinRaise (c • (fun q => φ q k)) p + spinRaise (c • φ p) k = _
  simp only [spinRaise_smul, auxRaise, Pi.smul_apply, smul_eq_mul]
  ring

def auxRaiseLinear (Q : ℕ) : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q where
  toFun := auxRaise
  map_add' := auxRaise_add
  map_smul' := auxRaise_smul

theorem auxRaise_zero (Q : ℕ) : auxRaise (0 : ThreeBodyAux Q) = 0 :=
  (auxRaiseLinear Q).map_zero

/-- Every application of the raising operator lowers the total deficit by one. -/
theorem auxRaise_power_support {Q : ℕ} (φ : ThreeBodyAux Q) (z : ℕ)
    (hφ : ∀ p k, z < p.val + k.val → φ p k = 0) (n : ℕ)
    (p : Fin (2*Q+1)) (k : Orbital Q) (h : z < p.val+k.val+n) :
    ((auxRaiseLinear Q)^n) φ p k = 0 := by
  induction n generalizing p k with
  | zero =>
    simpa using hφ p k (by omega)
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    change auxRaise (((auxRaiseLinear Q)^n) φ) p k = 0
    have hp : spinRaise (fun q => ((auxRaiseLinear Q)^n) φ q k) p = 0 := by
      unfold spinRaise
      split_ifs with hp
      · change (spinRaiseCoeff (2*Q) p.val : ℂ) *
          ((auxRaiseLinear Q)^n) φ ⟨p.val+1, by omega⟩ k = 0
        rw [ih ⟨p.val+1, by omega⟩ k (by change z < (p.val+1)+k.val+n; omega), mul_zero]
      · rfl
    have hk : spinRaise (((auxRaiseLinear Q)^n) φ p) k = 0 := by
      unfold spinRaise
      split_ifs with hk
      · rw [ih p ⟨k.val+1, by omega⟩ (by change z < p.val+(k.val+1)+n; omega), mul_zero]
      · rfl
    change _ + _ = 0
    rw [hp, hk, zero_add]

theorem auxRaise_nilpotent (Q : ℕ) :
    (auxRaiseLinear Q) ^ (3*Q+1) = 0 := by
  apply LinearMap.ext
  intro φ
  funext p k
  change ((auxRaiseLinear Q) ^ (3*Q+1)) φ p k = 0
  apply auxRaise_power_support φ (3*Q)
  · intro p k h
    have hp := p.isLt
    have hk := k.isLt
    omega
  · omega

theorem spinRaise_castSucc {D : ℕ} (ψ : Fin (D+1) → ℂ) (i : Fin D) :
    spinRaise ψ i.castSucc = (spinRaiseCoeff D i.val : ℂ) * ψ i.succ := by
  simp only [spinRaise, Fin.val_castSucc, i.isLt, dite_true]
  congr 1

theorem spinRaise_last {D : ℕ} (ψ : Fin (D+1) → ℂ) :
    spinRaise ψ (Fin.last D) = 0 := by
  simp [spinRaise]

theorem spinLower_succ {D : ℕ} (ψ : Fin (D+1) → ℂ) (i : Fin D) :
    spinLower ψ i.succ = (spinRaiseCoeff D i.val : ℂ) * ψ i.castSucc := by
  simp only [spinLower, Fin.val_succ, Nat.add_pos_right, dite_true, Nat.add_sub_cancel]
  congr 1

theorem spinLower_zero {D : ℕ} (ψ : Fin (D+1) → ℂ) :
    spinLower ψ 0 = 0 := by
  simp [spinLower]

/-- Transposition identity for the real ladder matrices. -/
theorem spinRaise_bilinear {D : ℕ} (ψ χ : Fin (D+1) → ℂ) :
    (∑ i, ψ i * spinRaise χ i) = ∑ i, spinLower ψ i * χ i := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [spinRaise_castSucc, spinRaise_last, mul_zero, add_zero,
    spinLower_zero, zero_mul, zero_add, spinLower_succ]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem spinLower_bilinear {D : ℕ} (ψ χ : Fin (D+1) → ℂ) :
    (∑ i, ψ i * spinLower χ i) = ∑ i, spinRaise ψ i * χ i := by
  simpa only [mul_comm] using (spinRaise_bilinear χ ψ).symm

theorem spinLower_star {D : ℕ} (ψ : Fin (D+1) → ℂ) (i : Fin (D+1)) :
    spinLower (fun j => star (ψ j)) i = star (spinLower ψ i) := by
  unfold spinLower
  split_ifs <;> simp

theorem spinRaise_adjoint {D : ℕ} (ψ χ : Fin (D+1) → ℂ) :
    (∑ i, star (ψ i) * spinRaise χ i) = ∑ i, star (spinLower ψ i) * χ i := by
  simpa only [spinLower_star] using spinRaise_bilinear (fun i => star (ψ i)) χ

theorem spinRaise_spinLower {D : ℕ} (ψ : Fin (D+1) → ℂ) (i : Fin (D+1)) :
    spinRaise (spinLower ψ) i =
      (((i.val+1 : ℕ) : ℂ) * ((D-i.val : ℕ) : ℂ)) * ψ i := by
  by_cases hi : i.val < D
  · have he : (⟨i.val+1-1, by omega⟩ : Fin (D+1)) = i := by ext; simp
    simp only [spinRaise, hi, dite_true, spinLower, Fin.val_mk]
    rw [dif_pos (by omega : 0 < i.val+1)]
    simp only [Nat.add_sub_cancel, he]
    have hs : (spinRaiseCoeff D i.val : ℂ) * (spinRaiseCoeff D i.val : ℂ) =
        ((i.val+1 : ℕ) : ℂ) * ((D-i.val : ℕ) : ℂ) := by
      have h := congrArg Complex.ofReal (spinRaiseCoeff_sq D i.val)
      push_cast at h
      simpa only [pow_two, Nat.cast_add, Nat.cast_one] using h
    rw [← mul_assoc, hs]
  · have hiD : i.val = D := by omega
    simp [spinRaise, hi, hiD]

theorem spinLower_spinRaise {D : ℕ} (ψ : Fin (D+1) → ℂ) (i : Fin (D+1)) :
    spinLower (spinRaise ψ) i =
      ((i.val : ℂ) * ((D+1-i.val : ℕ) : ℂ)) * ψ i := by
  by_cases hi : 0 < i.val
  · have he : (⟨i.val-1+1, by omega⟩ : Fin (D+1)) = i := by
      apply Fin.ext
      change i.val-1+1 = i.val
      omega
    simp only [spinLower, hi, dite_true, spinRaise, Fin.val_mk]
    rw [dif_pos (by omega : i.val-1 < D)]
    rw [he, ← mul_assoc]
    have hs : (spinRaiseCoeff D (i.val-1) : ℂ) * (spinRaiseCoeff D (i.val-1) : ℂ) =
        ((i.val : ℂ) * ((D+1-i.val : ℕ) : ℂ)) := by
      have h1 : i.val-1+1 = i.val := by omega
      have h2 : D-(i.val-1) = D+1-i.val := by omega
      have h := congrArg Complex.ofReal (spinRaiseCoeff_sq D (i.val-1))
      simp only [h1, h2] at h
      push_cast at h
      simpa only [pow_two] using h
    rw [hs]
  · have hi0 : i.val = 0 := by omega
    simp [spinLower, hi, hi0]

theorem spinRaise_lower_commutator {D : ℕ} (ψ : Fin (D+1) → ℂ) :
    spinRaise (spinLower ψ) - spinLower (spinRaise ψ) = spinWeight ψ := by
  funext i
  simp only [Pi.sub_apply, spinRaise_spinLower, spinLower_spinRaise, spinWeight]
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : i.val ≤ D),
    Nat.cast_sub (by omega : i.val ≤ D+1), Nat.cast_add, Nat.cast_one]
  ring

end
end BosonicLaughlin

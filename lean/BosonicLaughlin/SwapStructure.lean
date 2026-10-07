import BosonicLaughlin.ThreeBodyGram
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! The actual compressed exchange as a Hermitian, deficit-preserving matrix.
Total deficit is p+k in the fixed orthonormal pair/spectator basis. -/
namespace BosonicLaughlin
noncomputable section
open Finset
open scoped Matrix

abbrev ThreeBodyIndex (Q : ℕ) := Fin (2*Q+1) × Orbital Q

/-- Support in the fixed total orbital-deficit block z. -/
def AuxSupported {Q : ℕ} (z : ℕ) (φ : ThreeBodyAux Q) : Prop :=
  ∀ p k, p.val + k.val ≠ z → φ p k = 0

def auxDeficitProject {Q : ℕ} (z : ℕ) (φ : ThreeBodyAux Q) : ThreeBodyAux Q :=
  fun p k => if p.val + k.val = z then φ p k else 0

def compressedSwapMatrix (Q : ℕ) : Matrix (ThreeBodyIndex Q) (ThreeBodyIndex Q) ℂ :=
  fun a b => ∑ x : Orbital Q,
    (pairVector Q a.1.val x b.2 : ℂ) * (pairVector Q b.1.val x a.2 : ℂ)

theorem compressedSwap_add {Q : ℕ} (φ χ : ThreeBodyAux Q) :
    compressedSwap (φ+χ) = compressedSwap φ + compressedSwap χ := by
  funext p k
  simp [compressedSwap, mul_add, Finset.sum_add_distrib]

theorem compressedSwap_smul {Q : ℕ} (c : ℂ) (φ : ThreeBodyAux Q) :
    compressedSwap (c • φ) = c • compressedSwap φ := by
  funext p k
  simp only [compressedSwap, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm _ c, ← Finset.mul_sum]

def compressedSwapLinear (Q : ℕ) : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q where
  toFun := compressedSwap
  map_add' := compressedSwap_add
  map_smul' := compressedSwap_smul

theorem compressedSwap_zero (Q : ℕ) : compressedSwap (0 : ThreeBodyAux Q) = 0 := by
  exact (compressedSwapLinear Q).map_zero

theorem compressedSwap_matrix_apply {Q : ℕ} (φ : ThreeBodyAux Q)
    (p : Fin (2*Q+1)) (k : Orbital Q) :
    compressedSwap φ p k = ∑ q : Fin (2*Q+1), ∑ y : Orbital Q,
      compressedSwapMatrix Q (p,k) (q,y) * φ q y := by
  simp only [compressedSwap, compressedSwapMatrix, Finset.sum_mul]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]

theorem compressedSwapMatrix_mulVec {Q : ℕ} (φ : ThreeBodyAux Q) :
    compressedSwapMatrix Q *ᵥ (fun a => φ a.1 a.2) =
      (fun a => compressedSwap φ a.1 a.2) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  exact (compressedSwap_matrix_apply φ a.1 a.2).symm

theorem compressedSwapMatrix_hermitian (Q : ℕ) :
    (compressedSwapMatrix Q).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  simp [compressedSwapMatrix, mul_comm]

theorem compressedSwapMatrix_off_deficit (Q : ℕ) (a b : ThreeBodyIndex Q)
    (h : a.1.val + a.2.val ≠ b.1.val + b.2.val) :
    compressedSwapMatrix Q a b = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases h₁ : x.val + b.2.val = a.1.val
  · have h₂ : x.val + a.2.val ≠ b.1.val := by omega
    simp [pairVector, h₂]
  · simp [pairVector, h₁]

theorem auxDeficitProject_supported {Q : ℕ} (z : ℕ) (φ : ThreeBodyAux Q) :
    AuxSupported z (auxDeficitProject z φ) := by
  intro p k h
  simp [auxDeficitProject, h]

theorem auxDeficitProject_eq_self {Q : ℕ} (z : ℕ) (φ : ThreeBodyAux Q)
    (hφ : AuxSupported z φ) : auxDeficitProject z φ = φ := by
  funext p k
  by_cases h : p.val+k.val=z
  · simp [auxDeficitProject, h]
  · simp [auxDeficitProject, h, hφ p k h]

theorem auxDeficitProject_smul {Q : ℕ} (z : ℕ) (c : ℂ) (φ : ThreeBodyAux Q) :
    auxDeficitProject z (c • φ) = c • auxDeficitProject z φ := by
  funext p k
  simp [auxDeficitProject, mul_ite]

theorem compressedSwap_deficit_project {Q : ℕ} (z : ℕ) (φ : ThreeBodyAux Q) :
    compressedSwap (auxDeficitProject z φ) = auxDeficitProject z (compressedSwap φ) := by
  funext p k
  rw [compressedSwap_matrix_apply]
  simp only [auxDeficitProject]
  by_cases hpk : p.val+k.val=z
  · rw [ite_eq_left hpk, compressedSwap_matrix_apply]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro y _
    by_cases hqy : q.val+y.val=z
    · simp [hqy]
    · have hd : p.val+k.val ≠ q.val+y.val := by omega
      simp [hqy, compressedSwapMatrix_off_deficit Q (p,k) (q,y) hd]
  · rw [ite_eq_right hpk]
    apply Finset.sum_eq_zero
    intro q _
    apply Finset.sum_eq_zero
    intro y _
    by_cases hqy : q.val+y.val=z
    · have hd : p.val+k.val ≠ q.val+y.val := by omega
      simp [hqy, compressedSwapMatrix_off_deficit Q (p,k) (q,y) hd]
    · simp [hqy]

theorem compressedSwap_supported {Q : ℕ} (z : ℕ) (φ : ThreeBodyAux Q)
    (hφ : AuxSupported z φ) : AuxSupported z (compressedSwap φ) := by
  have h := compressedSwap_deficit_project z φ
  rw [auxDeficitProject_eq_self z φ hφ] at h
  rw [h]
  exact auxDeficitProject_supported z _

theorem auxDeficitProject_exists_nonzero {Q : ℕ} (φ : ThreeBodyAux Q) (hφ : φ ≠ 0) :
    ∃ z ≤ 3*Q, auxDeficitProject z φ ≠ 0 := by
  have hex : ∃ p k, φ p k ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (by funext p k; exact h p k)
  obtain ⟨p,k,hpk⟩ := hex
  refine ⟨p.val+k.val, by omega, ?_⟩
  intro h
  have he := congrFun (congrFun h p) k
  simp [auxDeficitProject] at he
  exact hpk he

end
end BosonicLaughlin

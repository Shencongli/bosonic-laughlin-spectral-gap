import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-! Orthogonal projectors obtained by partitioning a finite orthonormal basis. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def spectralPartitionDiagonal {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (label : ι → κ) (z : κ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if label i = z then 1 else 0)

def spectralPartitionProjector {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ) (label : ι → κ) (z : κ) : Matrix ι ι ℂ :=
  e (spectralPartitionDiagonal label z)

theorem spectralPartitionDiagonal_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (label : ι → κ) :
    ∑ z, spectralPartitionDiagonal label z = 1 := by
  ext i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst j
    simp [spectralPartitionDiagonal]
  · simp [spectralPartitionDiagonal, Matrix.diagonal_apply, hij, Matrix.one_apply]

theorem spectralPartitionDiagonal_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (label : ι → κ) (z w : κ) :
    spectralPartitionDiagonal label z * spectralPartitionDiagonal label w =
      if z=w then spectralPartitionDiagonal label z else 0 := by
  rw [spectralPartitionDiagonal, spectralPartitionDiagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j <;> by_cases hzw : z=w <;>
    by_cases hiz : label i=z <;> by_cases hiw : label i=w <;>
    simp_all [spectralPartitionDiagonal, Matrix.diagonal_apply]

theorem spectralPartitionDiagonal_hermitian {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (label : ι → κ) (z : κ) :
    (spectralPartitionDiagonal label z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i=j <;> simp_all [spectralPartitionDiagonal, Matrix.diagonal_apply, eq_comm]

theorem spectralPartition_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ) (label : ι → κ) :
    ∑ z, spectralPartitionProjector e label z = 1 := by
  simp only [spectralPartitionProjector, ← map_sum, spectralPartitionDiagonal_sum, map_one]

theorem spectralPartition_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ) (label : ι → κ) (z w : κ) :
    spectralPartitionProjector e label z * spectralPartitionProjector e label w =
      if z=w then spectralPartitionProjector e label z else 0 := by
  simp only [spectralPartitionProjector, ← map_mul, spectralPartitionDiagonal_mul]
  split_ifs <;> simp

theorem spectralPartition_hermitian {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ) (label : ι → κ) (z : κ) :
    (spectralPartitionProjector e label z).IsHermitian := by
  change star (e (spectralPartitionDiagonal label z)) = e (spectralPartitionDiagonal label z)
  rw [← map_star]
  congr 1
  exact spectralPartitionDiagonal_hermitian label z

theorem spectralPartition_resolution {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ) (label : ι → κ) (eigenvalue : κ → ℂ) :
    (∑ z, eigenvalue z • spectralPartitionProjector e label z) =
      e (Matrix.diagonal (fun i => eigenvalue (label i))) := by
  have hd : (∑ z, eigenvalue z • spectralPartitionDiagonal label z) =
      Matrix.diagonal (fun i => eigenvalue (label i)) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i=j
    · subst j
      simp [spectralPartitionDiagonal]
    · simp [spectralPartitionDiagonal, Matrix.diagonal_apply, hij]
  rw [← hd, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (map_smul e (eigenvalue z) (spectralPartitionDiagonal label z)).symm

end
end BosonicLaughlin

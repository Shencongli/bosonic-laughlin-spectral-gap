import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Exact certificates that the proposed columns form the full kernel basis.
These are algebraic certificate lemmas; the identities must be checked for
each supplied frame, not inferred from a numerical rank. -/
namespace BosonicLaughlin
noncomputable section
open scoped Matrix

def HasKernelFrame {K : Type*} [Field K] {m n k : ℕ}
    (C : Matrix (Fin m) (Fin n) K) (U : Matrix (Fin n) (Fin k) K)
    (L : Matrix (Fin k) (Fin n) K) (V : Matrix (Fin n) (Fin m) K) : Prop :=
  C*U=0 ∧ L*U=1 ∧ U*L+V*C=1

theorem kernelFrame_columns_in_kernel {K : Type*} [Field K] {m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) K} {U : Matrix (Fin n) (Fin k) K}
    {L : Matrix (Fin k) (Fin n) K} {V : Matrix (Fin n) (Fin m) K}
    (h : HasKernelFrame C U L V) (c : Fin k → K) : C *ᵥ (U *ᵥ c)=0 := by
  rw [Matrix.mulVec_mulVec, h.1, Matrix.zero_mulVec]

theorem kernelFrame_left_inverse {K : Type*} [Field K] {m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) K} {U : Matrix (Fin n) (Fin k) K}
    {L : Matrix (Fin k) (Fin n) K} {V : Matrix (Fin n) (Fin m) K}
    (h : HasKernelFrame C U L V) (c : Fin k → K) : L *ᵥ (U *ᵥ c)=c := by
  rw [Matrix.mulVec_mulVec, h.2.1, Matrix.one_mulVec]

theorem kernelFrame_reconstruction {K : Type*} [Field K] {m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) K} {U : Matrix (Fin n) (Fin k) K}
    {L : Matrix (Fin k) (Fin n) K} {V : Matrix (Fin n) (Fin m) K}
    (h : HasKernelFrame C U L V) (ψ : Fin n → K) (hψ : C *ᵥ ψ=0) : U *ᵥ (L *ᵥ ψ)=ψ := by
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) K => A *ᵥ ψ) h.2.2
  simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hψ,
    Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] using he

def kernelFrameEquiv {K : Type*} [Field K] {m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) K} {U : Matrix (Fin n) (Fin k) K}
    {L : Matrix (Fin k) (Fin n) K} {V : Matrix (Fin n) (Fin m) K}
    (h : HasKernelFrame C U L V) : (Fin k → K) ≃ₗ[K] LinearMap.ker C.mulVecLin where
  toFun c := ⟨U *ᵥ c, kernelFrame_columns_in_kernel h c⟩
  invFun ψ := L *ᵥ ψ.val
  left_inv := kernelFrame_left_inverse h
  right_inv ψ := by
    apply Subtype.ext
    exact kernelFrame_reconstruction h ψ.val ψ.property
  map_add' c e := by
    apply Subtype.ext
    change U *ᵥ (c+e) = U *ᵥ c + U *ᵥ e
    exact Matrix.mulVec_add U c e
  map_smul' a c := by
    apply Subtype.ext
    change U *ᵥ (a • c) = a • (U *ᵥ c)
    exact Matrix.mulVec_smul U a c

theorem kernelFrame_finrank {K : Type*} [Field K] {m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) K} {U : Matrix (Fin n) (Fin k) K}
    {L : Matrix (Fin k) (Fin n) K} {V : Matrix (Fin n) (Fin m) K}
    (h : HasKernelFrame C U L V) : Module.finrank K (LinearMap.ker C.mulVecLin)=k := by
  rw [← (kernelFrameEquiv h).finrank_eq]
  simp

end
end BosonicLaughlin

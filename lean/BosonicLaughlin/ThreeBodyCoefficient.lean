import BosonicLaughlin.ThreeBodySpectral
import BosonicLaughlin.SwapProjectorEigenspaces
import BosonicLaughlin.ProjectionOccupation

/-! Physical three-particle coefficients obtained from auxiliary operators.
The adjoint relation is used on bosonic vectors, with the existing W₃ normalization. -/
namespace BosonicLaughlin
noncomputable section
open Finset Matrix
open scoped ComplexOrder

def threeBodyAdjointLinear (Q : ℕ) : State Q 3 →ₗ[ℂ] ThreeBodyAux Q where
  toFun := threeBodyAdjoint
  map_add' := threeBodyAdjoint_add
  map_smul' := threeBodyAdjoint_smul

/-- W₃ A W₃† in the full tensor coordinates, used on the bosonic subspace. -/
def threeBodyAuxCoefficient (Q : ℕ) (A : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q) :
    State Q 3 →ₗ[ℂ] State Q 3 :=
  (threeBodyMapLinear Q).comp (A.comp (threeBodyAdjointLinear Q))

/-- The positive three-body coefficient associated with one auxiliary spectral block. -/
def threeBodySpectralBlock (Q : ℕ) (z : Fin (Q+1)) : State Q 3 →ₗ[ℂ] State Q 3 :=
  threeBodyAuxCoefficient Q (compressedSwapProjectorLinear Q z)

theorem threeBodyAuxCoefficient_apply (Q : ℕ)
    (A : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q) (χ : State Q 3) :
    threeBodyAuxCoefficient Q A χ = threeBodyMap (A (threeBodyAdjoint χ)) := rfl

theorem threeBodyAuxCoefficient_isBosonic (Q : ℕ)
    (A : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q) (χ : State Q 3) :
    IsBosonic (threeBodyAuxCoefficient Q A χ) :=
  threeBodyMap_isBosonic _

/-- The physical sesquilinear form equals the auxiliary sesquilinear form.
Only the bra needs to be bosonic for this identity. -/
theorem threeBodyAuxCoefficient_inner (Q : ℕ)
    (A : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q) (ψ χ : State Q 3) (hψ : IsBosonic ψ) :
    inner ψ (threeBodyAuxCoefficient Q A χ) =
      ∑ p : Fin (2*Q+1), ∑ k : Orbital Q,
        star (threeBodyAdjoint ψ p k) * A (threeBodyAdjoint χ) p k := by
  rw [threeBodyAuxCoefficient_apply, ← inner_star,
    threeBody_adjoint_inner _ ψ hψ]
  simp only [star_sum, star_mul, star_star]

theorem threeBodyAuxCoefficient_nonneg (Q : ℕ)
    (A : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q)
    (hA : ∀ φ : ThreeBodyAux Q,
      0 ≤ (∑ p : Fin (2*Q+1), ∑ k : Orbital Q, star (φ p k) * A φ p k).re)
    (χ : State Q 3) (hχ : IsBosonic χ) :
    0 ≤ (inner χ (threeBodyAuxCoefficient Q A χ)).re := by
  rw [threeBodyAuxCoefficient_inner Q A χ χ hχ]
  exact hA (threeBodyAdjoint χ)

theorem threeBodyAuxCoefficient_hermitian (Q : ℕ)
    (A : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q)
    (hA : ∀ φ θ : ThreeBodyAux Q,
      (∑ p : Fin (2*Q+1), ∑ k : Orbital Q, star (φ p k) * A θ p k) =
        ∑ p : Fin (2*Q+1), ∑ k : Orbital Q, star (A φ p k) * θ p k)
    (ψ χ : State Q 3) (hψ : IsBosonic ψ) (hχ : IsBosonic χ) :
    inner ψ (threeBodyAuxCoefficient Q A χ) =
      inner (threeBodyAuxCoefficient Q A ψ) χ := by
  rw [threeBodyAuxCoefficient_inner Q A ψ χ hψ,
    threeBodyAuxCoefficient_apply, threeBody_adjoint_inner _ χ hχ]
  exact hA (threeBodyAdjoint ψ) (threeBodyAdjoint χ)

theorem compressedSwapProjector_aux_hermitian (Q : ℕ) (z : Fin (Q+1))
    (φ θ : ThreeBodyAux Q) :
    (∑ p : Fin (2*Q+1), ∑ k : Orbital Q,
      star (φ p k) * compressedSwapProjectorLinear Q z θ p k) =
    ∑ p : Fin (2*Q+1), ∑ k : Orbital Q,
      star (compressedSwapProjectorLinear Q z φ p k) * θ p k := by
  have hm : star (fun a : ThreeBodyIndex Q => φ a.1 a.2) ⬝ᵥ
      (compressedSwapProjector Q z *ᵥ (fun a => θ a.1 a.2)) =
      star (compressedSwapProjector Q z *ᵥ (fun a => φ a.1 a.2)) ⬝ᵥ
        (fun a : ThreeBodyIndex Q => θ a.1 a.2) := by
    rw [Matrix.star_mulVec, (compressedSwapProjector_hermitian Q z).eq,
      dotProduct_mulVec]
  simpa only [dotProduct, Fintype.sum_prod_type, Pi.star_apply,
    compressedSwapProjectorLinear, LinearMap.coe_mk, AddHom.coe_mk] using hm

theorem compressedSwapProjector_quadratic_nonneg (Q : ℕ) (z : Fin (Q+1))
    (φ : ThreeBodyAux Q) :
    0 ≤ (∑ p : Fin (2*Q+1), ∑ k : Orbital Q,
      star (φ p k) * compressedSwapProjectorLinear Q z φ p k).re := by
  have hP := projection_posSemidef (compressedSwapProjector Q z)
    (compressedSwapProjector_hermitian Q z) (compressedSwapProjector_idempotent Q z)
  have h := hP.dotProduct_mulVec_nonneg (fun a : ThreeBodyIndex Q => φ a.1 a.2)
  have hr := (Complex.nonneg_iff.mp h).1
  simpa only [dotProduct, Fintype.sum_prod_type, Pi.star_apply,
    compressedSwapProjectorLinear, LinearMap.coe_mk, AddHom.coe_mk] using hr

theorem threeBodySpectralBlock_nonneg (Q : ℕ) (z : Fin (Q+1))
    (χ : State Q 3) (hχ : IsBosonic χ) :
    0 ≤ (inner χ (threeBodySpectralBlock Q z χ)).re :=
  threeBodyAuxCoefficient_nonneg Q (compressedSwapProjectorLinear Q z)
    (compressedSwapProjector_quadratic_nonneg Q z) χ hχ

theorem threeBodySpectralBlock_hermitian (Q : ℕ) (z : Fin (Q+1))
    (ψ χ : State Q 3) (hψ : IsBosonic ψ) (hχ : IsBosonic χ) :
    inner ψ (threeBodySpectralBlock Q z χ) =
      inner (threeBodySpectralBlock Q z ψ) χ :=
  threeBodyAuxCoefficient_hermitian Q (compressedSwapProjectorLinear Q z)
    (compressedSwapProjector_aux_hermitian Q z) ψ χ hψ hχ

end
end BosonicLaughlin

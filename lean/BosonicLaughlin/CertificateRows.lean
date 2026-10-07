import BosonicLaughlin.PhysicalKernel

/-!
The finite row class used by the certificate, in physical tensor coordinates.
Coefficients are arbitrary: common-kernel preservation does not depend on
their proposed numerical values, support cutoff, or positivity certificates.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

/-- The one-body matrix unit sum, representing a_i† a_j on symmetric tensors. -/
def orbitalTransfer {Q N : ℕ} (i j : Orbital Q) (ψ : State Q N) : State Q N :=
  fun a => ∑ k : Fin N, if a k = i then ψ (Function.update a k j) else 0

theorem orbitalTransfer_add {Q N : ℕ} (i j : Orbital Q) (ψ φ : State Q N) :
    orbitalTransfer i j (ψ+φ) = orbitalTransfer i j ψ + orbitalTransfer i j φ := by
  funext a
  simp [orbitalTransfer, ite_add_zero, Finset.sum_add_distrib]

theorem orbitalTransfer_smul {Q N : ℕ} (i j : Orbital Q) (c : ℂ) (ψ : State Q N) :
    orbitalTransfer i j (c • ψ) = c • orbitalTransfer i j ψ := by
  funext a
  simp [orbitalTransfer, Finset.mul_sum, mul_ite]

def orbitalTransferLinear (Q N : ℕ) (i j : Orbital Q) : State Q N →ₗ[ℂ] State Q N where
  toFun := orbitalTransfer i j
  map_add' := orbitalTransfer_add i j
  map_smul' := orbitalTransfer_smul i j

theorem orbitalTransfer_isBosonic {Q N : ℕ} (i j : Orbital Q)
    (ψ : State Q N) (hψ : IsBosonic ψ) : IsBosonic (orbitalTransfer i j ψ) := by
  intro σ a
  simp only [orbitalTransfer, Function.comp_apply, update_permute, hψ σ]
  exact Equiv.sum_comp σ (fun k => if a k = i then ψ (Function.update a k j) else 0)

/-- λ B_t + Σp,i,j c(p,i,j) a_i† a_j B_p, from N+2 to N particles. -/
def certificateRow (Q N : ℕ) (t : Fin (2*Q+1)) (leading : ℂ)
    (coefficient : Fin (2*Q+1) → Orbital Q → Orbital Q → ℂ) :
    State Q (N+2) →ₗ[ℂ] State Q N :=
  leading • v0PairAnnihilateLinear Q N t +
    ∑ p : Fin (2*Q+1), ∑ i : Orbital Q, ∑ j : Orbital Q,
      coefficient p i j • (orbitalTransferLinear Q N i j).comp
        (v0PairAnnihilateLinear Q N p)

theorem certificateRow_annihilates_kernel (Q N : ℕ) (t : Fin (2*Q+1))
    (leading : ℂ) (coefficient : Fin (2*Q+1) → Orbital Q → Orbital Q → ℂ)
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) (hH : hamiltonian ψ = 0) :
    certificateRow Q N t leading coefficient ψ = 0 := by
  have hB := (hamiltonian_zero_iff_v0PairAnnihilate_zero ψ hψ).mp hH
  have hBL (p : Fin (2*Q+1)) : v0PairAnnihilateLinear Q N p ψ = 0 := hB p
  simp only [certificateRow, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, hBL, map_zero, smul_zero,
    Finset.sum_const_zero, add_zero]

theorem certificateRow_gram_annihilates_kernel (Q N : ℕ) (t : Fin (2*Q+1))
    (leading : ℂ) (coefficient : Fin (2*Q+1) → Orbital Q → Orbital Q → ℂ)
    (ψ φ : State Q (N+2)) (hφ : IsBosonic φ) (hH : hamiltonian φ = 0) :
    inner (certificateRow Q N t leading coefficient ψ)
      (certificateRow Q N t leading coefficient φ) = 0 := by
  rw [certificateRow_annihilates_kernel Q N t leading coefficient φ hφ hH]
  simp [inner]

theorem certificateRow_gram_nonneg (Q N : ℕ) (t : Fin (2*Q+1))
    (leading : ℂ) (coefficient : Fin (2*Q+1) → Orbital Q → Orbital Q → ℂ)
    (ψ : State Q (N+2)) :
    0 ≤ (inner (certificateRow Q N t leading coefficient ψ)
      (certificateRow Q N t leading coefficient ψ)).re :=
  stateNormSq_nonneg _

end
end BosonicLaughlin

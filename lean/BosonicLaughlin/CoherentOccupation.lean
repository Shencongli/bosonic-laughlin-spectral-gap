import BosonicLaughlin.ModeForms
import BosonicLaughlin.PairAnnihilation
import BosonicLaughlin.Occupation
import BosonicLaughlin.NumberAnnihilation
import BosonicLaughlin.PairOccupationAnnihilation

/-!
Occupation control and the two-particle-annihilation lift for the actual
spherical V₀ Hamiltonian. The normalized spinor (u,v) specifies beta.
All results below quantify over arbitrary flux and particle number.
-/
namespace BosonicLaughlin
noncomputable section
open Finset Matrix
open scoped ComplexOrder

/-- First-quantized number-operator matrix n_beta = sum_i |beta><beta|_i. -/
def modeNumberMatrix {Q N : ℕ} (β : Orbital Q → ℂ) :
    Matrix (Configuration Q N) (Configuration Q N) ℂ :=
  projectionNumber (fun i : Fin N => modeMatrix i β)

/-- Quadratic form of n_beta on the full tensor space. -/
def modeOccupation {Q N : ℕ} (β : Orbital Q → ℂ) (ψ : State Q N) : ℝ :=
  matrixQuadratic (modeNumberMatrix β) ψ

/-- Quadratic form of sum_{i<j} P_beta,i P_beta,j. For normalized beta this
is exactly n_beta(n_beta-I)/2, by `modeNumber_factorial_moment`. -/
def modePairOccupation {Q N : ℕ} (β : Orbital Q → ℂ) (ψ : State Q N) : ℝ :=
  matrixQuadratic (projectionPairs (fun i : Fin N => modeMatrix i β)) ψ

theorem matrixQuadratic_one_eq_normSq {Q N : ℕ} (ψ : State Q N) :
    matrixQuadratic (1 : Matrix (Configuration Q N) (Configuration Q N) ℂ) ψ = normSq ψ := by
  simp only [matrixQuadratic, Matrix.one_mulVec]
  rfl

theorem modeNumber_factorial_moment {Q N : ℕ} (β : Orbital Q → ℂ)
    (hβ : ∑ x, Complex.normSq (β x) = 1) :
    modeNumberMatrix (N:=N) β * modeNumberMatrix β - modeNumberMatrix β =
      projectionPairs (fun i : Fin N => modeMatrix i β) +
      projectionPairs (fun i : Fin N => modeMatrix i β) :=
  projection_factorial_moment (fun i : Fin N => modeMatrix i β)
    (fun i => modeMatrix_idempotent i β hβ) (fun i j => modeMatrix_commute i j β)

/-- The integer-occupation bound expressed using commuting slot projectors. -/
theorem modeOccupation_le_pairs_add_norm {Q N : ℕ} (β : Orbital Q → ℂ)
    (hβ : ∑ x, Complex.normSq (β x) = 1) (ψ : State Q N) :
    modeOccupation β ψ ≤ modePairOccupation β ψ + normSq ψ := by
  have h := projection_occupation_form (fun i : Fin N => modeMatrix i β)
    (fun i => modeMatrix_hermitian i β) (fun i => modeMatrix_idempotent i β hβ)
    (fun i j => modeMatrix_commute i j β) ψ
  rw [matrixQuadratic_one_eq_normSq] at h
  simpa only [modeOccupation, modeNumberMatrix, modePairOccupation, add_comm] using h

/-- H_Q controls the second factorial occupation moment for every spin-coherent beta. -/
theorem coherent_pairOccupation_le_energy {Q N : ℕ} (u v : ℂ)
    (hspinor : Complex.normSq u + Complex.normSq v = 1) (ψ : State Q N) :
    modePairOccupation (coherentOrbital Q u v) ψ ≤ energy ψ := by
  change (inner ψ (projectionPairs (fun i : Fin N => modeMatrix i (coherentOrbital Q u v)) *ᵥ ψ)).re ≤ _
  rw [projectionPairs_mode_energy_identity]
  exact coherent_pairCost_le_energy u v hspinor ψ

/-- n_beta ≤ H_Q+I at every flux and particle number, on the actual full model. -/
theorem coherent_occupation_bound {Q N : ℕ} (u v : ℂ)
    (hspinor : Complex.normSq u + Complex.normSq v = 1) (ψ : State Q N) :
    modeOccupation (coherentOrbital Q u v) ψ ≤ energy ψ + normSq ψ := by
  have h1 := modeOccupation_le_pairs_add_norm (coherentOrbital Q u v)
    (coherentOrbital_normalized Q u v hspinor) ψ
  have h2 := coherent_pairOccupation_le_energy u v hspinor ψ
  linarith

/-- Quadratic-form version of B_alpha† n_beta B_alpha ≤ B_alpha†(H_Q+I)B_alpha.
The input has N+2 particles, while H_Q and n_beta act in the output N sector.
The alpha orbital is arbitrary; beta is a normalized spin-coherent orbital. -/
theorem coherent_occupation_pair_lift {Q N : ℕ} (α : Orbital Q → ℂ) (u v : ℂ)
    (hspinor : Complex.normSq u + Complex.normSq v = 1) (ψ : State Q (N+2)) :
    modeOccupation (coherentOrbital Q u v) (pairAnnihilate α ψ) ≤
      energy (pairAnnihilate α ψ) + normSq (pairAnnihilate α ψ) :=
  coherent_occupation_bound u v hspinor (pairAnnihilate α ψ)

/-- On the physical bosonic sector, the number form equals the squared norm
of the standard normalized annihilation map. -/
theorem modeOccupation_eq_annihilate_normSq {Q N : ℕ} (β : Orbital Q → ℂ)
    (ψ : State Q (N+1)) (hψ : IsBosonic ψ) :
    modeOccupation β ψ = normSq (annihilate β ψ) :=
  projectionNumber_eq_annihilate_normSq β ψ hψ

/-- The same bound written directly with the physical annihilator. -/
theorem coherent_annihilation_bound {Q N : ℕ} (u v : ℂ)
    (hspinor : Complex.normSq u + Complex.normSq v = 1)
    (ψ : State Q (N+1)) (hψ : IsBosonic ψ) :
    normSq (annihilate (coherentOrbital Q u v) ψ) ≤ energy ψ + normSq ψ := by
  rw [← modeOccupation_eq_annihilate_normSq _ ψ hψ]
  exact coherent_occupation_bound u v hspinor ψ

/-- Fully typed annihilator version: Bα maps N+3 particles to N+1, then aβ
maps to N. The Hamiltonian on the right acts in the N+1 output sector. -/
theorem coherent_annihilation_pair_lift {Q N : ℕ} (α : Orbital Q → ℂ) (u v : ℂ)
    (hspinor : Complex.normSq u + Complex.normSq v = 1)
    (ψ : State Q (N+3)) (hψ : IsBosonic ψ) :
    normSq (annihilate (coherentOrbital Q u v) (pairAnnihilate α ψ)) ≤
      energy (pairAnnihilate α ψ) + normSq (pairAnnihilate α ψ) :=
  coherent_annihilation_bound u v hspinor (pairAnnihilate α ψ)
    (pairAnnihilate_isBosonic α ψ hψ)

/-- H_Q ≥ B_beta† B_beta for the physical bosonic sector, with B_beta=a_beta²/√2. -/
theorem coherent_pairAnnihilation_bound {Q N : ℕ} (u v : ℂ)
    (hspinor : Complex.normSq u + Complex.normSq v = 1)
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    normSq (pairAnnihilate (coherentOrbital Q u v) ψ) ≤ energy ψ := by
  rw [← projectionPairs_eq_pairAnnihilate_normSq _ ψ hψ]
  exact coherent_pairOccupation_le_energy u v hspinor ψ

end
end BosonicLaughlin

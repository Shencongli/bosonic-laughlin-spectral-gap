import BosonicLaughlin.Occupation
import BosonicLaughlin.HamiltonianForms

/-! Occupation control for the north-pole spin-coherent orbital e_0.
These inequalities hold on the whole finite tensor space, and hence on its
bosonic subspace, for every flux and every particle number. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem northPole_pairOccupation_le_energy {Q N : ℕ} (ψ : State Q N) :
    orbitalPairOccupation (0 : Orbital Q) ψ ≤ energy ψ := by
  rw [orbitalPairOccupation_eq_pair_sum, energy_eq_sum_pairs]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hij
  · exact pairApply_northPole_bound i j (ne_of_lt hij) ψ
  · exact le_rfl

/-- n_0 ≤ H_Q + I, with coefficient one at every N and Q. -/
theorem northPole_occupation_le_energy_add_norm {Q N : ℕ} (ψ : State Q N) :
    orbitalOccupation (0 : Orbital Q) ψ ≤ energy ψ + normSq ψ := by
  have h1 := orbitalOccupation_le_pairs_add_norm (0 : Orbital Q) ψ
  have h2 := northPole_pairOccupation_le_energy ψ
  linarith

/-- The bound remains valid after any map into the output N-particle sector.
In particular it can be applied to an explicitly defined two-particle
annihilation map. No constant depends on input or output particle number. -/
theorem northPole_occupation_lift {Q M N : ℕ}
    (B : State Q M →ₗ[ℂ] State Q N) (ψ : State Q M) :
    orbitalOccupation (0 : Orbital Q) (B ψ) ≤ energy (B ψ) + normSq (B ψ) :=
  northPole_occupation_le_energy_add_norm (B ψ)

end
end BosonicLaughlin

import BosonicLaughlin.CoherentPair
import BosonicLaughlin.HamiltonianForms
import Mathlib.Tactic.Linarith

namespace BosonicLaughlin
noncomputable section
open Finset

/-- Finite-dimensional Bessel inequality, proved by a squared residual. -/
theorem normalized_contraction_bound {ι : Type*} [Fintype ι]
    (c b : ι → ℂ) (hc : ∑ p, Complex.normSq (c p) = 1) :
    Complex.normSq (∑ p, star (c p) * b p) ≤ ∑ p, Complex.normSq (b p) := by
  let z : ℂ := ∑ p, star (c p) * b p
  have hz : ∑ p, b p * star (c p) = z := by simp only [z, mul_comm]
  have hcross : ∑ p, (b p * star (c p * z)).re = Complex.normSq z := by
    rw [← Complex.re_sum]
    simp only [Complex.star_def, map_mul, ← mul_assoc]
    rw [← Finset.sum_mul]
    change ((∑ p, b p * star (c p)) * star z).re = _
    rw [hz, mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re]
  have hn : 0 ≤ ∑ p, Complex.normSq (b p - c p * z) :=
    Finset.sum_nonneg fun p _ => Complex.normSq_nonneg _
  simp only [Complex.normSq_sub, Complex.normSq_mul, ← Complex.star_def] at hn
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    hc, one_mul, ← Finset.mul_sum, hcross] at hn
  change Complex.normSq z ≤ _
  linarith

/-- Contract two tensor slots against a specified orbital; the remaining slots
are retained exactly and no bosonic combinatorial normalization is inserted. -/
def modePairContraction {Q N : ℕ} (β : Orbital Q → ℂ) (i j : Fin N)
    (ψ : State Q N) (s : PairSpectator Q N i j) : ℂ :=
  ∑ x : Orbital Q, ∑ y : Orbital Q,
    star (β x) * star (β y) * ψ (pairConfiguration i j s x y)

theorem coherent_modePairContraction {Q N : ℕ} (u v : ℂ) (i j : Fin N)
    (ψ : State Q N) (s : PairSpectator Q N i j) :
    modePairContraction (coherentOrbital Q u v) i j ψ s =
      ∑ p : Fin (2*Q+1), star (coherentCoefficient (2*Q) p.val u v) *
        pairContraction i j ψ s p := by
  have hxy (x y : Orbital Q) :
      star (coherentOrbital Q u v x) * star (coherentOrbital Q u v y) =
        ∑ p : Fin (2*Q+1), (pairVector Q p.val x y : ℂ) *
          star (coherentCoefficient (2*Q) p.val u v) := by
    simp only [Complex.star_def]
    rw [← map_mul, coherentOrbital_pair_expansion, map_sum]
    simp only [map_mul, Complex.conj_ofReal]
  unfold modePairContraction
  simp_rw [hxy, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (univ : Finset (Orbital Q)))
    (t := (univ : Finset (Fin (2*Q+1))))]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  simp only [pairContraction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The actual V₀ pair projector dominates double occupancy of every normalized
spin-coherent orbital. The inequality holds on the full tensor state space. -/
theorem pairApply_coherent_bound {Q N : ℕ} (u v : ℂ)
    (hspinor : Complex.normSq u + Complex.normSq v = 1)
    (i j : Fin N) (hij : i ≠ j) (ψ : State Q N) :
    (∑ s : PairSpectator Q N i j,
      Complex.normSq (modePairContraction (coherentOrbital Q u v) i j ψ s)) ≤
      (inner ψ (pairApply i j ψ)).re := by
  rw [pairApply_energy_identity i j hij]
  apply Finset.sum_le_sum
  intro s _
  rw [coherent_modePairContraction]
  exact normalized_contraction_bound (coherentOrbital (2*Q) u v)
    (pairContraction i j ψ s) (coherentOrbital_normalized (2*Q) u v hspinor)

/-- Total coherent double-occupancy cost is bounded by the physical Hamiltonian. -/
theorem coherent_pairCost_le_energy {Q N : ℕ} (u v : ℂ)
    (hspinor : Complex.normSq u + Complex.normSq v = 1) (ψ : State Q N) :
    (∑ i : Fin N, ∑ j : Fin N, if i < j then
      ∑ s : PairSpectator Q N i j,
        Complex.normSq (modePairContraction (coherentOrbital Q u v) i j ψ s)
      else 0) ≤ energy ψ := by
  rw [energy_eq_sum_pairs]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hij
  · exact pairApply_coherent_bound u v hspinor i j (ne_of_lt hij) ψ
  · exact le_rfl

end
end BosonicLaughlin

import BosonicLaughlin.ModeProjectors
import BosonicLaughlin.HamiltonianForms
import BosonicLaughlin.ProjectionOccupation
import BosonicLaughlin.CoherentBound

/-!
Quadratic forms of actual one-orbital tensor-slot projectors. These identities
connect the matrix occupation operators to physical contraction amplitudes;
they do not assume that the orbital is normalized or coherent.
-/
namespace BosonicLaughlin
noncomputable section
open Finset Matrix

def modeSingleContraction {Q N : ℕ} (i : Fin N) (β : Orbital Q → ℂ)
    (ψ : State Q N) (s : SlotSpectator Q N i) : ℂ :=
  ∑ x : Orbital Q, star (β x) * ψ (slotConfiguration i s x)

theorem update_slotConfiguration {Q N : ℕ} (i : Fin N)
    (s : SlotSpectator Q N i) (x y : Orbital Q) :
    Function.update (slotConfiguration i s x) i y = slotConfiguration i s y := by
  funext k
  by_cases hi : k=i
  · subst k; simp
  · simp [slotConfiguration, hi]

theorem modeApply_slotConfiguration {Q N : ℕ} (i : Fin N) (β : Orbital Q → ℂ)
    (ψ : State Q N) (s : SlotSpectator Q N i) (x : Orbital Q) :
    modeApply i β ψ (slotConfiguration i s x) = β x * modeSingleContraction i β ψ s := by
  simp only [modeApply, slotConfiguration_at_slot, update_slotConfiguration,
    modeSingleContraction]

theorem modeMatrix_inner {Q N : ℕ} (i : Fin N) (β : Orbital Q → ℂ)
    (ψ φ : State Q N) : inner ψ (modeMatrix i β *ᵥ φ) =
      ∑ s : SlotSpectator Q N i,
        star (modeSingleContraction i β ψ s) * modeSingleContraction i β φ s := by
  rw [modeMatrix_mulVec]
  unfold inner
  rw [sum_configurations_slot i]
  apply Finset.sum_congr rfl
  intro s _
  simp only [modeApply_slotConfiguration, modeSingleContraction, Complex.star_def,
    map_sum, map_mul, starRingEnd_self_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem modeMatrix_energy_identity {Q N : ℕ} (i : Fin N) (β : Orbital Q → ℂ)
    (ψ : State Q N) : (inner ψ (modeMatrix i β *ᵥ ψ)).re =
      ∑ s : SlotSpectator Q N i, Complex.normSq (modeSingleContraction i β ψ s) := by
  rw [modeMatrix_inner]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  change (starRingEnd ℂ (modeSingleContraction i β ψ s) *
    modeSingleContraction i β ψ s).re = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem modeApply_pairConfiguration {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (β : Orbital Q → ℂ) (ψ : State Q N) (s : PairSpectator Q N i j)
    (x y : Orbital Q) :
    modeApply i β (modeApply j β ψ) (pairConfiguration i j s x y) =
      β x * β y * ∑ u : Orbital Q, ∑ v : Orbital Q,
        star (β u) * star (β v) * ψ (pairConfiguration i j s u v) := by
  simp only [modeApply, pairConfiguration_at_left,
    Function.update_of_ne hij.symm, pairConfiguration_at_right i j hij]
  change β x * (∑ u, star (β u) * (β y * ∑ v, star (β v) *
    ψ (replacePair (pairConfiguration i j s x y) i j u v))) = _
  simp only [replacePair_pairConfiguration i j hij]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem modeMatrix_pair_inner {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (β : Orbital Q → ℂ) (ψ φ : State Q N) :
    inner ψ ((modeMatrix i β * modeMatrix j β) *ᵥ φ) =
      ∑ s : PairSpectator Q N i j,
        star (modePairContraction β i j ψ s) * modePairContraction β i j φ s := by
  rw [← Matrix.mulVec_mulVec, modeMatrix_mulVec, modeMatrix_mulVec]
  unfold inner
  rw [sum_configurations_pair i j hij]
  apply Finset.sum_congr rfl
  intro s _
  simp only [modeApply_pairConfiguration i j hij, modePairContraction, Complex.star_def,
    map_sum, map_mul, starRingEnd_self_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem modeMatrix_pair_energy_identity {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (β : Orbital Q → ℂ) (ψ : State Q N) :
    (inner ψ ((modeMatrix i β * modeMatrix j β) *ᵥ ψ)).re =
      ∑ s : PairSpectator Q N i j, Complex.normSq (modePairContraction β i j ψ s) := by
  rw [modeMatrix_pair_inner i j hij]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  change (starRingEnd ℂ (modePairContraction β i j ψ s) *
    modePairContraction β i j ψ s).re = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem projectionNumber_mode_energy_identity {Q N : ℕ} (β : Orbital Q → ℂ)
    (ψ : State Q N) :
    (inner ψ (projectionNumber (fun i : Fin N => modeMatrix i β) *ᵥ ψ)).re =
      ∑ i : Fin N, ∑ s : SlotSpectator Q N i,
        Complex.normSq (modeSingleContraction i β ψ s) := by
  simp only [projectionNumber, Matrix.sum_mulVec, inner, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [inner, Complex.re_sum] using modeMatrix_energy_identity i β ψ

theorem projectionPairs_mode_energy_identity {Q N : ℕ} (β : Orbital Q → ℂ)
    (ψ : State Q N) :
    (inner ψ (projectionPairs (fun i : Fin N => modeMatrix i β) *ᵥ ψ)).re =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then
        ∑ s : PairSpectator Q N i j, Complex.normSq (modePairContraction β i j ψ s)
        else 0 := by
  have hinner : inner ψ (projectionPairs (fun i : Fin N => modeMatrix i β) *ᵥ ψ) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then
        inner ψ ((modeMatrix i β * modeMatrix j β) *ᵥ ψ) else 0 := by
    simp only [projectionPairs, Matrix.sum_mulVec, inner, Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hinner]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    exact modeMatrix_pair_energy_identity i j (ne_of_lt hij) β ψ
  · simp [hij]

end
end BosonicLaughlin

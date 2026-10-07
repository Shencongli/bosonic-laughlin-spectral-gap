import BosonicLaughlin.Model
import BosonicLaughlin.PairBlock

namespace BosonicLaughlin
noncomputable section
open Finset

/-- Coordinates of all tensor slots except the two indicated slots. -/
abbrev PairSpectator (Q N : ℕ) (i j : Fin N) :=
  {k : Fin N // k ≠ i ∧ k ≠ j} → Orbital Q

def pairConfiguration {Q N : ℕ} (i j : Fin N)
    (s : PairSpectator Q N i j) (x y : Orbital Q) : Configuration Q N :=
  fun k => if h : k = i then x else if h' : k = j then y else s ⟨k, h, h'⟩

@[simp] theorem pairConfiguration_at_left {Q N : ℕ} (i j : Fin N)
    (s : PairSpectator Q N i j) (x y : Orbital Q) :
    pairConfiguration i j s x y i = x := by simp [pairConfiguration]

@[simp] theorem pairConfiguration_at_right {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (s : PairSpectator Q N i j) (x y : Orbital Q) :
    pairConfiguration i j s x y j = y := by simp [pairConfiguration, hij.symm]

@[simp] theorem pairConfiguration_at_spectator {Q N : ℕ} (i j : Fin N)
    (s : PairSpectator Q N i j) (x y : Orbital Q)
    (k : {k : Fin N // k ≠ i ∧ k ≠ j}) :
    pairConfiguration i j s x y k = s k := by
  simp [pairConfiguration, k.property.1, k.property.2]

def pairConfigurationEquiv {Q N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    (PairSpectator Q N i j × (Orbital Q × Orbital Q)) ≃ Configuration Q N where
  toFun := fun z => pairConfiguration i j z.1 z.2.1 z.2.2
  invFun := fun a => (fun k => a k, a i, a j)
  left_inv := by
    intro ⟨s, x, y⟩
    simp only [Prod.mk.injEq, pairConfiguration_at_left,
      pairConfiguration_at_right i j hij, and_true]
    funext k
    exact pairConfiguration_at_spectator i j s x y k
  right_inv := by
    intro a
    funext k
    simp only [pairConfiguration]
    split_ifs with hi hj
    · subst k; rfl
    · subst k; rfl
    · rfl

/-- Exact decomposition of the tensor basis into two orbitals and spectators. -/
theorem sum_configurations_pair {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    {A : Type*} [AddCommMonoid A] (f : Configuration Q N → A) :
    ∑ a, f a = ∑ s : PairSpectator Q N i j,
      ∑ x : Orbital Q, ∑ y : Orbital Q, f (pairConfiguration i j s x y) := by
  rw [← (pairConfigurationEquiv i j hij).sum_comp f]
  simp only [Fintype.sum_prod_type, pairConfigurationEquiv, Equiv.coe_fn_mk]

@[simp] theorem replacePair_pairConfiguration {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (s : PairSpectator Q N i j) (x y u v : Orbital Q) :
    replacePair (pairConfiguration i j s x y) i j u v =
      pairConfiguration i j s u v := by
  funext k
  by_cases hi : k = i
  · subst k
    simp [replacePair, hij, pairConfiguration]
  by_cases hj : k = j
  · subst k
    simp [replacePair, hij.symm, pairConfiguration]
  simp [replacePair, hi, hj, pairConfiguration]

/-- Annihilation of a normalized V₀ pair, with every remaining tensor slot fixed. -/
def pairContraction {Q N : ℕ} (i j : Fin N) (ψ : State Q N)
    (s : PairSpectator Q N i j) (p : Fin (2*Q+1)) : ℂ :=
  ∑ x : Orbital Q, ∑ y : Orbital Q,
    (pairVector Q p.val x y : ℂ) * ψ (pairConfiguration i j s x y)

theorem pairApply_pairConfiguration {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State Q N) (s : PairSpectator Q N i j) (x y : Orbital Q) :
    pairApply i j ψ (pairConfiguration i j s x y) =
      ∑ p : Fin (2*Q+1), (pairVector Q p.val x y : ℂ) *
        pairContraction i j ψ s p := by
  simp only [pairApply, pairConfiguration_at_left, pairConfiguration_at_right i j hij,
    replacePair_pairConfiguration i j hij, pairContraction]

/-- Hermitian Gram factorization of the actual pair operator on the full tensor space. -/
theorem pairApply_inner {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ φ : State Q N) :
    inner ψ (pairApply i j φ) =
      ∑ s : PairSpectator Q N i j, ∑ p : Fin (2*Q+1),
        star (pairContraction i j ψ s p) * pairContraction i j φ s p := by
  unfold inner
  rw [sum_configurations_pair i j hij]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [pairApply_pairConfiguration i j hij, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (univ : Finset (Orbital Q)))
    (t := (univ : Finset (Fin (2*Q+1))))]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  simp only [pairContraction, Complex.star_def, map_sum, map_mul,
    Complex.conj_ofReal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem pairApply_energy_identity {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State Q N) :
    (inner ψ (pairApply i j ψ)).re =
      ∑ s : PairSpectator Q N i j, ∑ p : Fin (2*Q+1),
        Complex.normSq (pairContraction i j ψ s p) := by
  rw [pairApply_inner i j hij]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  change (starRingEnd ℂ (pairContraction i j ψ s p) *
    pairContraction i j ψ s p).re = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem pairApply_energy_nonneg {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State Q N) : 0 ≤ (inner ψ (pairApply i j ψ)).re := by
  rw [pairApply_energy_identity i j hij]
  exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun p _ => Complex.normSq_nonneg _

theorem pairVector_zero (Q : ℕ) (x y : Orbital Q) :
    pairVector Q 0 x y = if x = 0 ∧ y = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst x
    by_cases hy : y = 0
    · subst y
      simp [pairVector, pairCoefficient, pairWeight]
    · have hy' : y.val ≠ 0 := fun h => hy (Fin.ext h)
      simp [pairVector, hy, hy']
  · have hx' : x.val ≠ 0 := fun h => hx (Fin.ext h)
    simp [pairVector, hx]

theorem pairContraction_zero {Q N : ℕ} (i j : Fin N) (ψ : State Q N)
    (s : PairSpectator Q N i j) :
    pairContraction i j ψ s 0 = ψ (pairConfiguration i j s 0 0) := by
  simp [pairContraction, pairVector_zero, ite_and, apply_ite, ite_mul,
    Finset.sum_ite_irrel]

/-- The p=0 pair channel is the projector onto two north-pole coherent orbitals. -/
theorem pairApply_northPole_bound {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State Q N) :
    (∑ a : Configuration Q N,
      if a i = 0 ∧ a j = 0 then Complex.normSq (ψ a) else 0) ≤
      (inner ψ (pairApply i j ψ)).re := by
  rw [sum_configurations_pair i j hij, pairApply_energy_identity i j hij]
  simp only [pairConfiguration_at_left, pairConfiguration_at_right i j hij]
  simp only [ite_and]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_le_sum
  intro s _
  rw [← pairContraction_zero i j ψ s]
  exact Finset.single_le_sum (fun p _ => Complex.normSq_nonneg _) (Finset.mem_univ 0)

theorem inner_star {Q N : ℕ} (ψ φ : State Q N) :
    star (inner ψ φ) = inner φ ψ := by
  simp [inner, Complex.star_def, map_sum, mul_comm]

theorem pairApply_hermitian {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ φ : State Q N) : inner ψ (pairApply i j φ) = inner (pairApply i j ψ) φ := by
  conv_rhs => rw [← inner_star]
  rw [pairApply_inner i j hij, pairApply_inner i j hij]
  simp [Complex.star_def, map_sum, mul_comm]

theorem hamiltonian_inner {Q N : ℕ} (ψ φ : State Q N) :
    inner ψ (hamiltonian φ) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then inner ψ (pairApply i j φ) else 0 := by
  simp only [inner, hamiltonian, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem hamiltonian_hermitian {Q N : ℕ} (ψ φ : State Q N) :
    inner ψ (hamiltonian φ) = inner (hamiltonian ψ) φ := by
  conv_rhs => rw [← inner_star]
  rw [hamiltonian_inner, hamiltonian_inner]
  simp only [Complex.star_def, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    rw [pairApply_hermitian i j (ne_of_lt hij), ← Complex.star_def, inner_star]
  · simp [hij]

theorem energy_eq_sum_pairs {Q N : ℕ} (ψ : State Q N) :
    energy ψ = ∑ i : Fin N, ∑ j : Fin N,
      if i < j then (inner ψ (pairApply i j ψ)).re else 0 := by
  unfold energy
  rw [hamiltonian_inner]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

theorem energy_nonneg {Q N : ℕ} (ψ : State Q N) : 0 ≤ energy ψ := by
  rw [energy_eq_sum_pairs]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs with hij
  · exact pairApply_energy_nonneg i j (ne_of_lt hij) ψ
  · exact le_rfl

end
end BosonicLaughlin

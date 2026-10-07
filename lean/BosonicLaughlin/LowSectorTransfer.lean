import BosonicLaughlin.CertificateRows
import BosonicLaughlin.CertificateSingleIntertwiner

/-! One-body transfers in the one- and two-particle output sectors of a
certificate row. These identities perform the actual normal ordering. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def vacuumConfiguration (Q : ℕ) : Configuration Q 0 := Fin.elim0
def oneConfiguration {Q : ℕ} (i : Orbital Q) : Configuration Q 1 :=
  Fin.cons i (vacuumConfiguration Q)
def twoConfiguration {Q : ℕ} (i j : Orbital Q) : Configuration Q 2 :=
  Fin.cons i (oneConfiguration j)

theorem stateInner_vacuum {Q : ℕ} (ψ φ : State Q 0) :
    inner ψ φ=star (ψ (vacuumConfiguration Q))*φ (vacuumConfiguration Q) := by
  exact Fintype.sum_unique _

theorem stateInner_one {Q : ℕ} (ψ φ : State Q 1) :
    inner ψ φ=∑ i : Orbital Q, star (ψ (oneConfiguration i))*φ (oneConfiguration i) := by
  unfold inner
  rw [sum_configurations_cons]
  apply Finset.sum_congr rfl
  intro i _
  exact Fintype.sum_unique _

theorem stateInner_two {Q : ℕ} (ψ φ : State Q 2) :
    inner ψ φ=∑ i : Orbital Q, ∑ j : Orbital Q,
      star (ψ (twoConfiguration i j))*φ (twoConfiguration i j) := by
  unfold inner
  rw [sum_configurations_cons]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_configurations_cons]
  apply Finset.sum_congr rfl
  intro j _
  exact Fintype.sum_unique _

theorem twoConfiguration_swap {Q : ℕ} (i j : Orbital Q) :
    twoConfiguration i j ∘ Equiv.swap 0 1=twoConfiguration j i := by
  funext k
  fin_cases k <;> simp [twoConfiguration, oneConfiguration]

theorem bosonic_two_swap {Q : ℕ} (ψ : State Q 2) (hψ : IsBosonic ψ) (i j : Orbital Q) :
    ψ (twoConfiguration i j)=ψ (twoConfiguration j i) := by
  simpa only [twoConfiguration_swap] using (hψ (Equiv.swap 0 1) (twoConfiguration i j)).symm

theorem orbitalTransfer_one_apply {Q : ℕ} (i j x : Orbital Q) (ψ : State Q 1) :
    orbitalTransfer i j ψ (oneConfiguration x)=if x=i then ψ (oneConfiguration j) else 0 := by
  simp only [orbitalTransfer, Fin.sum_univ_one, oneConfiguration, Fin.cons_zero]
  congr 1
  congr 1
  funext k
  fin_cases k
  simp

theorem orbitalTransfer_two_apply {Q : ℕ} (i j x y : Orbital Q) (ψ : State Q 2) :
    orbitalTransfer i j ψ (twoConfiguration x y)=
      (if x=i then ψ (twoConfiguration j y) else 0) +
      (if y=i then ψ (twoConfiguration x j) else 0) := by
  have h0 : Function.update (twoConfiguration x y) 0 j=twoConfiguration j y := by
    funext k; fin_cases k <;> simp [twoConfiguration, oneConfiguration]
  have h1 : Function.update (twoConfiguration x y) 1 j=twoConfiguration x j := by
    funext k; fin_cases k <;> simp [twoConfiguration, oneConfiguration]
  simp only [orbitalTransfer, Fin.sum_univ_two, h0, h1]
  rfl

theorem single_annihilate_inner_one {Q : ℕ} (i j : Orbital Q) (ψ φ : State Q 1) :
    inner (annihilate (Pi.single i 1) ψ) (annihilate (Pi.single j 1) φ)=
      star (ψ (oneConfiguration i))*φ (oneConfiguration j) := by
  rw [stateInner_vacuum, annihilate_single_apply, annihilate_single_apply]
  simp [oneConfiguration]

theorem single_annihilate_inner_two {Q : ℕ} (i j : Orbital Q) (ψ φ : State Q 2) :
    inner (annihilate (Pi.single i 1) ψ) (annihilate (Pi.single j 1) φ)=
      2*∑ x : Orbital Q, star (ψ (twoConfiguration i x))*φ (twoConfiguration j x) := by
  rw [stateInner_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [annihilate_single_apply, annihilate_single_apply]
  norm_num only [Nat.cast_one, Nat.cast_zero, Nat.cast_add, zero_add]
  change star ((Real.sqrt 2 : ℂ)*ψ (twoConfiguration i x)) *
    ((Real.sqrt 2 : ℂ)*φ (twoConfiguration j x))=_
  have hs : (Real.sqrt 2 : ℂ)^2=2 := by norm_cast; exact Real.sq_sqrt (by norm_num)
  rw [star_mul, show star (Real.sqrt 2 : ℂ)=(Real.sqrt 2 : ℂ) by simp]
  linear_combination (star (ψ (twoConfiguration i x))*φ (twoConfiguration j x))*hs

theorem double_annihilate_inner_two {Q : ℕ} (i j k l : Orbital Q) (ψ φ : State Q 2) :
    inner (annihilate (Pi.single k 1) (annihilate (Pi.single j 1) ψ))
      (annihilate (Pi.single i 1) (annihilate (Pi.single l 1) φ)) =
        2*star (ψ (twoConfiguration j k))*φ (twoConfiguration l i) := by
  rw [single_annihilate_inner_one, annihilate_single_apply, annihilate_single_apply]
  norm_num only [Nat.cast_one, Nat.cast_zero, Nat.cast_add, zero_add]
  have hs : (Real.sqrt 2 : ℂ)^2=2 := by norm_cast; exact Real.sq_sqrt (by norm_num)
  change star ((Real.sqrt 2 : ℂ)*ψ (twoConfiguration j k)) *
    ((Real.sqrt 2 : ℂ)*φ (twoConfiguration l i))=_
  rw [star_mul, show star (Real.sqrt 2 : ℂ)=(Real.sqrt 2 : ℂ) by simp]
  linear_combination (star (ψ (twoConfiguration j k))*φ (twoConfiguration l i))*hs

theorem orbitalTransfer_inner_one {Q : ℕ} (i j : Orbital Q) (ψ φ : State Q 1) :
    inner ψ (orbitalTransfer i j φ)=
      inner (annihilate (Pi.single i 1) ψ) (annihilate (Pi.single j 1) φ) := by
  rw [stateInner_one, single_annihilate_inner_one]
  simp [orbitalTransfer_one_apply, mul_ite]

theorem orbitalTransfer_gram_one {Q : ℕ} (i j k l : Orbital Q) (ψ φ : State Q 1) :
    inner (orbitalTransfer i j ψ) (orbitalTransfer k l φ)=
      if i=k then inner (annihilate (Pi.single j 1) ψ) (annihilate (Pi.single l 1) φ) else 0 := by
  rw [stateInner_one, single_annihilate_inner_one]
  by_cases h : i=k
  · simp [orbitalTransfer_one_apply, h, mul_ite]
  · simp [orbitalTransfer_one_apply, h, Ne.symm h, mul_ite]

theorem orbitalTransfer_inner_two {Q : ℕ} (i j : Orbital Q) (ψ φ : State Q 2)
    (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner ψ (orbitalTransfer i j φ)=
      inner (annihilate (Pi.single i 1) ψ) (annihilate (Pi.single j 1) φ) := by
  rw [stateInner_two, single_annihilate_inner_two]
  simp only [orbitalTransfer_two_apply, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hs : (∑ x : Orbital Q, star (ψ (twoConfiguration x i))*φ (twoConfiguration x j))=
      ∑ x : Orbital Q, star (ψ (twoConfiguration i x))*φ (twoConfiguration j x) := by
    exact Finset.sum_congr rfl (fun x _ => by rw [bosonic_two_swap ψ hψ x i, bosonic_two_swap φ hφ x j])
  rw [hs]
  ring

theorem orbitalTransfer_gram_two {Q : ℕ} (i j k l : Orbital Q) (ψ φ : State Q 2)
    (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner (orbitalTransfer i j ψ) (orbitalTransfer k l φ)=
      (if i=k then inner (annihilate (Pi.single j 1) ψ) (annihilate (Pi.single l 1) φ) else 0) +
        inner (annihilate (Pi.single k 1) (annihilate (Pi.single j 1) ψ))
          (annihilate (Pi.single i 1) (annihilate (Pi.single l 1) φ)) := by
  rw [stateInner_two, single_annihilate_inner_two, double_annihilate_inner_two]
  simp only [orbitalTransfer_two_apply, star_add, add_mul, mul_add, Finset.sum_add_distrib]
  by_cases hik : i=k
  · subst k
    simp only [ite_true]
    simp [apply_ite, ite_mul, bosonic_two_swap ψ hψ, bosonic_two_swap φ hφ]
    ring
  · simp [hik, Ne.symm hik, apply_ite, ite_mul, bosonic_two_swap ψ hψ, bosonic_two_swap φ hφ]
    ring

end
end BosonicLaughlin

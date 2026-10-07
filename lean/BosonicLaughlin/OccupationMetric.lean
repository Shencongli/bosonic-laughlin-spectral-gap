import BosonicLaughlin.OccupationCoordinates
import BosonicLaughlin.OccupationPairFactorial
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Exact orbit multiplicities and the inherited occupation-coordinate metric. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem occupationOfConfiguration_eq_exists_permutation {Q N : ℕ}
    (a b : Configuration Q N) :
    occupationOfConfiguration a=occupationOfConfiguration b ↔
      ∃ σ : Equiv.Perm (Fin N), a ∘ σ=b := by
  constructor
  · intro hab
    have hp : List.Perm (List.ofFn a) (List.ofFn b) := Quotient.exact (congrArg Subtype.val hab)
    have hs : a ∘ Tuple.sort a = b ∘ Tuple.sort b := by
      apply List.ofFn_injective
      exact (((Tuple.sort a).ofFn_comp_perm a).trans
        (hp.trans ((Tuple.sort b).ofFn_comp_perm b).symm)).eq_of_pairwise'
        (Tuple.monotone_sort a).sortedLE_ofFn.pairwise
        (Tuple.monotone_sort b).sortedLE_ofFn.pairwise
    refine ⟨(Tuple.sort b).symm.trans (Tuple.sort a), ?_⟩
    funext i
    have h := congrFun hs ((Tuple.sort b).symm i)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.trans_apply] using h
  · rintro ⟨σ, rfl⟩
    exact (occupationOfConfiguration_permute a σ).symm

theorem occupationOfConfiguration_count {Q N : ℕ} (a : Configuration Q N) (j : Orbital Q) :
    (occupationOfConfiguration a).val.count j =
      Fintype.card {i : Fin N // a i=j} := by
  have hc : (List.ofFn a).count j = ∑ i : Fin N, if a i=j then 1 else 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ]
      rw [ih]
      split_ifs <;> simp_all [beq_iff_eq, add_comm]
  rw [show (occupationOfConfiguration a).val = (List.ofFn a : Multiset (Orbital Q)) from rfl,
    Multiset.coe_count]
  rw [hc, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

def occupationOrbitMultiplicity {Q N : ℕ} (A : Occupation Q N) : ℕ :=
  Fintype.card {a : Configuration Q N // occupationOfConfiguration a=A}

theorem occupationOrbitMultiplicity_mul_factorial {Q N : ℕ} (A : Occupation Q N) :
    occupationOrbitMultiplicity A * multisetOccupationFactorial A.val = N.factorial := by
  classical
  obtain ⟨a,rfl⟩ := occupationOfConfiguration_surjective Q N A
  let G := DomMulAct (Equiv.Perm (Fin N))
  letI : Fintype G := Fintype.ofEquiv (Equiv.Perm (Fin N)) DomMulAct.mk
  letI : Fintype (MulAction.orbit G a) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer G a) := Fintype.ofFinite _
  have ho : MulAction.orbit G a =
      {b : Configuration Q N | occupationOfConfiguration b=occupationOfConfiguration a} := by
    ext b
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      exact occupationOfConfiguration_permute a (DomMulAct.mk.symm g)
    · intro h
      obtain ⟨σ,hσ⟩ := (occupationOfConfiguration_eq_exists_permutation a b).mp h.symm
      exact ⟨DomMulAct.mk σ, hσ⟩
  have hoc : Fintype.card (MulAction.orbit G a) =
      occupationOrbitMultiplicity (occupationOfConfiguration a) :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun b => Set.ext_iff.mp ho b))
  have hs : Fintype.card (MulAction.stabilizer G a) =
      multisetOccupationFactorial (occupationOfConfiguration a).val := by
    calc
      _ = Fintype.card {σ : Equiv.Perm (Fin N) // a ∘ σ=a} :=
        Fintype.card_congr (Equiv.subtypeEquiv DomMulAct.mk.symm
          (fun _ => DomMulAct.mem_stabilizer_iff))
      _ = _ := by
        rw [DomMulAct.stabilizer_card]
        simp only [multisetOccupationFactorial, occupationOfConfiguration_count]
  have hg : Fintype.card G = N.factorial := by
    rw [← Fintype.card_congr (DomMulAct.mk : Equiv.Perm (Fin N) ≃ G),
      Fintype.card_perm, Fintype.card_fin]
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G a
  rw [hoc, hs, hg] at h
  exact h

theorem occupationOrbitMultiplicity_eq {Q N : ℕ} (A : Occupation Q N) :
    occupationOrbitMultiplicity A = N.factorial / multisetOccupationFactorial A.val := by
  rw [← occupationOrbitMultiplicity_mul_factorial A]
  exact (Nat.mul_div_cancel _ (multisetOccupationFactorial_pos A.val)).symm

theorem occupationInclude_inner {Q N : ℕ} (c e : OccupationState Q N) :
    inner (occupationInclude c) (occupationInclude e) =
      ∑ A : Occupation Q N, (occupationOrbitMultiplicity A : ℂ) * star (c A) * e A := by
  unfold inner occupationInclude
  rw [← Fintype.sum_fiberwise' (@occupationOfConfiguration Q N)
    (fun A => star (c A)*e A)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, occupationOrbitMultiplicity,
    mul_assoc]

end
end BosonicLaughlin

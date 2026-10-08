import BosonicLaughlin.OccupationLowering
import BosonicLaughlin.IndexedOccupationCM

/-! Computable affine-in-1/Q lowering entries in the verifier's sorted order.
The row reconstructs its source by i -> i-1, inverse to source j -> j+1.
The multiplicity always belongs to the source. -/
namespace BosonicLaughlin
open Finset

def multisetLowerEntry (i : ℕ) (B A : Multiset ℕ) : ℕ :=
  if 0 < i ∧ i ∈ B ∧ (i-1) ::ₘ B.erase i=A then A.count (i-1) else 0

def tupleLowerConstant (d : ℕ) (B A : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d+2), multisetLowerEntry i (B : Multiset ℕ) (A : Multiset ℕ)

def tupleLowerSlope (d : ℕ) (B A : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d+2), (i-1)*multisetLowerEntry i (B : Multiset ℕ) (A : Multiset ℕ)

theorem multisetLowerEntry_zero (A B : Multiset ℕ) : multisetLowerEntry 0 B A=0 := by
  simp [multisetLowerEntry]

theorem verifierRaiseMatrix_nat {Q N d : ℕ} (hQ : 0 < Q)
    (B : WeightOccupation Q N (d+1)) (A : WeightOccupation Q N d) :
    verifierRaiseMatrix Q N d B A=∑ i ∈ Finset.range (Q+1),
      (1-((i-1 : ℕ) : ℂ)/(Q : ℂ))*
        (multisetLowerEntry i (occupationNatMultiset B.val) (occupationNatMultiset A.val) : ℂ) := by
  classical
  have hq : (Q : ℂ)≠0 := by exact_mod_cast hQ.ne'
  rw [verifierRaiseMatrix_apply, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 < i.val
  · simp only [hi, dite_true]
    by_cases hm : i ∈ B.val.val
    · simp only [hm, dite_true]
      let j : Orbital Q := ⟨i.val-1, by omega⟩
      have he := occupationNatMultiset_replace_iff A.val B.val i j hm
      have hc := occupationNatMultiset_count A.val j
      simp only [multisetLowerEntry, hi, (occupationNatMultiset_mem B.val i).mpr hm, true_and]
      change (Q : ℂ)⁻¹*(if occupationReplace B.val i j hm=A.val then
        (((Q-j.val)*A.val.val.count j : ℕ) : ℂ) else 0)=
        (1-(j.val : ℂ)/(Q : ℂ))*((if j.val ::ₘ (occupationNatMultiset B.val).erase i.val=
          occupationNatMultiset A.val then (occupationNatMultiset A.val).count j.val else 0 : ℕ) : ℂ)
      by_cases hp : occupationReplace B.val i j hm=A.val
      · simp only [hp, he.mp hp, ite_true, hc, Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt_succ j.isLt)]
        field_simp
      · simp [hp, he.not.mp hp]
    · have hn := (occupationNatMultiset_mem B.val i).not.mpr hm
      rw [dite_eq_right hm]
      simp [multisetLowerEntry, hn]
  · have hz : i.val=0 := by omega
    simp [hz, multisetLowerEntry_zero]

theorem verifierRaiseMatrix_degree_sum {Q N d : ℕ} (hQ : 0 < Q) (hd : d+1≤Q)
    (B : WeightOccupation Q N (d+1)) (A : WeightOccupation Q N d) :
    verifierRaiseMatrix Q N d B A=∑ i ∈ Finset.range (d+2),
      (1-((i-1 : ℕ) : ℂ)/(Q : ℂ))*
        (multisetLowerEntry i (occupationNatMultiset B.val) (occupationNatMultiset A.val) : ℂ) := by
  rw [verifierRaiseMatrix_nat hQ]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i _ hi
  have hm : i ∉ occupationNatMultiset B.val := by
    intro hm
    have hb := occupationNatMultiset_mem_le_weight B.val hm
    rw [B.property] at hb
    simp only [Finset.mem_range] at hi
    omega
  simp [multisetLowerEntry, hm]

noncomputable def indexedVerifierRaiseMatrix {Q N d rows cols : ℕ} (hd : d+1≤Q)
    (src : SortedTupleEnumeration N d cols) (dst : SortedTupleEnumeration N (d+1) rows) :
    Matrix (Fin rows) (Fin cols) ℂ := fun i j => verifierRaiseMatrix Q N d
      (dst.occupationEquiv hd i) (src.occupationEquiv (by omega) j)

theorem indexedVerifierRaiseMatrix_apply {Q N d rows cols : ℕ} (hQ : 0 < Q) (hd : d+1≤Q)
    (src : SortedTupleEnumeration N d cols) (dst : SortedTupleEnumeration N (d+1) rows)
    (i : Fin rows) (j : Fin cols) :
    indexedVerifierRaiseMatrix hd src dst i j=
      (tupleLowerConstant d (List.ofFn (dst.tuple i).val) (List.ofFn (src.tuple j).val) : ℂ)-
      (Q : ℂ)⁻¹*(tupleLowerSlope d (List.ofFn (dst.tuple i).val) (List.ofFn (src.tuple j).val) : ℂ) := by
  rw [indexedVerifierRaiseMatrix, verifierRaiseMatrix_degree_sum hQ hd]
  change (∑ l ∈ Finset.range (d+2), (1-((l-1 : ℕ) : ℂ)/(Q : ℂ))*
    (multisetLowerEntry l (occupationNatMultiset (sortedDegreeOccupationEquiv hd (dst.tuple i)).val)
      (occupationNatMultiset (sortedDegreeOccupationEquiv (show d≤Q by omega) (src.tuple j)).val) : ℂ))=_
  rw [sortedDegreeOccupationEquiv_nat, sortedDegreeOccupationEquiv_nat]
  simp only [tupleLowerConstant, tupleLowerSlope, Nat.cast_sum, Nat.cast_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem indexedVerifierRaiseMatrix_eq_arrays {Q N d rows cols : ℕ} (hQ : 0 < Q) (hd : d+1≤Q)
    (src : SortedTupleEnumeration N d cols) (dst : SortedTupleEnumeration N (d+1) rows)
    (C S : Matrix (Fin rows) (Fin cols) ℕ)
    (hC : ∀ i j, C i j=tupleLowerConstant d (List.ofFn (dst.tuple i).val) (List.ofFn (src.tuple j).val))
    (hS : ∀ i j, S i j=tupleLowerSlope d (List.ofFn (dst.tuple i).val) (List.ofFn (src.tuple j).val)) :
    indexedVerifierRaiseMatrix hd src dst=C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • S.map (Nat.castRingHom ℂ) := by
  ext i j
  rw [indexedVerifierRaiseMatrix_apply hQ hd]
  simp [Matrix.map_apply, hC, hS]

theorem indexedVerifierRaiseMatrix_mulVec {Q N d rows cols : ℕ} (hd : d+1≤Q)
    (src : SortedTupleEnumeration N d cols) (dst : SortedTupleEnumeration N (d+1) rows)
    (c : Fin cols → ℂ) (i : Fin rows) :
    (indexedVerifierRaiseMatrix hd src dst).mulVec c i=
      verifierRaiseBlock Q N d (c ∘ (src.occupationEquiv (by omega)).symm) (dst.occupationEquiv hd i) := by
  rw [← verifierRaiseMatrix_mulVec]
  simp only [Matrix.mulVec, dotProduct, indexedVerifierRaiseMatrix, Function.comp_apply]
  rw [← (src.occupationEquiv (show d≤Q by omega)).sum_comp]
  simp

end BosonicLaughlin

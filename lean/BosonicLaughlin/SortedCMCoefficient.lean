import BosonicLaughlin.OccupationSortedCoordinates
import BosonicLaughlin.OccupationCMBlocks

/-! Computable integer CM entries on natural sorted tuples, connected to the
actual spherical occupation matrix. The row reconstructs its source by
replacing one label i by i+1; this is the inverse of the script's source rule. -/
namespace BosonicLaughlin
open Finset

def multisetCMEntry (i : ℕ) (B A : Multiset ℕ) : ℕ :=
  if i ∈ B ∧ (i+1) ::ₘ B.erase i = A then (i+1) * A.count (i+1) else 0

def tupleCMCoefficient (d : ℕ) (B A : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range d, multisetCMEntry i (B : Multiset ℕ) (A : Multiset ℕ)

def sortedCMCoefficient {N d : ℕ}
    (B : SortedDegreeTuple N (d-1)) (A : SortedDegreeTuple N d) : ℕ :=
  tupleCMCoefficient d (List.ofFn B.val) (List.ofFn A.val)

def occupationNatMultiset {Q N : ℕ} (A : Occupation Q N) : Multiset ℕ :=
  A.val.map Fin.val

theorem occupationNatMultiset_mem {Q N : ℕ} (A : Occupation Q N) (i : Orbital Q) :
    i.val ∈ occupationNatMultiset A ↔ i ∈ A.val := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := Multiset.mem_map.mp h
    exact (Fin.ext he) ▸ hj
  · intro h
    exact Multiset.mem_map.mpr ⟨i,h,rfl⟩

theorem occupationNatMultiset_mem_le {Q N i : ℕ} (A : Occupation Q N)
    (hi : i ∈ occupationNatMultiset A) : i ≤ Q := by
  obtain ⟨j,_,rfl⟩ := Multiset.mem_map.mp hi
  exact Nat.le_of_lt_succ j.isLt

theorem occupationNatMultiset_count {Q N : ℕ} (A : Occupation Q N) (i : Orbital Q) :
    (occupationNatMultiset A).count i.val = A.val.count i :=
  Multiset.count_map_eq_count' Fin.val A.val Fin.val_injective i

theorem occupationNatMultiset_replace_iff {Q N : ℕ} (A B : Occupation Q N)
    (i j : Orbital Q) (hi : i ∈ B.val) :
    occupationReplace B i j hi = A ↔
      j.val ::ₘ (occupationNatMultiset B).erase i.val = occupationNatMultiset A := by
  have hm := Multiset.map_erase Fin.val Fin.val_injective i B.val
  constructor
  · intro h
    have he := congrArg (fun S : Occupation Q N => S.val.map Fin.val) h
    simpa only [occupationReplace_val, Multiset.map_cons, hm, occupationNatMultiset] using he
  · intro h
    apply Sym.ext
    apply Multiset.map_injective Fin.val_injective
    change (j ::ₘ B.val.erase i).map Fin.val = A.val.map Fin.val
    simpa only [occupationReplace_val, Multiset.map_cons, hm, occupationNatMultiset] using h

theorem multisetCMEntry_above_cap {Q N i : ℕ} (A B : Occupation Q N)
    (hi : Q ≤ i) : multisetCMEntry i (occupationNatMultiset B) (occupationNatMultiset A)=0 := by
  unfold multisetCMEntry
  split_ifs with h
  · have hm : i+1 ∈ occupationNatMultiset A := h.2 ▸ Multiset.mem_cons_self _ _
    have hb := occupationNatMultiset_mem_le A hm
    omega
  · rfl

set_option backward.isDefEq.respectTransparency false in
theorem occupationCMMatrix_nat (Q N : ℕ) (B A : Occupation Q N) :
    occupationCMMatrix Q N B A =
      ((∑ i ∈ Finset.range (Q+1),
        multisetCMEntry i (occupationNatMultiset B) (occupationNatMultiset A) : ℕ) : ℂ) := by
  classical
  rw [occupationCMMatrix_apply, ← Fin.sum_univ_eq_sum_range]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val<Q
  · simp only [hi, dite_true]
    by_cases hm : i ∈ B.val
    · simp only [hm, dite_true]
      let j : Orbital Q := ⟨i.val+1, by omega⟩
      have he := occupationNatMultiset_replace_iff A B i j hm
      have hc := occupationNatMultiset_count A j
      change _ = (multisetCMEntry i.val (occupationNatMultiset B) (occupationNatMultiset A) : ℂ)
      simp only [multisetCMEntry, (occupationNatMultiset_mem B i).mpr hm, true_and]
      change (if occupationReplace B i j hm=A then
        ((i.val : ℂ)+1) * (A.val.count j : ℂ) else 0) =
        ((if j.val ::ₘ (occupationNatMultiset B).erase i.val=occupationNatMultiset A then
          j.val * (occupationNatMultiset A).count j.val else 0 : ℕ) : ℂ)
      by_cases hp : occupationReplace B i j hm=A
      · have hp' := he.mp hp
        simp only [hp, hp', ite_eq_left, Nat.cast_mul, hc]
        simp [j]
      · have hp' := he.not.mp hp
        simp [hp, hp']
    · have hn := (occupationNatMultiset_mem B i).not.mpr hm
      rw [dif_neg hm]
      simp [multisetCMEntry, hn]
  · have hb : Q ≤ i.val := by omega
    simp [hi, multisetCMEntry_above_cap A B hb]

theorem occupationNatMultiset_mem_le_weight {Q N i : ℕ} (A : Occupation Q N)
    (hi : i ∈ occupationNatMultiset A) : i ≤ occupationWeight A := by
  have he := congrArg Multiset.sum (Multiset.cons_erase hi)
  change (i ::ₘ (occupationNatMultiset A).erase i).sum = occupationWeight A at he
  rw [Multiset.sum_cons] at he
  omega

theorem occupationCMBlockMatrix_nat {Q N d : ℕ} (hd : d≤Q) (hpos : 0<d)
    (B : WeightOccupation Q N (d-1)) (A : WeightOccupation Q N d) :
    occupationCMBlockMatrix Q N d B A =
      ((∑ i ∈ Finset.range d,
        multisetCMEntry i (occupationNatMultiset B.val) (occupationNatMultiset A.val) : ℕ) : ℂ) := by
  have he : occupationCMBlockMatrix Q N d B A = occupationCMMatrix Q N B.val A.val := by
    rw [occupationCMBlockMatrix_apply, occupationCMMatrix_apply]
  rw [he, occupationCMMatrix_nat]
  congr 1
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i _ hi
  have hid : d ≤ i := by simpa only [Finset.mem_range, not_lt] using hi
  have hm : i ∉ occupationNatMultiset B.val := by
    intro hm
    have hb := occupationNatMultiset_mem_le_weight B.val hm
    rw [B.property] at hb
    omega
  simp [multisetCMEntry, hm]

theorem sortedDegreeOccupationEquiv_nat {Q N d : ℕ} (hd : d≤Q)
    (A : SortedDegreeTuple N d) :
    occupationNatMultiset (sortedDegreeOccupationEquiv hd A).val =
      (List.ofFn A.val : Multiset ℕ) := by
  simp [occupationNatMultiset, sortedDegreeOccupationEquiv, sortedDegreeOrbitalEquiv,
    sortedOrbitalOccupationEquiv, occupationOfConfiguration, List.map_ofFn]
  exact List.Perm.refl _

theorem sortedCMCoefficient_eq_occupationCMBlockMatrix {Q N d : ℕ}
    (hd : d≤Q) (hpos : 0<d)
    (B : SortedDegreeTuple N (d-1)) (A : SortedDegreeTuple N d) :
    (sortedCMCoefficient B A : ℂ) = occupationCMBlockMatrix Q N d
      (sortedDegreeOccupationEquiv (Nat.le_trans (Nat.sub_le _ _) hd) B)
      (sortedDegreeOccupationEquiv hd A) := by
  rw [occupationCMBlockMatrix_nat hd hpos, sortedDegreeOccupationEquiv_nat,
    sortedDegreeOccupationEquiv_nat]
  rfl

end BosonicLaughlin

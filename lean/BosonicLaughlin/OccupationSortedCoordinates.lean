import BosonicLaughlin.OccupationWeightCoordinates

/-! Exact sorted-tuple indices for occupation coefficients. The uncapped natural
tuples have the defining constraints used by `parts(n,D)`: length n,
nondecreasing entries, and sum D. No assertion about a Python enumeration
algorithm or its output order is needed for this coordinate equivalence. -/
namespace BosonicLaughlin
noncomputable section
open Finset

abbrev SortedOrbitalTuple (Q N d : ℕ) :=
  {a : Configuration Q N // Monotone a ∧ configurationWeight a=d}

abbrev SortedDegreeTuple (N d : ℕ) :=
  {a : Fin N → ℕ // Monotone a ∧ ∑ i : Fin N, a i=d}

theorem occupationOfConfiguration_injective_monotone {Q N : ℕ}
    (a b : Configuration Q N) (ha : Monotone a) (hb : Monotone b)
    (hab : occupationOfConfiguration a=occupationOfConfiguration b) : a=b := by
  apply List.ofFn_injective
  have hp : List.Perm (List.ofFn a) (List.ofFn b) := Quotient.exact (congrArg Subtype.val hab)
  exact hp.eq_of_pairwise' ha.sortedLE_ofFn.pairwise hb.sortedLE_ofFn.pairwise

def occupationSortedRepresentative {Q N : ℕ} (A : Occupation Q N) : Configuration Q N :=
  occupationRepresentative A ∘ Tuple.sort (occupationRepresentative A)

theorem occupationSortedRepresentative_monotone {Q N : ℕ} (A : Occupation Q N) :
    Monotone (occupationSortedRepresentative A) := Tuple.monotone_sort _

theorem occupationOfConfiguration_sortedRepresentative {Q N : ℕ} (A : Occupation Q N) :
    occupationOfConfiguration (occupationSortedRepresentative A)=A := by
  rw [occupationSortedRepresentative, occupationOfConfiguration_permute,
    occupationOfConfiguration_representative]

theorem occupationSortedRepresentative_weight {Q N : ℕ} (A : Occupation Q N) :
    configurationWeight (occupationSortedRepresentative A)=occupationWeight A := by
  rw [← occupationOfConfiguration_weight, occupationOfConfiguration_sortedRepresentative]

def sortedOrbitalOccupationEquiv (Q N d : ℕ) :
    SortedOrbitalTuple Q N d ≃ WeightOccupation Q N d where
  toFun a := ⟨occupationOfConfiguration a.val,
    (occupationOfConfiguration_weight a.val).trans a.property.2⟩
  invFun A := ⟨occupationSortedRepresentative A.val,
    occupationSortedRepresentative_monotone A.val,
    (occupationSortedRepresentative_weight A.val).trans A.property⟩
  left_inv a := by
    apply Subtype.ext
    apply occupationOfConfiguration_injective_monotone _ _
      (occupationSortedRepresentative_monotone _) a.property.1
    exact occupationOfConfiguration_sortedRepresentative _
  right_inv A := by
    apply Subtype.ext
    exact occupationOfConfiguration_sortedRepresentative _

/-- An entry of a nonnegative tuple cannot exceed its total sum. -/
theorem sortedDegreeTuple_entry_le {N d : ℕ} (a : SortedDegreeTuple N d) (i : Fin N) :
    a.val i ≤ d := by
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq a.property.2

def sortedDegreeOrbitalEquiv {Q N d : ℕ} (hd : d ≤ Q) :
    SortedDegreeTuple N d ≃ SortedOrbitalTuple Q N d where
  toFun a := ⟨fun i => ⟨a.val i, by have h := sortedDegreeTuple_entry_le a i; omega⟩,
    (by intro i j hij; exact a.property.1 hij), a.property.2⟩
  invFun a := ⟨fun i => (a.val i).val,
    (by intro i j hij; exact a.property.1 hij), a.property.2⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl

/-- For Q>=d, the physical occupation indices are exactly the uncapped sorted
natural tuples of length N and total d. -/
def sortedDegreeOccupationEquiv {Q N d : ℕ} (hd : d ≤ Q) :
    SortedDegreeTuple N d ≃ WeightOccupation Q N d :=
  (sortedDegreeOrbitalEquiv hd).trans (sortedOrbitalOccupationEquiv Q N d)

end
end BosonicLaughlin

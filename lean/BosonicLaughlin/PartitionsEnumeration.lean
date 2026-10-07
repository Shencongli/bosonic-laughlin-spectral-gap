import BosonicLaughlin.OccupationSortedCoordinates

/-! A finite recursive enumeration of sorted nonnegative tuples.  The lower
bound is carried through the recursion, so no rectangular tuple search is
needed.  Completeness is proved independently of the exported Python tables. -/
namespace BosonicLaughlin

def degreePartitions : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, d, _ => if d=0 then [[]] else []
  | n+1, d, lo => (List.range (d+1)).flatMap fun j =>
      if lo≤j then (degreePartitions n (d-j) j).map (List.cons j) else []

def DegreePartitionSpec (n d lo : ℕ) (a : List ℕ) : Prop :=
  a.length=n ∧ a.sum=d ∧ a.Pairwise (·≤·) ∧ ∀ x∈a, lo≤x

theorem mem_degreePartitions (n d lo : ℕ) (a : List ℕ) :
    a ∈ degreePartitions n d lo ↔ DegreePartitionSpec n d lo a := by
  induction n generalizing d lo a with
  | zero =>
    cases a with
    | nil => simp [degreePartitions, DegreePartitionSpec, eq_comm]
    | cons x xs => simp [degreePartitions, DegreePartitionSpec]
  | succ n ih =>
    cases a with
    | nil => simp [degreePartitions, DegreePartitionSpec]
    | cons x xs =>
      simp only [degreePartitions, List.mem_flatMap, List.mem_range]
      constructor
      · rintro ⟨j, hj, ha⟩
        split_ifs at ha with hlo
        · obtain ⟨b, hb, he⟩ := List.mem_map.mp ha
          cases he
          obtain ⟨hlen, hsum, hsorted, hbound⟩ := (ih _ _ _).mp hb
          refine ⟨by simp [hlen], ?_, ?_, ?_⟩
          · simp only [List.sum_cons]
            omega
          · exact List.pairwise_cons.mpr ⟨hbound, hsorted⟩
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hlo
            · exact hlo.trans (hbound y hy)
        · simp at ha
      · rintro ⟨hlen, hsum, hsorted, hbound⟩
        have hx : x≤d := by simp only [List.sum_cons] at hsum; omega
        have hlo : lo≤x := hbound x (by simp)
        refine ⟨x, by omega, ?_⟩
        rw [ite_eq_left hlo]
        apply List.mem_map.mpr
        refine ⟨xs, (ih _ _ _).mpr ?_, rfl⟩
        refine ⟨by simpa using hlen, ?_, (List.pairwise_cons.mp hsorted).2,
          (List.pairwise_cons.mp hsorted).1⟩
        simp only [List.sum_cons] at hsum
        omega

theorem degreePartitions_nodup (n d lo : ℕ) : (degreePartitions n d lo).Nodup := by
  induction n generalizing d lo with
  | zero => simp [degreePartitions]; split <;> simp
  | succ n ih =>
    rw [degreePartitions, List.nodup_flatMap]
    constructor
    · intro j hj
      split_ifs
      · exact (ih _ _).map (by intro a b h; exact (List.cons.inj h).2)
      · exact List.nodup_nil
    · apply (show (List.range (d+1)).Nodup from List.nodup_range).imp
      intro i j hij a hi hj
      dsimp only at hi hj
      split_ifs at hi hj with hli hlj
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hi
        obtain ⟨c,hc,he⟩ := List.mem_map.mp hj
        exact hij (List.cons.inj he).1.symm
      all_goals simp_all

def partitionTuple {N : ℕ} (a : List ℕ) (hlen : a.length=N) : Fin N → ℕ :=
  fun i => a.get ⟨i.val, by omega⟩

theorem ofFn_partitionTuple {N : ℕ} (a : List ℕ) (hlen : a.length=N) :
    List.ofFn (partitionTuple a hlen)=a := by
  subst N
  exact List.ofFn_get a

theorem partitionTuple_monotone {N : ℕ} (a : List ℕ) (hlen : a.length=N)
    (hsorted : a.Pairwise (·≤·)) : Monotone (partitionTuple a hlen) := by
  intro i j hij
  exact hsorted.rel_get_of_le hij

theorem partitionTuple_sum {N d : ℕ} (a : List ℕ) (hlen : a.length=N)
    (hsum : a.sum=d) : ∑ i, partitionTuple a hlen i=d := by
  rw [← List.sum_ofFn, ofFn_partitionTuple]
  exact hsum

theorem sortedDegreeTuple_mem_partitions {N d : ℕ} (a : SortedDegreeTuple N d) :
    List.ofFn a.val ∈ degreePartitions N d 0 := by
  apply (mem_degreePartitions _ _ _ _).mpr
  exact ⟨List.length_ofFn, by simpa only [List.sum_ofFn] using a.property.2,
    a.property.1.sortedLE_ofFn.pairwise, by intros; omega⟩

def degreePartitionTableTuple {N d : ℕ} (table : List (List ℕ))
    (ht : table=degreePartitions N d 0) (i : Fin table.length) : SortedDegreeTuple N d := by
  have hm : table.get i ∈ degreePartitions N d 0 := ht ▸ List.get_mem table i
  have hs := (mem_degreePartitions N d 0 (table.get i)).mp hm
  exact ⟨partitionTuple (table.get i) hs.1,
    partitionTuple_monotone _ hs.1 hs.2.2.1, partitionTuple_sum _ hs.1 hs.2.1⟩

theorem ofFn_degreePartitionTableTuple {N d : ℕ} (table : List (List ℕ))
    (ht : table=degreePartitions N d 0) (i : Fin table.length) :
    List.ofFn (degreePartitionTableTuple table ht i).val=table.get i :=
  by simp only [degreePartitionTableTuple, ofFn_partitionTuple]

theorem degreePartitionTableTuple_injective {N d : ℕ} (table : List (List ℕ))
    (ht : table=degreePartitions N d 0) : Function.Injective (degreePartitionTableTuple table ht) := by
  intro i j hij
  have he := congrArg (fun a : SortedDegreeTuple N d => List.ofFn a.val) hij
  simp only [ofFn_degreePartitionTableTuple] at he
  have hn : table.Nodup := ht ▸ degreePartitions_nodup N d 0
  exact hn.injective_get he

theorem degreePartitionTableTuple_surjective {N d : ℕ} (table : List (List ℕ))
    (ht : table=degreePartitions N d 0) : Function.Surjective (degreePartitionTableTuple table ht) := by
  intro a
  have hm : List.ofFn a.val ∈ table := ht ▸ sortedDegreeTuple_mem_partitions a
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
  refine ⟨i, ?_⟩
  apply Subtype.ext
  apply List.ofFn_injective
  rw [ofFn_degreePartitionTableTuple, hi]

end BosonicLaughlin

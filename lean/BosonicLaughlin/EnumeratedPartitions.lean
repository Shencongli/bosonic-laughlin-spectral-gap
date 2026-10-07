import BosonicLaughlin.PartitionsEnumeration
import BosonicLaughlin.IndexedOccupationCM

/-! A literal table is accepted only after equality to the complete recursive
enumeration has been proved. Its order is retained in the coordinate maps. -/
namespace BosonicLaughlin

def sortedEnumerationOfTable {N d : ℕ} (table : List (List ℕ))
    (ht : table=degreePartitions N d 0) : SortedTupleEnumeration N d table.length where
  tuple := degreePartitionTableTuple table ht
  injective := degreePartitionTableTuple_injective table ht
  surjective := degreePartitionTableTuple_surjective table ht

theorem sortedEnumerationOfTable_ofFn {N d : ℕ} (table : List (List ℕ))
    (ht : table=degreePartitions N d 0) (i : Fin table.length) :
    List.ofFn ((sortedEnumerationOfTable table ht).tuple i).val=table.get i :=
  ofFn_degreePartitionTableTuple table ht i

end BosonicLaughlin

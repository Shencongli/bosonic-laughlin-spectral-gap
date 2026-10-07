import BosonicLaughlin.EnumeratedPartitions
import BosonicLaughlin.RetainedCMFrames

/-! Complete index tables and the exact identification of the retained
CM arrays with the physical occupation CM matrix for Q >= d > 0.
Literal table equality and every integer entry are checked in Lean. -/
namespace BosonicLaughlin

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def retainedParts_3_0 : List (List ℕ) := [
  [0, 0, 0]
]

theorem retainedParts_3_0_complete : retainedParts_3_0=degreePartitions 3 0 0 := by
  decide +kernel

def retainedEnum_3_0 : SortedTupleEnumeration 3 0 1 :=
  sortedEnumerationOfTable retainedParts_3_0 retainedParts_3_0_complete

def retainedParts_3_1 : List (List ℕ) := [
  [0, 0, 1]
]

theorem retainedParts_3_1_complete : retainedParts_3_1=degreePartitions 3 1 0 := by
  decide +kernel

def retainedEnum_3_1 : SortedTupleEnumeration 3 1 1 :=
  sortedEnumerationOfTable retainedParts_3_1 retainedParts_3_1_complete

theorem retainedCM_3_1_integer_entries : ∀ (i : Fin 1) (j : Fin 1),
    sparseIntRowEval (retainedCM_3_1CS i) j =
      (tupleCMCoefficient 1 (retainedParts_3_0.get i) (retainedParts_3_1.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_3_1_physical_matrix (Q : ℕ) (hd : 1≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_3_1 retainedEnum_3_0 =
      retainedCM_3_1C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_3_1CS i) j : ℚ) = _
  simp only [retainedEnum_3_1, retainedEnum_3_0]
  rw [sortedEnumerationOfTable_ofFn retainedParts_3_0 retainedParts_3_0_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_3_1 retainedParts_3_1_complete j]
  exact_mod_cast retainedCM_3_1_integer_entries i j

def retainedParts_3_2 : List (List ℕ) := [
  [0, 0, 2],
  [0, 1, 1]
]

theorem retainedParts_3_2_complete : retainedParts_3_2=degreePartitions 3 2 0 := by
  decide +kernel

def retainedEnum_3_2 : SortedTupleEnumeration 3 2 2 :=
  sortedEnumerationOfTable retainedParts_3_2 retainedParts_3_2_complete

theorem retainedCM_3_2_integer_entries : ∀ (i : Fin 1) (j : Fin 2),
    sparseIntRowEval (retainedCM_3_2CS i) j =
      (tupleCMCoefficient 2 (retainedParts_3_1.get i) (retainedParts_3_2.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_3_2_physical_matrix (Q : ℕ) (hd : 2≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_3_2 retainedEnum_3_1 =
      retainedCM_3_2C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_3_2CS i) j : ℚ) = _
  simp only [retainedEnum_3_2, retainedEnum_3_1]
  rw [sortedEnumerationOfTable_ofFn retainedParts_3_1 retainedParts_3_1_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_3_2 retainedParts_3_2_complete j]
  exact_mod_cast retainedCM_3_2_integer_entries i j

def retainedParts_3_3 : List (List ℕ) := [
  [0, 0, 3],
  [0, 1, 2],
  [1, 1, 1]
]

theorem retainedParts_3_3_complete : retainedParts_3_3=degreePartitions 3 3 0 := by
  decide +kernel

def retainedEnum_3_3 : SortedTupleEnumeration 3 3 3 :=
  sortedEnumerationOfTable retainedParts_3_3 retainedParts_3_3_complete

theorem retainedCM_3_3_integer_entries : ∀ (i : Fin 2) (j : Fin 3),
    sparseIntRowEval (retainedCM_3_3CS i) j =
      (tupleCMCoefficient 3 (retainedParts_3_2.get i) (retainedParts_3_3.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_3_3_physical_matrix (Q : ℕ) (hd : 3≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_3_3 retainedEnum_3_2 =
      retainedCM_3_3C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_3_3CS i) j : ℚ) = _
  simp only [retainedEnum_3_3, retainedEnum_3_2]
  rw [sortedEnumerationOfTable_ofFn retainedParts_3_2 retainedParts_3_2_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_3_3 retainedParts_3_3_complete j]
  exact_mod_cast retainedCM_3_3_integer_entries i j

def retainedParts_3_4 : List (List ℕ) := [
  [0, 0, 4],
  [0, 1, 3],
  [0, 2, 2],
  [1, 1, 2]
]

theorem retainedParts_3_4_complete : retainedParts_3_4=degreePartitions 3 4 0 := by
  decide +kernel

def retainedEnum_3_4 : SortedTupleEnumeration 3 4 4 :=
  sortedEnumerationOfTable retainedParts_3_4 retainedParts_3_4_complete

theorem retainedCM_3_4_integer_entries : ∀ (i : Fin 3) (j : Fin 4),
    sparseIntRowEval (retainedCM_3_4CS i) j =
      (tupleCMCoefficient 4 (retainedParts_3_3.get i) (retainedParts_3_4.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_3_4_physical_matrix (Q : ℕ) (hd : 4≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_3_4 retainedEnum_3_3 =
      retainedCM_3_4C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_3_4CS i) j : ℚ) = _
  simp only [retainedEnum_3_4, retainedEnum_3_3]
  rw [sortedEnumerationOfTable_ofFn retainedParts_3_3 retainedParts_3_3_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_3_4 retainedParts_3_4_complete j]
  exact_mod_cast retainedCM_3_4_integer_entries i j

def retainedParts_3_5 : List (List ℕ) := [
  [0, 0, 5],
  [0, 1, 4],
  [0, 2, 3],
  [1, 1, 3],
  [1, 2, 2]
]

theorem retainedParts_3_5_complete : retainedParts_3_5=degreePartitions 3 5 0 := by
  decide +kernel

def retainedEnum_3_5 : SortedTupleEnumeration 3 5 5 :=
  sortedEnumerationOfTable retainedParts_3_5 retainedParts_3_5_complete

theorem retainedCM_3_5_integer_entries : ∀ (i : Fin 4) (j : Fin 5),
    sparseIntRowEval (retainedCM_3_5CS i) j =
      (tupleCMCoefficient 5 (retainedParts_3_4.get i) (retainedParts_3_5.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_3_5_physical_matrix (Q : ℕ) (hd : 5≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_3_5 retainedEnum_3_4 =
      retainedCM_3_5C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_3_5CS i) j : ℚ) = _
  simp only [retainedEnum_3_5, retainedEnum_3_4]
  rw [sortedEnumerationOfTable_ofFn retainedParts_3_4 retainedParts_3_4_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_3_5 retainedParts_3_5_complete j]
  exact_mod_cast retainedCM_3_5_integer_entries i j

def retainedParts_3_6 : List (List ℕ) := [
  [0, 0, 6],
  [0, 1, 5],
  [0, 2, 4],
  [0, 3, 3],
  [1, 1, 4],
  [1, 2, 3],
  [2, 2, 2]
]

theorem retainedParts_3_6_complete : retainedParts_3_6=degreePartitions 3 6 0 := by
  decide +kernel

def retainedEnum_3_6 : SortedTupleEnumeration 3 6 7 :=
  sortedEnumerationOfTable retainedParts_3_6 retainedParts_3_6_complete

theorem retainedCM_3_6_integer_entries : ∀ (i : Fin 5) (j : Fin 7),
    sparseIntRowEval (retainedCM_3_6CS i) j =
      (tupleCMCoefficient 6 (retainedParts_3_5.get i) (retainedParts_3_6.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_3_6_physical_matrix (Q : ℕ) (hd : 6≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_3_6 retainedEnum_3_5 =
      retainedCM_3_6C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_3_6CS i) j : ℚ) = _
  simp only [retainedEnum_3_6, retainedEnum_3_5]
  rw [sortedEnumerationOfTable_ofFn retainedParts_3_5 retainedParts_3_5_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_3_6 retainedParts_3_6_complete j]
  exact_mod_cast retainedCM_3_6_integer_entries i j

def retainedParts_3_7 : List (List ℕ) := [
  [0, 0, 7],
  [0, 1, 6],
  [0, 2, 5],
  [0, 3, 4],
  [1, 1, 5],
  [1, 2, 4],
  [1, 3, 3],
  [2, 2, 3]
]

theorem retainedParts_3_7_complete : retainedParts_3_7=degreePartitions 3 7 0 := by
  decide +kernel

def retainedEnum_3_7 : SortedTupleEnumeration 3 7 8 :=
  sortedEnumerationOfTable retainedParts_3_7 retainedParts_3_7_complete

theorem retainedCM_3_7_integer_entries : ∀ (i : Fin 7) (j : Fin 8),
    sparseIntRowEval (retainedCM_3_7CS i) j =
      (tupleCMCoefficient 7 (retainedParts_3_6.get i) (retainedParts_3_7.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_3_7_physical_matrix (Q : ℕ) (hd : 7≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_3_7 retainedEnum_3_6 =
      retainedCM_3_7C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_3_7CS i) j : ℚ) = _
  simp only [retainedEnum_3_7, retainedEnum_3_6]
  rw [sortedEnumerationOfTable_ofFn retainedParts_3_6 retainedParts_3_6_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_3_7 retainedParts_3_7_complete j]
  exact_mod_cast retainedCM_3_7_integer_entries i j

def retainedParts_3_8 : List (List ℕ) := [
  [0, 0, 8],
  [0, 1, 7],
  [0, 2, 6],
  [0, 3, 5],
  [0, 4, 4],
  [1, 1, 6],
  [1, 2, 5],
  [1, 3, 4],
  [2, 2, 4],
  [2, 3, 3]
]

theorem retainedParts_3_8_complete : retainedParts_3_8=degreePartitions 3 8 0 := by
  decide +kernel

def retainedEnum_3_8 : SortedTupleEnumeration 3 8 10 :=
  sortedEnumerationOfTable retainedParts_3_8 retainedParts_3_8_complete

theorem retainedCM_3_8_integer_entries : ∀ (i : Fin 8) (j : Fin 10),
    sparseIntRowEval (retainedCM_3_8CS i) j =
      (tupleCMCoefficient 8 (retainedParts_3_7.get i) (retainedParts_3_8.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_3_8_physical_matrix (Q : ℕ) (hd : 8≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_3_8 retainedEnum_3_7 =
      retainedCM_3_8C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_3_8CS i) j : ℚ) = _
  simp only [retainedEnum_3_8, retainedEnum_3_7]
  rw [sortedEnumerationOfTable_ofFn retainedParts_3_7 retainedParts_3_7_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_3_8 retainedParts_3_8_complete j]
  exact_mod_cast retainedCM_3_8_integer_entries i j

def retainedParts_4_0 : List (List ℕ) := [
  [0, 0, 0, 0]
]

theorem retainedParts_4_0_complete : retainedParts_4_0=degreePartitions 4 0 0 := by
  decide +kernel

def retainedEnum_4_0 : SortedTupleEnumeration 4 0 1 :=
  sortedEnumerationOfTable retainedParts_4_0 retainedParts_4_0_complete

def retainedParts_4_1 : List (List ℕ) := [
  [0, 0, 0, 1]
]

theorem retainedParts_4_1_complete : retainedParts_4_1=degreePartitions 4 1 0 := by
  decide +kernel

def retainedEnum_4_1 : SortedTupleEnumeration 4 1 1 :=
  sortedEnumerationOfTable retainedParts_4_1 retainedParts_4_1_complete

theorem retainedCM_4_1_integer_entries : ∀ (i : Fin 1) (j : Fin 1),
    sparseIntRowEval (retainedCM_4_1CS i) j =
      (tupleCMCoefficient 1 (retainedParts_4_0.get i) (retainedParts_4_1.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_1_physical_matrix (Q : ℕ) (hd : 1≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_1 retainedEnum_4_0 =
      retainedCM_4_1C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_1CS i) j : ℚ) = _
  simp only [retainedEnum_4_1, retainedEnum_4_0]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_0 retainedParts_4_0_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_1 retainedParts_4_1_complete j]
  exact_mod_cast retainedCM_4_1_integer_entries i j

def retainedParts_4_2 : List (List ℕ) := [
  [0, 0, 0, 2],
  [0, 0, 1, 1]
]

theorem retainedParts_4_2_complete : retainedParts_4_2=degreePartitions 4 2 0 := by
  decide +kernel

def retainedEnum_4_2 : SortedTupleEnumeration 4 2 2 :=
  sortedEnumerationOfTable retainedParts_4_2 retainedParts_4_2_complete

theorem retainedCM_4_2_integer_entries : ∀ (i : Fin 1) (j : Fin 2),
    sparseIntRowEval (retainedCM_4_2CS i) j =
      (tupleCMCoefficient 2 (retainedParts_4_1.get i) (retainedParts_4_2.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_2_physical_matrix (Q : ℕ) (hd : 2≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_2 retainedEnum_4_1 =
      retainedCM_4_2C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_2CS i) j : ℚ) = _
  simp only [retainedEnum_4_2, retainedEnum_4_1]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_1 retainedParts_4_1_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_2 retainedParts_4_2_complete j]
  exact_mod_cast retainedCM_4_2_integer_entries i j

def retainedParts_4_3 : List (List ℕ) := [
  [0, 0, 0, 3],
  [0, 0, 1, 2],
  [0, 1, 1, 1]
]

theorem retainedParts_4_3_complete : retainedParts_4_3=degreePartitions 4 3 0 := by
  decide +kernel

def retainedEnum_4_3 : SortedTupleEnumeration 4 3 3 :=
  sortedEnumerationOfTable retainedParts_4_3 retainedParts_4_3_complete

theorem retainedCM_4_3_integer_entries : ∀ (i : Fin 2) (j : Fin 3),
    sparseIntRowEval (retainedCM_4_3CS i) j =
      (tupleCMCoefficient 3 (retainedParts_4_2.get i) (retainedParts_4_3.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_3_physical_matrix (Q : ℕ) (hd : 3≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_3 retainedEnum_4_2 =
      retainedCM_4_3C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_3CS i) j : ℚ) = _
  simp only [retainedEnum_4_3, retainedEnum_4_2]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_2 retainedParts_4_2_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_3 retainedParts_4_3_complete j]
  exact_mod_cast retainedCM_4_3_integer_entries i j

def retainedParts_4_4 : List (List ℕ) := [
  [0, 0, 0, 4],
  [0, 0, 1, 3],
  [0, 0, 2, 2],
  [0, 1, 1, 2],
  [1, 1, 1, 1]
]

theorem retainedParts_4_4_complete : retainedParts_4_4=degreePartitions 4 4 0 := by
  decide +kernel

def retainedEnum_4_4 : SortedTupleEnumeration 4 4 5 :=
  sortedEnumerationOfTable retainedParts_4_4 retainedParts_4_4_complete

theorem retainedCM_4_4_integer_entries : ∀ (i : Fin 3) (j : Fin 5),
    sparseIntRowEval (retainedCM_4_4CS i) j =
      (tupleCMCoefficient 4 (retainedParts_4_3.get i) (retainedParts_4_4.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_4_physical_matrix (Q : ℕ) (hd : 4≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_4 retainedEnum_4_3 =
      retainedCM_4_4C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_4CS i) j : ℚ) = _
  simp only [retainedEnum_4_4, retainedEnum_4_3]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_3 retainedParts_4_3_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_4 retainedParts_4_4_complete j]
  exact_mod_cast retainedCM_4_4_integer_entries i j

def retainedParts_4_5 : List (List ℕ) := [
  [0, 0, 0, 5],
  [0, 0, 1, 4],
  [0, 0, 2, 3],
  [0, 1, 1, 3],
  [0, 1, 2, 2],
  [1, 1, 1, 2]
]

theorem retainedParts_4_5_complete : retainedParts_4_5=degreePartitions 4 5 0 := by
  decide +kernel

def retainedEnum_4_5 : SortedTupleEnumeration 4 5 6 :=
  sortedEnumerationOfTable retainedParts_4_5 retainedParts_4_5_complete

theorem retainedCM_4_5_integer_entries : ∀ (i : Fin 5) (j : Fin 6),
    sparseIntRowEval (retainedCM_4_5CS i) j =
      (tupleCMCoefficient 5 (retainedParts_4_4.get i) (retainedParts_4_5.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_5_physical_matrix (Q : ℕ) (hd : 5≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_5 retainedEnum_4_4 =
      retainedCM_4_5C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_5CS i) j : ℚ) = _
  simp only [retainedEnum_4_5, retainedEnum_4_4]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_4 retainedParts_4_4_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_5 retainedParts_4_5_complete j]
  exact_mod_cast retainedCM_4_5_integer_entries i j

def retainedParts_4_6 : List (List ℕ) := [
  [0, 0, 0, 6],
  [0, 0, 1, 5],
  [0, 0, 2, 4],
  [0, 0, 3, 3],
  [0, 1, 1, 4],
  [0, 1, 2, 3],
  [0, 2, 2, 2],
  [1, 1, 1, 3],
  [1, 1, 2, 2]
]

theorem retainedParts_4_6_complete : retainedParts_4_6=degreePartitions 4 6 0 := by
  decide +kernel

def retainedEnum_4_6 : SortedTupleEnumeration 4 6 9 :=
  sortedEnumerationOfTable retainedParts_4_6 retainedParts_4_6_complete

theorem retainedCM_4_6_integer_entries : ∀ (i : Fin 6) (j : Fin 9),
    sparseIntRowEval (retainedCM_4_6CS i) j =
      (tupleCMCoefficient 6 (retainedParts_4_5.get i) (retainedParts_4_6.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_6_physical_matrix (Q : ℕ) (hd : 6≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_6 retainedEnum_4_5 =
      retainedCM_4_6C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_6CS i) j : ℚ) = _
  simp only [retainedEnum_4_6, retainedEnum_4_5]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_5 retainedParts_4_5_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_6 retainedParts_4_6_complete j]
  exact_mod_cast retainedCM_4_6_integer_entries i j

def retainedParts_4_7 : List (List ℕ) := [
  [0, 0, 0, 7],
  [0, 0, 1, 6],
  [0, 0, 2, 5],
  [0, 0, 3, 4],
  [0, 1, 1, 5],
  [0, 1, 2, 4],
  [0, 1, 3, 3],
  [0, 2, 2, 3],
  [1, 1, 1, 4],
  [1, 1, 2, 3],
  [1, 2, 2, 2]
]

theorem retainedParts_4_7_complete : retainedParts_4_7=degreePartitions 4 7 0 := by
  decide +kernel

def retainedEnum_4_7 : SortedTupleEnumeration 4 7 11 :=
  sortedEnumerationOfTable retainedParts_4_7 retainedParts_4_7_complete

theorem retainedCM_4_7_integer_entries : ∀ (i : Fin 9) (j : Fin 11),
    sparseIntRowEval (retainedCM_4_7CS i) j =
      (tupleCMCoefficient 7 (retainedParts_4_6.get i) (retainedParts_4_7.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_7_physical_matrix (Q : ℕ) (hd : 7≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_7 retainedEnum_4_6 =
      retainedCM_4_7C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_7CS i) j : ℚ) = _
  simp only [retainedEnum_4_7, retainedEnum_4_6]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_6 retainedParts_4_6_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_7 retainedParts_4_7_complete j]
  exact_mod_cast retainedCM_4_7_integer_entries i j

def retainedParts_4_8 : List (List ℕ) := [
  [0, 0, 0, 8],
  [0, 0, 1, 7],
  [0, 0, 2, 6],
  [0, 0, 3, 5],
  [0, 0, 4, 4],
  [0, 1, 1, 6],
  [0, 1, 2, 5],
  [0, 1, 3, 4],
  [0, 2, 2, 4],
  [0, 2, 3, 3],
  [1, 1, 1, 5],
  [1, 1, 2, 4],
  [1, 1, 3, 3],
  [1, 2, 2, 3],
  [2, 2, 2, 2]
]

theorem retainedParts_4_8_complete : retainedParts_4_8=degreePartitions 4 8 0 := by
  decide +kernel

def retainedEnum_4_8 : SortedTupleEnumeration 4 8 15 :=
  sortedEnumerationOfTable retainedParts_4_8 retainedParts_4_8_complete

theorem retainedCM_4_8_integer_entries : ∀ (i : Fin 11) (j : Fin 15),
    sparseIntRowEval (retainedCM_4_8CS i) j =
      (tupleCMCoefficient 8 (retainedParts_4_7.get i) (retainedParts_4_8.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_8_physical_matrix (Q : ℕ) (hd : 8≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_8 retainedEnum_4_7 =
      retainedCM_4_8C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_8CS i) j : ℚ) = _
  simp only [retainedEnum_4_8, retainedEnum_4_7]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_7 retainedParts_4_7_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_8 retainedParts_4_8_complete j]
  exact_mod_cast retainedCM_4_8_integer_entries i j

def retainedParts_4_9 : List (List ℕ) := [
  [0, 0, 0, 9],
  [0, 0, 1, 8],
  [0, 0, 2, 7],
  [0, 0, 3, 6],
  [0, 0, 4, 5],
  [0, 1, 1, 7],
  [0, 1, 2, 6],
  [0, 1, 3, 5],
  [0, 1, 4, 4],
  [0, 2, 2, 5],
  [0, 2, 3, 4],
  [0, 3, 3, 3],
  [1, 1, 1, 6],
  [1, 1, 2, 5],
  [1, 1, 3, 4],
  [1, 2, 2, 4],
  [1, 2, 3, 3],
  [2, 2, 2, 3]
]

theorem retainedParts_4_9_complete : retainedParts_4_9=degreePartitions 4 9 0 := by
  decide +kernel

def retainedEnum_4_9 : SortedTupleEnumeration 4 9 18 :=
  sortedEnumerationOfTable retainedParts_4_9 retainedParts_4_9_complete

theorem retainedCM_4_9_integer_entries : ∀ (i : Fin 15) (j : Fin 18),
    sparseIntRowEval (retainedCM_4_9CS i) j =
      (tupleCMCoefficient 9 (retainedParts_4_8.get i) (retainedParts_4_9.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_9_physical_matrix (Q : ℕ) (hd : 9≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_9 retainedEnum_4_8 =
      retainedCM_4_9C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_9CS i) j : ℚ) = _
  simp only [retainedEnum_4_9, retainedEnum_4_8]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_8 retainedParts_4_8_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_9 retainedParts_4_9_complete j]
  exact_mod_cast retainedCM_4_9_integer_entries i j

def retainedParts_4_10 : List (List ℕ) := [
  [0, 0, 0, 10],
  [0, 0, 1, 9],
  [0, 0, 2, 8],
  [0, 0, 3, 7],
  [0, 0, 4, 6],
  [0, 0, 5, 5],
  [0, 1, 1, 8],
  [0, 1, 2, 7],
  [0, 1, 3, 6],
  [0, 1, 4, 5],
  [0, 2, 2, 6],
  [0, 2, 3, 5],
  [0, 2, 4, 4],
  [0, 3, 3, 4],
  [1, 1, 1, 7],
  [1, 1, 2, 6],
  [1, 1, 3, 5],
  [1, 1, 4, 4],
  [1, 2, 2, 5],
  [1, 2, 3, 4],
  [1, 3, 3, 3],
  [2, 2, 2, 4],
  [2, 2, 3, 3]
]

theorem retainedParts_4_10_complete : retainedParts_4_10=degreePartitions 4 10 0 := by
  decide +kernel

def retainedEnum_4_10 : SortedTupleEnumeration 4 10 23 :=
  sortedEnumerationOfTable retainedParts_4_10 retainedParts_4_10_complete

theorem retainedCM_4_10_integer_entries : ∀ (i : Fin 18) (j : Fin 23),
    sparseIntRowEval (retainedCM_4_10CS i) j =
      (tupleCMCoefficient 10 (retainedParts_4_9.get i) (retainedParts_4_10.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_10_physical_matrix (Q : ℕ) (hd : 10≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_10 retainedEnum_4_9 =
      retainedCM_4_10C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_10CS i) j : ℚ) = _
  simp only [retainedEnum_4_10, retainedEnum_4_9]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_9 retainedParts_4_9_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_10 retainedParts_4_10_complete j]
  exact_mod_cast retainedCM_4_10_integer_entries i j

def retainedParts_4_11 : List (List ℕ) := [
  [0, 0, 0, 11],
  [0, 0, 1, 10],
  [0, 0, 2, 9],
  [0, 0, 3, 8],
  [0, 0, 4, 7],
  [0, 0, 5, 6],
  [0, 1, 1, 9],
  [0, 1, 2, 8],
  [0, 1, 3, 7],
  [0, 1, 4, 6],
  [0, 1, 5, 5],
  [0, 2, 2, 7],
  [0, 2, 3, 6],
  [0, 2, 4, 5],
  [0, 3, 3, 5],
  [0, 3, 4, 4],
  [1, 1, 1, 8],
  [1, 1, 2, 7],
  [1, 1, 3, 6],
  [1, 1, 4, 5],
  [1, 2, 2, 6],
  [1, 2, 3, 5],
  [1, 2, 4, 4],
  [1, 3, 3, 4],
  [2, 2, 2, 5],
  [2, 2, 3, 4],
  [2, 3, 3, 3]
]

theorem retainedParts_4_11_complete : retainedParts_4_11=degreePartitions 4 11 0 := by
  decide +kernel

def retainedEnum_4_11 : SortedTupleEnumeration 4 11 27 :=
  sortedEnumerationOfTable retainedParts_4_11 retainedParts_4_11_complete

theorem retainedCM_4_11_integer_entries : ∀ (i : Fin 23) (j : Fin 27),
    sparseIntRowEval (retainedCM_4_11CS i) j =
      (tupleCMCoefficient 11 (retainedParts_4_10.get i) (retainedParts_4_11.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_11_physical_matrix (Q : ℕ) (hd : 11≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_11 retainedEnum_4_10 =
      retainedCM_4_11C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_11CS i) j : ℚ) = _
  simp only [retainedEnum_4_11, retainedEnum_4_10]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_10 retainedParts_4_10_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_11 retainedParts_4_11_complete j]
  exact_mod_cast retainedCM_4_11_integer_entries i j

def retainedParts_4_12 : List (List ℕ) := [
  [0, 0, 0, 12],
  [0, 0, 1, 11],
  [0, 0, 2, 10],
  [0, 0, 3, 9],
  [0, 0, 4, 8],
  [0, 0, 5, 7],
  [0, 0, 6, 6],
  [0, 1, 1, 10],
  [0, 1, 2, 9],
  [0, 1, 3, 8],
  [0, 1, 4, 7],
  [0, 1, 5, 6],
  [0, 2, 2, 8],
  [0, 2, 3, 7],
  [0, 2, 4, 6],
  [0, 2, 5, 5],
  [0, 3, 3, 6],
  [0, 3, 4, 5],
  [0, 4, 4, 4],
  [1, 1, 1, 9],
  [1, 1, 2, 8],
  [1, 1, 3, 7],
  [1, 1, 4, 6],
  [1, 1, 5, 5],
  [1, 2, 2, 7],
  [1, 2, 3, 6],
  [1, 2, 4, 5],
  [1, 3, 3, 5],
  [1, 3, 4, 4],
  [2, 2, 2, 6],
  [2, 2, 3, 5],
  [2, 2, 4, 4],
  [2, 3, 3, 4],
  [3, 3, 3, 3]
]

theorem retainedParts_4_12_complete : retainedParts_4_12=degreePartitions 4 12 0 := by
  decide +kernel

def retainedEnum_4_12 : SortedTupleEnumeration 4 12 34 :=
  sortedEnumerationOfTable retainedParts_4_12 retainedParts_4_12_complete

theorem retainedCM_4_12_integer_entries : ∀ (i : Fin 27) (j : Fin 34),
    sparseIntRowEval (retainedCM_4_12CS i) j =
      (tupleCMCoefficient 12 (retainedParts_4_11.get i) (retainedParts_4_12.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_12_physical_matrix (Q : ℕ) (hd : 12≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_12 retainedEnum_4_11 =
      retainedCM_4_12C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_12CS i) j : ℚ) = _
  simp only [retainedEnum_4_12, retainedEnum_4_11]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_11 retainedParts_4_11_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_12 retainedParts_4_12_complete j]
  exact_mod_cast retainedCM_4_12_integer_entries i j

def retainedParts_4_13 : List (List ℕ) := [
  [0, 0, 0, 13],
  [0, 0, 1, 12],
  [0, 0, 2, 11],
  [0, 0, 3, 10],
  [0, 0, 4, 9],
  [0, 0, 5, 8],
  [0, 0, 6, 7],
  [0, 1, 1, 11],
  [0, 1, 2, 10],
  [0, 1, 3, 9],
  [0, 1, 4, 8],
  [0, 1, 5, 7],
  [0, 1, 6, 6],
  [0, 2, 2, 9],
  [0, 2, 3, 8],
  [0, 2, 4, 7],
  [0, 2, 5, 6],
  [0, 3, 3, 7],
  [0, 3, 4, 6],
  [0, 3, 5, 5],
  [0, 4, 4, 5],
  [1, 1, 1, 10],
  [1, 1, 2, 9],
  [1, 1, 3, 8],
  [1, 1, 4, 7],
  [1, 1, 5, 6],
  [1, 2, 2, 8],
  [1, 2, 3, 7],
  [1, 2, 4, 6],
  [1, 2, 5, 5],
  [1, 3, 3, 6],
  [1, 3, 4, 5],
  [1, 4, 4, 4],
  [2, 2, 2, 7],
  [2, 2, 3, 6],
  [2, 2, 4, 5],
  [2, 3, 3, 5],
  [2, 3, 4, 4],
  [3, 3, 3, 4]
]

theorem retainedParts_4_13_complete : retainedParts_4_13=degreePartitions 4 13 0 := by
  decide +kernel

def retainedEnum_4_13 : SortedTupleEnumeration 4 13 39 :=
  sortedEnumerationOfTable retainedParts_4_13 retainedParts_4_13_complete

theorem retainedCM_4_13_integer_entries : ∀ (i : Fin 34) (j : Fin 39),
    sparseIntRowEval (retainedCM_4_13CS i) j =
      (tupleCMCoefficient 13 (retainedParts_4_12.get i) (retainedParts_4_13.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_13_physical_matrix (Q : ℕ) (hd : 13≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_13 retainedEnum_4_12 =
      retainedCM_4_13C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_13CS i) j : ℚ) = _
  simp only [retainedEnum_4_13, retainedEnum_4_12]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_12 retainedParts_4_12_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_13 retainedParts_4_13_complete j]
  exact_mod_cast retainedCM_4_13_integer_entries i j

def retainedParts_4_14 : List (List ℕ) := [
  [0, 0, 0, 14],
  [0, 0, 1, 13],
  [0, 0, 2, 12],
  [0, 0, 3, 11],
  [0, 0, 4, 10],
  [0, 0, 5, 9],
  [0, 0, 6, 8],
  [0, 0, 7, 7],
  [0, 1, 1, 12],
  [0, 1, 2, 11],
  [0, 1, 3, 10],
  [0, 1, 4, 9],
  [0, 1, 5, 8],
  [0, 1, 6, 7],
  [0, 2, 2, 10],
  [0, 2, 3, 9],
  [0, 2, 4, 8],
  [0, 2, 5, 7],
  [0, 2, 6, 6],
  [0, 3, 3, 8],
  [0, 3, 4, 7],
  [0, 3, 5, 6],
  [0, 4, 4, 6],
  [0, 4, 5, 5],
  [1, 1, 1, 11],
  [1, 1, 2, 10],
  [1, 1, 3, 9],
  [1, 1, 4, 8],
  [1, 1, 5, 7],
  [1, 1, 6, 6],
  [1, 2, 2, 9],
  [1, 2, 3, 8],
  [1, 2, 4, 7],
  [1, 2, 5, 6],
  [1, 3, 3, 7],
  [1, 3, 4, 6],
  [1, 3, 5, 5],
  [1, 4, 4, 5],
  [2, 2, 2, 8],
  [2, 2, 3, 7],
  [2, 2, 4, 6],
  [2, 2, 5, 5],
  [2, 3, 3, 6],
  [2, 3, 4, 5],
  [2, 4, 4, 4],
  [3, 3, 3, 5],
  [3, 3, 4, 4]
]

theorem retainedParts_4_14_complete : retainedParts_4_14=degreePartitions 4 14 0 := by
  decide +kernel

def retainedEnum_4_14 : SortedTupleEnumeration 4 14 47 :=
  sortedEnumerationOfTable retainedParts_4_14 retainedParts_4_14_complete

theorem retainedCM_4_14_integer_entries : ∀ (i : Fin 39) (j : Fin 47),
    sparseIntRowEval (retainedCM_4_14CS i) j =
      (tupleCMCoefficient 14 (retainedParts_4_13.get i) (retainedParts_4_14.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_14_physical_matrix (Q : ℕ) (hd : 14≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_14 retainedEnum_4_13 =
      retainedCM_4_14C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_14CS i) j : ℚ) = _
  simp only [retainedEnum_4_14, retainedEnum_4_13]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_13 retainedParts_4_13_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_14 retainedParts_4_14_complete j]
  exact_mod_cast retainedCM_4_14_integer_entries i j

def retainedParts_4_15 : List (List ℕ) := [
  [0, 0, 0, 15],
  [0, 0, 1, 14],
  [0, 0, 2, 13],
  [0, 0, 3, 12],
  [0, 0, 4, 11],
  [0, 0, 5, 10],
  [0, 0, 6, 9],
  [0, 0, 7, 8],
  [0, 1, 1, 13],
  [0, 1, 2, 12],
  [0, 1, 3, 11],
  [0, 1, 4, 10],
  [0, 1, 5, 9],
  [0, 1, 6, 8],
  [0, 1, 7, 7],
  [0, 2, 2, 11],
  [0, 2, 3, 10],
  [0, 2, 4, 9],
  [0, 2, 5, 8],
  [0, 2, 6, 7],
  [0, 3, 3, 9],
  [0, 3, 4, 8],
  [0, 3, 5, 7],
  [0, 3, 6, 6],
  [0, 4, 4, 7],
  [0, 4, 5, 6],
  [0, 5, 5, 5],
  [1, 1, 1, 12],
  [1, 1, 2, 11],
  [1, 1, 3, 10],
  [1, 1, 4, 9],
  [1, 1, 5, 8],
  [1, 1, 6, 7],
  [1, 2, 2, 10],
  [1, 2, 3, 9],
  [1, 2, 4, 8],
  [1, 2, 5, 7],
  [1, 2, 6, 6],
  [1, 3, 3, 8],
  [1, 3, 4, 7],
  [1, 3, 5, 6],
  [1, 4, 4, 6],
  [1, 4, 5, 5],
  [2, 2, 2, 9],
  [2, 2, 3, 8],
  [2, 2, 4, 7],
  [2, 2, 5, 6],
  [2, 3, 3, 7],
  [2, 3, 4, 6],
  [2, 3, 5, 5],
  [2, 4, 4, 5],
  [3, 3, 3, 6],
  [3, 3, 4, 5],
  [3, 4, 4, 4]
]

theorem retainedParts_4_15_complete : retainedParts_4_15=degreePartitions 4 15 0 := by
  decide +kernel

def retainedEnum_4_15 : SortedTupleEnumeration 4 15 54 :=
  sortedEnumerationOfTable retainedParts_4_15 retainedParts_4_15_complete

theorem retainedCM_4_15_integer_entries : ∀ (i : Fin 47) (j : Fin 54),
    sparseIntRowEval (retainedCM_4_15CS i) j =
      (tupleCMCoefficient 15 (retainedParts_4_14.get i) (retainedParts_4_15.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_15_physical_matrix (Q : ℕ) (hd : 15≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_15 retainedEnum_4_14 =
      retainedCM_4_15C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_15CS i) j : ℚ) = _
  simp only [retainedEnum_4_15, retainedEnum_4_14]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_14 retainedParts_4_14_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_15 retainedParts_4_15_complete j]
  exact_mod_cast retainedCM_4_15_integer_entries i j

def retainedParts_4_16 : List (List ℕ) := [
  [0, 0, 0, 16],
  [0, 0, 1, 15],
  [0, 0, 2, 14],
  [0, 0, 3, 13],
  [0, 0, 4, 12],
  [0, 0, 5, 11],
  [0, 0, 6, 10],
  [0, 0, 7, 9],
  [0, 0, 8, 8],
  [0, 1, 1, 14],
  [0, 1, 2, 13],
  [0, 1, 3, 12],
  [0, 1, 4, 11],
  [0, 1, 5, 10],
  [0, 1, 6, 9],
  [0, 1, 7, 8],
  [0, 2, 2, 12],
  [0, 2, 3, 11],
  [0, 2, 4, 10],
  [0, 2, 5, 9],
  [0, 2, 6, 8],
  [0, 2, 7, 7],
  [0, 3, 3, 10],
  [0, 3, 4, 9],
  [0, 3, 5, 8],
  [0, 3, 6, 7],
  [0, 4, 4, 8],
  [0, 4, 5, 7],
  [0, 4, 6, 6],
  [0, 5, 5, 6],
  [1, 1, 1, 13],
  [1, 1, 2, 12],
  [1, 1, 3, 11],
  [1, 1, 4, 10],
  [1, 1, 5, 9],
  [1, 1, 6, 8],
  [1, 1, 7, 7],
  [1, 2, 2, 11],
  [1, 2, 3, 10],
  [1, 2, 4, 9],
  [1, 2, 5, 8],
  [1, 2, 6, 7],
  [1, 3, 3, 9],
  [1, 3, 4, 8],
  [1, 3, 5, 7],
  [1, 3, 6, 6],
  [1, 4, 4, 7],
  [1, 4, 5, 6],
  [1, 5, 5, 5],
  [2, 2, 2, 10],
  [2, 2, 3, 9],
  [2, 2, 4, 8],
  [2, 2, 5, 7],
  [2, 2, 6, 6],
  [2, 3, 3, 8],
  [2, 3, 4, 7],
  [2, 3, 5, 6],
  [2, 4, 4, 6],
  [2, 4, 5, 5],
  [3, 3, 3, 7],
  [3, 3, 4, 6],
  [3, 3, 5, 5],
  [3, 4, 4, 5],
  [4, 4, 4, 4]
]

theorem retainedParts_4_16_complete : retainedParts_4_16=degreePartitions 4 16 0 := by
  decide +kernel

def retainedEnum_4_16 : SortedTupleEnumeration 4 16 64 :=
  sortedEnumerationOfTable retainedParts_4_16 retainedParts_4_16_complete

theorem retainedCM_4_16_integer_entries : ∀ (i : Fin 54) (j : Fin 64),
    sparseIntRowEval (retainedCM_4_16CS i) j =
      (tupleCMCoefficient 16 (retainedParts_4_15.get i) (retainedParts_4_16.get j) : ℤ) := by
  decide +kernel

theorem retainedCM_4_16_physical_matrix (Q : ℕ) (hd : 16≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_16 retainedEnum_4_15 =
      retainedCM_4_16C.map (Rat.castHom ℂ) := by
  apply indexedOccupationCMMatrix_eq_array hd (by decide)
  intro i j
  change (sparseIntRowEval (retainedCM_4_16CS i) j : ℚ) = _
  simp only [retainedEnum_4_16, retainedEnum_4_15]
  rw [sortedEnumerationOfTable_ofFn retainedParts_4_15 retainedParts_4_15_complete i,
    sortedEnumerationOfTable_ofFn retainedParts_4_16 retainedParts_4_16_complete j]
  exact_mod_cast retainedCM_4_16_integer_entries i j

end BosonicLaughlin

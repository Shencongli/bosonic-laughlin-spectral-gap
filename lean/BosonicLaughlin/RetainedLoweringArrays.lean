import BosonicLaughlin.IndexedOccupationLowering
import BosonicLaughlin.RetainedCMCoordinates

/-! All 24 degree-raising steps used by the spherical verifier.
The arrays C,S are extracted from its actual raise_frame routine.
Lean checks every entry and proves R(Q)=C-S/Q for integer Q>d.
No assertion about interval arithmetic is made here. -/
namespace BosonicLaughlin
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def retainedRaise_3_0C : Matrix (Fin 1) (Fin 1) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 3
  | _, _ => 0

def retainedRaise_3_0S : Matrix (Fin 1) (Fin 1) ℕ := fun i j =>
  match i.val, j.val with
  | _, _ => 0

theorem retainedRaise_3_0_entries :
    (∀ (i : Fin 1) (j : Fin 1), retainedRaise_3_0C i j=
      tupleLowerConstant 0 (retainedParts_3_1.get i) (retainedParts_3_0.get j)) ∧
    (∀ (i : Fin 1) (j : Fin 1), retainedRaise_3_0S i j=
      tupleLowerSlope 0 (retainedParts_3_1.get i) (retainedParts_3_0.get j)) := by
  unfold retainedRaise_3_0C retainedRaise_3_0S
  decide +kernel

theorem retainedRaise_3_0_physical (Q : ℕ) (hd : 1≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_3_0 retainedEnum_3_1=
      retainedRaise_3_0C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_3_0S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_3_0, retainedEnum_3_1]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_1 retainedParts_3_1_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_0 retainedParts_3_0_complete j]
    exact retainedRaise_3_0_entries.1 i j
  · intro i j
    simp only [retainedEnum_3_0, retainedEnum_3_1]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_1 retainedParts_3_1_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_0 retainedParts_3_0_complete j]
    exact retainedRaise_3_0_entries.2 i j

def retainedRaise_3_1C : Matrix (Fin 2) (Fin 1) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 2
  | _, _ => 0

def retainedRaise_3_1S : Matrix (Fin 2) (Fin 1) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | _, _ => 0

theorem retainedRaise_3_1_entries :
    (∀ (i : Fin 2) (j : Fin 1), retainedRaise_3_1C i j=
      tupleLowerConstant 1 (retainedParts_3_2.get i) (retainedParts_3_1.get j)) ∧
    (∀ (i : Fin 2) (j : Fin 1), retainedRaise_3_1S i j=
      tupleLowerSlope 1 (retainedParts_3_2.get i) (retainedParts_3_1.get j)) := by
  unfold retainedRaise_3_1C retainedRaise_3_1S
  decide +kernel

theorem retainedRaise_3_1_physical (Q : ℕ) (hd : 2≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_3_1 retainedEnum_3_2=
      retainedRaise_3_1C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_3_1S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_3_1, retainedEnum_3_2]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_2 retainedParts_3_2_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_1 retainedParts_3_1_complete j]
    exact retainedRaise_3_1_entries.1 i j
  · intro i j
    simp only [retainedEnum_3_1, retainedEnum_3_2]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_2 retainedParts_3_2_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_1 retainedParts_3_1_complete j]
    exact retainedRaise_3_1_entries.2 i j

def retainedRaise_3_2C : Matrix (Fin 3) (Fin 2) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 2
  | 1, 1 => 2
  | 2, 1 => 1
  | _, _ => 0

def retainedRaise_3_2S : Matrix (Fin 3) (Fin 2) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 2
  | 1, 1 => 2
  | _, _ => 0

theorem retainedRaise_3_2_entries :
    (∀ (i : Fin 3) (j : Fin 2), retainedRaise_3_2C i j=
      tupleLowerConstant 2 (retainedParts_3_3.get i) (retainedParts_3_2.get j)) ∧
    (∀ (i : Fin 3) (j : Fin 2), retainedRaise_3_2S i j=
      tupleLowerSlope 2 (retainedParts_3_3.get i) (retainedParts_3_2.get j)) := by
  unfold retainedRaise_3_2C retainedRaise_3_2S
  decide +kernel

theorem retainedRaise_3_2_physical (Q : ℕ) (hd : 3≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_3_2 retainedEnum_3_3=
      retainedRaise_3_2C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_3_2S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_3_2, retainedEnum_3_3]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_3 retainedParts_3_3_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_2 retainedParts_3_2_complete j]
    exact retainedRaise_3_2_entries.1 i j
  · intro i j
    simp only [retainedEnum_3_2, retainedEnum_3_3]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_3 retainedParts_3_3_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_2 retainedParts_3_2_complete j]
    exact retainedRaise_3_2_entries.2 i j

def retainedRaise_3_3C : Matrix (Fin 4) (Fin 3) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 2
  | 1, 1 => 1
  | 2, 1 => 1
  | 3, 1 => 1
  | 3, 2 => 3
  | _, _ => 0

def retainedRaise_3_3S : Matrix (Fin 4) (Fin 3) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 3
  | 1, 1 => 2
  | 2, 1 => 1
  | 3, 2 => 3
  | _, _ => 0

theorem retainedRaise_3_3_entries :
    (∀ (i : Fin 4) (j : Fin 3), retainedRaise_3_3C i j=
      tupleLowerConstant 3 (retainedParts_3_4.get i) (retainedParts_3_3.get j)) ∧
    (∀ (i : Fin 4) (j : Fin 3), retainedRaise_3_3S i j=
      tupleLowerSlope 3 (retainedParts_3_4.get i) (retainedParts_3_3.get j)) := by
  unfold retainedRaise_3_3C retainedRaise_3_3S
  decide +kernel

theorem retainedRaise_3_3_physical (Q : ℕ) (hd : 4≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_3_3 retainedEnum_3_4=
      retainedRaise_3_3C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_3_3S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_3_3, retainedEnum_3_4]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_4 retainedParts_3_4_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_3 retainedParts_3_3_complete j]
    exact retainedRaise_3_3_entries.1 i j
  · intro i j
    simp only [retainedEnum_3_3, retainedEnum_3_4]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_4 retainedParts_3_4_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_3 retainedParts_3_3_complete j]
    exact retainedRaise_3_3_entries.2 i j

def retainedRaise_3_4C : Matrix (Fin 5) (Fin 4) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 2
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 2
  | 3, 1 => 1
  | 3, 3 => 1
  | 4, 2 => 1
  | 4, 3 => 2
  | _, _ => 0

def retainedRaise_3_4S : Matrix (Fin 5) (Fin 4) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 4
  | 1, 1 => 3
  | 2, 1 => 1
  | 2, 2 => 4
  | 3, 3 => 2
  | 4, 3 => 2
  | _, _ => 0

theorem retainedRaise_3_4_entries :
    (∀ (i : Fin 5) (j : Fin 4), retainedRaise_3_4C i j=
      tupleLowerConstant 4 (retainedParts_3_5.get i) (retainedParts_3_4.get j)) ∧
    (∀ (i : Fin 5) (j : Fin 4), retainedRaise_3_4S i j=
      tupleLowerSlope 4 (retainedParts_3_5.get i) (retainedParts_3_4.get j)) := by
  unfold retainedRaise_3_4C retainedRaise_3_4S
  decide +kernel

theorem retainedRaise_3_4_physical (Q : ℕ) (hd : 5≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_3_4 retainedEnum_3_5=
      retainedRaise_3_4C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_3_4S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_3_4, retainedEnum_3_5]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_5 retainedParts_3_5_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_4 retainedParts_3_4_complete j]
    exact retainedRaise_3_4_entries.1 i j
  · intro i j
    simp only [retainedEnum_3_4, retainedEnum_3_5]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_5 retainedParts_3_5_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_4 retainedParts_3_4_complete j]
    exact retainedRaise_3_4_entries.2 i j

def retainedRaise_3_5C : Matrix (Fin 7) (Fin 5) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 2
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 4, 1 => 1
  | 4, 3 => 1
  | 5, 2 => 1
  | 5, 3 => 2
  | 5, 4 => 2
  | 6, 4 => 1
  | _, _ => 0

def retainedRaise_3_5S : Matrix (Fin 7) (Fin 5) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 5
  | 1, 1 => 4
  | 2, 1 => 1
  | 2, 2 => 3
  | 3, 2 => 2
  | 4, 3 => 3
  | 5, 3 => 2
  | 5, 4 => 4
  | 6, 4 => 1
  | _, _ => 0

theorem retainedRaise_3_5_entries :
    (∀ (i : Fin 7) (j : Fin 5), retainedRaise_3_5C i j=
      tupleLowerConstant 5 (retainedParts_3_6.get i) (retainedParts_3_5.get j)) ∧
    (∀ (i : Fin 7) (j : Fin 5), retainedRaise_3_5S i j=
      tupleLowerSlope 5 (retainedParts_3_6.get i) (retainedParts_3_5.get j)) := by
  unfold retainedRaise_3_5C retainedRaise_3_5S
  decide +kernel

theorem retainedRaise_3_5_physical (Q : ℕ) (hd : 6≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_3_5 retainedEnum_3_6=
      retainedRaise_3_5C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_3_5S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_3_5, retainedEnum_3_6]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_6 retainedParts_3_6_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_5 retainedParts_3_5_complete j]
    exact retainedRaise_3_5_entries.1 i j
  · intro i j
    simp only [retainedEnum_3_5, retainedEnum_3_6]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_6 retainedParts_3_6_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_5 retainedParts_3_5_complete j]
    exact retainedRaise_3_5_entries.2 i j

def retainedRaise_3_6C : Matrix (Fin 8) (Fin 7) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 2
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 2
  | 4, 1 => 1
  | 4, 4 => 1
  | 5, 2 => 1
  | 5, 4 => 2
  | 5, 5 => 1
  | 6, 3 => 1
  | 6, 5 => 1
  | 7, 5 => 1
  | 7, 6 => 3
  | _, _ => 0

def retainedRaise_3_6S : Matrix (Fin 8) (Fin 7) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 6
  | 1, 1 => 5
  | 2, 1 => 1
  | 2, 2 => 4
  | 3, 2 => 2
  | 3, 3 => 6
  | 4, 4 => 4
  | 5, 4 => 2
  | 5, 5 => 3
  | 6, 5 => 2
  | 7, 5 => 1
  | 7, 6 => 6
  | _, _ => 0

theorem retainedRaise_3_6_entries :
    (∀ (i : Fin 8) (j : Fin 7), retainedRaise_3_6C i j=
      tupleLowerConstant 6 (retainedParts_3_7.get i) (retainedParts_3_6.get j)) ∧
    (∀ (i : Fin 8) (j : Fin 7), retainedRaise_3_6S i j=
      tupleLowerSlope 6 (retainedParts_3_7.get i) (retainedParts_3_6.get j)) := by
  unfold retainedRaise_3_6C retainedRaise_3_6S
  decide +kernel

theorem retainedRaise_3_6_physical (Q : ℕ) (hd : 7≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_3_6 retainedEnum_3_7=
      retainedRaise_3_6C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_3_6S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_3_6, retainedEnum_3_7]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_7 retainedParts_3_7_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_6 retainedParts_3_6_complete j]
    exact retainedRaise_3_6_entries.1 i j
  · intro i j
    simp only [retainedEnum_3_6, retainedEnum_3_7]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_7 retainedParts_3_7_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_6 retainedParts_3_6_complete j]
    exact retainedRaise_3_6_entries.2 i j

def retainedRaise_3_7C : Matrix (Fin 10) (Fin 8) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 2
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 1
  | 4, 3 => 1
  | 5, 1 => 1
  | 5, 4 => 1
  | 6, 2 => 1
  | 6, 4 => 2
  | 6, 5 => 1
  | 7, 3 => 1
  | 7, 5 => 1
  | 7, 6 => 2
  | 8, 5 => 1
  | 8, 7 => 1
  | 9, 6 => 1
  | 9, 7 => 2
  | _, _ => 0

def retainedRaise_3_7S : Matrix (Fin 10) (Fin 8) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 7
  | 1, 1 => 6
  | 2, 1 => 1
  | 2, 2 => 5
  | 3, 2 => 2
  | 3, 3 => 4
  | 4, 3 => 3
  | 5, 4 => 5
  | 6, 4 => 2
  | 6, 5 => 4
  | 7, 5 => 2
  | 7, 6 => 6
  | 8, 5 => 1
  | 8, 7 => 3
  | 9, 6 => 1
  | 9, 7 => 4
  | _, _ => 0

theorem retainedRaise_3_7_entries :
    (∀ (i : Fin 10) (j : Fin 8), retainedRaise_3_7C i j=
      tupleLowerConstant 7 (retainedParts_3_8.get i) (retainedParts_3_7.get j)) ∧
    (∀ (i : Fin 10) (j : Fin 8), retainedRaise_3_7S i j=
      tupleLowerSlope 7 (retainedParts_3_8.get i) (retainedParts_3_7.get j)) := by
  unfold retainedRaise_3_7C retainedRaise_3_7S
  decide +kernel

theorem retainedRaise_3_7_physical (Q : ℕ) (hd : 8≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_3_7 retainedEnum_3_8=
      retainedRaise_3_7C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_3_7S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_3_7, retainedEnum_3_8]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_8 retainedParts_3_8_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_7 retainedParts_3_7_complete j]
    exact retainedRaise_3_7_entries.1 i j
  · intro i j
    simp only [retainedEnum_3_7, retainedEnum_3_8]
    rw [sortedEnumerationOfTable_ofFn retainedParts_3_8 retainedParts_3_8_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_3_7 retainedParts_3_7_complete j]
    exact retainedRaise_3_7_entries.2 i j

def retainedRaise_4_0C : Matrix (Fin 1) (Fin 1) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 4
  | _, _ => 0

def retainedRaise_4_0S : Matrix (Fin 1) (Fin 1) ℕ := fun i j =>
  match i.val, j.val with
  | _, _ => 0

theorem retainedRaise_4_0_entries :
    (∀ (i : Fin 1) (j : Fin 1), retainedRaise_4_0C i j=
      tupleLowerConstant 0 (retainedParts_4_1.get i) (retainedParts_4_0.get j)) ∧
    (∀ (i : Fin 1) (j : Fin 1), retainedRaise_4_0S i j=
      tupleLowerSlope 0 (retainedParts_4_1.get i) (retainedParts_4_0.get j)) := by
  unfold retainedRaise_4_0C retainedRaise_4_0S
  decide +kernel

theorem retainedRaise_4_0_physical (Q : ℕ) (hd : 1≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_0 retainedEnum_4_1=
      retainedRaise_4_0C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_0S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_0, retainedEnum_4_1]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_1 retainedParts_4_1_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_0 retainedParts_4_0_complete j]
    exact retainedRaise_4_0_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_0, retainedEnum_4_1]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_1 retainedParts_4_1_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_0 retainedParts_4_0_complete j]
    exact retainedRaise_4_0_entries.2 i j

def retainedRaise_4_1C : Matrix (Fin 2) (Fin 1) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | _, _ => 0

def retainedRaise_4_1S : Matrix (Fin 2) (Fin 1) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | _, _ => 0

theorem retainedRaise_4_1_entries :
    (∀ (i : Fin 2) (j : Fin 1), retainedRaise_4_1C i j=
      tupleLowerConstant 1 (retainedParts_4_2.get i) (retainedParts_4_1.get j)) ∧
    (∀ (i : Fin 2) (j : Fin 1), retainedRaise_4_1S i j=
      tupleLowerSlope 1 (retainedParts_4_2.get i) (retainedParts_4_1.get j)) := by
  unfold retainedRaise_4_1C retainedRaise_4_1S
  decide +kernel

theorem retainedRaise_4_1_physical (Q : ℕ) (hd : 2≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_1 retainedEnum_4_2=
      retainedRaise_4_1C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_1S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_1, retainedEnum_4_2]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_2 retainedParts_4_2_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_1 retainedParts_4_1_complete j]
    exact retainedRaise_4_1_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_1, retainedEnum_4_2]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_2 retainedParts_4_2_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_1 retainedParts_4_1_complete j]
    exact retainedRaise_4_1_entries.2 i j

def retainedRaise_4_2C : Matrix (Fin 3) (Fin 2) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 2
  | 2, 1 => 2
  | _, _ => 0

def retainedRaise_4_2S : Matrix (Fin 3) (Fin 2) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 2
  | 1, 1 => 2
  | _, _ => 0

theorem retainedRaise_4_2_entries :
    (∀ (i : Fin 3) (j : Fin 2), retainedRaise_4_2C i j=
      tupleLowerConstant 2 (retainedParts_4_3.get i) (retainedParts_4_2.get j)) ∧
    (∀ (i : Fin 3) (j : Fin 2), retainedRaise_4_2S i j=
      tupleLowerSlope 2 (retainedParts_4_3.get i) (retainedParts_4_2.get j)) := by
  unfold retainedRaise_4_2C retainedRaise_4_2S
  decide +kernel

theorem retainedRaise_4_2_physical (Q : ℕ) (hd : 3≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_2 retainedEnum_4_3=
      retainedRaise_4_2C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_2S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_2, retainedEnum_4_3]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_3 retainedParts_4_3_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_2 retainedParts_4_2_complete j]
    exact retainedRaise_4_2_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_2, retainedEnum_4_3]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_3 retainedParts_4_3_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_2 retainedParts_4_2_complete j]
    exact retainedRaise_4_2_entries.2 i j

def retainedRaise_4_3C : Matrix (Fin 5) (Fin 3) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 3, 1 => 2
  | 3, 2 => 3
  | 4, 2 => 1
  | _, _ => 0

def retainedRaise_4_3S : Matrix (Fin 5) (Fin 3) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 3
  | 1, 1 => 2
  | 2, 1 => 1
  | 3, 2 => 3
  | _, _ => 0

theorem retainedRaise_4_3_entries :
    (∀ (i : Fin 5) (j : Fin 3), retainedRaise_4_3C i j=
      tupleLowerConstant 3 (retainedParts_4_4.get i) (retainedParts_4_3.get j)) ∧
    (∀ (i : Fin 5) (j : Fin 3), retainedRaise_4_3S i j=
      tupleLowerSlope 3 (retainedParts_4_4.get i) (retainedParts_4_3.get j)) := by
  unfold retainedRaise_4_3C retainedRaise_4_3S
  decide +kernel

theorem retainedRaise_4_3_physical (Q : ℕ) (hd : 4≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_3 retainedEnum_4_4=
      retainedRaise_4_3C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_3S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_3, retainedEnum_4_4]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_4 retainedParts_4_4_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_3 retainedParts_4_3_complete j]
    exact retainedRaise_4_3_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_3, retainedEnum_4_4]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_4 retainedParts_4_4_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_3 retainedParts_4_3_complete j]
    exact retainedRaise_4_3_entries.2 i j

def retainedRaise_4_4C : Matrix (Fin 6) (Fin 5) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 2
  | 3, 1 => 2
  | 3, 3 => 1
  | 4, 2 => 2
  | 4, 3 => 2
  | 5, 3 => 1
  | 5, 4 => 4
  | _, _ => 0

def retainedRaise_4_4S : Matrix (Fin 6) (Fin 5) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 4
  | 1, 1 => 3
  | 2, 1 => 1
  | 2, 2 => 4
  | 3, 3 => 2
  | 4, 3 => 2
  | 5, 4 => 4
  | _, _ => 0

theorem retainedRaise_4_4_entries :
    (∀ (i : Fin 6) (j : Fin 5), retainedRaise_4_4C i j=
      tupleLowerConstant 4 (retainedParts_4_5.get i) (retainedParts_4_4.get j)) ∧
    (∀ (i : Fin 6) (j : Fin 5), retainedRaise_4_4S i j=
      tupleLowerSlope 4 (retainedParts_4_5.get i) (retainedParts_4_4.get j)) := by
  unfold retainedRaise_4_4C retainedRaise_4_4S
  decide +kernel

theorem retainedRaise_4_4_physical (Q : ℕ) (hd : 5≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_4 retainedEnum_4_5=
      retainedRaise_4_4C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_4S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_4, retainedEnum_4_5]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_5 retainedParts_4_5_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_4 retainedParts_4_4_complete j]
    exact retainedRaise_4_4_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_4, retainedEnum_4_5]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_5 retainedParts_4_5_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_4 retainedParts_4_4_complete j]
    exact retainedRaise_4_4_entries.2 i j

def retainedRaise_4_5C : Matrix (Fin 9) (Fin 6) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 4, 1 => 2
  | 4, 3 => 1
  | 5, 2 => 2
  | 5, 3 => 2
  | 5, 4 => 2
  | 6, 4 => 1
  | 7, 3 => 1
  | 7, 5 => 1
  | 8, 4 => 1
  | 8, 5 => 3
  | _, _ => 0

def retainedRaise_4_5S : Matrix (Fin 9) (Fin 6) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 5
  | 1, 1 => 4
  | 2, 1 => 1
  | 2, 2 => 3
  | 3, 2 => 2
  | 4, 3 => 3
  | 5, 3 => 2
  | 5, 4 => 4
  | 6, 4 => 1
  | 7, 5 => 2
  | 8, 5 => 3
  | _, _ => 0

theorem retainedRaise_4_5_entries :
    (∀ (i : Fin 9) (j : Fin 6), retainedRaise_4_5C i j=
      tupleLowerConstant 5 (retainedParts_4_6.get i) (retainedParts_4_5.get j)) ∧
    (∀ (i : Fin 9) (j : Fin 6), retainedRaise_4_5S i j=
      tupleLowerSlope 5 (retainedParts_4_6.get i) (retainedParts_4_5.get j)) := by
  unfold retainedRaise_4_5C retainedRaise_4_5S
  decide +kernel

theorem retainedRaise_4_5_physical (Q : ℕ) (hd : 6≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_5 retainedEnum_4_6=
      retainedRaise_4_5C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_5S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_5, retainedEnum_4_6]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_6 retainedParts_4_6_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_5 retainedParts_4_5_complete j]
    exact retainedRaise_4_5_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_5, retainedEnum_4_6]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_6 retainedParts_4_6_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_5 retainedParts_4_5_complete j]
    exact retainedRaise_4_5_entries.2 i j

def retainedRaise_4_6C : Matrix (Fin 11) (Fin 9) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 2
  | 4, 1 => 2
  | 4, 4 => 1
  | 5, 2 => 2
  | 5, 4 => 2
  | 5, 5 => 1
  | 6, 3 => 2
  | 6, 5 => 1
  | 7, 5 => 1
  | 7, 6 => 3
  | 8, 4 => 1
  | 8, 7 => 1
  | 9, 5 => 1
  | 9, 7 => 3
  | 9, 8 => 2
  | 10, 6 => 1
  | 10, 8 => 2
  | _, _ => 0

def retainedRaise_4_6S : Matrix (Fin 11) (Fin 9) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 6
  | 1, 1 => 5
  | 2, 1 => 1
  | 2, 2 => 4
  | 3, 2 => 2
  | 3, 3 => 6
  | 4, 4 => 4
  | 5, 4 => 2
  | 5, 5 => 3
  | 6, 5 => 2
  | 7, 5 => 1
  | 7, 6 => 6
  | 8, 7 => 3
  | 9, 7 => 3
  | 9, 8 => 4
  | 10, 8 => 2
  | _, _ => 0

theorem retainedRaise_4_6_entries :
    (∀ (i : Fin 11) (j : Fin 9), retainedRaise_4_6C i j=
      tupleLowerConstant 6 (retainedParts_4_7.get i) (retainedParts_4_6.get j)) ∧
    (∀ (i : Fin 11) (j : Fin 9), retainedRaise_4_6S i j=
      tupleLowerSlope 6 (retainedParts_4_7.get i) (retainedParts_4_6.get j)) := by
  unfold retainedRaise_4_6C retainedRaise_4_6S
  decide +kernel

theorem retainedRaise_4_6_physical (Q : ℕ) (hd : 7≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_6 retainedEnum_4_7=
      retainedRaise_4_6C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_6S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_6, retainedEnum_4_7]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_7 retainedParts_4_7_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_6 retainedParts_4_6_complete j]
    exact retainedRaise_4_6_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_6, retainedEnum_4_7]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_7 retainedParts_4_7_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_6 retainedParts_4_6_complete j]
    exact retainedRaise_4_6_entries.2 i j

def retainedRaise_4_7C : Matrix (Fin 15) (Fin 11) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 1
  | 4, 3 => 1
  | 5, 1 => 2
  | 5, 4 => 1
  | 6, 2 => 2
  | 6, 4 => 2
  | 6, 5 => 1
  | 7, 3 => 2
  | 7, 5 => 1
  | 7, 6 => 2
  | 8, 5 => 1
  | 8, 7 => 1
  | 9, 6 => 1
  | 9, 7 => 2
  | 10, 4 => 1
  | 10, 8 => 1
  | 11, 5 => 1
  | 11, 8 => 3
  | 11, 9 => 1
  | 12, 6 => 1
  | 12, 9 => 1
  | 13, 7 => 1
  | 13, 9 => 2
  | 13, 10 => 3
  | 14, 10 => 1
  | _, _ => 0

def retainedRaise_4_7S : Matrix (Fin 15) (Fin 11) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 7
  | 1, 1 => 6
  | 2, 1 => 1
  | 2, 2 => 5
  | 3, 2 => 2
  | 3, 3 => 4
  | 4, 3 => 3
  | 5, 4 => 5
  | 6, 4 => 2
  | 6, 5 => 4
  | 7, 5 => 2
  | 7, 6 => 6
  | 8, 5 => 1
  | 8, 7 => 3
  | 9, 6 => 1
  | 9, 7 => 4
  | 10, 8 => 4
  | 11, 8 => 3
  | 11, 9 => 3
  | 12, 9 => 2
  | 13, 9 => 2
  | 13, 10 => 6
  | 14, 10 => 1
  | _, _ => 0

theorem retainedRaise_4_7_entries :
    (∀ (i : Fin 15) (j : Fin 11), retainedRaise_4_7C i j=
      tupleLowerConstant 7 (retainedParts_4_8.get i) (retainedParts_4_7.get j)) ∧
    (∀ (i : Fin 15) (j : Fin 11), retainedRaise_4_7S i j=
      tupleLowerSlope 7 (retainedParts_4_8.get i) (retainedParts_4_7.get j)) := by
  unfold retainedRaise_4_7C retainedRaise_4_7S
  decide +kernel

theorem retainedRaise_4_7_physical (Q : ℕ) (hd : 8≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_7 retainedEnum_4_8=
      retainedRaise_4_7C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_7S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_7, retainedEnum_4_8]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_8 retainedParts_4_8_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_7 retainedParts_4_7_complete j]
    exact retainedRaise_4_7_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_7, retainedEnum_4_8]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_8 retainedParts_4_8_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_7 retainedParts_4_7_complete j]
    exact retainedRaise_4_7_entries.2 i j

def retainedRaise_4_8C : Matrix (Fin 18) (Fin 15) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 1
  | 4, 3 => 1
  | 4, 4 => 2
  | 5, 1 => 2
  | 5, 5 => 1
  | 6, 2 => 2
  | 6, 5 => 2
  | 6, 6 => 1
  | 7, 3 => 2
  | 7, 6 => 1
  | 7, 7 => 1
  | 8, 4 => 2
  | 8, 7 => 1
  | 9, 6 => 1
  | 9, 8 => 1
  | 10, 7 => 1
  | 10, 8 => 2
  | 10, 9 => 2
  | 11, 9 => 1
  | 12, 5 => 1
  | 12, 10 => 1
  | 13, 6 => 1
  | 13, 10 => 3
  | 13, 11 => 1
  | 14, 7 => 1
  | 14, 11 => 1
  | 14, 12 => 2
  | 15, 8 => 1
  | 15, 11 => 2
  | 15, 13 => 1
  | 16, 9 => 1
  | 16, 12 => 2
  | 16, 13 => 2
  | 17, 13 => 1
  | 17, 14 => 4
  | _, _ => 0

def retainedRaise_4_8S : Matrix (Fin 18) (Fin 15) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 8
  | 1, 1 => 7
  | 2, 1 => 1
  | 2, 2 => 6
  | 3, 2 => 2
  | 3, 3 => 5
  | 4, 3 => 3
  | 4, 4 => 8
  | 5, 5 => 6
  | 6, 5 => 2
  | 6, 6 => 5
  | 7, 6 => 2
  | 7, 7 => 4
  | 8, 7 => 3
  | 9, 6 => 1
  | 9, 8 => 4
  | 10, 7 => 1
  | 10, 8 => 4
  | 10, 9 => 6
  | 11, 9 => 2
  | 12, 10 => 5
  | 13, 10 => 3
  | 13, 11 => 4
  | 14, 11 => 2
  | 14, 12 => 6
  | 15, 11 => 2
  | 15, 13 => 3
  | 16, 12 => 2
  | 16, 13 => 4
  | 17, 13 => 1
  | 17, 14 => 8
  | _, _ => 0

theorem retainedRaise_4_8_entries :
    (∀ (i : Fin 18) (j : Fin 15), retainedRaise_4_8C i j=
      tupleLowerConstant 8 (retainedParts_4_9.get i) (retainedParts_4_8.get j)) ∧
    (∀ (i : Fin 18) (j : Fin 15), retainedRaise_4_8S i j=
      tupleLowerSlope 8 (retainedParts_4_9.get i) (retainedParts_4_8.get j)) := by
  unfold retainedRaise_4_8C retainedRaise_4_8S
  decide +kernel

theorem retainedRaise_4_8_physical (Q : ℕ) (hd : 9≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_8 retainedEnum_4_9=
      retainedRaise_4_8C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_8S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_8, retainedEnum_4_9]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_9 retainedParts_4_9_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_8 retainedParts_4_8_complete j]
    exact retainedRaise_4_8_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_8, retainedEnum_4_9]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_9 retainedParts_4_9_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_8 retainedParts_4_8_complete j]
    exact retainedRaise_4_8_entries.2 i j

def retainedRaise_4_9C : Matrix (Fin 23) (Fin 18) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 5, 4 => 1
  | 6, 1 => 2
  | 6, 5 => 1
  | 7, 2 => 2
  | 7, 5 => 2
  | 7, 6 => 1
  | 8, 3 => 2
  | 8, 6 => 1
  | 8, 7 => 1
  | 9, 4 => 2
  | 9, 7 => 1
  | 9, 8 => 2
  | 10, 6 => 1
  | 10, 9 => 1
  | 11, 7 => 1
  | 11, 9 => 2
  | 11, 10 => 1
  | 12, 8 => 1
  | 12, 10 => 1
  | 13, 10 => 1
  | 13, 11 => 3
  | 14, 5 => 1
  | 14, 12 => 1
  | 15, 6 => 1
  | 15, 12 => 3
  | 15, 13 => 1
  | 16, 7 => 1
  | 16, 13 => 1
  | 16, 14 => 1
  | 17, 8 => 1
  | 17, 14 => 1
  | 18, 9 => 1
  | 18, 13 => 2
  | 18, 15 => 1
  | 19, 10 => 1
  | 19, 14 => 2
  | 19, 15 => 2
  | 19, 16 => 2
  | 20, 11 => 1
  | 20, 16 => 1
  | 21, 15 => 1
  | 21, 17 => 1
  | 22, 16 => 1
  | 22, 17 => 3
  | _, _ => 0

def retainedRaise_4_9S : Matrix (Fin 23) (Fin 18) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 9
  | 1, 1 => 8
  | 2, 1 => 1
  | 2, 2 => 7
  | 3, 2 => 2
  | 3, 3 => 6
  | 4, 3 => 3
  | 4, 4 => 5
  | 5, 4 => 4
  | 6, 5 => 7
  | 7, 5 => 2
  | 7, 6 => 6
  | 8, 6 => 2
  | 8, 7 => 5
  | 9, 7 => 3
  | 9, 8 => 8
  | 10, 6 => 1
  | 10, 9 => 5
  | 11, 7 => 1
  | 11, 9 => 4
  | 11, 10 => 4
  | 12, 8 => 1
  | 12, 10 => 3
  | 13, 10 => 2
  | 13, 11 => 9
  | 14, 12 => 6
  | 15, 12 => 3
  | 15, 13 => 5
  | 16, 13 => 2
  | 16, 14 => 4
  | 17, 14 => 3
  | 18, 13 => 2
  | 18, 15 => 4
  | 19, 14 => 2
  | 19, 15 => 4
  | 19, 16 => 6
  | 20, 16 => 2
  | 21, 15 => 1
  | 21, 17 => 3
  | 22, 16 => 1
  | 22, 17 => 6
  | _, _ => 0

theorem retainedRaise_4_9_entries :
    (∀ (i : Fin 23) (j : Fin 18), retainedRaise_4_9C i j=
      tupleLowerConstant 9 (retainedParts_4_10.get i) (retainedParts_4_9.get j)) ∧
    (∀ (i : Fin 23) (j : Fin 18), retainedRaise_4_9S i j=
      tupleLowerSlope 9 (retainedParts_4_10.get i) (retainedParts_4_9.get j)) := by
  unfold retainedRaise_4_9C retainedRaise_4_9S
  decide +kernel

theorem retainedRaise_4_9_physical (Q : ℕ) (hd : 10≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_9 retainedEnum_4_10=
      retainedRaise_4_9C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_9S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_9, retainedEnum_4_10]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_10 retainedParts_4_10_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_9 retainedParts_4_9_complete j]
    exact retainedRaise_4_9_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_9, retainedEnum_4_10]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_10 retainedParts_4_10_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_9 retainedParts_4_9_complete j]
    exact retainedRaise_4_9_entries.2 i j

def retainedRaise_4_10C : Matrix (Fin 27) (Fin 23) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 5, 4 => 1
  | 5, 5 => 2
  | 6, 1 => 2
  | 6, 6 => 1
  | 7, 2 => 2
  | 7, 6 => 2
  | 7, 7 => 1
  | 8, 3 => 2
  | 8, 7 => 1
  | 8, 8 => 1
  | 9, 4 => 2
  | 9, 8 => 1
  | 9, 9 => 1
  | 10, 5 => 2
  | 10, 9 => 1
  | 11, 7 => 1
  | 11, 10 => 1
  | 12, 8 => 1
  | 12, 10 => 2
  | 12, 11 => 1
  | 13, 9 => 1
  | 13, 11 => 1
  | 13, 12 => 2
  | 14, 11 => 1
  | 14, 13 => 1
  | 15, 12 => 1
  | 15, 13 => 2
  | 16, 6 => 1
  | 16, 14 => 1
  | 17, 7 => 1
  | 17, 14 => 3
  | 17, 15 => 1
  | 18, 8 => 1
  | 18, 15 => 1
  | 18, 16 => 1
  | 19, 9 => 1
  | 19, 16 => 1
  | 19, 17 => 2
  | 20, 10 => 1
  | 20, 15 => 2
  | 20, 18 => 1
  | 21, 11 => 1
  | 21, 16 => 2
  | 21, 18 => 2
  | 21, 19 => 1
  | 22, 12 => 1
  | 22, 17 => 2
  | 22, 19 => 1
  | 23, 13 => 1
  | 23, 19 => 1
  | 23, 20 => 3
  | 24, 18 => 1
  | 24, 21 => 1
  | 25, 19 => 1
  | 25, 21 => 3
  | 25, 22 => 2
  | 26, 20 => 1
  | 26, 22 => 2
  | _, _ => 0

def retainedRaise_4_10S : Matrix (Fin 27) (Fin 23) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 10
  | 1, 1 => 9
  | 2, 1 => 1
  | 2, 2 => 8
  | 3, 2 => 2
  | 3, 3 => 7
  | 4, 3 => 3
  | 4, 4 => 6
  | 5, 4 => 4
  | 5, 5 => 10
  | 6, 6 => 8
  | 7, 6 => 2
  | 7, 7 => 7
  | 8, 7 => 2
  | 8, 8 => 6
  | 9, 8 => 3
  | 9, 9 => 5
  | 10, 9 => 4
  | 11, 7 => 1
  | 11, 10 => 6
  | 12, 8 => 1
  | 12, 10 => 4
  | 12, 11 => 5
  | 13, 9 => 1
  | 13, 11 => 3
  | 13, 12 => 8
  | 14, 11 => 2
  | 14, 13 => 4
  | 15, 12 => 2
  | 15, 13 => 6
  | 16, 14 => 7
  | 17, 14 => 3
  | 17, 15 => 6
  | 18, 15 => 2
  | 18, 16 => 5
  | 19, 16 => 3
  | 19, 17 => 8
  | 20, 15 => 2
  | 20, 18 => 5
  | 21, 16 => 2
  | 21, 18 => 4
  | 21, 19 => 4
  | 22, 17 => 2
  | 22, 19 => 3
  | 23, 19 => 2
  | 23, 20 => 9
  | 24, 18 => 1
  | 24, 21 => 4
  | 25, 19 => 1
  | 25, 21 => 6
  | 25, 22 => 6
  | 26, 20 => 1
  | 26, 22 => 4
  | _, _ => 0

theorem retainedRaise_4_10_entries :
    (∀ (i : Fin 27) (j : Fin 23), retainedRaise_4_10C i j=
      tupleLowerConstant 10 (retainedParts_4_11.get i) (retainedParts_4_10.get j)) ∧
    (∀ (i : Fin 27) (j : Fin 23), retainedRaise_4_10S i j=
      tupleLowerSlope 10 (retainedParts_4_11.get i) (retainedParts_4_10.get j)) := by
  unfold retainedRaise_4_10C retainedRaise_4_10S
  decide +kernel

theorem retainedRaise_4_10_physical (Q : ℕ) (hd : 11≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_10 retainedEnum_4_11=
      retainedRaise_4_10C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_10S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_10, retainedEnum_4_11]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_11 retainedParts_4_11_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_10 retainedParts_4_10_complete j]
    exact retainedRaise_4_10_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_10, retainedEnum_4_11]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_11 retainedParts_4_11_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_10 retainedParts_4_10_complete j]
    exact retainedRaise_4_10_entries.2 i j

def retainedRaise_4_11C : Matrix (Fin 34) (Fin 27) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 5, 4 => 1
  | 5, 5 => 1
  | 6, 5 => 1
  | 7, 1 => 2
  | 7, 6 => 1
  | 8, 2 => 2
  | 8, 6 => 2
  | 8, 7 => 1
  | 9, 3 => 2
  | 9, 7 => 1
  | 9, 8 => 1
  | 10, 4 => 2
  | 10, 8 => 1
  | 10, 9 => 1
  | 11, 5 => 2
  | 11, 9 => 1
  | 11, 10 => 2
  | 12, 7 => 1
  | 12, 11 => 1
  | 13, 8 => 1
  | 13, 11 => 2
  | 13, 12 => 1
  | 14, 9 => 1
  | 14, 12 => 1
  | 14, 13 => 1
  | 15, 10 => 1
  | 15, 13 => 1
  | 16, 12 => 1
  | 16, 14 => 1
  | 17, 13 => 1
  | 17, 14 => 2
  | 17, 15 => 2
  | 18, 15 => 1
  | 19, 6 => 1
  | 19, 16 => 1
  | 20, 7 => 1
  | 20, 16 => 3
  | 20, 17 => 1
  | 21, 8 => 1
  | 21, 17 => 1
  | 21, 18 => 1
  | 22, 9 => 1
  | 22, 18 => 1
  | 22, 19 => 1
  | 23, 10 => 1
  | 23, 19 => 1
  | 24, 11 => 1
  | 24, 17 => 2
  | 24, 20 => 1
  | 25, 12 => 1
  | 25, 18 => 2
  | 25, 20 => 2
  | 25, 21 => 1
  | 26, 13 => 1
  | 26, 19 => 2
  | 26, 21 => 1
  | 26, 22 => 2
  | 27, 14 => 1
  | 27, 21 => 1
  | 27, 23 => 1
  | 28, 15 => 1
  | 28, 22 => 1
  | 28, 23 => 2
  | 29, 20 => 1
  | 29, 24 => 1
  | 30, 21 => 1
  | 30, 24 => 3
  | 30, 25 => 1
  | 31, 22 => 1
  | 31, 25 => 1
  | 32, 23 => 1
  | 32, 25 => 2
  | 32, 26 => 3
  | 33, 26 => 1
  | _, _ => 0

def retainedRaise_4_11S : Matrix (Fin 34) (Fin 27) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 11
  | 1, 1 => 10
  | 2, 1 => 1
  | 2, 2 => 9
  | 3, 2 => 2
  | 3, 3 => 8
  | 4, 3 => 3
  | 4, 4 => 7
  | 5, 4 => 4
  | 5, 5 => 6
  | 6, 5 => 5
  | 7, 6 => 9
  | 8, 6 => 2
  | 8, 7 => 8
  | 9, 7 => 2
  | 9, 8 => 7
  | 10, 8 => 3
  | 10, 9 => 6
  | 11, 9 => 4
  | 11, 10 => 10
  | 12, 7 => 1
  | 12, 11 => 7
  | 13, 8 => 1
  | 13, 11 => 4
  | 13, 12 => 6
  | 14, 9 => 1
  | 14, 12 => 3
  | 14, 13 => 5
  | 15, 10 => 1
  | 15, 13 => 4
  | 16, 12 => 2
  | 16, 14 => 5
  | 17, 13 => 2
  | 17, 14 => 6
  | 17, 15 => 8
  | 18, 15 => 3
  | 19, 16 => 8
  | 20, 16 => 3
  | 20, 17 => 7
  | 21, 17 => 2
  | 21, 18 => 6
  | 22, 18 => 3
  | 22, 19 => 5
  | 23, 19 => 4
  | 24, 17 => 2
  | 24, 20 => 6
  | 25, 18 => 2
  | 25, 20 => 4
  | 25, 21 => 5
  | 26, 19 => 2
  | 26, 21 => 3
  | 26, 22 => 8
  | 27, 21 => 2
  | 27, 23 => 4
  | 28, 22 => 2
  | 28, 23 => 6
  | 29, 20 => 1
  | 29, 24 => 5
  | 30, 21 => 1
  | 30, 24 => 6
  | 30, 25 => 4
  | 31, 22 => 1
  | 31, 25 => 3
  | 32, 23 => 1
  | 32, 25 => 4
  | 32, 26 => 9
  | 33, 26 => 2
  | _, _ => 0

theorem retainedRaise_4_11_entries :
    (∀ (i : Fin 34) (j : Fin 27), retainedRaise_4_11C i j=
      tupleLowerConstant 11 (retainedParts_4_12.get i) (retainedParts_4_11.get j)) ∧
    (∀ (i : Fin 34) (j : Fin 27), retainedRaise_4_11S i j=
      tupleLowerSlope 11 (retainedParts_4_12.get i) (retainedParts_4_11.get j)) := by
  unfold retainedRaise_4_11C retainedRaise_4_11S
  decide +kernel

theorem retainedRaise_4_11_physical (Q : ℕ) (hd : 12≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_11 retainedEnum_4_12=
      retainedRaise_4_11C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_11S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_11, retainedEnum_4_12]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_12 retainedParts_4_12_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_11 retainedParts_4_11_complete j]
    exact retainedRaise_4_11_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_11, retainedEnum_4_12]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_12 retainedParts_4_12_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_11 retainedParts_4_11_complete j]
    exact retainedRaise_4_11_entries.2 i j

def retainedRaise_4_12C : Matrix (Fin 39) (Fin 34) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 5, 4 => 1
  | 5, 5 => 1
  | 6, 5 => 1
  | 6, 6 => 2
  | 7, 1 => 2
  | 7, 7 => 1
  | 8, 2 => 2
  | 8, 7 => 2
  | 8, 8 => 1
  | 9, 3 => 2
  | 9, 8 => 1
  | 9, 9 => 1
  | 10, 4 => 2
  | 10, 9 => 1
  | 10, 10 => 1
  | 11, 5 => 2
  | 11, 10 => 1
  | 11, 11 => 1
  | 12, 6 => 2
  | 12, 11 => 1
  | 13, 8 => 1
  | 13, 12 => 1
  | 14, 9 => 1
  | 14, 12 => 2
  | 14, 13 => 1
  | 15, 10 => 1
  | 15, 13 => 1
  | 15, 14 => 1
  | 16, 11 => 1
  | 16, 14 => 1
  | 16, 15 => 2
  | 17, 13 => 1
  | 17, 16 => 1
  | 18, 14 => 1
  | 18, 16 => 2
  | 18, 17 => 1
  | 19, 15 => 1
  | 19, 17 => 1
  | 20, 17 => 1
  | 20, 18 => 3
  | 21, 7 => 1
  | 21, 19 => 1
  | 22, 8 => 1
  | 22, 19 => 3
  | 22, 20 => 1
  | 23, 9 => 1
  | 23, 20 => 1
  | 23, 21 => 1
  | 24, 10 => 1
  | 24, 21 => 1
  | 24, 22 => 1
  | 25, 11 => 1
  | 25, 22 => 1
  | 25, 23 => 2
  | 26, 12 => 1
  | 26, 20 => 2
  | 26, 24 => 1
  | 27, 13 => 1
  | 27, 21 => 2
  | 27, 24 => 2
  | 27, 25 => 1
  | 28, 14 => 1
  | 28, 22 => 2
  | 28, 25 => 1
  | 28, 26 => 1
  | 29, 15 => 1
  | 29, 23 => 2
  | 29, 26 => 1
  | 30, 16 => 1
  | 30, 25 => 1
  | 30, 27 => 1
  | 31, 17 => 1
  | 31, 26 => 1
  | 31, 27 => 2
  | 31, 28 => 2
  | 32, 18 => 1
  | 32, 28 => 1
  | 33, 24 => 1
  | 33, 29 => 1
  | 34, 25 => 1
  | 34, 29 => 3
  | 34, 30 => 1
  | 35, 26 => 1
  | 35, 30 => 1
  | 35, 31 => 2
  | 36, 27 => 1
  | 36, 30 => 2
  | 36, 32 => 1
  | 37, 28 => 1
  | 37, 31 => 2
  | 37, 32 => 2
  | 38, 32 => 1
  | 38, 33 => 4
  | _, _ => 0

def retainedRaise_4_12S : Matrix (Fin 39) (Fin 34) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 12
  | 1, 1 => 11
  | 2, 1 => 1
  | 2, 2 => 10
  | 3, 2 => 2
  | 3, 3 => 9
  | 4, 3 => 3
  | 4, 4 => 8
  | 5, 4 => 4
  | 5, 5 => 7
  | 6, 5 => 5
  | 6, 6 => 12
  | 7, 7 => 10
  | 8, 7 => 2
  | 8, 8 => 9
  | 9, 8 => 2
  | 9, 9 => 8
  | 10, 9 => 3
  | 10, 10 => 7
  | 11, 10 => 4
  | 11, 11 => 6
  | 12, 11 => 5
  | 13, 8 => 1
  | 13, 12 => 8
  | 14, 9 => 1
  | 14, 12 => 4
  | 14, 13 => 7
  | 15, 10 => 1
  | 15, 13 => 3
  | 15, 14 => 6
  | 16, 11 => 1
  | 16, 14 => 4
  | 16, 15 => 10
  | 17, 13 => 2
  | 17, 16 => 6
  | 18, 14 => 2
  | 18, 16 => 6
  | 18, 17 => 5
  | 19, 15 => 2
  | 19, 17 => 4
  | 20, 17 => 3
  | 20, 18 => 12
  | 21, 19 => 9
  | 22, 19 => 3
  | 22, 20 => 8
  | 23, 20 => 2
  | 23, 21 => 7
  | 24, 21 => 3
  | 24, 22 => 6
  | 25, 22 => 4
  | 25, 23 => 10
  | 26, 20 => 2
  | 26, 24 => 7
  | 27, 21 => 2
  | 27, 24 => 4
  | 27, 25 => 6
  | 28, 22 => 2
  | 28, 25 => 3
  | 28, 26 => 5
  | 29, 23 => 2
  | 29, 26 => 4
  | 30, 25 => 2
  | 30, 27 => 5
  | 31, 26 => 2
  | 31, 27 => 6
  | 31, 28 => 8
  | 32, 28 => 3
  | 33, 24 => 1
  | 33, 29 => 6
  | 34, 25 => 1
  | 34, 29 => 6
  | 34, 30 => 5
  | 35, 26 => 1
  | 35, 30 => 3
  | 35, 31 => 8
  | 36, 27 => 1
  | 36, 30 => 4
  | 36, 32 => 4
  | 37, 28 => 1
  | 37, 31 => 4
  | 37, 32 => 6
  | 38, 32 => 2
  | 38, 33 => 12
  | _, _ => 0

theorem retainedRaise_4_12_entries :
    (∀ (i : Fin 39) (j : Fin 34), retainedRaise_4_12C i j=
      tupleLowerConstant 12 (retainedParts_4_13.get i) (retainedParts_4_12.get j)) ∧
    (∀ (i : Fin 39) (j : Fin 34), retainedRaise_4_12S i j=
      tupleLowerSlope 12 (retainedParts_4_13.get i) (retainedParts_4_12.get j)) := by
  unfold retainedRaise_4_12C retainedRaise_4_12S
  decide +kernel

theorem retainedRaise_4_12_physical (Q : ℕ) (hd : 13≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_12 retainedEnum_4_13=
      retainedRaise_4_12C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_12S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_12, retainedEnum_4_13]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_13 retainedParts_4_13_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_12 retainedParts_4_12_complete j]
    exact retainedRaise_4_12_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_12, retainedEnum_4_13]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_13 retainedParts_4_13_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_12 retainedParts_4_12_complete j]
    exact retainedRaise_4_12_entries.2 i j

def retainedRaise_4_13C : Matrix (Fin 47) (Fin 39) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 5, 4 => 1
  | 5, 5 => 1
  | 6, 5 => 1
  | 6, 6 => 1
  | 7, 6 => 1
  | 8, 1 => 2
  | 8, 7 => 1
  | 9, 2 => 2
  | 9, 7 => 2
  | 9, 8 => 1
  | 10, 3 => 2
  | 10, 8 => 1
  | 10, 9 => 1
  | 11, 4 => 2
  | 11, 9 => 1
  | 11, 10 => 1
  | 12, 5 => 2
  | 12, 10 => 1
  | 12, 11 => 1
  | 13, 6 => 2
  | 13, 11 => 1
  | 13, 12 => 2
  | 14, 8 => 1
  | 14, 13 => 1
  | 15, 9 => 1
  | 15, 13 => 2
  | 15, 14 => 1
  | 16, 10 => 1
  | 16, 14 => 1
  | 16, 15 => 1
  | 17, 11 => 1
  | 17, 15 => 1
  | 17, 16 => 1
  | 18, 12 => 1
  | 18, 16 => 1
  | 19, 14 => 1
  | 19, 17 => 1
  | 20, 15 => 1
  | 20, 17 => 2
  | 20, 18 => 1
  | 21, 16 => 1
  | 21, 18 => 1
  | 21, 19 => 2
  | 22, 18 => 1
  | 22, 20 => 1
  | 23, 19 => 1
  | 23, 20 => 2
  | 24, 7 => 1
  | 24, 21 => 1
  | 25, 8 => 1
  | 25, 21 => 3
  | 25, 22 => 1
  | 26, 9 => 1
  | 26, 22 => 1
  | 26, 23 => 1
  | 27, 10 => 1
  | 27, 23 => 1
  | 27, 24 => 1
  | 28, 11 => 1
  | 28, 24 => 1
  | 28, 25 => 1
  | 29, 12 => 1
  | 29, 25 => 1
  | 30, 13 => 1
  | 30, 22 => 2
  | 30, 26 => 1
  | 31, 14 => 1
  | 31, 23 => 2
  | 31, 26 => 2
  | 31, 27 => 1
  | 32, 15 => 1
  | 32, 24 => 2
  | 32, 27 => 1
  | 32, 28 => 1
  | 33, 16 => 1
  | 33, 25 => 2
  | 33, 28 => 1
  | 33, 29 => 2
  | 34, 17 => 1
  | 34, 27 => 1
  | 34, 30 => 1
  | 35, 18 => 1
  | 35, 28 => 1
  | 35, 30 => 2
  | 35, 31 => 1
  | 36, 19 => 1
  | 36, 29 => 1
  | 36, 31 => 1
  | 37, 20 => 1
  | 37, 31 => 1
  | 37, 32 => 3
  | 38, 26 => 1
  | 38, 33 => 1
  | 39, 27 => 1
  | 39, 33 => 3
  | 39, 34 => 1
  | 40, 28 => 1
  | 40, 34 => 1
  | 40, 35 => 1
  | 41, 29 => 1
  | 41, 35 => 1
  | 42, 30 => 1
  | 42, 34 => 2
  | 42, 36 => 1
  | 43, 31 => 1
  | 43, 35 => 2
  | 43, 36 => 2
  | 43, 37 => 2
  | 44, 32 => 1
  | 44, 37 => 1
  | 45, 36 => 1
  | 45, 38 => 1
  | 46, 37 => 1
  | 46, 38 => 3
  | _, _ => 0

def retainedRaise_4_13S : Matrix (Fin 47) (Fin 39) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 13
  | 1, 1 => 12
  | 2, 1 => 1
  | 2, 2 => 11
  | 3, 2 => 2
  | 3, 3 => 10
  | 4, 3 => 3
  | 4, 4 => 9
  | 5, 4 => 4
  | 5, 5 => 8
  | 6, 5 => 5
  | 6, 6 => 7
  | 7, 6 => 6
  | 8, 7 => 11
  | 9, 7 => 2
  | 9, 8 => 10
  | 10, 8 => 2
  | 10, 9 => 9
  | 11, 9 => 3
  | 11, 10 => 8
  | 12, 10 => 4
  | 12, 11 => 7
  | 13, 11 => 5
  | 13, 12 => 12
  | 14, 8 => 1
  | 14, 13 => 9
  | 15, 9 => 1
  | 15, 13 => 4
  | 15, 14 => 8
  | 16, 10 => 1
  | 16, 14 => 3
  | 16, 15 => 7
  | 17, 11 => 1
  | 17, 15 => 4
  | 17, 16 => 6
  | 18, 12 => 1
  | 18, 16 => 5
  | 19, 14 => 2
  | 19, 17 => 7
  | 20, 15 => 2
  | 20, 17 => 6
  | 20, 18 => 6
  | 21, 16 => 2
  | 21, 18 => 4
  | 21, 19 => 10
  | 22, 18 => 3
  | 22, 20 => 5
  | 23, 19 => 3
  | 23, 20 => 8
  | 24, 21 => 10
  | 25, 21 => 3
  | 25, 22 => 9
  | 26, 22 => 2
  | 26, 23 => 8
  | 27, 23 => 3
  | 27, 24 => 7
  | 28, 24 => 4
  | 28, 25 => 6
  | 29, 25 => 5
  | 30, 22 => 2
  | 30, 26 => 8
  | 31, 23 => 2
  | 31, 26 => 4
  | 31, 27 => 7
  | 32, 24 => 2
  | 32, 27 => 3
  | 32, 28 => 6
  | 33, 25 => 2
  | 33, 28 => 4
  | 33, 29 => 10
  | 34, 27 => 2
  | 34, 30 => 6
  | 35, 28 => 2
  | 35, 30 => 6
  | 35, 31 => 5
  | 36, 29 => 2
  | 36, 31 => 4
  | 37, 31 => 3
  | 37, 32 => 12
  | 38, 26 => 1
  | 38, 33 => 7
  | 39, 27 => 1
  | 39, 33 => 6
  | 39, 34 => 6
  | 40, 28 => 1
  | 40, 34 => 3
  | 40, 35 => 5
  | 41, 29 => 1
  | 41, 35 => 4
  | 42, 30 => 1
  | 42, 34 => 4
  | 42, 36 => 5
  | 43, 31 => 1
  | 43, 35 => 4
  | 43, 36 => 6
  | 43, 37 => 8
  | 44, 32 => 1
  | 44, 37 => 3
  | 45, 36 => 2
  | 45, 38 => 4
  | 46, 37 => 2
  | 46, 38 => 9
  | _, _ => 0

theorem retainedRaise_4_13_entries :
    (∀ (i : Fin 47) (j : Fin 39), retainedRaise_4_13C i j=
      tupleLowerConstant 13 (retainedParts_4_14.get i) (retainedParts_4_13.get j)) ∧
    (∀ (i : Fin 47) (j : Fin 39), retainedRaise_4_13S i j=
      tupleLowerSlope 13 (retainedParts_4_14.get i) (retainedParts_4_13.get j)) := by
  unfold retainedRaise_4_13C retainedRaise_4_13S
  decide +kernel

theorem retainedRaise_4_13_physical (Q : ℕ) (hd : 14≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_13 retainedEnum_4_14=
      retainedRaise_4_13C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_13S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_13, retainedEnum_4_14]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_14 retainedParts_4_14_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_13 retainedParts_4_13_complete j]
    exact retainedRaise_4_13_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_13, retainedEnum_4_14]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_14 retainedParts_4_14_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_13 retainedParts_4_13_complete j]
    exact retainedRaise_4_13_entries.2 i j

def retainedRaise_4_14C : Matrix (Fin 54) (Fin 47) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 5, 4 => 1
  | 5, 5 => 1
  | 6, 5 => 1
  | 6, 6 => 1
  | 7, 6 => 1
  | 7, 7 => 2
  | 8, 1 => 2
  | 8, 8 => 1
  | 9, 2 => 2
  | 9, 8 => 2
  | 9, 9 => 1
  | 10, 3 => 2
  | 10, 9 => 1
  | 10, 10 => 1
  | 11, 4 => 2
  | 11, 10 => 1
  | 11, 11 => 1
  | 12, 5 => 2
  | 12, 11 => 1
  | 12, 12 => 1
  | 13, 6 => 2
  | 13, 12 => 1
  | 13, 13 => 1
  | 14, 7 => 2
  | 14, 13 => 1
  | 15, 9 => 1
  | 15, 14 => 1
  | 16, 10 => 1
  | 16, 14 => 2
  | 16, 15 => 1
  | 17, 11 => 1
  | 17, 15 => 1
  | 17, 16 => 1
  | 18, 12 => 1
  | 18, 16 => 1
  | 18, 17 => 1
  | 19, 13 => 1
  | 19, 17 => 1
  | 19, 18 => 2
  | 20, 15 => 1
  | 20, 19 => 1
  | 21, 16 => 1
  | 21, 19 => 2
  | 21, 20 => 1
  | 22, 17 => 1
  | 22, 20 => 1
  | 22, 21 => 1
  | 23, 18 => 1
  | 23, 21 => 1
  | 24, 20 => 1
  | 24, 22 => 1
  | 25, 21 => 1
  | 25, 22 => 2
  | 25, 23 => 2
  | 26, 23 => 1
  | 27, 8 => 1
  | 27, 24 => 1
  | 28, 9 => 1
  | 28, 24 => 3
  | 28, 25 => 1
  | 29, 10 => 1
  | 29, 25 => 1
  | 29, 26 => 1
  | 30, 11 => 1
  | 30, 26 => 1
  | 30, 27 => 1
  | 31, 12 => 1
  | 31, 27 => 1
  | 31, 28 => 1
  | 32, 13 => 1
  | 32, 28 => 1
  | 32, 29 => 2
  | 33, 14 => 1
  | 33, 25 => 2
  | 33, 30 => 1
  | 34, 15 => 1
  | 34, 26 => 2
  | 34, 30 => 2
  | 34, 31 => 1
  | 35, 16 => 1
  | 35, 27 => 2
  | 35, 31 => 1
  | 35, 32 => 1
  | 36, 17 => 1
  | 36, 28 => 2
  | 36, 32 => 1
  | 36, 33 => 1
  | 37, 18 => 1
  | 37, 29 => 2
  | 37, 33 => 1
  | 38, 19 => 1
  | 38, 31 => 1
  | 38, 34 => 1
  | 39, 20 => 1
  | 39, 32 => 1
  | 39, 34 => 2
  | 39, 35 => 1
  | 40, 21 => 1
  | 40, 33 => 1
  | 40, 35 => 1
  | 40, 36 => 2
  | 41, 22 => 1
  | 41, 35 => 1
  | 41, 37 => 1
  | 42, 23 => 1
  | 42, 36 => 1
  | 42, 37 => 2
  | 43, 30 => 1
  | 43, 38 => 1
  | 44, 31 => 1
  | 44, 38 => 3
  | 44, 39 => 1
  | 45, 32 => 1
  | 45, 39 => 1
  | 45, 40 => 1
  | 46, 33 => 1
  | 46, 40 => 1
  | 46, 41 => 2
  | 47, 34 => 1
  | 47, 39 => 2
  | 47, 42 => 1
  | 48, 35 => 1
  | 48, 40 => 2
  | 48, 42 => 2
  | 48, 43 => 1
  | 49, 36 => 1
  | 49, 41 => 2
  | 49, 43 => 1
  | 50, 37 => 1
  | 50, 43 => 1
  | 50, 44 => 3
  | 51, 42 => 1
  | 51, 45 => 1
  | 52, 43 => 1
  | 52, 45 => 3
  | 52, 46 => 2
  | 53, 44 => 1
  | 53, 46 => 2
  | _, _ => 0

def retainedRaise_4_14S : Matrix (Fin 54) (Fin 47) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 14
  | 1, 1 => 13
  | 2, 1 => 1
  | 2, 2 => 12
  | 3, 2 => 2
  | 3, 3 => 11
  | 4, 3 => 3
  | 4, 4 => 10
  | 5, 4 => 4
  | 5, 5 => 9
  | 6, 5 => 5
  | 6, 6 => 8
  | 7, 6 => 6
  | 7, 7 => 14
  | 8, 8 => 12
  | 9, 8 => 2
  | 9, 9 => 11
  | 10, 9 => 2
  | 10, 10 => 10
  | 11, 10 => 3
  | 11, 11 => 9
  | 12, 11 => 4
  | 12, 12 => 8
  | 13, 12 => 5
  | 13, 13 => 7
  | 14, 13 => 6
  | 15, 9 => 1
  | 15, 14 => 10
  | 16, 10 => 1
  | 16, 14 => 4
  | 16, 15 => 9
  | 17, 11 => 1
  | 17, 15 => 3
  | 17, 16 => 8
  | 18, 12 => 1
  | 18, 16 => 4
  | 18, 17 => 7
  | 19, 13 => 1
  | 19, 17 => 5
  | 19, 18 => 12
  | 20, 15 => 2
  | 20, 19 => 8
  | 21, 16 => 2
  | 21, 19 => 6
  | 21, 20 => 7
  | 22, 17 => 2
  | 22, 20 => 4
  | 22, 21 => 6
  | 23, 18 => 2
  | 23, 21 => 5
  | 24, 20 => 3
  | 24, 22 => 6
  | 25, 21 => 3
  | 25, 22 => 8
  | 25, 23 => 10
  | 26, 23 => 4
  | 27, 24 => 11
  | 28, 24 => 3
  | 28, 25 => 10
  | 29, 25 => 2
  | 29, 26 => 9
  | 30, 26 => 3
  | 30, 27 => 8
  | 31, 27 => 4
  | 31, 28 => 7
  | 32, 28 => 5
  | 32, 29 => 12
  | 33, 25 => 2
  | 33, 30 => 9
  | 34, 26 => 2
  | 34, 30 => 4
  | 34, 31 => 8
  | 35, 27 => 2
  | 35, 31 => 3
  | 35, 32 => 7
  | 36, 28 => 2
  | 36, 32 => 4
  | 36, 33 => 6
  | 37, 29 => 2
  | 37, 33 => 5
  | 38, 31 => 2
  | 38, 34 => 7
  | 39, 32 => 2
  | 39, 34 => 6
  | 39, 35 => 6
  | 40, 33 => 2
  | 40, 35 => 4
  | 40, 36 => 10
  | 41, 35 => 3
  | 41, 37 => 5
  | 42, 36 => 3
  | 42, 37 => 8
  | 43, 30 => 1
  | 43, 38 => 8
  | 44, 31 => 1
  | 44, 38 => 6
  | 44, 39 => 7
  | 45, 32 => 1
  | 45, 39 => 3
  | 45, 40 => 6
  | 46, 33 => 1
  | 46, 40 => 4
  | 46, 41 => 10
  | 47, 34 => 1
  | 47, 39 => 4
  | 47, 42 => 6
  | 48, 35 => 1
  | 48, 40 => 4
  | 48, 42 => 6
  | 48, 43 => 5
  | 49, 36 => 1
  | 49, 41 => 4
  | 49, 43 => 4
  | 50, 37 => 1
  | 50, 43 => 3
  | 50, 44 => 12
  | 51, 42 => 2
  | 51, 45 => 5
  | 52, 43 => 2
  | 52, 45 => 9
  | 52, 46 => 8
  | 53, 44 => 2
  | 53, 46 => 6
  | _, _ => 0

theorem retainedRaise_4_14_entries :
    (∀ (i : Fin 54) (j : Fin 47), retainedRaise_4_14C i j=
      tupleLowerConstant 14 (retainedParts_4_15.get i) (retainedParts_4_14.get j)) ∧
    (∀ (i : Fin 54) (j : Fin 47), retainedRaise_4_14S i j=
      tupleLowerSlope 14 (retainedParts_4_15.get i) (retainedParts_4_14.get j)) := by
  unfold retainedRaise_4_14C retainedRaise_4_14S
  decide +kernel

theorem retainedRaise_4_14_physical (Q : ℕ) (hd : 15≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_14 retainedEnum_4_15=
      retainedRaise_4_14C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_14S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_14, retainedEnum_4_15]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_15 retainedParts_4_15_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_14 retainedParts_4_14_complete j]
    exact retainedRaise_4_14_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_14, retainedEnum_4_15]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_15 retainedParts_4_15_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_14 retainedParts_4_14_complete j]
    exact retainedRaise_4_14_entries.2 i j

def retainedRaise_4_15C : Matrix (Fin 64) (Fin 54) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 3, 3 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 5, 4 => 1
  | 5, 5 => 1
  | 6, 5 => 1
  | 6, 6 => 1
  | 7, 6 => 1
  | 7, 7 => 1
  | 8, 7 => 1
  | 9, 1 => 2
  | 9, 8 => 1
  | 10, 2 => 2
  | 10, 8 => 2
  | 10, 9 => 1
  | 11, 3 => 2
  | 11, 9 => 1
  | 11, 10 => 1
  | 12, 4 => 2
  | 12, 10 => 1
  | 12, 11 => 1
  | 13, 5 => 2
  | 13, 11 => 1
  | 13, 12 => 1
  | 14, 6 => 2
  | 14, 12 => 1
  | 14, 13 => 1
  | 15, 7 => 2
  | 15, 13 => 1
  | 15, 14 => 2
  | 16, 9 => 1
  | 16, 15 => 1
  | 17, 10 => 1
  | 17, 15 => 2
  | 17, 16 => 1
  | 18, 11 => 1
  | 18, 16 => 1
  | 18, 17 => 1
  | 19, 12 => 1
  | 19, 17 => 1
  | 19, 18 => 1
  | 20, 13 => 1
  | 20, 18 => 1
  | 20, 19 => 1
  | 21, 14 => 1
  | 21, 19 => 1
  | 22, 16 => 1
  | 22, 20 => 1
  | 23, 17 => 1
  | 23, 20 => 2
  | 23, 21 => 1
  | 24, 18 => 1
  | 24, 21 => 1
  | 24, 22 => 1
  | 25, 19 => 1
  | 25, 22 => 1
  | 25, 23 => 2
  | 26, 21 => 1
  | 26, 24 => 1
  | 27, 22 => 1
  | 27, 24 => 2
  | 27, 25 => 1
  | 28, 23 => 1
  | 28, 25 => 1
  | 29, 25 => 1
  | 29, 26 => 3
  | 30, 8 => 1
  | 30, 27 => 1
  | 31, 9 => 1
  | 31, 27 => 3
  | 31, 28 => 1
  | 32, 10 => 1
  | 32, 28 => 1
  | 32, 29 => 1
  | 33, 11 => 1
  | 33, 29 => 1
  | 33, 30 => 1
  | 34, 12 => 1
  | 34, 30 => 1
  | 34, 31 => 1
  | 35, 13 => 1
  | 35, 31 => 1
  | 35, 32 => 1
  | 36, 14 => 1
  | 36, 32 => 1
  | 37, 15 => 1
  | 37, 28 => 2
  | 37, 33 => 1
  | 38, 16 => 1
  | 38, 29 => 2
  | 38, 33 => 2
  | 38, 34 => 1
  | 39, 17 => 1
  | 39, 30 => 2
  | 39, 34 => 1
  | 39, 35 => 1
  | 40, 18 => 1
  | 40, 31 => 2
  | 40, 35 => 1
  | 40, 36 => 1
  | 41, 19 => 1
  | 41, 32 => 2
  | 41, 36 => 1
  | 41, 37 => 2
  | 42, 20 => 1
  | 42, 34 => 1
  | 42, 38 => 1
  | 43, 21 => 1
  | 43, 35 => 1
  | 43, 38 => 2
  | 43, 39 => 1
  | 44, 22 => 1
  | 44, 36 => 1
  | 44, 39 => 1
  | 44, 40 => 1
  | 45, 23 => 1
  | 45, 37 => 1
  | 45, 40 => 1
  | 46, 24 => 1
  | 46, 39 => 1
  | 46, 41 => 1
  | 47, 25 => 1
  | 47, 40 => 1
  | 47, 41 => 2
  | 47, 42 => 2
  | 48, 26 => 1
  | 48, 42 => 1
  | 49, 33 => 1
  | 49, 43 => 1
  | 50, 34 => 1
  | 50, 43 => 3
  | 50, 44 => 1
  | 51, 35 => 1
  | 51, 44 => 1
  | 51, 45 => 1
  | 52, 36 => 1
  | 52, 45 => 1
  | 52, 46 => 1
  | 53, 37 => 1
  | 53, 46 => 1
  | 54, 38 => 1
  | 54, 44 => 2
  | 54, 47 => 1
  | 55, 39 => 1
  | 55, 45 => 2
  | 55, 47 => 2
  | 55, 48 => 1
  | 56, 40 => 1
  | 56, 46 => 2
  | 56, 48 => 1
  | 56, 49 => 2
  | 57, 41 => 1
  | 57, 48 => 1
  | 57, 50 => 1
  | 58, 42 => 1
  | 58, 49 => 1
  | 58, 50 => 2
  | 59, 47 => 1
  | 59, 51 => 1
  | 60, 48 => 1
  | 60, 51 => 3
  | 60, 52 => 1
  | 61, 49 => 1
  | 61, 52 => 1
  | 62, 50 => 1
  | 62, 52 => 2
  | 62, 53 => 3
  | 63, 53 => 1
  | _, _ => 0

def retainedRaise_4_15S : Matrix (Fin 64) (Fin 54) ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 15
  | 1, 1 => 14
  | 2, 1 => 1
  | 2, 2 => 13
  | 3, 2 => 2
  | 3, 3 => 12
  | 4, 3 => 3
  | 4, 4 => 11
  | 5, 4 => 4
  | 5, 5 => 10
  | 6, 5 => 5
  | 6, 6 => 9
  | 7, 6 => 6
  | 7, 7 => 8
  | 8, 7 => 7
  | 9, 8 => 13
  | 10, 8 => 2
  | 10, 9 => 12
  | 11, 9 => 2
  | 11, 10 => 11
  | 12, 10 => 3
  | 12, 11 => 10
  | 13, 11 => 4
  | 13, 12 => 9
  | 14, 12 => 5
  | 14, 13 => 8
  | 15, 13 => 6
  | 15, 14 => 14
  | 16, 9 => 1
  | 16, 15 => 11
  | 17, 10 => 1
  | 17, 15 => 4
  | 17, 16 => 10
  | 18, 11 => 1
  | 18, 16 => 3
  | 18, 17 => 9
  | 19, 12 => 1
  | 19, 17 => 4
  | 19, 18 => 8
  | 20, 13 => 1
  | 20, 18 => 5
  | 20, 19 => 7
  | 21, 14 => 1
  | 21, 19 => 6
  | 22, 16 => 2
  | 22, 20 => 9
  | 23, 17 => 2
  | 23, 20 => 6
  | 23, 21 => 8
  | 24, 18 => 2
  | 24, 21 => 4
  | 24, 22 => 7
  | 25, 19 => 2
  | 25, 22 => 5
  | 25, 23 => 12
  | 26, 21 => 3
  | 26, 24 => 7
  | 27, 22 => 3
  | 27, 24 => 8
  | 27, 25 => 6
  | 28, 23 => 3
  | 28, 25 => 5
  | 29, 25 => 4
  | 29, 26 => 15
  | 30, 27 => 12
  | 31, 27 => 3
  | 31, 28 => 11
  | 32, 28 => 2
  | 32, 29 => 10
  | 33, 29 => 3
  | 33, 30 => 9
  | 34, 30 => 4
  | 34, 31 => 8
  | 35, 31 => 5
  | 35, 32 => 7
  | 36, 32 => 6
  | 37, 28 => 2
  | 37, 33 => 10
  | 38, 29 => 2
  | 38, 33 => 4
  | 38, 34 => 9
  | 39, 30 => 2
  | 39, 34 => 3
  | 39, 35 => 8
  | 40, 31 => 2
  | 40, 35 => 4
  | 40, 36 => 7
  | 41, 32 => 2
  | 41, 36 => 5
  | 41, 37 => 12
  | 42, 34 => 2
  | 42, 38 => 8
  | 43, 35 => 2
  | 43, 38 => 6
  | 43, 39 => 7
  | 44, 36 => 2
  | 44, 39 => 4
  | 44, 40 => 6
  | 45, 37 => 2
  | 45, 40 => 5
  | 46, 39 => 3
  | 46, 41 => 6
  | 47, 40 => 3
  | 47, 41 => 8
  | 47, 42 => 10
  | 48, 42 => 4
  | 49, 33 => 1
  | 49, 43 => 9
  | 50, 34 => 1
  | 50, 43 => 6
  | 50, 44 => 8
  | 51, 35 => 1
  | 51, 44 => 3
  | 51, 45 => 7
  | 52, 36 => 1
  | 52, 45 => 4
  | 52, 46 => 6
  | 53, 37 => 1
  | 53, 46 => 5
  | 54, 38 => 1
  | 54, 44 => 4
  | 54, 47 => 7
  | 55, 39 => 1
  | 55, 45 => 4
  | 55, 47 => 6
  | 55, 48 => 6
  | 56, 40 => 1
  | 56, 46 => 4
  | 56, 48 => 4
  | 56, 49 => 10
  | 57, 41 => 1
  | 57, 48 => 3
  | 57, 50 => 5
  | 58, 42 => 1
  | 58, 49 => 3
  | 58, 50 => 8
  | 59, 47 => 2
  | 59, 51 => 6
  | 60, 48 => 2
  | 60, 51 => 9
  | 60, 52 => 5
  | 61, 49 => 2
  | 61, 52 => 4
  | 62, 50 => 2
  | 62, 52 => 6
  | 62, 53 => 12
  | 63, 53 => 3
  | _, _ => 0

theorem retainedRaise_4_15_entries :
    (∀ (i : Fin 64) (j : Fin 54), retainedRaise_4_15C i j=
      tupleLowerConstant 15 (retainedParts_4_16.get i) (retainedParts_4_15.get j)) ∧
    (∀ (i : Fin 64) (j : Fin 54), retainedRaise_4_15S i j=
      tupleLowerSlope 15 (retainedParts_4_16.get i) (retainedParts_4_15.get j)) := by
  unfold retainedRaise_4_15C retainedRaise_4_15S
  decide +kernel

theorem retainedRaise_4_15_physical (Q : ℕ) (hd : 16≤Q) :
    indexedVerifierRaiseMatrix hd retainedEnum_4_15 retainedEnum_4_16=
      retainedRaise_4_15C.map (Nat.castRingHom ℂ)-(Q : ℂ)⁻¹ • retainedRaise_4_15S.map (Nat.castRingHom ℂ) := by
  apply indexedVerifierRaiseMatrix_eq_arrays (by omega) hd
  · intro i j
    simp only [retainedEnum_4_15, retainedEnum_4_16]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_16 retainedParts_4_16_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_15 retainedParts_4_15_complete j]
    exact retainedRaise_4_15_entries.1 i j
  · intro i j
    simp only [retainedEnum_4_15, retainedEnum_4_16]
    rw [sortedEnumerationOfTable_ofFn retainedParts_4_16 retainedParts_4_16_complete i,
      sortedEnumerationOfTable_ofFn retainedParts_4_15 retainedParts_4_15_complete j]
    exact retainedRaise_4_15_entries.2 i j

end BosonicLaughlin

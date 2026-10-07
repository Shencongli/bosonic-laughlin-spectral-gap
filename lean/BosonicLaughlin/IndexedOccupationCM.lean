import BosonicLaughlin.SortedCMCoefficient

/-! A checked enumeration is a bijection, not merely a list of valid indices.
The interface accepts the original array order and transports it to the actual
occupation matrix without choosing a different basis order. -/
namespace BosonicLaughlin
noncomputable section

structure SortedTupleEnumeration (N d n : ℕ) where
  tuple : Fin n → SortedDegreeTuple N d
  injective : Function.Injective tuple
  surjective : Function.Surjective tuple

def SortedTupleEnumeration.equiv {N d n : ℕ} (e : SortedTupleEnumeration N d n) :
    Fin n ≃ SortedDegreeTuple N d := Equiv.ofBijective e.tuple ⟨e.injective,e.surjective⟩

def SortedTupleEnumeration.occupationEquiv {Q N d n : ℕ}
    (e : SortedTupleEnumeration N d n) (hd : d≤Q) : Fin n ≃ WeightOccupation Q N d :=
  e.equiv.trans (sortedDegreeOccupationEquiv hd)

def SortedTupleEnumeration.ofRaw {N d n : ℕ} (parts : Fin n → Fin N → ℕ)
    (hmon : ∀ i, Monotone (parts i)) (hsum : ∀ i, ∑ j, parts i j=d)
    (hinj : Function.Injective parts)
    (hcomplete : ∀ a : Fin N → ℕ, Monotone a → (∑ j, a j)=d → ∃ i, parts i=a) :
    SortedTupleEnumeration N d n where
  tuple i := ⟨parts i,hmon i,hsum i⟩
  injective := by intro i j h; exact hinj (congrArg Subtype.val h)
  surjective := by
    intro a
    obtain ⟨i,hi⟩ := hcomplete a.val a.property.1 a.property.2
    exact ⟨i,Subtype.ext hi⟩

def indexedOccupationCMMatrix {Q N d rows cols : ℕ} (hd : d≤Q)
    (src : SortedTupleEnumeration N d cols)
    (dst : SortedTupleEnumeration N (d-1) rows) : Matrix (Fin rows) (Fin cols) ℂ :=
  fun i j => occupationCMBlockMatrix Q N d
    (dst.occupationEquiv (Nat.le_trans (Nat.sub_le _ _) hd) i) (src.occupationEquiv hd j)

theorem indexedOccupationCMMatrix_apply {Q N d rows cols : ℕ}
    (hd : d≤Q) (hpos : 0<d)
    (src : SortedTupleEnumeration N d cols)
    (dst : SortedTupleEnumeration N (d-1) rows) (i : Fin rows) (j : Fin cols) :
    indexedOccupationCMMatrix hd src dst i j =
      (tupleCMCoefficient d (List.ofFn (dst.tuple i).val)
        (List.ofFn (src.tuple j).val) : ℂ) := by
  exact (sortedCMCoefficient_eq_occupationCMBlockMatrix hd hpos (dst.tuple i) (src.tuple j)).symm

/-- Entrywise equality is an explicit certificate obligation; a frame checker
cannot silently assume that an external array is the actual CM matrix. -/
theorem indexedOccupationCMMatrix_eq_array {Q N d rows cols : ℕ}
    (hd : d≤Q) (hpos : 0<d)
    (src : SortedTupleEnumeration N d cols)
    (dst : SortedTupleEnumeration N (d-1) rows)
    (C : Matrix (Fin rows) (Fin cols) ℚ)
    (hC : ∀ i j, C i j = (tupleCMCoefficient d (List.ofFn (dst.tuple i).val)
      (List.ofFn (src.tuple j).val) : ℚ)) :
    indexedOccupationCMMatrix hd src dst = C.map (Rat.castHom ℂ) := by
  ext i j
  rw [indexedOccupationCMMatrix_apply hd hpos, Matrix.map_apply, hC]
  simp

end
end BosonicLaughlin

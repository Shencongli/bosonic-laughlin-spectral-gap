import BosonicLaughlin.AngularCommutators

/-! Descendants of a highest-weight vector under the actual auxiliary spin algebra. -/
namespace BosonicLaughlin
noncomputable section

theorem auxLower_power_succ {Q : ℕ} (φ : ThreeBodyAux Q) (n : ℕ) :
    (auxLowerLinear Q ^ (n+1)) φ = auxLower ((auxLowerLinear Q ^ n) φ) := by
  rw [pow_succ', Module.End.mul_apply]
  rfl

theorem auxRaise_lower {Q : ℕ} (φ : ThreeBodyAux Q) :
    auxRaise (auxLower φ) = auxLower (auxRaise φ) + auxWeight φ := by
  have h := auxRaise_lower_commutator φ
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem auxWeight_lower {Q : ℕ} (φ : ThreeBodyAux Q) :
    auxWeight (auxLower φ) = auxLower (auxWeight φ) + (-2 : ℂ) • auxLower φ := by
  have h := auxWeight_lower_commutator φ
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem auxWeight_lower_power {Q : ℕ} (φ : ThreeBodyAux Q) (w : ℂ)
    (hw : auxWeight φ = w • φ) (n : ℕ) :
    auxWeight ((auxLowerLinear Q ^ n) φ) =
      (w - 2*(n : ℂ)) • ((auxLowerLinear Q ^ n) φ) := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
    rw [auxLower_power_succ, auxWeight_lower, ih, auxLower_smul]
    push_cast
    module

/-- The exact ladder coefficient, with twice-spin weight `w`. -/
theorem auxRaise_lower_power {Q : ℕ} (φ : ThreeBodyAux Q) (w : ℂ)
    (he : auxRaise φ = 0) (hw : auxWeight φ = w • φ) (n : ℕ) :
    auxRaise ((auxLowerLinear Q ^ (n+1)) φ) =
      (((n+1 : ℕ) : ℂ) * (w - (n : ℂ))) • ((auxLowerLinear Q ^ n) φ) := by
  induction n with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_one,
      Nat.cast_zero, sub_zero, one_mul]
    change auxRaise (auxLower φ) = w • φ
    rw [auxRaise_lower, he, show auxLower (0 : ThreeBodyAux Q) = 0 from
      (auxLowerLinear Q).map_zero, zero_add, hw]
  | succ n ih =>
    rw [auxLower_power_succ φ (n+1), auxRaise_lower, ih, auxLower_smul,
      auxWeight_lower_power φ w hw (n+1), ← auxLower_power_succ]
    push_cast
    module

end
end BosonicLaughlin

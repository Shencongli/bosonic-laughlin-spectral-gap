import BosonicLaughlin.SwapEigenvalues

namespace BosonicLaughlin
noncomputable section

theorem recouplingRatio_succ_lt (Q z : ℕ) (hz : z < Q) :
    recouplingRatio Q (z+1) < recouplingRatio Q z := by
  have hd : (0 : ℝ) < ((2*Q-z : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2*Q-z by omega)
  have hs : ((Q-z : ℕ) : ℝ) / ((2*Q-z : ℕ) : ℝ) < 1 := by
    rw [div_lt_one hd]
    exact_mod_cast (show Q-z < 2*Q-z by omega)
  rw [recouplingRatio_succ]
  simpa using mul_lt_mul_of_pos_right hs (recouplingRatio_pos Q z (by omega))

theorem recouplingRatio_strict_decrease (Q a b : ℕ) (hab : a < b) (hb : b ≤ Q) :
    recouplingRatio Q b < recouplingRatio Q a := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases he : a = b
    · subst a
      exact recouplingRatio_succ_lt Q b (by omega)
    · exact lt_trans (recouplingRatio_succ_lt Q b (by omega))
        (ih (by omega) (by omega))

theorem recouplingEigenvalue_abs (Q z : ℕ) (hz : z ≤ Q) :
    |recouplingEigenvalue Q z| = recouplingRatio Q z := by
  rw [recouplingEigenvalue, abs_mul, abs_pow,
    abs_of_pos (recouplingRatio_pos Q z hz)]
  norm_num

/-- Distinct z labels have distinct eigenvalues, including the alternating signs. -/
theorem recouplingEigenvalue_injective (Q : ℕ) :
    Function.Injective (fun z : Fin (Q+1) => recouplingEigenvalue Q z.val) := by
  intro a b he
  have hf := congrArg abs he
  rw [recouplingEigenvalue_abs Q a.val (by omega),
    recouplingEigenvalue_abs Q b.val (by omega)] at hf
  apply Fin.ext
  rcases lt_trichotomy a.val b.val with hab | hab | hab
  · have hlt := recouplingRatio_strict_decrease Q a.val b.val hab (by omega)
    exact False.elim ((ne_of_lt hlt) hf.symm)
  · exact hab
  · have hlt := recouplingRatio_strict_decrease Q b.val a.val hab (by omega)
    exact False.elim ((ne_of_lt hlt) hf)

end
end BosonicLaughlin

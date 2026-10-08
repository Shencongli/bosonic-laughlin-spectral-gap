import BosonicLaughlin.TensorSpin

/-! Physical lowering descendants and their complete Gram normalization.
The highest weight m is twice the total spin. At level n the squared ladder
factor is n! m!/(m-n)!; no normalization of the initial vector is assumed. -/
namespace BosonicLaughlin
noncomputable section

def tensorDescendant {Q N : ℕ} (ψ : State Q N) (n : ℕ) : State Q N :=
  (tensorLowerLinear Q N ^ n) ψ

theorem tensorDescendant_zero {Q N : ℕ} (ψ : State Q N) : tensorDescendant ψ 0=ψ := rfl

theorem tensorDescendant_succ {Q N : ℕ} (ψ : State Q N) (n : ℕ) :
    tensorDescendant ψ (n+1)=tensorLower (tensorDescendant ψ n) := by
  simp [tensorDescendant, pow_succ', Module.End.mul_apply, tensorLower]

theorem tensorWeight_descendant {Q N : ℕ} (ψ : State Q N) (w : ℂ)
    (hw : tensorWeight ψ=w • ψ) (n : ℕ) :
    tensorWeight (tensorDescendant ψ n)=(w-2*(n : ℂ)) • tensorDescendant ψ n := by
  induction n with
  | zero => simpa [tensorDescendant_zero] using hw
  | succ n ih =>
    have hc := sub_eq_iff_eq_add.mp (tensorWeight_lower_commutator (tensorDescendant ψ n))
    rw [tensorDescendant_succ, hc, ih]
    change (-2 : ℂ) • tensorLower (tensorDescendant ψ n) +
      tensorLowerLinear Q N ((w-2*(n : ℂ)) • tensorDescendant ψ n) = _
    rw [map_smul]
    change (-2 : ℂ) • tensorLower (tensorDescendant ψ n) +
      (w-2*(n : ℂ)) • tensorLower (tensorDescendant ψ n) =
      (w-2*((n+1 : ℕ) : ℂ)) • tensorLower (tensorDescendant ψ n)
    push_cast
    module

theorem tensorRaise_descendant {Q N : ℕ} (ψ : State Q N) (w : ℂ)
    (he : tensorRaise ψ=0) (hw : tensorWeight ψ=w • ψ) (n : ℕ) :
    tensorRaise (tensorDescendant ψ (n+1)) =
      (((n+1 : ℕ) : ℂ)*(w-(n : ℂ))) • tensorDescendant ψ n := by
  induction n with
  | zero =>
    rw [tensorDescendant_succ, tensorDescendant_zero]
    have hc := sub_eq_iff_eq_add.mp (tensorRaise_lower_commutator ψ)
    rw [hc, he, hw]
    simp [tensorLower, map_zero]
  | succ n ih =>
    rw [tensorDescendant_succ ψ (n+1)]
    have hc := sub_eq_iff_eq_add.mp (tensorRaise_lower_commutator (tensorDescendant ψ (n+1)))
    rw [hc, ih, tensorWeight_descendant ψ w hw (n+1)]
    change _ + tensorLowerLinear Q N (_ • tensorDescendant ψ n) = _
    rw [map_smul]
    rw [tensorDescendant_succ ψ n]
    change (w-2*((n+1 : ℕ) : ℂ)) • tensorLower (tensorDescendant ψ n) +
      (((n+1 : ℕ) : ℂ)*(w-(n : ℂ))) • tensorLower (tensorDescendant ψ n) =
      (((n+1+1 : ℕ) : ℂ)*(w-((n+1 : ℕ) : ℂ))) • tensorLower (tensorDescendant ψ n)
    push_cast
    module

def descendantFactor (m n : ℕ) : ℕ := n.factorial * m.descFactorial n

theorem descendantFactor_zero (m : ℕ) : descendantFactor m 0=1 := by simp [descendantFactor]

theorem descendantFactor_succ (m n : ℕ) :
    descendantFactor m (n+1)=(n+1)*(m-n)*descendantFactor m n := by
  simp [descendantFactor, Nat.factorial_succ, Nat.descFactorial_succ]
  ring

theorem descendantFactor_pos {m n : ℕ} (hn : n≤m) : 0<descendantFactor m n :=
  Nat.mul_pos (Nat.factorial_pos n) (Nat.descFactorial_pos.mpr hn)

theorem descendantFactor_factorial {m n : ℕ} (hn : n≤m) :
    (m-n).factorial * descendantFactor m n = n.factorial * m.factorial := by
  unfold descendantFactor
  rw [Nat.mul_left_comm, Nat.factorial_mul_descFactorial hn]

theorem tensorDescendant_inner {Q N : ℕ} (ψ φ : State Q N) (m : ℕ)
    (hE : tensorRaise φ=0) (hW : tensorWeight φ=(m : ℂ) • φ)
    (n : ℕ) (hn : n≤m) :
    inner (tensorDescendant ψ n) (tensorDescendant φ n)=
      (descendantFactor m n : ℂ)*inner ψ φ := by
  induction n with
  | zero => simp [tensorDescendant_zero, descendantFactor_zero]
  | succ n ih =>
    rw [tensorDescendant_succ ψ n, ← tensorRaise_adjoint,
      tensorRaise_descendant φ (m : ℂ) hE hW n, stateInner_smul_right, ih (by omega),
      descendantFactor_succ, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : n≤m)]
    ring

theorem tensorDescendant_normSq {Q N : ℕ} (ψ : State Q N) (m : ℕ)
    (hE : tensorRaise ψ=0) (hW : tensorWeight ψ=(m : ℂ) • ψ)
    (n : ℕ) (hn : n≤m) : normSq (tensorDescendant ψ n)=
      (descendantFactor m n : ℝ)*normSq ψ := by
  simpa [normSq, Complex.mul_re] using congrArg Complex.re (tensorDescendant_inner ψ ψ m hE hW n hn)

theorem tensorDescendant_endpoint {Q N : ℕ} (ψ : State Q N) (m : ℕ)
    (hE : tensorRaise ψ=0) (hW : tensorWeight ψ=(m : ℂ) • ψ) :
    tensorDescendant ψ (m+1)=0 := by
  apply (stateNormSq_zero_iff _).mp
  have hi : inner (tensorDescendant ψ (m+1)) (tensorDescendant ψ (m+1))=0 := by
    rw [tensorDescendant_succ ψ m, ← tensorRaise_adjoint]
    rw [← tensorDescendant_succ, tensorRaise_descendant ψ (m : ℂ) hE hW m]
    simp [inner]
  exact congrArg Complex.re hi

theorem tensorDescendant_nonzero {Q N : ℕ} (ψ : State Q N) (m : ℕ)
    (hψ : ψ≠0) (hE : tensorRaise ψ=0) (hW : tensorWeight ψ=(m : ℂ) • ψ)
    (n : ℕ) (hn : n≤m) : tensorDescendant ψ n≠0 := by
  intro hz
  have hh := tensorDescendant_normSq ψ m hE hW n hn
  rw [(stateNormSq_zero_iff _).mpr hz] at hh
  have hp : (descendantFactor m n : ℝ)≠0 := by
    exact_mod_cast (descendantFactor_pos hn).ne'
  exact hψ ((stateNormSq_zero_iff ψ).mp ((mul_eq_zero.mp hh.symm).resolve_left hp))

theorem tensorDescendant_isBosonic {Q N : ℕ} (ψ : State Q N) (hψ : IsBosonic ψ) (n : ℕ) :
    IsBosonic (tensorDescendant ψ n) := by
  induction n with
  | zero => exact hψ
  | succ n ih => rw [tensorDescendant_succ]; exact tensorLower_isBosonic _ ih

theorem tensorDescendant_supported {Q N d : ℕ} (ψ : State Q N)
    (hψ : WeightSupported d ψ) (n : ℕ) : WeightSupported (d+n) (tensorDescendant ψ n) := by
  induction n with
  | zero => simpa [tensorDescendant_zero] using hψ
  | succ n ih => simpa [tensorDescendant_succ, Nat.add_assoc] using tensorLower_weightSupported (d+n) _ ih

theorem stateInner_of_disjoint_weights {Q N d e : ℕ} (ψ φ : State Q N)
    (hψ : WeightSupported d ψ) (hφ : WeightSupported e φ) (hde : d≠e) : inner ψ φ=0 := by
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : configurationWeight a=d
  · rw [hφ a (by omega), mul_zero]
  · rw [hψ a ha, star_zero, zero_mul]

def normalizedTensorDescendant {Q N : ℕ} (ψ : State Q N) (m n : ℕ) : State Q N :=
  (((Real.sqrt (descendantFactor m n : ℝ))⁻¹ : ℝ) : ℂ) • tensorDescendant ψ n

theorem normalizedTensorDescendant_inner {Q N : ℕ} (ψ φ : State Q N) (m : ℕ)
    (hE : tensorRaise φ=0) (hW : tensorWeight φ=(m : ℂ) • φ)
    (n : ℕ) (hn : n≤m) :
    inner (normalizedTensorDescendant ψ m n) (normalizedTensorDescendant φ m n)=inner ψ φ := by
  rw [normalizedTensorDescendant, normalizedTensorDescendant, stateInner_real_smul_both,
    tensorDescendant_inner ψ φ m hE hW n hn]
  have hp : (0 : ℝ)<descendantFactor m n := by exact_mod_cast descendantFactor_pos hn
  have hs : (Real.sqrt (descendantFactor m n : ℝ))⁻¹ ^ 2 * (descendantFactor m n : ℝ)=1 := by
    rw [inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  have hc : (((Real.sqrt (descendantFactor m n : ℝ))⁻¹ ^ 2 : ℝ) : ℂ) *
      (descendantFactor m n : ℂ)=1 := by exact_mod_cast hs
  rw [← mul_assoc, hc, one_mul]

theorem normalizedTensorDescendant_orthogonal {Q N d : ℕ} (ψ φ : State Q N)
    (hψ : WeightSupported d ψ) (hφ : WeightSupported d φ) (m n k : ℕ) (hnk : n≠k) :
    inner (normalizedTensorDescendant ψ m n) (normalizedTensorDescendant φ m k)=0 := by
  rw [normalizedTensorDescendant, normalizedTensorDescendant, stateInner_smul_left, stateInner_smul_right,
    stateInner_of_disjoint_weights _ _ (tensorDescendant_supported ψ hψ n)
      (tensorDescendant_supported φ hφ k) (by omega), mul_zero, mul_zero]

end
end BosonicLaughlin

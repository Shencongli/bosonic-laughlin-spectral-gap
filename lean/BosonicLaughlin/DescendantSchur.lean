import BosonicLaughlin.VerifierDescendants

/-! Finite Schur reduction on a physical highest-weight block.
The sum runs over the spin index and retains every multiplicity matrix
entry. Identification with a group average requires the explicit commutation
and matrix-valued partial-trace premises below; no Haar integral is defined. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem tensorDescendant_commuting_form {Q N : ℕ}
    (A : State Q N →ₗ[ℂ] State Q N)
    (hA : ∀ v, tensorRaise (A v)=A (tensorRaise v))
    (ψ φ : State Q N) (m : ℕ)
    (hE : tensorRaise φ=0) (hW : tensorWeight φ=(m : ℂ) • φ)
    (n : ℕ) (hn : n≤m) :
    inner (tensorDescendant ψ n) (A (tensorDescendant φ n))=
      (descendantFactor m n : ℂ)*inner ψ (A φ) := by
  induction n with
  | zero => simp [tensorDescendant_zero, descendantFactor_zero]
  | succ n ih =>
    rw [tensorDescendant_succ ψ n, ← tensorRaise_adjoint, hA,
      tensorRaise_descendant φ (m : ℂ) hE hW n, map_smul,
      stateInner_smul_right, ih (by omega), descendantFactor_succ,
      Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : n≤m)]
    ring

theorem normalizedDescendant_commuting_form {Q N : ℕ}
    (A : State Q N →ₗ[ℂ] State Q N)
    (hA : ∀ v, tensorRaise (A v)=A (tensorRaise v))
    (ψ φ : State Q N) (m : ℕ)
    (hE : tensorRaise φ=0) (hW : tensorWeight φ=(m : ℂ) • φ)
    (n : ℕ) (hn : n≤m) :
    inner (normalizedTensorDescendant ψ m n) (A (normalizedTensorDescendant φ m n))=
      inner ψ (A φ) := by
  rw [normalizedTensorDescendant, normalizedTensorDescendant, map_smul,
    stateInner_real_smul_both, tensorDescendant_commuting_form A hA ψ φ m hE hW n hn]
  have hp : (0 : ℝ)<descendantFactor m n := by exact_mod_cast descendantFactor_pos hn
  have hc : (((Real.sqrt (descendantFactor m n : ℝ))⁻¹ ^ 2 : ℝ) : ℂ) *
      (descendantFactor m n : ℂ)=1 := by
    norm_cast
    rw [inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  rw [← mul_assoc, hc, one_mul]

/-- Partial trace over one spin ladder, with the two multiplicity vectors free. -/
def descendantPartialTrace {Q N : ℕ} (m : ℕ)
    (A : State Q N →ₗ[ℂ] State Q N) (ψ φ : State Q N) : ℂ :=
  ∑ n : Fin (m+1), inner (normalizedTensorDescendant ψ m n.val)
    (A (normalizedTensorDescendant φ m n.val))

def descendantSchurForm {Q N : ℕ} (m : ℕ)
    (A : State Q N →ₗ[ℂ] State Q N) (ψ φ : State Q N) : ℂ :=
  ((m+1 : ℕ) : ℂ)⁻¹ * descendantPartialTrace m A ψ φ

theorem descendantPartialTrace_commuting {Q N : ℕ}
    (A : State Q N →ₗ[ℂ] State Q N)
    (hA : ∀ v, tensorRaise (A v)=A (tensorRaise v))
    (ψ φ : State Q N) (m : ℕ)
    (hE : tensorRaise φ=0) (hW : tensorWeight φ=(m : ℂ) • φ) :
    descendantPartialTrace m A ψ φ=((m+1 : ℕ) : ℂ)*inner ψ (A φ) := by
  unfold descendantPartialTrace
  have heq (n : Fin (m+1)) := normalizedDescendant_commuting_form A hA ψ φ m hE hW n.val (by omega)
  simp_rw [heq]
  simp

theorem descendantSchurForm_commuting {Q N : ℕ}
    (A : State Q N →ₗ[ℂ] State Q N)
    (hA : ∀ v, tensorRaise (A v)=A (tensorRaise v))
    (ψ φ : State Q N) (m : ℕ)
    (hE : tensorRaise φ=0) (hW : tensorWeight φ=(m : ℂ) • φ) :
    descendantSchurForm m A ψ φ=inner ψ (A φ) := by
  rw [descendantSchurForm, descendantPartialTrace_commuting A hA ψ φ m hE hW,
    ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero m), one_mul]

/-- A conditional identification, with the matrix-valued trace hypothesis
explicit. A single scalar trace over the full multiplicity space is insufficient. -/
theorem schurForm_of_commuting_partialTrace {Q N : ℕ}
    (A B : State Q N →ₗ[ℂ] State Q N)
    (hB : ∀ v, tensorRaise (B v)=B (tensorRaise v))
    (ψ φ : State Q N) (m : ℕ)
    (hE : tensorRaise φ=0) (hW : tensorWeight φ=(m : ℂ) • φ)
    (htrace : descendantPartialTrace m B ψ φ=descendantPartialTrace m A ψ φ) :
    inner ψ (B φ)=descendantSchurForm m A ψ φ := by
  rw [← descendantSchurForm_commuting B hB ψ φ m hE hW]
  exact congrArg (((m+1 : ℕ) : ℂ)⁻¹ * ·) htrace

def descendantSchurMatrix {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d)
    (A : State Q N →ₗ[ℂ] State Q N) : Matrix (Fin k) (Fin k) ℂ :=
  (((N*Q-2*d+1 : ℕ) : ℂ)⁻¹) •
    ∑ n : Fin (N*Q-2*d+1), physicalFormMatrix (normalizedDescendantFrame E n.val) A

theorem descendantSchurMatrix_apply {Q N d k : ℕ}
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d)
    (A : State Q N →ₗ[ℂ] State Q N) (i j : Fin k) :
    descendantSchurMatrix E A i j=descendantSchurForm (N*Q-2*d) A
      (highestWeightPhysicalFrame E (Pi.single i 1))
      (highestWeightPhysicalFrame E (Pi.single j 1)) := by
  simp [descendantSchurMatrix, descendantSchurForm, descendantPartialTrace,
    Matrix.sum_apply, physicalFormMatrix_apply, normalizedDescendantFrame_apply]

theorem highestWeightPhysicalFrame_weight {Q N d k : ℕ} (hd : 2*d≤N*Q)
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d) (c : Fin k → ℂ) :
    tensorWeight (highestWeightPhysicalFrame E c)=
      ((N*Q-2*d : ℕ) : ℂ) • highestWeightPhysicalFrame E c := by
  simpa only [Nat.cast_sub hd, Nat.cast_mul, Nat.cast_ofNat] using
    tensorWeight_of_supported _ (highestWeightPhysicalFrame_supported E c)

theorem descendantSchurMatrix_commuting {Q N d k : ℕ} (hd : 2*d≤N*Q)
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d)
    (A : State Q N →ₗ[ℂ] State Q N)
    (hA : ∀ v, tensorRaise (A v)=A (tensorRaise v)) :
    descendantSchurMatrix E A=physicalFormMatrix (highestWeightPhysicalFrame E) A := by
  ext i j
  rw [descendantSchurMatrix_apply, physicalFormMatrix_apply]
  exact descendantSchurForm_commuting A hA _ _ _
    (highestWeightPhysicalFrame_raise E _) (highestWeightPhysicalFrame_weight hd E _)

theorem schurMatrix_of_commuting_partialTrace {Q N d k : ℕ} (hd : 2*d≤N*Q)
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d)
    (A B : State Q N →ₗ[ℂ] State Q N)
    (hB : ∀ v, tensorRaise (B v)=B (tensorRaise v))
    (htrace : ∀ i j : Fin k, descendantPartialTrace (N*Q-2*d) B
        (highestWeightPhysicalFrame E (Pi.single i 1))
        (highestWeightPhysicalFrame E (Pi.single j 1))=
      descendantPartialTrace (N*Q-2*d) A
        (highestWeightPhysicalFrame E (Pi.single i 1))
        (highestWeightPhysicalFrame E (Pi.single j 1))) :
    physicalFormMatrix (highestWeightPhysicalFrame E) B=descendantSchurMatrix E A := by
  ext i j
  rw [physicalFormMatrix_apply, descendantSchurMatrix_apply]
  exact schurForm_of_commuting_partialTrace A B hB _ _ _
    (highestWeightPhysicalFrame_raise E _) (highestWeightPhysicalFrame_weight hd E _) (htrace i j)

theorem certificateSchurForm_verifier {Q N d : ℕ} (hQ : 0 < Q) (hd : 2*d≤N*Q)
    (A : State Q N →ₗ[ℂ] State Q N) (c e : WeightOccupationState Q N d) :
    descendantSchurForm (N*Q-2*d) A (certificateWeightCoordinates Q N d c)
      (certificateWeightCoordinates Q N d e)=
      (((N*Q-2*d+1 : ℕ) : ℂ)⁻¹) * ∑ n : Fin (N*Q-2*d+1),
        ((verifierDescendantNorm Q N d n.val : ℂ)⁻¹)*
          inner (certificateWeightCoordinates Q N (d+n.val) (verifierDescendant Q N d n.val c))
            (A (certificateWeightCoordinates Q N (d+n.val) (verifierDescendant Q N d n.val e))) := by
  unfold descendantSchurForm descendantPartialTrace
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact verifierDescendant_normalized_form hQ hd c e n.val (by omega) A

/-- The prefactor used by the verifier after x=1/Q, including its 2Q+1
coherent-state normalization. This is a scalar identity, not an integral theorem. -/
theorem verifierSchur_prefactor {Q N d : ℕ} (hQ : 0 < Q) (hd : 2*d≤N*Q) :
    ((2 : ℂ)+(Q : ℂ)⁻¹)/((N : ℂ)+(Q : ℂ)⁻¹*(1-2*(d : ℂ)))=
      ((2*Q+1 : ℕ) : ℂ)/((N*Q-2*d+1 : ℕ) : ℂ) := by
  have hq : (Q : ℂ)≠0 := by exact_mod_cast hQ.ne'
  simp only [Nat.cast_add, Nat.cast_sub hd]
  push_cast
  field_simp
  ring

theorem tensorWeight_adjoint {Q N : ℕ} (ψ φ : State Q N) :
    inner (tensorWeight ψ) φ=inner ψ (tensorWeight φ) := by
  unfold inner
  apply Finset.sum_congr rfl
  intro a _
  simp only [tensorWeight_apply, star_mul, star_sub, star_natCast, star_ofNat]
  ring

theorem stateInner_distinct_weight_eigenvalues {Q N : ℕ} (ψ φ : State Q N)
    (w z : ℝ) (hw : tensorWeight ψ=(w : ℂ) • ψ)
    (hz : tensorWeight φ=(z : ℂ) • φ) (hwz : w≠z) : inner ψ φ=0 := by
  have h := tensorWeight_adjoint ψ φ
  rw [hw, hz, stateInner_smul_left, stateInner_smul_right, Complex.star_def,
    Complex.conj_ofReal] at h
  have hsub : ((w : ℂ)-(z : ℂ))*inner ψ φ=0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (by exact_mod_cast sub_ne_zero.mpr hwz)

theorem normalizedDescendant_weight {Q N : ℕ} (ψ : State Q N) (m n : ℕ)
    (hw : tensorWeight ψ=(m : ℂ) • ψ) :
    tensorWeight (normalizedTensorDescendant ψ m n)=
      (((m : ℝ)-2*(n : ℝ) : ℝ) : ℂ) • normalizedTensorDescendant ψ m n := by
  unfold normalizedTensorDescendant
  change tensorWeightLinear Q N (_ • _) = _
  rw [map_smul]
  change _ • tensorWeight _ = _
  rw [tensorWeight_descendant ψ (m : ℂ) hw]
  push_cast
  exact smul_comm _ _ _

theorem normalizedDescendant_commuting_offdiagonal {Q N : ℕ}
    (A : State Q N →ₗ[ℂ] State Q N)
    (hA : ∀ v, tensorWeight (A v)=A (tensorWeight v))
    (ψ φ : State Q N) (m n l : ℕ)
    (hψ : tensorWeight ψ=(m : ℂ) • ψ) (hφ : tensorWeight φ=(m : ℂ) • φ)
    (hnl : n≠l) :
    inner (normalizedTensorDescendant ψ m n) (A (normalizedTensorDescendant φ m l))=0 := by
  apply stateInner_distinct_weight_eigenvalues _ _ ((m : ℝ)-2*n) ((m : ℝ)-2*l)
  · exact normalizedDescendant_weight ψ m n hψ
  · rw [hA, normalizedDescendant_weight φ m l hφ, map_smul]
  · intro h
    have he : (n : ℝ)=(l : ℝ) := by linarith
    exact hnl (by exact_mod_cast he)

theorem normalizedDescendantFrame_commutant_block {Q N d k : ℕ} (hd : 2*d≤N*Q)
    (E : (Fin k → ℂ) ≃ₗ[ℂ] physicalHighestWeightSubspace Q N d)
    (A : State Q N →ₗ[ℂ] State Q N)
    (hE : ∀ v, tensorRaise (A v)=A (tensorRaise v))
    (hW : ∀ v, tensorWeight (A v)=A (tensorWeight v))
    (n l : Fin (N*Q-2*d+1)) (c e : Fin k → ℂ) :
    inner (normalizedDescendantFrame E n.val c) (A (normalizedDescendantFrame E l.val e))=
      if n=l then inner (highestWeightPhysicalFrame E c) (A (highestWeightPhysicalFrame E e)) else 0 := by
  simp only [normalizedDescendantFrame_apply]
  by_cases h : n=l
  · subst l
    rw [ite_eq_left rfl]
    exact normalizedDescendant_commuting_form A hE _ _ _ (highestWeightPhysicalFrame_raise E _)
      (highestWeightPhysicalFrame_weight hd E _) n.val (by omega)
  · rw [ite_eq_right h]
    exact normalizedDescendant_commuting_offdiagonal A hW _ _ _ _ _
      (highestWeightPhysicalFrame_weight hd E _) (highestWeightPhysicalFrame_weight hd E _)
      (fun he => h (Fin.ext he))

end
end BosonicLaughlin

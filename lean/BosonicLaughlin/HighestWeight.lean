import BosonicLaughlin.Recoupling
import BosonicLaughlin.AngularMomentum
import BosonicLaughlin.SwapStructure

/-!
Concrete highest-weight vectors of the pair-spin × spectator auxiliary space.
The raising kernel is determined by its pair-index-zero row; together with
fixed total deficit, this proves uniqueness and excludes all deficits above Q.
-/
namespace BosonicLaughlin
noncomputable section

theorem auxRaise_supported_pred {Q z : ℕ} (φ : ThreeBodyAux Q)
    (hs : AuxSupported (z + 1) φ) : AuxSupported z (auxRaise φ) := by
  intro p k hpk
  simp only [auxRaise, spinRaise]
  have ha : (if h : p.val < 2 * Q then
      (spinRaiseCoeff (2 * Q) p.val : ℂ) * φ ⟨p.val + 1, by omega⟩ k else 0) = 0 := by
    split_ifs with hp
    · rw [hs _ _ (by simp only [Fin.val_mk]; omega), mul_zero]
    · rfl
  have hb : (if h : k.val < Q then
      (spinRaiseCoeff Q k.val : ℂ) * φ p ⟨k.val + 1, by omega⟩ else 0) = 0 := by
    split_ifs with hk
    · rw [hs _ _ (by simp only [Fin.val_mk]; omega), mul_zero]
    · rfl
  change _ + _ = 0
  rw [ha, hb, add_zero]

theorem auxRaise_supported_zero {Q : ℕ} (φ : ThreeBodyAux Q)
    (hs : AuxSupported 0 φ) : auxRaise φ = 0 := by
  funext p k
  simp only [auxRaise, spinRaise, Pi.zero_apply]
  have ha : (if h : p.val < 2 * Q then
      (spinRaiseCoeff (2 * Q) p.val : ℂ) * φ ⟨p.val + 1, by omega⟩ k else 0) = 0 := by
    split_ifs with hp
    · rw [hs _ _ (by simp only [Fin.val_mk]; omega), mul_zero]
    · rfl
  have hb : (if h : k.val < Q then
      (spinRaiseCoeff Q k.val : ℂ) * φ p ⟨k.val + 1, by omega⟩ else 0) = 0 := by
    split_ifs with hk
    · rw [hs _ _ (by simp only [Fin.val_mk]; omega), mul_zero]
    · rfl
  change _ + _ = 0
  rw [ha, hb, add_zero]

/-- The finite recurrence vector, embedded into the actual auxiliary space. -/
def auxHighestWeight (Q z : ℕ) : ThreeBodyAux Q := fun p k =>
  if p.val + k.val = z then (highestWeightCoefficient Q z p.val : ℂ) else 0

theorem auxHighestWeight_supported (Q z : ℕ) :
    AuxSupported z (auxHighestWeight Q z) := by
  intro p k h
  simp [auxHighestWeight, h]

theorem auxHighestWeight_first (Q z : ℕ) (hz : z ≤ Q) :
    auxHighestWeight Q z ⟨0, by omega⟩ ⟨z, by omega⟩ = 1 := by
  simp [auxHighestWeight, highestWeightCoefficient_zero]

theorem auxHighestWeight_nonzero (Q z : ℕ) (hz : z ≤ Q) :
    auxHighestWeight Q z ≠ 0 := by
  intro h
  have he := congrFun (congrFun h ⟨0, by omega⟩) ⟨z, by omega⟩
  simpa [auxHighestWeight, highestWeightCoefficient_zero] using he

theorem auxHighestWeight_raise (Q z : ℕ) (hz : z ≤ Q) :
    auxRaise (auxHighestWeight Q z) = 0 := by
  funext p k
  by_cases hs : p.val + k.val + 1 = z
  · have hp : p.val < 2 * Q := by omega
    have hk : k.val < Q := by omega
    have hpz : p.val < z := by omega
    have ha : z - p.val = k.val + 1 := by omega
    have hb : Q - z + p.val + 1 = Q - k.val := by omega
    have hs' : p.val + 1 + k.val = z := by omega
    have hs'' : p.val + (k.val + 1) = z := by omega
    have hc := congrArg Complex.ofReal
      (highestWeightCoefficient_ladder_cancel Q z p.val hpz hz)
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_zero] at hc
    simpa [auxRaise, spinRaise, hp, hk, auxHighestWeight, hs, hs', hs'',
      spinRaiseCoeff, ha, hb, Nat.add_assoc] using hc
  · have hs' : p.val + 1 + k.val ≠ z := by omega
    simp only [auxRaise, spinRaise, auxHighestWeight, Pi.zero_apply]
    split_ifs <;> simp_all [Nat.add_assoc]

theorem auxHighestWeight_weight (Q z : ℕ) :
    auxWeight (auxHighestWeight Q z) =
      ((3 * Q : ℕ) - (2 * z : ℕ) : ℂ) • auxHighestWeight Q z := by
  funext p k
  by_cases hs : p.val + k.val = z
  · have hc : (p.val : ℂ) + (k.val : ℂ) = (z : ℂ) := by exact_mod_cast hs
    simp only [auxWeight, spinWeight, Pi.smul_apply, smul_eq_mul,
      auxHighestWeight, hs, ite_true, Nat.cast_mul, Nat.cast_ofNat]
    rw [← hc]
    ring
  · simp [auxWeight, spinWeight, auxHighestWeight, hs]

/-- The raising equation determines all pair-index rows from the first row. -/
theorem auxRaise_kernel_firstRow_injective {Q : ℕ} (φ : ThreeBodyAux Q)
    (hE : auxRaise φ = 0)
    (hfirst : ∀ k, φ ⟨0, by omega⟩ k = 0) : φ = 0 := by
  funext p
  induction p using Fin.induction with
  | zero => exact funext hfirst
  | succ p ih =>
    funext k
    have he := congrFun (congrFun hE p.castSucc) k
    have hp : p.val < 2 * Q := p.isLt
    have hc : (spinRaiseCoeff (2 * Q) p.val : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      apply ne_of_gt
      unfold spinRaiseCoeff
      apply Real.sqrt_pos.mpr
      apply mul_pos (by positivity)
      exact_mod_cast Nat.sub_pos_of_lt hp
    simp only [auxRaise, spinRaise, Fin.coe_castSucc, hp, dite_true,
      Pi.zero_apply] at he
    by_cases hk : k.val < Q
    · rw [dif_pos hk] at he
      have hi := congrFun ih ⟨k.val + 1, by omega⟩
      change φ p.castSucc ⟨k.val + 1, by omega⟩ = 0 at hi
      rw [hi, mul_zero, add_zero] at he
      exact (mul_eq_zero.mp he).resolve_left hc
    · rw [dif_neg hk, add_zero] at he
      exact (mul_eq_zero.mp he).resolve_left hc

theorem auxHighestWeight_unique {Q z : ℕ} (hz : z ≤ Q) (φ : ThreeBodyAux Q)
    (hs : AuxSupported z φ) (hE : auxRaise φ = 0) :
    φ = φ ⟨0, by omega⟩ ⟨z, by omega⟩ • auxHighestWeight Q z := by
  apply sub_eq_zero.mp
  apply auxRaise_kernel_firstRow_injective
  · change (auxRaiseLinear Q) (φ - _ • auxHighestWeight Q z) = 0
    rw [map_sub, map_smul]
    change auxRaise φ - _ • auxRaise (auxHighestWeight Q z) = 0
    rw [hE, auxHighestWeight_raise Q z hz, smul_zero, sub_self]
  · intro k
    change φ ⟨0, by omega⟩ k -
      φ ⟨0, by omega⟩ ⟨z, by omega⟩ * auxHighestWeight Q z ⟨0, by omega⟩ k = 0
    by_cases hk : k.val = z
    · have heq : k = ⟨z, by omega⟩ := Fin.ext hk
      rw [heq]
      simp [auxHighestWeight, highestWeightCoefficient_zero]
    · have hφ := hs ⟨0, by omega⟩ k (by simpa using hk)
      change φ 0 k = 0 at hφ
      simp [hφ, auxHighestWeight, hk]

theorem auxRaise_kernel_highDeficit_zero {Q z : ℕ} (hz : Q < z)
    (φ : ThreeBodyAux Q) (hs : AuxSupported z φ) (hE : auxRaise φ = 0) : φ = 0 := by
  apply auxRaise_kernel_firstRow_injective φ hE
  intro k
  apply hs
  have hk := k.isLt
  simp only [Fin.val_mk]
  omega

theorem auxRaise_kernel_deficit_le {Q z : ℕ} (φ : ThreeBodyAux Q)
    (hs : AuxSupported z φ) (hE : auxRaise φ = 0) (hφ : φ ≠ 0) : z ≤ Q := by
  by_contra hz
  exact hφ (auxRaise_kernel_highDeficit_zero (by omega) φ hs hE)

/-- Endpoint of the actual compressed exchange on the concrete recurrence vector. -/
theorem auxHighestWeight_swap_endpoint (Q z : ℕ) (hz : z ≤ Q) :
    compressedSwap (auxHighestWeight Q z) ⟨0, by omega⟩ ⟨z, by omega⟩ =
      ((-1 : ℝ) ^ z * recouplingRatio Q z : ℝ) := by
  simp only [compressedSwap, pairVector_zero, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero, ite_mul, one_mul, zero_mul]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hsum : (∑ q : Fin (2 * Q + 1),
      (pairVector Q q.val ⟨0, by omega⟩ ⟨z, by omega⟩ : ℂ) *
        auxHighestWeight Q z q ⟨0, by omega⟩) =
      (pairCoefficient Q z 0 : ℂ) * (highestWeightCoefficient Q z z : ℂ) := by
    rw [Finset.sum_eq_single (⟨z, by omega⟩ : Fin (2 * Q + 1))]
    · simp [auxHighestWeight, pairVector]
    · intro q _ hq
      have hqz : q.val ≠ z := by intro h; exact hq (Fin.ext h)
      simp [auxHighestWeight, hqz]
    · simp
  change (∑ q : Fin (2 * Q + 1),
    (pairVector Q q.val 0 ⟨z, by omega⟩ : ℂ) * auxHighestWeight Q z q 0) =
    (pairCoefficient Q z 0 : ℂ) * (highestWeightCoefficient Q z z : ℂ) at hsum
  rw [hsum]
  have he := congrArg Complex.ofReal (recoupling_endpoint_coefficient Q z hz)
  simpa only [Complex.ofReal_mul, mul_comm] using he

/-- Kernel uniqueness upgrades endpoint extraction to an eigenvector once the
actual compressed exchange is shown to commute with raising. -/
theorem auxHighestWeight_swap_of_raise_commutes (Q z : ℕ) (hz : z ≤ Q)
    (hcomm : auxRaise (compressedSwap (auxHighestWeight Q z)) =
      compressedSwap (auxRaise (auxHighestWeight Q z))) :
    compressedSwap (auxHighestWeight Q z) =
      (((-1 : ℝ) ^ z * recouplingRatio Q z : ℝ) : ℂ) • auxHighestWeight Q z := by
  have hE : auxRaise (compressedSwap (auxHighestWeight Q z)) = 0 := by
    rw [hcomm, auxHighestWeight_raise Q z hz, compressedSwap_zero]
  have hu := auxHighestWeight_unique hz (compressedSwap (auxHighestWeight Q z))
    (compressedSwap_supported z _ (auxHighestWeight_supported Q z)) hE
  rw [auxHighestWeight_swap_endpoint Q z hz] at hu
  exact hu

end
end BosonicLaughlin

import BosonicLaughlin.Model
import BosonicLaughlin.PairBlock

/-!
The complete two-orbital V₀ kernel.  The coefficient normalization here is
over the physical orbital set `Fin (Q+1)` in both tensor slots, rather than
over an auxiliary fixed-sum block with zero padding.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem pairVector_row_norm (Q p : ℕ) (x : Orbital Q) :
    ∑ y : Orbital Q, pairVector Q p x y ^ 2 =
      if x.val ≤ p then pairCoefficient Q p x.val ^ 2 else 0 := by
  by_cases hx : x.val ≤ p
  · rw [ite_eq_left hx]
    by_cases hy : p-x.val ≤ Q
    · let y₀ : Orbital Q := ⟨p-x.val, by omega⟩
      have he : ∀ y : Orbital Q, x.val+y.val=p ↔ y=y₀ := by
        intro y
        constructor
        · intro h
          apply Fin.ext
          change y.val = p-x.val
          omega
        · intro h
          subst y
          change x.val+(p-x.val)=p
          omega
      simp [pairVector, he]
    · have hz := pairCoefficient_zero_right Q p x.val (by omega)
      simp [pairVector, hz]
  · rw [ite_eq_right hx]
    have he : ∀ y : Orbital Q, ¬ x.val+y.val=p := by
      intro y h
      omega
    simp [pairVector, he]

/-- Normalization in the actual two-particle orbital tensor space. -/
theorem pairVector_normalized (Q p : ℕ) (hp : p ≤ 2*Q) :
    ∑ x : Orbital Q, ∑ y : Orbital Q, pairVector Q p x y ^ 2 = 1 := by
  simp_rw [pairVector_row_norm]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i ≤ p then pairCoefficient Q p i ^ 2 else 0)]
  let f : ℕ → ℝ := fun i => if i ≤ p then pairCoefficient Q p i ^ 2 else 0
  change (∑ i ∈ range (Q+1), f i) = 1
  have hQ : (∑ i ∈ range (Q+1), f i) = ∑ i ∈ range (Q+p+1), f i := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hn
    have hQi : Q < i := by simp only [mem_range] at hn; omega
    simp [f, pairCoefficient_zero_left Q p i hQi]
  have hp' : (∑ i ∈ range (p+1), f i) = ∑ i ∈ range (Q+p+1), f i := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hn
    have hpi : ¬ i ≤ p := by simp only [mem_range] at hn; omega
    simp [f, hpi]
  rw [hQ, ← hp']
  have hf : (∑ i ∈ range (p+1), f i) =
      ∑ i ∈ range (p+1), pairCoefficient Q p i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hip : i ≤ p := by simp only [mem_range] at hi; omega
    simp [f, hip]
  rw [hf]
  exact pairCoefficient_normalized Q p hp

/-- Distinct orbital sums have disjoint support. -/
theorem pairVector_orthogonal (Q p r : ℕ) (hpr : p ≠ r) :
    ∑ x : Orbital Q, ∑ y : Orbital Q,
      pairVector Q p x y * pairVector Q r x y = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  by_cases hp : x.val+y.val=p
  · have hr : x.val+y.val ≠ r := by omega
    simp [pairVector, hr]
  · simp [pairVector, hp]

theorem pairVector_overlap (Q p r : ℕ) (hp : p ≤ 2*Q) :
    ∑ x : Orbital Q, ∑ y : Orbital Q,
      pairVector Q p x y * pairVector Q r x y = if p=r then 1 else 0 := by
  by_cases h : p=r
  · subst r
    simp only [ite_true, ← pow_two]
    exact pairVector_normalized Q p hp
  · rw [ite_eq_right h]
    exact pairVector_orthogonal Q p r h

theorem pairVector_overlap_complex (Q p r : ℕ) (hp : p ≤ 2*Q) :
    ∑ x : Orbital Q, ∑ y : Orbital Q,
      (pairVector Q p x y : ℂ) * (pairVector Q r x y : ℂ) =
        if p=r then 1 else 0 := by
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, apply_ite,
    Complex.ofReal_one, Complex.ofReal_zero] using
    congrArg Complex.ofReal (pairVector_overlap Q p r hp)

/-- Successive replacements of the same two slots discard the first pair. -/
theorem replacePair_replacePair {Q N : ℕ} (a : Configuration Q N)
    (i j : Fin N) (x y u v : Orbital Q) :
    replacePair (replacePair a i j x y) i j u v = replacePair a i j u v := by
  funext k
  by_cases hj : k=j
  · subst k
    simp [replacePair]
  · by_cases hi : k=i
    · subst k
      simp [replacePair, hj]
    · simp [replacePair, hi, hj]

theorem replacePair_left {Q N : ℕ} (a : Configuration Q N)
    (i j : Fin N) (hij : i ≠ j) (x y : Orbital Q) :
    replacePair a i j x y i = x := by
  simp [replacePair, hij]

theorem replacePair_right {Q N : ℕ} (a : Configuration Q N)
    (i j : Fin N) (x y : Orbital Q) :
    replacePair a i j x y j = y := by
  simp [replacePair]

/-- Contraction of two tensor slots against a normalized pair-spin-Q vector. -/
def pairTensorAmplitude {Q N : ℕ} (i j : Fin N) (p : Fin (2*Q+1))
    (ψ : State Q N) (a : Configuration Q N) : ℂ :=
  ∑ x : Orbital Q, ∑ y : Orbital Q,
    (pairVector Q p.val x y : ℂ) * ψ (replacePair a i j x y)

theorem pairTensorAmplitude_apply {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (p : Fin (2*Q+1)) (ψ : State Q N) (a : Configuration Q N) :
    pairTensorAmplitude i j p (pairApply i j ψ) a = pairTensorAmplitude i j p ψ a := by
  let f : Orbital Q → Orbital Q → Fin (2*Q+1) → ℂ := fun x y r =>
    (pairVector Q p.val x y : ℂ) *
      ((pairVector Q r.val x y : ℂ) * pairTensorAmplitude i j r ψ a)
  have he : pairTensorAmplitude i j p (pairApply i j ψ) a =
      ∑ x, ∑ y, ∑ r, f x y r := by
    simp only [pairTensorAmplitude, pairApply, replacePair_left a i j hij,
      replacePair_right, replacePair_replacePair, Finset.mul_sum, f]
  rw [he]
  have hs : (∑ x, ∑ y, ∑ r, f x y r) = ∑ r, ∑ x, ∑ y, f x y r := by
    calc
      _ = ∑ x, ∑ r, ∑ y, f x y r := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hs]
  simp_rw [f, ← mul_assoc, ← Finset.sum_mul]
  have hp : p.val ≤ 2*Q := by omega
  simp_rw [pairVector_overlap_complex Q p.val _ hp]
  simp [Fin.val_inj]

/-- The physical two-slot V₀ operator is idempotent for distinct tensor slots. -/
theorem pairApply_idempotent {Q N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State Q N) : pairApply i j (pairApply i j ψ) = pairApply i j ψ := by
  funext a
  change (∑ p : Fin (2*Q+1),
    (pairVector Q p.val (a i) (a j) : ℂ) *
      pairTensorAmplitude i j p (pairApply i j ψ) a) = _
  simp_rw [pairTensorAmplitude_apply i j hij]
  rfl

end
end BosonicLaughlin

import BosonicLaughlin.BosonicProjection
import BosonicLaughlin.ThreeBodySlices
import BosonicLaughlin.StateForms

/-!
The normalized three-body lift on each finite bosonic particle sector.
For M=N+3 its ambient extension is choose(M,3) P_M (A tensor I_N) P_M.
It is zero for M<3. Positivity is required only on the physical three-boson
subspace; slicing a symmetric M-particle state stays in that subspace.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def threeBodyLiftAbove (Q N : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3) :
    State Q (N+3) →ₗ[ℂ] State Q (N+3) :=
  ((N+3).choose 3 : ℂ) • (bosonicProjectionLinear Q (N+3)).comp
    ((firstThreeApplyLinear Q N A).comp (bosonicProjectionLinear Q (N+3)))

theorem threeBodyLiftAbove_apply (Q N : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3)
    (ψ : State Q (N+3)) :
    threeBodyLiftAbove Q N A ψ = ((N+3).choose 3 : ℂ) •
      bosonicProjection (firstThreeApply A (bosonicProjection ψ)) := rfl

def threeBodyLift (Q : ℕ) : (M : ℕ) → (State Q 3 →ₗ[ℂ] State Q 3) →
    (State Q M →ₗ[ℂ] State Q M)
  | 0, _ => 0
  | 1, _ => 0
  | 2, _ => 0
  | N+3, A => threeBodyLiftAbove Q N A

theorem threeBodyLift_above (Q N : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3) :
    threeBodyLift Q (N+3) A = threeBodyLiftAbove Q N A := rfl

theorem threeBodyLift_small_sector (Q M : ℕ) (hM : M ≤ 2)
    (A : State Q 3 →ₗ[ℂ] State Q 3) : threeBodyLift Q M A = 0 := by
  interval_cases M <;> rfl

theorem threeBodyLiftAbove_isBosonic (Q N : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3)
    (ψ : State Q (N+3)) : IsBosonic (threeBodyLiftAbove Q N A ψ) := by
  exact (bosonicSubspace Q (N+3)).smul_mem _ (bosonicProjection_isBosonic _)

theorem threeBodyLiftAbove_inner (Q N : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3)
    (ψ φ : State Q (N+3)) :
    inner ψ (threeBodyLiftAbove Q N A φ) = ((N+3).choose 3 : ℂ) *
      ∑ a : Configuration Q N, inner (threeBodySlice (bosonicProjection ψ) a)
        (A (threeBodySlice (bosonicProjection φ) a)) := by
  rw [threeBodyLiftAbove_apply, stateInner_smul_right,
    bosonicProjection_hermitian, inner_firstThreeApply]

theorem threeBodyLiftAbove_inner_bosonic (Q N : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3)
    (ψ φ : State Q (N+3)) (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner ψ (threeBodyLiftAbove Q N A φ) = ((N+3).choose 3 : ℂ) *
      ∑ a : Configuration Q N, inner (threeBodySlice ψ a) (A (threeBodySlice φ a)) := by
  rw [threeBodyLiftAbove_inner, bosonicProjection_eq_self ψ hψ,
    bosonicProjection_eq_self φ hφ]

theorem threeBodyLiftAbove_nonneg (Q N : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3)
    (hA : ∀ χ, IsBosonic χ → 0 ≤ (inner χ (A χ)).re) (ψ : State Q (N+3)) :
    0 ≤ (inner ψ (threeBodyLiftAbove Q N A ψ)).re := by
  rw [threeBodyLiftAbove_inner]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.re_sum]
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro a _
  exact hA _ (threeBodySlice_isBosonic _ (bosonicProjection_isBosonic ψ) a)

theorem threeBodyLift_nonneg (Q M : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3)
    (hA : ∀ χ, IsBosonic χ → 0 ≤ (inner χ (A χ)).re) (ψ : State Q M) :
    0 ≤ (inner ψ (threeBodyLift Q M A ψ)).re := by
  rcases M with _ | (_ | (_ | N))
  · simp [threeBodyLift, inner]
  · simp [threeBodyLift, inner]
  · simp [threeBodyLift, inner]
  · exact threeBodyLiftAbove_nonneg Q N A hA ψ

theorem threeBodyLiftAbove_mono (Q N : ℕ) (A B : State Q 3 →ₗ[ℂ] State Q 3)
    (hAB : ∀ χ, IsBosonic χ → (inner χ (A χ)).re ≤ (inner χ (B χ)).re)
    (ψ : State Q (N+3)) :
    (inner ψ (threeBodyLiftAbove Q N A ψ)).re ≤
      (inner ψ (threeBodyLiftAbove Q N B ψ)).re := by
  rw [threeBodyLiftAbove_inner, threeBodyLiftAbove_inner]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.re_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro a _
  exact hAB _ (threeBodySlice_isBosonic _ (bosonicProjection_isBosonic ψ) a)

theorem threeBodyLift_mono (Q M : ℕ) (A B : State Q 3 →ₗ[ℂ] State Q 3)
    (hAB : ∀ χ, IsBosonic χ → (inner χ (A χ)).re ≤ (inner χ (B χ)).re)
    (ψ : State Q M) :
    (inner ψ (threeBodyLift Q M A ψ)).re ≤ (inner ψ (threeBodyLift Q M B ψ)).re := by
  rcases M with _ | (_ | (_ | N))
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact threeBodyLiftAbove_mono Q N A B hAB ψ

theorem threeBodyLiftAbove_congr (Q N : ℕ) (A B : State Q 3 →ₗ[ℂ] State Q 3)
    (hAB : ∀ χ, IsBosonic χ → A χ = B χ) :
    threeBodyLiftAbove Q N A = threeBodyLiftAbove Q N B := by
  apply LinearMap.ext
  intro φ
  apply stateInner_ext
  intro ψ
  rw [threeBodyLiftAbove_inner, threeBodyLiftAbove_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [hAB _ (threeBodySlice_isBosonic _ (bosonicProjection_isBosonic φ) a)]

theorem firstThreeApply_id {Q N : ℕ} (ψ : State Q (N+3)) :
    firstThreeApply (LinearMap.id : State Q 3 →ₗ[ℂ] State Q 3) ψ = ψ := by
  funext c
  exact congrArg ψ (threeBodyInsert_head_tail c)

theorem threeBodyLiftAbove_id (Q N : ℕ) (ψ : State Q (N+3)) (hψ : IsBosonic ψ) :
    threeBodyLiftAbove Q N LinearMap.id ψ = ((N+3).choose 3 : ℂ) • ψ := by
  rw [threeBodyLiftAbove_apply, bosonicProjection_eq_self ψ hψ,
    firstThreeApply_id, bosonicProjection_eq_self ψ hψ]

theorem threeBodyLift_id (Q M : ℕ) (ψ : State Q M) (hψ : IsBosonic ψ) :
    threeBodyLift Q M LinearMap.id ψ = (M.choose 3 : ℂ) • ψ := by
  rcases M with _ | (_ | (_ | N))
  · norm_num [threeBodyLift, Nat.choose]
  · norm_num [threeBodyLift, Nat.choose]
  · norm_num [threeBodyLift, Nat.choose]
  · exact threeBodyLiftAbove_id Q N ψ hψ

theorem threeBodyLiftAbove_add (Q N : ℕ) (A B : State Q 3 →ₗ[ℂ] State Q 3) :
    threeBodyLiftAbove Q N (A+B) = threeBodyLiftAbove Q N A + threeBodyLiftAbove Q N B := by
  apply LinearMap.ext
  intro ψ
  simp only [LinearMap.add_apply, threeBodyLiftAbove_apply]
  change ((N+3).choose 3 : ℂ) • bosonicProjection
    (firstThreeApply A (bosonicProjection ψ) + firstThreeApply B (bosonicProjection ψ)) = _
  rw [bosonicProjection_add, smul_add]

theorem threeBodyLiftAbove_smul (Q N : ℕ) (c : ℂ) (A : State Q 3 →ₗ[ℂ] State Q 3) :
    threeBodyLiftAbove Q N (c • A) = c • threeBodyLiftAbove Q N A := by
  apply LinearMap.ext
  intro ψ
  simp only [LinearMap.smul_apply, threeBodyLiftAbove_apply]
  change ((N+3).choose 3 : ℂ) • bosonicProjection
    (c • firstThreeApply A (bosonicProjection ψ)) = _
  rw [bosonicProjection_smul]
  exact smul_comm _ _ _

theorem threeBodyLift_add (Q M : ℕ) (A B : State Q 3 →ₗ[ℂ] State Q 3) :
    threeBodyLift Q M (A+B) = threeBodyLift Q M A + threeBodyLift Q M B := by
  rcases M with _ | (_ | (_ | N))
  · simp [threeBodyLift]
  · simp [threeBodyLift]
  · simp [threeBodyLift]
  · exact threeBodyLiftAbove_add Q N A B

theorem threeBodyLift_smul (Q M : ℕ) (c : ℂ) (A : State Q 3 →ₗ[ℂ] State Q 3) :
    threeBodyLift Q M (c • A) = c • threeBodyLift Q M A := by
  rcases M with _ | (_ | (_ | N))
  · simp [threeBodyLift]
  · simp [threeBodyLift]
  · simp [threeBodyLift]
  · exact threeBodyLiftAbove_smul Q N c A

def threeBodyLiftLinear (Q M : ℕ) :
    (State Q 3 →ₗ[ℂ] State Q 3) →ₗ[ℂ] (State Q M →ₗ[ℂ] State Q M) where
  toFun := threeBodyLift Q M
  map_add' := threeBodyLift_add Q M
  map_smul' := threeBodyLift_smul Q M

theorem threeBodyLift_congr (Q M : ℕ) (A B : State Q 3 →ₗ[ℂ] State Q 3)
    (hAB : ∀ χ, IsBosonic χ → A χ = B χ) :
    threeBodyLift Q M A = threeBodyLift Q M B := by
  rcases M with _ | (_ | (_ | N))
  · rfl
  · rfl
  · rfl
  · exact threeBodyLiftAbove_congr Q N A B hAB

theorem bosonic_stateInner_ext {Q M : ℕ} (φ χ : State Q M)
    (hφ : IsBosonic φ) (hχ : IsBosonic χ)
    (h : ∀ ψ, IsBosonic ψ → inner ψ φ = inner ψ χ) : φ = χ := by
  apply stateInner_ext
  intro ψ
  calc
    inner ψ φ = inner (bosonicProjection ψ) φ := by
      rw [← bosonicProjection_hermitian, bosonicProjection_eq_self φ hφ]
    _ = inner (bosonicProjection ψ) χ := h _ (bosonicProjection_isBosonic ψ)
    _ = inner ψ χ := by
      rw [← bosonicProjection_hermitian, bosonicProjection_eq_self χ hχ]

end
end BosonicLaughlin

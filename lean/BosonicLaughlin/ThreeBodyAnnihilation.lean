import BosonicLaughlin.ThreeBodyLift

/-!
Normalized three-particle creation and annihilation maps. The rank-one lift
is identified with their actual composition on every finite particle sector.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def threeAnnihilate {Q N : ℕ} (w : State Q 3) (ψ : State Q (N + 3)) : State Q N :=
  fun a => (Real.sqrt ((N + 3).choose 3) : ℂ) *
    inner w (threeBodySlice (bosonicProjection ψ) a)

def threeCreate {Q N : ℕ} (w : State Q 3) (χ : State Q N) : State Q (N + 3) :=
  (Real.sqrt ((N + 3).choose 3) : ℂ) •
    bosonicProjection (fun c => w (threeBodyHead c) * χ (threeBodyTail c))

theorem threeAnnihilate_add {Q N : ℕ} (w : State Q 3) (ψ φ : State Q (N + 3)) :
    threeAnnihilate w (ψ + φ) = threeAnnihilate w ψ + threeAnnihilate w φ := by
  funext a
  simp [threeAnnihilate, bosonicProjection_add, threeBodySlice_add,
    stateInner_add_right, mul_add]

theorem threeAnnihilate_smul {Q N : ℕ} (w : State Q 3) (c : ℂ) (ψ : State Q (N + 3)) :
    threeAnnihilate w (c • ψ) = c • threeAnnihilate w ψ := by
  funext a
  simp only [threeAnnihilate, bosonicProjection_smul, threeBodySlice_smul,
    stateInner_smul_right, Pi.smul_apply, smul_eq_mul]
  ring

def threeAnnihilateLinear (Q N : ℕ) (w : State Q 3) : State Q (N + 3) →ₗ[ℂ] State Q N where
  toFun := threeAnnihilate w
  map_add' := threeAnnihilate_add w
  map_smul' := threeAnnihilate_smul w

theorem threeCreate_add {Q N : ℕ} (w : State Q 3) (χ η : State Q N) :
    threeCreate w (χ + η) = threeCreate w χ + threeCreate w η := by
  have h : (fun c : Configuration Q (N + 3) => w (threeBodyHead c) * (χ + η) (threeBodyTail c)) =
      (fun c => w (threeBodyHead c) * χ (threeBodyTail c)) +
        (fun c => w (threeBodyHead c) * η (threeBodyTail c)) := by
    funext c
    simp [mul_add]
  simp only [threeCreate, h, bosonicProjection_add, smul_add]

theorem threeCreate_smul {Q N : ℕ} (w : State Q 3) (s : ℂ) (χ : State Q N) :
    threeCreate w (s • χ) = s • threeCreate w χ := by
  have h : (fun c : Configuration Q (N + 3) => w (threeBodyHead c) * (s • χ) (threeBodyTail c)) =
      s • (fun c => w (threeBodyHead c) * χ (threeBodyTail c)) := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp only [threeCreate, h, bosonicProjection_smul, smul_smul]
  rw [mul_comm]

def threeCreateLinear (Q N : ℕ) (w : State Q 3) : State Q N →ₗ[ℂ] State Q (N + 3) where
  toFun := threeCreate w
  map_add' := threeCreate_add w
  map_smul' := threeCreate_smul w

theorem threeCreate_isBosonic {Q N : ℕ} (w : State Q 3) (χ : State Q N) :
    IsBosonic (threeCreate w χ) :=
  (bosonicSubspace Q (N + 3)).smul_mem _ (bosonicProjection_isBosonic _)

/-- The three-particle wavefunction is the vector created from normalized vacuum. -/
theorem threeCreate_vacuum {Q : ℕ} (w : State Q 3) (hw : IsBosonic w) :
    threeCreate (N := 0) w (fun _ => 1) = w := by
  simp only [threeCreate, Nat.reduceAdd, Nat.choose_self, Nat.cast_one, Real.sqrt_one,
    Complex.ofReal_one, one_smul, mul_one]
  change bosonicProjection w = w
  exact bosonicProjection_eq_self w hw

theorem threeBodySlice_tail_permute {Q N : ℕ} (ψ : State Q (N + 3))
    (hψ : IsBosonic ψ) (a : Configuration Q N) (σ : Equiv.Perm (Fin N)) :
    threeBodySlice ψ (a ∘ σ) = threeBodySlice ψ a := by
  funext b
  simp only [threeBodySlice, threeBodyInsert, cons_comp_fixFirst,
    hψ (fixFirstPermutation (fixFirstPermutation (fixFirstPermutation σ)))]

theorem threeAnnihilate_isBosonic {Q N : ℕ} (w : State Q 3) (ψ : State Q (N + 3)) :
    IsBosonic (threeAnnihilate w ψ) := by
  intro σ a
  simp only [threeAnnihilate,
    threeBodySlice_tail_permute _ (bosonicProjection_isBosonic ψ) a σ]

theorem threeAnnihilate_bosonic_formula {Q N : ℕ} (w : State Q 3)
    (ψ : State Q (N + 3)) (hψ : IsBosonic ψ) (a : Configuration Q N) :
    threeAnnihilate w ψ a = (Real.sqrt ((N + 3).choose 3) : ℂ) *
      inner w (threeBodySlice ψ a) := by
  rw [threeAnnihilate, bosonicProjection_eq_self ψ hψ]

theorem threeCreate_inner {Q N : ℕ} (w : State Q 3) (χ : State Q N)
    (ψ : State Q (N + 3)) : inner (threeCreate w χ) ψ = inner χ (threeAnnihilate w ψ) := by
  have hs : inner (fun c : Configuration Q (N + 3) =>
      w (threeBodyHead c) * χ (threeBodyTail c)) (bosonicProjection ψ) =
      ∑ a : Configuration Q N, star (χ a) *
        inner w (threeBodySlice (bosonicProjection ψ) a) := by
    rw [inner_threeBodySlices]
    apply Finset.sum_congr rfl
    intro a _
    simp only [inner, threeBodySlice, threeBodyHead_insert, threeBodyTail_insert,
      star_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [threeCreate, stateInner_smul_left, ← bosonicProjection_hermitian, hs]
  rw [show star (Real.sqrt ((N + 3).choose 3) : ℂ) =
    (Real.sqrt ((N + 3).choose 3) : ℂ) by simp]
  simp only [inner, threeAnnihilate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

def rankOneThree {Q : ℕ} (w w' : State Q 3) : State Q 3 →ₗ[ℂ] State Q 3 where
  toFun φ := fun b => w b * inner w' φ
  map_add' := by
    intro φ χ
    funext b
    simp [stateInner_add_right, mul_add]
  map_smul' := by
    intro c φ
    funext b
    simp only [stateInner_smul_right, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem threeBodyLiftAbove_rankOne (Q N : ℕ) (w w' : State Q 3)
    (ψ : State Q (N + 3)) :
    threeBodyLiftAbove Q N (rankOneThree w w') ψ = threeCreate w (threeAnnihilate w' ψ) := by
  have hfactor : (fun c : Configuration Q (N + 3) =>
      w (threeBodyHead c) * threeAnnihilate w' ψ (threeBodyTail c)) =
      (Real.sqrt ((N + 3).choose 3) : ℂ) •
        firstThreeApply (rankOneThree w w') (bosonicProjection ψ) := by
    funext c
    simp only [threeAnnihilate, firstThreeApply, rankOneThree, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
    ring
  have hs : (Real.sqrt ((N + 3).choose 3) : ℂ) *
      (Real.sqrt ((N + 3).choose 3) : ℂ) = ((N + 3).choose 3 : ℂ) := by
    have h := congrArg Complex.ofReal (Real.mul_self_sqrt
      (show (0 : ℝ) ≤ ((N + 3).choose 3 : ℝ) by positivity))
    simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using h
  rw [threeBodyLiftAbove_apply, threeCreate, hfactor,
    bosonicProjection_smul, smul_smul, hs]

end
end BosonicLaughlin

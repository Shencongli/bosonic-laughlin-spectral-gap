import BosonicLaughlin.FockCorrespondence
import Mathlib.Logic.Equiv.Fintype

/-! Exact first-three-slot slices in the full tensor-coordinate space. -/
namespace BosonicLaughlin
noncomputable section
open Finset

def threeBodySlot (N : ℕ) : Fin 3 ↪ Fin (N + 3) where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j h; exact Fin.ext (congrArg (fun k : Fin (N + 3) => k.val) h)

def threeBodyInsert {Q N : ℕ} (a : Configuration Q N) (b : Configuration Q 3) :
    Configuration Q (N + 3) := Fin.cons (b 0) (Fin.cons (b 1) (Fin.cons (b 2) a))

def threeBodyHead {Q N : ℕ} (c : Configuration Q (N + 3)) : Configuration Q 3 :=
  fun i => c (threeBodySlot N i)

def threeBodyTail {Q N : ℕ} (c : Configuration Q (N + 3)) : Configuration Q N :=
  fun j => c j.succ.succ.succ

theorem threeBodyInsert_slot {Q N : ℕ} (a : Configuration Q N) (b : Configuration Q 3)
    (i : Fin 3) : threeBodyInsert a b (threeBodySlot N i) = b i := by
  fin_cases i <;> rfl

theorem threeBodyInsert_tail {Q N : ℕ} (a : Configuration Q N) (b : Configuration Q 3)
    (j : Fin N) : threeBodyInsert a b j.succ.succ.succ = a j := rfl

theorem threeBodyHead_insert {Q N : ℕ} (a : Configuration Q N) (b : Configuration Q 3) :
    threeBodyHead (threeBodyInsert a b) = b := funext (threeBodyInsert_slot a b)

theorem threeBodyTail_insert {Q N : ℕ} (a : Configuration Q N) (b : Configuration Q 3) :
    threeBodyTail (threeBodyInsert a b) = a := rfl

theorem threeBodyInsert_head_tail {Q N : ℕ} (c : Configuration Q (N + 3)) :
    threeBodyInsert (threeBodyTail c) (threeBodyHead c) = c := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · rfl

theorem threeBodyHead_eq_vector {Q N : ℕ} (c : Configuration Q (N + 3)) :
    threeBodyHead c = ![c 0, c 1, c 2] := by
  funext i
  fin_cases i <;> rfl

def threeBodyConfigurationEquiv (Q N : ℕ) :
    (Configuration Q N × Configuration Q 3) ≃ Configuration Q (N + 3) where
  toFun ab := threeBodyInsert ab.1 ab.2
  invFun c := (threeBodyTail c, threeBodyHead c)
  left_inv := by intro ab; simp [threeBodyTail_insert, threeBodyHead_insert]
  right_inv := threeBodyInsert_head_tail

def threeBodySlice {Q N : ℕ} (ψ : State Q (N + 3)) (a : Configuration Q N) : State Q 3 :=
  fun b => ψ (threeBodyInsert a b)

theorem threeBodySlice_add {Q N : ℕ} (ψ φ : State Q (N + 3)) (a : Configuration Q N) :
    threeBodySlice (ψ + φ) a = threeBodySlice ψ a + threeBodySlice φ a := rfl

theorem threeBodySlice_smul {Q N : ℕ} (c : ℂ) (ψ : State Q (N + 3)) (a : Configuration Q N) :
    threeBodySlice (c • ψ) a = c • threeBodySlice ψ a := rfl

def firstThreePermutation (N : ℕ) (σ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin (N + 3)) :=
  σ.viaFintypeEmbedding (threeBodySlot N)

theorem threeBodyTailSlot_not_range (N : ℕ) (j : Fin N) :
    j.succ.succ.succ ∉ Set.range (threeBodySlot N) := by
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hb := i.isLt
  change i.val = j.val + 1 + 1 + 1 at hv
  omega

theorem threeBodyInsert_permute {Q N : ℕ} (a : Configuration Q N) (b : Configuration Q 3)
    (σ : Equiv.Perm (Fin 3)) :
    threeBodyInsert a (b ∘ σ) = threeBodyInsert a b ∘ firstThreePermutation N σ := by
  funext i
  by_cases hi : i.val < 3
  · let j : Fin 3 := ⟨i.val, hi⟩
    have hj : threeBodySlot N j = i := Fin.ext rfl
    rw [← hj]
    simp only [Function.comp_apply, firstThreePermutation,
      Equiv.Perm.viaFintypeEmbedding_apply_image, threeBodyInsert_slot]
  · obtain ⟨j, rfl⟩ : ∃ j : Fin N, j.succ.succ.succ = i := by
      refine ⟨⟨i.val - 3, by omega⟩, Fin.ext ?_⟩
      simp only [Fin.val_succ, Fin.val_mk]
      omega
    simp only [Function.comp_apply, firstThreePermutation,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range σ (threeBodySlot N)
        (threeBodyTailSlot_not_range N j), threeBodyInsert_tail]

theorem threeBodySlice_isBosonic {Q N : ℕ} (ψ : State Q (N + 3))
    (hψ : IsBosonic ψ) (a : Configuration Q N) : IsBosonic (threeBodySlice ψ a) := by
  intro σ b
  simp only [threeBodySlice, threeBodyInsert_permute, hψ (firstThreePermutation N σ)]

theorem threeBodyInsert_update {Q N : ℕ} (a : Configuration Q N) (b : Configuration Q 3)
    (i : Fin 3) (x : Orbital Q) :
    threeBodyInsert a (Function.update b i x) =
      Function.update (threeBodyInsert a b) (threeBodySlot N i) x := by
  funext j
  by_cases hj : j.val < 3
  · let k : Fin 3 := ⟨j.val, hj⟩
    have hk : threeBodySlot N k = j := Fin.ext rfl
    rw [← hk, threeBodyInsert_slot]
    by_cases hki : k = i
    · rw [hki]
      simp only [Function.update_self]
    · have hne : threeBodySlot N k ≠ threeBodySlot N i :=
        (threeBodySlot N).injective.ne hki
      simp [hki, hne, threeBodyInsert_slot]
  · obtain ⟨k, rfl⟩ : ∃ k : Fin N, k.succ.succ.succ = j := by
      refine ⟨⟨j.val - 3, by omega⟩, Fin.ext ?_⟩
      simp only [Fin.val_succ, Fin.val_mk]
      omega
    have hne : k.succ.succ.succ ≠ threeBodySlot N i := by
      intro he
      exact threeBodyTailSlot_not_range N k ⟨i, he.symm⟩
    simp [hne, threeBodyInsert_tail]

theorem threeBodyInsert_replacePair {Q N : ℕ} (a : Configuration Q N)
    (b : Configuration Q 3) (i j : Fin 3) (x y : Orbital Q) :
    threeBodyInsert a (replacePair b i j x y) =
      replacePair (threeBodyInsert a b) (threeBodySlot N i) (threeBodySlot N j) x y := by
  simp only [replacePair, threeBodyInsert_update]

theorem threeBodySlice_pairApply {Q N : ℕ} (ψ : State Q (N + 3))
    (a : Configuration Q N) (i j : Fin 3) :
    threeBodySlice (pairApply (threeBodySlot N i) (threeBodySlot N j) ψ) a =
      pairApply i j (threeBodySlice ψ a) := by
  funext b
  simp only [threeBodySlice, pairApply, threeBodyInsert_slot, threeBodyInsert_replacePair]

theorem threeBodySlice_pairProduct {Q N : ℕ} (ψ : State Q (N + 3))
    (a : Configuration Q N) (i j k l : Fin 3) :
    threeBodySlice (pairApply (threeBodySlot N i) (threeBodySlot N j)
      (pairApply (threeBodySlot N k) (threeBodySlot N l) ψ)) a =
      pairApply i j (pairApply k l (threeBodySlice ψ a)) := by
  rw [threeBodySlice_pairApply, threeBodySlice_pairApply]

theorem sum_configurations_threeBody {Q N : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Configuration Q (N + 3) → A) :
    ∑ c, f c = ∑ a : Configuration Q N, ∑ b : Configuration Q 3,
      f (threeBodyInsert a b) := by
  rw [← (threeBodyConfigurationEquiv Q N).sum_comp f]
  simp only [Fintype.sum_prod_type, threeBodyConfigurationEquiv, Equiv.coe_fn_mk]

theorem inner_threeBodySlices {Q N : ℕ} (ψ φ : State Q (N + 3)) :
    inner ψ φ = ∑ a : Configuration Q N, inner (threeBodySlice ψ a) (threeBodySlice φ a) := by
  unfold inner
  rw [sum_configurations_threeBody]
  rfl

theorem inner_firstThree_pairProduct {Q N : ℕ} (ψ φ : State Q (N + 3)) :
    inner ψ (pairApply 0 1 (pairApply 0 2 φ)) =
      ∑ a : Configuration Q N,
        inner (threeBodySlice ψ a) (pairApply 0 1 (pairApply 0 2 (threeBodySlice φ a))) := by
  rw [inner_threeBodySlices]
  apply Finset.sum_congr rfl
  intro a _
  have h := threeBodySlice_pairProduct φ a 0 1 0 2
  have hs0 : threeBodySlot N 0 = 0 := rfl
  have hs1 : threeBodySlot N 1 = 1 := rfl
  have hs2 : threeBodySlot N 2 = 2 := rfl
  rw [hs0, hs1, hs2] at h
  rw [h]

/-- Apply a three-particle linear map on the first three tensor slots. -/
def firstThreeApply {Q N : ℕ} (A : State Q 3 →ₗ[ℂ] State Q 3)
    (ψ : State Q (N + 3)) : State Q (N + 3) := fun c =>
  A (threeBodySlice ψ (threeBodyTail c)) (threeBodyHead c)

theorem threeBodySlice_firstThreeApply {Q N : ℕ} (A : State Q 3 →ₗ[ℂ] State Q 3)
    (ψ : State Q (N + 3)) (a : Configuration Q N) :
    threeBodySlice (firstThreeApply A ψ) a = A (threeBodySlice ψ a) := by
  funext b
  simp only [threeBodySlice, firstThreeApply, threeBodyTail_insert, threeBodyHead_insert]

theorem firstThreeApply_add {Q N : ℕ} (A : State Q 3 →ₗ[ℂ] State Q 3)
    (ψ φ : State Q (N + 3)) : firstThreeApply A (ψ + φ) =
      firstThreeApply A ψ + firstThreeApply A φ := by
  funext c
  simp [firstThreeApply, threeBodySlice_add, map_add]

theorem firstThreeApply_smul {Q N : ℕ} (A : State Q 3 →ₗ[ℂ] State Q 3)
    (s : ℂ) (ψ : State Q (N + 3)) : firstThreeApply A (s • ψ) = s • firstThreeApply A ψ := by
  funext c
  simp [firstThreeApply, threeBodySlice_smul]

def firstThreeApplyLinear (Q N : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3) :
    State Q (N + 3) →ₗ[ℂ] State Q (N + 3) where
  toFun := firstThreeApply A
  map_add' := firstThreeApply_add A
  map_smul' := firstThreeApply_smul A

theorem inner_firstThreeApply {Q N : ℕ} (A : State Q 3 →ₗ[ℂ] State Q 3)
    (ψ φ : State Q (N + 3)) : inner ψ (firstThreeApply A φ) =
      ∑ a : Configuration Q N, inner (threeBodySlice ψ a) (A (threeBodySlice φ a)) := by
  rw [inner_threeBodySlices]
  simp_rw [threeBodySlice_firstThreeApply]

end
end BosonicLaughlin

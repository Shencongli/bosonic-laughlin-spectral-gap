import BosonicLaughlin.BosonicProjection

/-!
Exact total-orbital-deficit sectors in the finite spherical tensor model.
The integer weight is the sum of the orbital indices, before imposing Bose
symmetry. It is conserved by every distinct-slot V0 pair projector.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def configurationWeight {Q N : ℕ} (a : Configuration Q N) : ℕ :=
  ∑ i : Fin N, (a i).val

def WeightSupported {Q N : ℕ} (d : ℕ) (ψ : State Q N) : Prop :=
  ∀ a, configurationWeight a ≠ d → ψ a = 0

def weightProjection {Q N : ℕ} (d : ℕ) (ψ : State Q N) : State Q N := fun a =>
  if configurationWeight a = d then ψ a else 0

theorem configurationWeight_le {Q N : ℕ} (a : Configuration Q N) :
    configurationWeight a ≤ N*Q := by
  calc
    _ ≤ ∑ _i : Fin N, Q := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.le_of_lt_succ (a i).isLt
    _ = _ := by simp

theorem configurationWeight_permute {Q N : ℕ} (a : Configuration Q N)
    (σ : Equiv.Perm (Fin N)) : configurationWeight (a ∘ σ) = configurationWeight a :=
  Equiv.sum_comp σ (fun i => (a i).val)

theorem configurationWeight_update {Q N : ℕ} (a : Configuration Q N)
    (i : Fin N) (x : Orbital Q) :
    configurationWeight (Function.update a i x) + (a i).val =
      configurationWeight a + x.val := by
  have he : (fun k => (Function.update a i x k).val) =
      Function.update (fun k => (a k).val) i x.val := by
    funext k
    by_cases hki : k=i <;> simp [hki]
  unfold configurationWeight
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  have hs := Finset.add_sum_erase (univ : Finset (Fin N)) (fun k => (a k).val) (mem_univ i)
  omega

theorem configurationWeight_replacePair {Q N : ℕ} (a : Configuration Q N)
    (i j : Fin N) (hij : i≠j) (x y : Orbital Q)
    (hs : x.val+y.val = (a i).val+(a j).val) :
    configurationWeight (replacePair a i j x y) = configurationWeight a := by
  have h1 := configurationWeight_update a i x
  have h2 := configurationWeight_update (Function.update a i x) j y
  rw [Function.update_of_ne hij.symm] at h2
  change configurationWeight (Function.update (Function.update a i x) j y) = _
  omega

theorem weightProjection_add {Q N : ℕ} (d : ℕ) (ψ φ : State Q N) :
    weightProjection d (ψ+φ) = weightProjection d ψ + weightProjection d φ := by
  funext a
  simp only [weightProjection, Pi.add_apply]
  split_ifs <;> simp

theorem weightProjection_smul {Q N : ℕ} (d : ℕ) (c : ℂ) (ψ : State Q N) :
    weightProjection d (c • ψ) = c • weightProjection d ψ := by
  funext a
  simp only [weightProjection, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def weightProjectionLinear (Q N d : ℕ) : State Q N →ₗ[ℂ] State Q N where
  toFun := weightProjection d
  map_add' := weightProjection_add d
  map_smul' := weightProjection_smul d

theorem weightProjection_supported {Q N : ℕ} (d : ℕ) (ψ : State Q N) :
    WeightSupported d (weightProjection d ψ) := by
  intro a ha
  simp [weightProjection, ha]

theorem weightProjection_eq_self {Q N : ℕ} (d : ℕ) (ψ : State Q N)
    (hψ : WeightSupported d ψ) : weightProjection d ψ = ψ := by
  funext a
  by_cases ha : configurationWeight a=d
  · simp [weightProjection, ha]
  · simp [weightProjection, ha, hψ a ha]

theorem weightProjection_fixed_iff {Q N : ℕ} (d : ℕ) (ψ : State Q N) :
    weightProjection d ψ = ψ ↔ WeightSupported d ψ := by
  constructor
  · intro h
    rw [← h]
    exact weightProjection_supported d ψ
  · exact weightProjection_eq_self d ψ

theorem weightProjection_idempotent {Q N : ℕ} (d : ℕ) (ψ : State Q N) :
    weightProjection d (weightProjection d ψ) = weightProjection d ψ :=
  weightProjection_eq_self d _ (weightProjection_supported d ψ)

theorem weightProjection_isBosonic {Q N : ℕ} (d : ℕ) (ψ : State Q N)
    (hψ : IsBosonic ψ) : IsBosonic (weightProjection d ψ) := by
  intro σ a
  simp only [weightProjection, configurationWeight_permute, hψ σ]

theorem weightProjection_bosonicProjection {Q N : ℕ} (d : ℕ) (ψ : State Q N) :
    weightProjection d (bosonicProjection ψ) = bosonicProjection (weightProjection d ψ) := by
  funext a
  simp only [bosonicProjection, weightProjection, configurationWeight_permute]
  by_cases ha : configurationWeight a=d <;> simp [ha]

theorem weightProjection_outside {Q N : ℕ} (d : ℕ) (hd : N*Q < d) (ψ : State Q N) :
    weightProjection d ψ = 0 := by
  funext a
  have ha : configurationWeight a≠d := by
    have h := configurationWeight_le a
    omega
  simp [weightProjection, ha]

theorem pairApply_weightProjection {Q N : ℕ} (d : ℕ) (i j : Fin N) (hij : i≠j)
    (ψ : State Q N) :
    pairApply i j (weightProjection d ψ) = weightProjection d (pairApply i j ψ) := by
  funext a
  have hterm (p : Fin (2*Q+1)) (x y : Orbital Q) :
      (pairVector Q p.val (a i) (a j) : ℂ) * (pairVector Q p.val x y : ℂ) *
        weightProjection d ψ (replacePair a i j x y) =
      if configurationWeight a=d then
        (pairVector Q p.val (a i) (a j) : ℂ) * (pairVector Q p.val x y : ℂ) *
          ψ (replacePair a i j x y) else 0 := by
    by_cases hp : (a i).val+(a j).val=p.val
    · by_cases hxy : x.val+y.val=p.val
      · have hw := configurationWeight_replacePair a i j hij x y (hxy.trans hp.symm)
        simp only [weightProjection, hw]
        split_ifs <;> simp_all only [mul_zero]
      · simp [pairVector, hxy]
    · simp [pairVector, hp]
  simp only [pairApply, Finset.mul_sum, ← mul_assoc]
  simp_rw [hterm]
  unfold weightProjection
  split_ifs <;> simp [pairApply, Finset.mul_sum, mul_assoc]

theorem pairApply_weightSupported {Q N : ℕ} (d : ℕ) (i j : Fin N) (hij : i≠j)
    (ψ : State Q N) (hψ : WeightSupported d ψ) : WeightSupported d (pairApply i j ψ) := by
  apply (weightProjection_fixed_iff d _).mp
  rw [← pairApply_weightProjection d i j hij, weightProjection_eq_self d ψ hψ]

theorem hamiltonian_weightProjection {Q N : ℕ} (d : ℕ) (ψ : State Q N) :
    hamiltonian (weightProjection d ψ) = weightProjection d (hamiltonian ψ) := by
  funext a
  unfold hamiltonian
  have ht (i j : Fin N) :
      (if i<j then pairApply i j (weightProjection d ψ) a else 0) =
        (if configurationWeight a=d then if i<j then pairApply i j ψ a else 0 else 0) := by
    by_cases hij : i<j
    · simp only [hij, ite_true, pairApply_weightProjection d i j (ne_of_lt hij), weightProjection]
    · simp [hij]
  simp_rw [ht]
  unfold weightProjection
  split_ifs <;> simp

theorem hamiltonian_weightSupported {Q N : ℕ} (d : ℕ) (ψ : State Q N)
    (hψ : WeightSupported d ψ) : WeightSupported d (hamiltonian ψ) := by
  apply (weightProjection_fixed_iff d _).mp
  rw [← hamiltonian_weightProjection, weightProjection_eq_self d ψ hψ]

end
end BosonicLaughlin

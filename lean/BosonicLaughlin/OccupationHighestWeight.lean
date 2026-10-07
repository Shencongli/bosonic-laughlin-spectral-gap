import BosonicLaughlin.PolynomialHighestWeight
import BosonicLaughlin.OccupationPairChannels

/-!
The integer occupation matrix of the actual total raising operator in
factorial polynomial coordinates. A source orbital j is replaced by j-1
with coefficient j times its source multiplicity. No selected relative
basis or RREF output is assumed.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def occupationReplace {Q N : ℕ} (A : Occupation Q N) (x y : Orbital Q)
    (hx : x ∈ A.val) : Occupation Q N :=
  ⟨y ::ₘ A.val.erase x, by
    rw [Multiset.card_cons]
    exact (Multiset.card_erase_add_one hx).trans A.property⟩

theorem occupationReplace_val {Q N : ℕ} (A : Occupation Q N) (x y : Orbital Q)
    (hx : x ∈ A.val) : (occupationReplace A x y hx).val = y ::ₘ A.val.erase x := rfl

theorem occupationReplace_mem {Q N : ℕ} (A : Occupation Q N) (x y : Orbital Q)
    (hx : x ∈ A.val) : y ∈ (occupationReplace A x y hx).val := by
  change y ∈ y ::ₘ A.val.erase x
  exact Multiset.mem_cons_self _ _

theorem occupationReplace_inverse {Q N : ℕ} (A : Occupation Q N) (x y : Orbital Q)
    (hx : x ∈ A.val) :
    occupationReplace (occupationReplace A x y hx) y x (occupationReplace_mem A x y hx) = A := by
  apply Sym.ext
  change x ::ₘ (y ::ₘ A.val.erase x).erase y = A.val
  rw [Multiset.erase_cons_head]
  exact Multiset.cons_erase hx

theorem occupationOfConfiguration_mem {Q N : ℕ} (a : Configuration Q N) (k : Fin N) :
    a k ∈ (occupationOfConfiguration a).val := by
  change a k ∈ (List.ofFn a : Multiset (Orbital Q))
  simp only [Multiset.mem_coe, List.mem_ofFn]
  exact ⟨k,rfl⟩

theorem occupationOfConfiguration_update {Q N : ℕ} (a : Configuration Q N)
    (k : Fin N) (x : Orbital Q) :
    occupationOfConfiguration (Function.update a k x) =
      occupationReplace (occupationOfConfiguration a) (a k) x (occupationOfConfiguration_mem a k) := by
  cases N with
  | zero => exact Fin.elim0 k
  | succ N =>
    let σ : Equiv.Perm (Fin (N+1)) := Equiv.swap 0 k
    let b : Configuration Q N := Fin.tail (a ∘ σ)
    have hs : σ 0=k := Equiv.swap_apply_left 0 k
    have ha : a ∘ σ=Fin.cons (a k) b := by
      rw [← Fin.cons_self_tail (a ∘ σ)]
      simp only [Function.comp_apply, hs]
      rfl
    have hv : (occupationOfConfiguration a).val = (a k) ::ₘ (occupationOfConfiguration b).val := by
      rw [← occupationOfConfiguration_permute a σ, ha, occupationOfConfiguration_cons,
        occupation_cons_val]
    have hu : Function.update (a ∘ σ) 0 x = Fin.cons x b := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · change Function.update (a ∘ σ) 0 x j.succ = (a ∘ σ) j.succ
        simp
    have ht : Function.update a k x ∘ σ = Fin.cons x b := by
      rw [← hs, ← update_permute, hu]
    apply Sym.ext
    change (occupationOfConfiguration (Function.update a k x)).val =
      x ::ₘ (occupationOfConfiguration a).val.erase (a k)
    rw [← occupationOfConfiguration_permute (Function.update a k x) σ, ht,
      occupationOfConfiguration_cons, occupation_cons_val,
      hv, Multiset.erase_cons_head]

theorem sum_slots_occupation_count {Q N : ℕ} (a : Configuration Q N)
    (f : Orbital Q → ℂ) :
    (∑ k : Fin N, f (a k)) = ∑ x : Orbital Q,
      ((occupationOfConfiguration a).val.count x : ℂ) * f x := by
  induction N with
  | zero => simp [occupationOfConfiguration]
  | succ N ih =>
    have ha : occupationOfConfiguration a = Sym.cons (a 0) (occupationOfConfiguration (Fin.tail a)) := by
      rw [← occupationOfConfiguration_cons, Fin.cons_self_tail]
    rw [Fin.sum_univ_succ, ih (fun i => a i.succ), ha]
    simp only [occupation_cons_val, Multiset.count_cons, Nat.cast_add, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
    simp [Fin.tail, add_comm]
    rfl

theorem occupationReplace_factorial {Q N : ℕ} (A : Occupation Q N)
    (x y : Orbital Q) (hx : x ∈ A.val) :
    A.val.count x * occupationFactorial (occupationReplace A x y hx) =
      (occupationReplace A x y hx).val.count y * occupationFactorial A := by
  have he : A.val=x ::ₘ A.val.erase x := (Multiset.cons_erase hx).symm
  simp only [occupationFactorial, occupationReplace_val,
    multisetOccupationFactorial_cons, Multiset.count_cons_self]
  rw [he, Multiset.count_cons_self, multisetOccupationFactorial_cons]
  rw [Multiset.erase_cons_head]
  ring

/-- In each row B, replace one output label i by the source label i+1.
The coefficient uses the multiplicity in that source occupation. -/
def occupationCM {Q N : ℕ} (c : OccupationState Q N) : OccupationState Q N := fun B =>
  ∑ i : Orbital Q, if hi : i.val < Q then if hm : i ∈ B.val then
    let j : Orbital Q := ⟨i.val+1, by omega⟩
    let A := occupationReplace B i j hm
    ((j.val * A.val.count j : ℕ) : ℂ) * c A
  else 0 else 0

theorem occupationCM_add {Q N : ℕ} (c e : OccupationState Q N) :
    occupationCM (c+e) = occupationCM c + occupationCM e := by
  funext B
  simp only [occupationCM, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [mul_add]

theorem occupationCM_smul {Q N : ℕ} (z : ℂ) (c : OccupationState Q N) :
    occupationCM (z • c) = z • occupationCM c := by
  funext B
  simp only [occupationCM, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

def occupationCMLinear (Q N : ℕ) : OccupationState Q N →ₗ[ℂ] OccupationState Q N where
  toFun := occupationCM
  map_add' := occupationCM_add
  map_smul' := occupationCM_smul

theorem polynomialOccupationInclude_CM {Q N : ℕ} (c : OccupationState Q N) :
    polynomialCM (polynomialOccupationInclude c) = polynomialOccupationInclude (occupationCM c) := by
  funext a
  let B := occupationOfConfiguration a
  let f : Orbital Q → ℂ := fun i => if hi : i.val < Q then if hm : i ∈ B.val then
    let j : Orbital Q := ⟨i.val+1, by omega⟩
    let A := occupationReplace B i j hm
    (j.val : ℂ) * (occupationFactorial A : ℂ) * c A else 0 else 0
  have hs : polynomialCM (polynomialOccupationInclude c) a = ∑ k : Fin N, f (a k) := by
    apply Finset.sum_congr rfl
    intro k _
    have hm : a k ∈ B.val := occupationOfConfiguration_mem a k
    simp only [polynomialOccupationInclude, occupationOfConfiguration_update,
      f, hm, dite_true]
    split_ifs <;> ring
  rw [hs, sum_slots_occupation_count]
  change (∑ i : Orbital Q, (B.val.count i : ℂ) * f i) =
    (occupationFactorial B : ℂ) * occupationCM c B
  simp only [occupationCM, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [f]
  split_ifs with hi hm
  · have he := occupationReplace_factorial B i (⟨i.val+1, by omega⟩ : Orbital Q) hm
    have hc : (B.val.count i : ℂ) *
        (occupationFactorial (occupationReplace B i ⟨i.val+1, by omega⟩ hm) : ℂ) =
      ((occupationReplace B i ⟨i.val+1, by omega⟩ hm).val.count ⟨i.val+1, by omega⟩ : ℂ) *
        (occupationFactorial B : ℂ) := by exact_mod_cast he
    push_cast
    linear_combination (((i.val : ℂ)+1) *
      c (occupationReplace B i ⟨i.val+1, by omega⟩ hm)) * hc
  · simp
  · simp

theorem polynomialOccupationInclude_CM_zero_iff {Q N : ℕ} (c : OccupationState Q N) :
    polynomialCM (polynomialOccupationInclude c)=0 ↔ occupationCM c=0 := by
  rw [polynomialOccupationInclude_CM]
  constructor
  · intro h
    apply polynomialOccupationInclude_injective Q N
    rw [h]
    exact ((polynomialOccupationIncludeLinear Q N).map_zero).symm
  · intro h
    rw [h]
    exact (polynomialOccupationIncludeLinear Q N).map_zero

def occupationCMMatrix (Q N : ℕ) : Matrix (Occupation Q N) (Occupation Q N) ℂ :=
  LinearMap.toMatrix' (occupationCMLinear Q N)

theorem occupationCMMatrix_mulVec {Q N : ℕ} (c : OccupationState Q N) :
    (occupationCMMatrix Q N).mulVec c = occupationCM c := LinearMap.toMatrix'_mulVec _ _

/-- The matrix coefficient is j times the multiplicity of the removed source
label j. Reconstructing the source from the row avoids any list-order convention. -/
theorem occupationCMMatrix_apply (Q N : ℕ) (B A : Occupation Q N) :
    occupationCMMatrix Q N B A = ∑ i : Orbital Q,
      if hi : i.val < Q then if hm : i ∈ B.val then
        let j : Orbital Q := ⟨i.val+1, by omega⟩
        if occupationReplace B i j hm=A then ((j.val * A.val.count j : ℕ) : ℂ) else 0
      else 0 else 0 := by
  rw [occupationCMMatrix, LinearMap.toMatrix'_apply]
  change occupationCM (Pi.single A 1) B = _
  unfold occupationCM
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi hm
  · dsimp only
    by_cases he : occupationReplace B i ⟨i.val+1, by omega⟩ hm=A
    · rw [he]
      simp
    · simp [Pi.single_apply, he, Ne.symm he]
  · rfl
  · rfl

/-- Reconstructing the source by i→j is exactly the source-column rule j→i. -/
theorem occupationReplace_eq_iff_reverse {Q N : ℕ} (A B : Occupation Q N)
    (i j : Orbital Q) (hi : i ∈ B.val) :
    occupationReplace B i j hi=A ↔ ∃ hj : j ∈ A.val, occupationReplace A j i hj=B := by
  constructor
  · intro h
    subst A
    exact ⟨occupationReplace_mem B i j hi, occupationReplace_inverse B i j hi⟩
  · rintro ⟨hj,h⟩
    subst B
    exact occupationReplace_inverse A j i hj

/-- The actual spherical highest-weight condition in the factorial occupation
coordinates. Any additional nonzero scalar normalization of a sector preserves
this kernel condition; its operator intertwiner must retain that scalar. -/
theorem tensorRaise_polynomialOccupation_zero_iff {Q N : ℕ} (c : OccupationState Q N) :
    tensorRaise ((polynomialCoordinates Q N).symm (polynomialOccupationInclude c))=0 ↔
      (occupationCMMatrix Q N).mulVec c=0 := by
  rw [← polynomialCM_coordinates_zero_iff, LinearEquiv.apply_symm_apply,
    polynomialOccupationInclude_CM_zero_iff, occupationCMMatrix_mulVec]

theorem tensorRaise_smul_zero_iff {Q N : ℕ} (c : ℂ) (hc : c≠0) (ψ : State Q N) :
    tensorRaise (c • ψ)=0 ↔ tensorRaise ψ=0 := by
  rw [tensorRaise_smul, smul_eq_zero]
  simp only [hc, false_or]

theorem tensorRaise_scaledPolynomialOccupation_zero_iff {Q N : ℕ}
    (c : ℂ) (hc : c≠0) (u : OccupationState Q N) :
    tensorRaise (c • (polynomialCoordinates Q N).symm (polynomialOccupationInclude u))=0 ↔
      (occupationCMMatrix Q N).mulVec u=0 := by
  rw [tensorRaise_smul_zero_iff c hc, tensorRaise_polynomialOccupation_zero_iff]

end
end BosonicLaughlin

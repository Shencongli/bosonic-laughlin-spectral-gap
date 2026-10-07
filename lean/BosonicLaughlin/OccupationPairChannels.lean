import BosonicLaughlin.OccupationCoordinates
import BosonicLaughlin.OccupationPairFactorial
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Exact integer occupation coefficients for the polynomial pair channels.
The one-label derivative removes a source occurrence with its multiplicity;
two successive derivatives also cover coinciding labels. The coordinate
embedding multiplies each ordered-tensor amplitude by the occupation factorial.
It is not an orthonormal Fock-basis identification.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def occupationFactorial {Q N : ℕ} (A : Occupation Q N) : ℕ :=
  multisetOccupationFactorial A.val

theorem occupationFactorial_pos {Q N : ℕ} (A : Occupation Q N) :
    0 < occupationFactorial A := multisetOccupationFactorial_pos A.val

theorem occupationFactorial_cons {Q N : ℕ} (x : Orbital Q) (A : Occupation Q N) :
    occupationFactorial (Sym.cons x A) = (A.val.count x + 1) * occupationFactorial A :=
  multisetOccupationFactorial_cons x A.val

theorem occupation_cons_val {Q N : ℕ} (x : Orbital Q) (A : Occupation Q N) :
    (Sym.cons x A).val = x ::ₘ A.val := rfl

def polynomialOccupationInclude {Q N : ℕ} (c : OccupationState Q N) : State Q N :=
  fun a => (occupationFactorial (occupationOfConfiguration a) : ℂ) *
    c (occupationOfConfiguration a)

theorem polynomialOccupationInclude_isBosonic {Q N : ℕ} (c : OccupationState Q N) :
    IsBosonic (polynomialOccupationInclude c) := by
  intro σ a
  simp only [polynomialOccupationInclude, occupationOfConfiguration_permute]

theorem polynomialOccupationInclude_injective (Q N : ℕ) :
    Function.Injective (@polynomialOccupationInclude Q N) := by
  intro c e h
  funext A
  have he := congrFun h (occupationRepresentative A)
  simp only [polynomialOccupationInclude, occupationOfConfiguration_representative] at he
  apply mul_left_cancel₀ _ he
  exact_mod_cast (occupationFactorial_pos A).ne'

def polynomialOccupationIncludeLinear (Q N : ℕ) : OccupationState Q N →ₗ[ℂ] State Q N where
  toFun := polynomialOccupationInclude
  map_add' c e := by funext a; simp [polynomialOccupationInclude, mul_add]
  map_smul' z c := by
    funext a
    simp only [polynomialOccupationInclude, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The row formula for the canonical polynomial derivative d_x. -/
def occupationAnnihilate {Q N : ℕ} (x : Orbital Q) (c : OccupationState Q (N+1)) :
    OccupationState Q N := fun B =>
  ((Sym.cons x B).val.count x : ℂ) * c (Sym.cons x B)

/-- The exact sum of sequential derivatives d_y d_x over x+y=p. -/
def occupationPairChannel {Q N : ℕ} (p : ℕ) (c : OccupationState Q (N+2)) :
    OccupationState Q N := fun B =>
  ∑ x : Orbital Q, ∑ y : Orbital Q,
    if x.val+y.val=p then occupationAnnihilate y (occupationAnnihilate x c) B else 0

theorem occupationPairChannel_add {Q N : ℕ} (p : ℕ) (c e : OccupationState Q (N+2)) :
    occupationPairChannel p (c+e) = occupationPairChannel p c + occupationPairChannel p e := by
  funext B
  simp [occupationPairChannel, occupationAnnihilate, mul_add, ite_add_zero,
    Finset.sum_add_distrib]

theorem occupationPairChannel_smul {Q N : ℕ} (p : ℕ) (z : ℂ)
    (c : OccupationState Q (N+2)) : occupationPairChannel p (z • c) = z • occupationPairChannel p c := by
  funext B
  simp only [occupationPairChannel, occupationAnnihilate, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> ring

def occupationPairChannelLinear (Q N p : ℕ) :
    OccupationState Q (N+2) →ₗ[ℂ] OccupationState Q N where
  toFun := occupationPairChannel p
  map_add' := occupationPairChannel_add p
  map_smul' := occupationPairChannel_smul p

theorem polynomialOccupationInclude_pairChannel {Q N : ℕ} (p : ℕ)
    (c : OccupationState Q (N+2)) :
    polynomialPairChannel p (polynomialOccupationInclude c) =
      polynomialOccupationInclude (occupationPairChannel p c) := by
  funext a
  simp only [polynomialPairChannel, polynomialOccupationInclude, occupationPairChannel,
    occupationAnnihilate, occupationOfConfiguration_cons, Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs
  · simp only [occupationFactorial, occupation_cons_val,
      multisetOccupationFactorial_cons_twice, Nat.cast_mul]
    ring
  · rfl

theorem polynomialOccupationInclude_pairChannel_zero_iff {Q N : ℕ} (p : ℕ)
    (c : OccupationState Q (N+2)) :
    polynomialPairChannel p (polynomialOccupationInclude c) = 0 ↔ occupationPairChannel p c = 0 := by
  rw [polynomialOccupationInclude_pairChannel]
  constructor
  · intro h
    apply polynomialOccupationInclude_injective Q N
    rw [h]
    exact ((polynomialOccupationIncludeLinear Q N).map_zero).symm
  · intro h
    rw [h]
    exact (polynomialOccupationIncludeLinear Q N).map_zero

theorem occupationAnnihilate_twice_single {Q N : ℕ} (x y : Orbital Q)
    (A : Occupation Q (N+2)) (B : Occupation Q N) :
    occupationAnnihilate y (occupationAnnihilate x (Pi.single A 1)) B =
      if Sym.cons x (Sym.cons y B) = A then
        ((A.val.count x * (A.val.erase x).count y : ℕ) : ℂ) else 0 := by
  by_cases h : Sym.cons x (Sym.cons y B) = A
  · rw [← h]
    simp only [occupationAnnihilate, Pi.single_eq_same, occupation_cons_val,
      Multiset.erase_cons_head, ite_true, mul_one, Nat.cast_mul]
    ring
  · simp [occupationAnnihilate, Pi.single_apply, h, Ne.symm h]

/-- Reconstructing the source is equivalent to the script's successive removals. -/
theorem multiset_cons_twice_iff_erase {α : Type*} [DecidableEq α]
    (x y : α) (A B : Multiset α) :
    x ::ₘ y ::ₘ B = A ↔
      x ∈ A ∧ y ∈ A.erase x ∧ (A.erase x).erase y = B := by
  constructor
  · intro h
    rw [← h]
    simp
  · rintro ⟨hx, hy, he⟩
    rw [← Multiset.cons_erase hx, ← Multiset.cons_erase hy, he]

def occupationPairMatrix (Q N p : ℕ) :
    Matrix (Occupation Q N) (Occupation Q (N+2)) ℂ :=
  LinearMap.toMatrix' (occupationPairChannelLinear Q N p)

theorem occupationPairMatrix_mulVec {Q N : ℕ} (p : ℕ) (c : OccupationState Q (N+2)) :
    (occupationPairMatrix Q N p).mulVec c = occupationPairChannel p c :=
  LinearMap.toMatrix'_mulVec _ _

/-- The integer coefficient count_x(A) count_y(A\{x}) includes n_x(n_x-1)
for a repeated label. Source and target are indexed by multisets. -/
theorem occupationPairMatrix_apply (Q N p : ℕ) (B : Occupation Q N)
    (A : Occupation Q (N+2)) : occupationPairMatrix Q N p B A =
      ∑ x : Orbital Q, ∑ y : Orbital Q,
        if x.val+y.val=p then
          if Sym.cons x (Sym.cons y B) = A then
            ((A.val.count x * (A.val.erase x).count y : ℕ) : ℂ) else 0
        else 0 := by
  rw [occupationPairMatrix, LinearMap.toMatrix'_apply]
  simp only [occupationPairChannelLinear, LinearMap.coe_mk, AddHom.coe_mk,
    occupationPairChannel, occupationAnnihilate_twice_single]

end
end BosonicLaughlin

import BosonicLaughlin.WeightBlockForms
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fin.Tuple.Sort

/-! Occupation coordinates are multisets of the actual spherical orbitals.
The unscaled inclusion assigns the same tensor amplitude to every ordering.
It is an exact linear identification with the bosonic tensor subspace. -/
namespace BosonicLaughlin
noncomputable section
open Finset

abbrev Occupation (Q N : ℕ) := Sym (Orbital Q) N
abbrev OccupationState (Q N : ℕ) := Occupation Q N → ℂ

def occupationOfConfiguration {Q N : ℕ} (a : Configuration Q N) : Occupation Q N :=
  ⟨(List.ofFn a : Multiset (Orbital Q)), by simp⟩

def occupationWeight {Q N : ℕ} (A : Occupation Q N) : ℕ :=
  (A.val.map Fin.val).sum

abbrev WeightOccupation (Q N d : ℕ) :=
  {A : Occupation Q N // occupationWeight A=d}

theorem occupationOfConfiguration_cons {Q N : ℕ} (x : Orbital Q)
    (a : Configuration Q N) :
    occupationOfConfiguration (Fin.cons x a) = Sym.cons x (occupationOfConfiguration a) := by
  apply Sym.ext
  change (List.ofFn (Fin.cons x a) : Multiset (Orbital Q)) = x ::ₘ (List.ofFn a : Multiset _)
  simp [List.ofFn_succ]

theorem occupationOfConfiguration_permute {Q N : ℕ} (a : Configuration Q N)
    (σ : Equiv.Perm (Fin N)) :
    occupationOfConfiguration (a ∘ σ) = occupationOfConfiguration a := by
  apply Sym.ext
  exact Quotient.sound (σ.ofFn_comp_perm a)

theorem occupationOfConfiguration_weight {Q N : ℕ} (a : Configuration Q N) :
    occupationWeight (occupationOfConfiguration a) = configurationWeight a := by
  simp [occupationWeight, occupationOfConfiguration, configurationWeight,
    List.map_ofFn, List.sum_ofFn]

/-- A chosen ordered representative; later sorted-coordinate statements are independent
of this choice. -/
def occupationRepresentative {Q N : ℕ} (A : Occupation Q N) : Configuration Q N :=
  List.Vector.get (⟨A.val.toList, by simp⟩ : List.Vector (Orbital Q) N)

theorem occupationOfConfiguration_representative {Q N : ℕ} (A : Occupation Q N) :
    occupationOfConfiguration (occupationRepresentative A) = A := by
  apply Sym.ext
  let v : List.Vector (Orbital Q) N := ⟨A.val.toList, by simp⟩
  have hv : List.ofFn (List.Vector.get v) = v.val := by
    have h := congrArg (fun w : List.Vector (Orbital Q) N => w.val)
      (List.Vector.ofFn_get v)
    exact (List.Vector.toList_ofFn _).symm.trans h
  change (List.ofFn (List.Vector.get v) : Multiset (Orbital Q)) = A.val
  calc
    _ = (v.val : Multiset (Orbital Q)) := congrArg
      (fun l : List (Orbital Q) => (l : Multiset (Orbital Q))) hv
    _ = A.val := Multiset.coe_toList _

theorem occupationOfConfiguration_surjective (Q N : ℕ) :
    Function.Surjective (@occupationOfConfiguration Q N) :=
  fun A => ⟨occupationRepresentative A, occupationOfConfiguration_representative A⟩

theorem isBosonic_eq_of_occupation_eq {Q N : ℕ} (ψ : State Q N) (hψ : IsBosonic ψ)
    (a b : Configuration Q N) (hab : occupationOfConfiguration a=occupationOfConfiguration b) :
    ψ a=ψ b := by
  have hp : List.Perm (List.ofFn a) (List.ofFn b) := Quotient.exact (congrArg Subtype.val hab)
  have hs : a ∘ Tuple.sort a = b ∘ Tuple.sort b := by
    apply List.ofFn_injective
    exact (((Tuple.sort a).ofFn_comp_perm a).trans
      (hp.trans ((Tuple.sort b).ofFn_comp_perm b).symm)).eq_of_pairwise'
      (Tuple.monotone_sort a).sortedLE_ofFn.pairwise
      (Tuple.monotone_sort b).sortedLE_ofFn.pairwise
  calc
    ψ a = ψ (a ∘ Tuple.sort a) := (hψ (Tuple.sort a) a).symm
    _ = ψ (b ∘ Tuple.sort b) := congrArg ψ hs
    _ = ψ b := hψ (Tuple.sort b) b

def occupationInclude {Q N : ℕ} (c : OccupationState Q N) : State Q N :=
  fun a => c (occupationOfConfiguration a)

def occupationRestrict {Q N : ℕ} (ψ : State Q N) : OccupationState Q N :=
  fun A => ψ (occupationRepresentative A)

theorem occupationInclude_isBosonic {Q N : ℕ} (c : OccupationState Q N) :
    IsBosonic (occupationInclude c) := by
  intro σ a
  simp only [occupationInclude, occupationOfConfiguration_permute]

theorem occupationRestrict_include {Q N : ℕ} (c : OccupationState Q N) :
    occupationRestrict (occupationInclude c) = c := by
  funext A
  simp only [occupationRestrict, occupationInclude, occupationOfConfiguration_representative]

theorem occupationInclude_restrict {Q N : ℕ} (ψ : State Q N) (hψ : IsBosonic ψ) :
    occupationInclude (occupationRestrict ψ)=ψ := by
  funext a
  exact isBosonic_eq_of_occupation_eq ψ hψ _ a
    (occupationOfConfiguration_representative _)

theorem occupationInclude_injective (Q N : ℕ) :
    Function.Injective (@occupationInclude Q N) := by
  intro c e h
  have he := congrArg (@occupationRestrict Q N) h
  simpa only [occupationRestrict_include] using he

def occupationIncludeLinear (Q N : ℕ) : OccupationState Q N →ₗ[ℂ] State Q N where
  toFun := occupationInclude
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def occupationCoordinateEquiv (Q N : ℕ) :
    OccupationState Q N ≃ₗ[ℂ] bosonicSubspace Q N where
  toFun c := ⟨occupationInclude c, occupationInclude_isBosonic c⟩
  invFun ψ := occupationRestrict ψ.val
  left_inv := occupationRestrict_include
  right_inv ψ := by
    apply Subtype.ext
    exact occupationInclude_restrict ψ.val ψ.property
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end BosonicLaughlin

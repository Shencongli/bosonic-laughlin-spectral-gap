import BosonicLaughlin.OrbitalCap
import BosonicLaughlin.PolynomialCoordinates

/-!
On a fixed total-deficit block, the unweighted polynomial pair equations are
independent of the orbital cap Q once Q ≥ d. The proof transports the actual
finite sums, discarding only coefficients forced to vanish by their support.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

def capOrbital {Q d : ℕ} (hd : d ≤ Q) (x : Orbital d) : Orbital Q :=
  ⟨x.val, by have h := x.isLt; omega⟩

theorem capOrbital_injective {Q d : ℕ} (hd : d ≤ Q) :
    Function.Injective (capOrbital hd) := by
  intro x y h
  exact Fin.ext (congrArg (fun k : Orbital Q => k.val) h)

theorem sum_orbital_cap {Q d : ℕ} (hd : d ≤ Q) (f : Orbital Q → ℂ)
    (hf : ∀ x, d < x.val → f x=0) :
    (∑ x : Orbital Q, f x) = ∑ x : Orbital d, f (capOrbital hd x) := by
  symm
  apply Fintype.sum_of_injective (capOrbital hd) (capOrbital_injective hd)
  · intro x hx
    apply hf x
    by_contra hb
    have hxd : x.val < d+1 := by omega
    exact hx ⟨⟨x.val,hxd⟩, by apply Fin.ext; rfl⟩
  · intro x
    rfl

theorem capConfiguration_cons {Q d N : ℕ} (hd : d ≤ Q) (x : Orbital d)
    (a : Configuration d N) :
    capConfiguration hd (Fin.cons x a) = Fin.cons (capOrbital hd x) (capConfiguration hd a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem cap_configurationWeight_cons {Q N : ℕ} (x : Orbital Q) (a : Configuration Q N) :
    configurationWeight (Fin.cons x a) = x.val + configurationWeight a := by
  simp only [configurationWeight, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem weightSupported_pair_zero_of_large_label {Q N d : ℕ}
    (χ : State Q (N+2)) (hχ : WeightSupported d χ) (x y : Orbital Q)
    (a : Configuration Q N) (h : d < x.val ∨ d < y.val) :
    χ (Fin.cons x (Fin.cons y a)) = 0 := by
  apply hχ
  rw [cap_configurationWeight_cons, cap_configurationWeight_cons]
  omega

theorem polynomialPairChannel_cap {Q N d : ℕ} (hd : d ≤ Q) (p : ℕ)
    (χ : State Q (N+2)) (hχ : WeightSupported d χ) (a : Configuration d N) :
    polynomialPairChannel p χ (capConfiguration hd a) =
      polynomialPairChannel p (fun b => χ (capConfiguration hd b)) a := by
  unfold polynomialPairChannel
  rw [sum_orbital_cap hd _ (by
    intro x hx
    apply Finset.sum_eq_zero
    intro y _
    simp [weightSupported_pair_zero_of_large_label χ hχ x y
      (capConfiguration hd a) (Or.inl hx)])]
  apply Finset.sum_congr rfl
  intro x _
  rw [sum_orbital_cap hd _ (by
    intro y hy
    simp [weightSupported_pair_zero_of_large_label χ hχ (capOrbital hd x) y
      (capConfiguration hd a) (Or.inr hy)])]
  apply Finset.sum_congr rfl
  intro y _
  simp only [capConfiguration_cons, capOrbital]
  rfl

theorem polynomialPairChannel_zero_of_large_weight {Q N d : ℕ}
    (χ : State Q (N+2)) (hχ : WeightSupported d χ) (p : ℕ)
    (a : Configuration Q N) (ha : d < configurationWeight a) :
    polynomialPairChannel p χ a = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  have hz : χ (Fin.cons x (Fin.cons y a))=0 := by
    apply hχ
    rw [cap_configurationWeight_cons, cap_configurationWeight_cons]
    omega
  simp [hz]

theorem polynomialPairChannels_cap_iff {Q N d : ℕ} (hd : d ≤ Q)
    (χ : State Q (N+2)) (hχ : WeightSupported d χ) :
    (∀ p : ℕ, polynomialPairChannel p χ=0) ↔
      ∀ p : ℕ, polynomialPairChannel p (fun b => χ (capConfiguration hd b))=0 := by
  constructor
  · intro h p
    funext a
    rw [← polynomialPairChannel_cap hd p χ hχ a, h p]
    rfl
  · intro h p
    funext a
    by_cases ha : d < configurationWeight a
    · exact polynomialPairChannel_zero_of_large_weight χ hχ p a ha
    · let b : Configuration d N := fun i => ⟨(a i).val, by
        have hi := orbital_le_configurationWeight a i
        omega⟩
      have hb : capConfiguration hd b=a := by
        funext i
        apply Fin.ext
        rfl
      rw [← hb, polynomialPairChannel_cap hd p χ hχ b, h p]
      rfl

theorem polynomialPairChannel_outside {Q N : ℕ} (p : ℕ) (hp : 2*Q < p)
    (χ : State Q (N+2)) : polynomialPairChannel p χ=0 := by
  funext a
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  have hxy : x.val+y.val≠p := by
    have hx := x.isLt
    have hy := y.isLt
    omega
  simp [hxy]

theorem polynomialPairChannels_nat_iff_fin {Q N : ℕ} (χ : State Q (N+2)) :
    (∀ p : ℕ, polynomialPairChannel p χ=0) ↔
      ∀ p : Fin (2*Q+1), polynomialPairChannel p.val χ=0 := by
  constructor
  · intro h p
    exact h p.val
  · intro h p
    by_cases hp : p < 2*Q+1
    · exact h ⟨p,hp⟩
    · exact polynomialPairChannel_outside p (by omega) χ

/-- The common polynomial pair kernel is transported by the actual cap
coordinate equivalence, including the different channel-index ranges. -/
theorem capWeightStateEquiv_pairKernel_iff {Q N d : ℕ} (hd : d ≤ Q)
    (φ : WeightState Q (N+2) d) :
    (∀ p : Fin (2*Q+1), polynomialPairChannel p.val (weightInclude d φ)=0) ↔
      ∀ p : Fin (2*d+1),
        polynomialPairChannel p.val (weightInclude d (capWeightStateEquiv hd φ))=0 := by
  rw [← polynomialPairChannels_nat_iff_fin, ← polynomialPairChannels_nat_iff_fin]
  have he : (fun b => weightInclude d φ (capConfiguration hd b)) =
      weightInclude d (capWeightStateEquiv hd φ) := by
    funext b
    exact (capWeightStateEquiv_include hd φ b).symm
  simpa only [he] using polynomialPairChannels_cap_iff hd (weightInclude d φ)
    (weightInclude_supported φ)

end
end BosonicLaughlin

import BosonicLaughlin.PhysicalKernel
import BosonicLaughlin.ThreeBodyCoefficient
import BosonicLaughlin.NormalOrdering

/-! Exact kernel preservation by operators with physical V₀ annihilators on the right.
The sandwich form uses the normalized physical pair maps; left factors can be
arbitrary linear maps. The concrete S₃, S₄ and W₃ A W₃† consequences are included. -/
namespace BosonicLaughlin
noncomputable section
open Finset

/-- The sesquilinear form of Σp,q Bp† A_pq Bq, without choosing an ambient extension
of the bosonic creation adjoints. -/
def v0PairSandwichForm {Q N : ℕ}
    (A : Fin (2*Q+1) → Fin (2*Q+1) → State Q N →ₗ[ℂ] State Q N)
    (ψ φ : State Q (N+2)) : ℂ :=
  ∑ p, ∑ q, inner (v0PairAnnihilate p ψ) (A p q (v0PairAnnihilate q φ))

theorem v0PairSandwichForm_right_zero {Q N : ℕ}
    (A : Fin (2*Q+1) → Fin (2*Q+1) → State Q N →ₗ[ℂ] State Q N)
    (ψ φ : State Q (N+2)) (hφ : IsBosonic φ) (hH : hamiltonian φ = 0) :
    v0PairSandwichForm A ψ φ = 0 := by
  have hB := (hamiltonian_zero_iff_v0PairAnnihilate_zero φ hφ).mp hH
  simp [v0PairSandwichForm, hB, inner]

theorem v0PairSandwichForm_left_zero {Q N : ℕ}
    (A : Fin (2*Q+1) → Fin (2*Q+1) → State Q N →ₗ[ℂ] State Q N)
    (ψ φ : State Q (N+2)) (hψ : IsBosonic ψ) (hH : hamiltonian ψ = 0) :
    v0PairSandwichForm A ψ φ = 0 := by
  have hB := (hamiltonian_zero_iff_v0PairAnnihilate_zero ψ hψ).mp hH
  simp [v0PairSandwichForm, hB, inner]

/-- Left factors may in particular be pair creators composed with auxiliary operators. -/
def v0PairRightFactoredOperator (Q N : ℕ)
    (L : Fin (2*Q+1) → Fin (2*Q+1) → State Q N →ₗ[ℂ] State Q (N+2)) :
    State Q (N+2) →ₗ[ℂ] State Q (N+2) :=
  ∑ p, ∑ q, (L p q).comp (v0PairAnnihilateLinear Q N q)

theorem v0PairRightFactoredOperator_kernel_zero {Q N : ℕ}
    (L : Fin (2*Q+1) → Fin (2*Q+1) → State Q N →ₗ[ℂ] State Q (N+2))
    (φ : State Q (N+2)) (hφ : IsBosonic φ) (hH : hamiltonian φ = 0) :
    v0PairRightFactoredOperator Q N L φ = 0 := by
  have hB := (hamiltonian_zero_iff_v0PairAnnihilate_zero φ hφ).mp hH
  simp [v0PairRightFactoredOperator, LinearMap.sum_apply, LinearMap.comp_apply,
    v0PairAnnihilateLinear, hB]

/-- A physical operator represented by the actual pair-sandwich form annihilates
the physical Hamiltonian kernel. Bosonic range is needed for nondegenerate testing. -/
theorem operator_kernel_zero_of_v0PairSandwichForm {Q N : ℕ}
    (A : Fin (2*Q+1) → Fin (2*Q+1) → State Q N →ₗ[ℂ] State Q N)
    (C : State Q (N+2) →ₗ[ℂ] State Q (N+2))
    (hC : ∀ χ, IsBosonic χ → IsBosonic (C χ))
    (hform : ∀ ψ φ, IsBosonic ψ → IsBosonic φ → inner ψ (C φ) = v0PairSandwichForm A ψ φ)
    (φ : State Q (N+2)) (hφ : IsBosonic φ) (hH : hamiltonian φ = 0) : C φ = 0 := by
  apply (stateNormSq_zero_iff (C φ)).mp
  unfold normSq
  rw [hform (C φ) φ (hC φ hφ) hφ,
    v0PairSandwichForm_right_zero A (C φ) φ hφ hH]
  rfl

theorem pairApply_product_kernel_zero {Q N : ℕ} (i j k l : Fin N)
    (hkl : k ≠ l) (ψ : State Q N) (hH : hamiltonian ψ = 0) :
    pairApply i j (pairApply k l ψ) = 0 := by
  rw [(hamiltonian_zero_iff_pairs_zero ψ).mp hH k l hkl]
  exact (pairApplyLinear Q N i j).map_zero

theorem normalThreeBody_kernel_zero {Q N : ℕ} (ψ : State Q N)
    (hH : hamiltonian ψ = 0) : normalThreeBodyApply ψ = 0 := by
  funext a
  simp only [normalThreeBodyApply, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with hij
  · apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    split_ifs with hkl ho
    · exact congrFun (pairApply_product_kernel_zero i j k l (ne_of_lt hkl) ψ hH) a
    · rfl
    · rfl
  · rfl

theorem normalFourBody_kernel_zero {Q N : ℕ} (ψ : State Q N)
    (hH : hamiltonian ψ = 0) : normalFourBodyApply ψ = 0 := by
  funext a
  simp only [normalFourBodyApply, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with hij
  · apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    split_ifs with hkl hd
    · exact congrFun (pairApply_product_kernel_zero i j k l (ne_of_lt hkl) ψ hH) a
    · rfl
    · rfl
  · rfl

theorem threeBodyAdjoint_eq_v0PairAnnihilate {Q : ℕ} (ψ : State Q 3)
    (p : Fin (2*Q+1)) (k : Orbital Q) :
    threeBodyAdjoint ψ p k = v0PairAnnihilate (N:=1) p ψ (fun _ => k) := by
  have hc (x y : Orbital Q) :
      (Fin.cons x (Fin.cons y (fun _ : Fin 1 => k)) : Configuration Q 3) = ![x,y,k] := by
    funext i
    fin_cases i <;> rfl
  simp only [threeBodyAdjoint, v0PairAnnihilate, v0PairAmplitude, hc]
  norm_num

theorem threeBodyAdjoint_kernel_zero {Q : ℕ} (ψ : State Q 3)
    (hψ : IsBosonic ψ) (hH : hamiltonian ψ = 0) : threeBodyAdjoint ψ = 0 := by
  have hB := (hamiltonian_zero_iff_v0PairAnnihilate_zero (N:=1) ψ hψ).mp hH
  funext p k
  rw [threeBodyAdjoint_eq_v0PairAnnihilate, hB p]
  rfl

theorem threeBodyAuxCoefficient_kernel_zero {Q : ℕ}
    (A : ThreeBodyAux Q →ₗ[ℂ] ThreeBodyAux Q) (ψ : State Q 3)
    (hψ : IsBosonic ψ) (hH : hamiltonian ψ = 0) : threeBodyAuxCoefficient Q A ψ = 0 := by
  rw [threeBodyAuxCoefficient_apply, threeBodyAdjoint_kernel_zero ψ hψ hH, map_zero]
  exact (threeBodyMapLinear Q).map_zero

theorem threeBodySpectralBlock_kernel_zero {Q : ℕ} (z : Fin (Q+1)) (ψ : State Q 3)
    (hψ : IsBosonic ψ) (hH : hamiltonian ψ = 0) : threeBodySpectralBlock Q z ψ = 0 :=
  threeBodyAuxCoefficient_kernel_zero (compressedSwapProjectorLinear Q z) ψ hψ hH

end
end BosonicLaughlin

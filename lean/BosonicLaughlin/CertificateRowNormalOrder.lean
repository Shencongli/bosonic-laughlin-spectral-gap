import BosonicLaughlin.LowSectorTransfer

/-! Actual normal ordering of a finite selected certificate row in the
three- and four-particle input sectors. Coefficients may be complex. -/
namespace BosonicLaughlin
noncomputable section
open Finset

theorem stateInner_add_left {Q N : ℕ} (ψ φ χ : State Q N) :
    inner (ψ+φ) χ=inner ψ χ+inner φ χ := by
  simp [inner, star_add, add_mul, Finset.sum_add_distrib]

theorem stateInner_sum_right {Q N : ℕ} {ι : Type*} [Fintype ι]
    (ψ : State Q N) (φ : ι → State Q N) :
    inner ψ (∑ a, φ a)=∑ a, inner ψ (φ a) := by
  simp only [inner, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem stateInner_sum_left {Q N : ℕ} {ι : Type*} [Fintype ι]
    (ψ : ι → State Q N) (φ : State Q N) :
    inner (∑ a, ψ a) φ=∑ a, inner (ψ a) φ := by
  simp only [inner, Finset.sum_apply, star_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem stateInner_row_expansion {Q N : ℕ} {ι : Type*} [Fintype ι]
    (leading : ℂ) (α : ι → ℂ) (u v : State Q N) (ψ φ : ι → State Q N) :
    inner (leading • u+∑ a, α a • ψ a) (leading • v+∑ a, α a • φ a) =
      star leading*leading*inner u v +
      (∑ a, (star leading*α a*inner u (φ a)+star (α a)*leading*inner (ψ a) v)) +
      ∑ a, ∑ b, star (α a)*α b*inner (ψ a) (φ b) := by
  simp only [stateInner_add_left, stateInner_add_right]
  simp only [stateInner_sum_left]
  simp only [stateInner_sum_right]
  simp only [stateInner_smul_left, stateInner_smul_right, Finset.sum_add_distrib, mul_assoc]
  simp only [mul_comm, mul_assoc, add_left_comm, add_assoc]

theorem orbitalTransfer_inner_one_left {Q : ℕ} (i j : Orbital Q) (ψ φ : State Q 1) :
    inner (orbitalTransfer i j ψ) φ=
      inner (annihilate (Pi.single j 1) ψ) (annihilate (Pi.single i 1) φ) := by
  rw [← inner_star φ, orbitalTransfer_inner_one, inner_star]

theorem orbitalTransfer_inner_two_left {Q : ℕ} (i j : Orbital Q) (ψ φ : State Q 2)
    (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner (orbitalTransfer i j ψ) φ=
      inner (annihilate (Pi.single j 1) ψ) (annihilate (Pi.single i 1) φ) := by
  rw [← inner_star φ, orbitalTransfer_inner_two i j φ ψ hφ hψ, inner_star]

/-- A finite list of spectator transfers, from N+2 to N physical particles. -/
def selectedCertificateRow {ι : Type*} [Fintype ι] (Q N : ℕ)
    (t : Fin (2*Q+1)) (leading : ℂ) (p : ι → Fin (2*Q+1))
    (i j : ι → Orbital Q) (α : ι → ℂ) : State Q (N+2) →ₗ[ℂ] State Q N :=
  leading • v0PairAnnihilateLinear Q N t + ∑ a,
    α a • (orbitalTransferLinear Q N (i a) (j a)).comp (v0PairAnnihilateLinear Q N (p a))

theorem selectedCertificateRow_apply {ι : Type*} [Fintype ι] (Q N : ℕ)
    (t : Fin (2*Q+1)) (leading : ℂ) (p : ι → Fin (2*Q+1))
    (i j : ι → Orbital Q) (α : ι → ℂ) (ψ : State Q (N+2)) :
    selectedCertificateRow Q N t leading p i j α ψ =
      leading • v0PairAnnihilate t ψ+∑ a, α a • orbitalTransfer (i a) (j a) (v0PairAnnihilate (p a) ψ) := by
  simp only [selectedCertificateRow, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply]
  rfl

theorem selectedCertificateRow_all_terms (Q N : ℕ) (t : Fin (2*Q+1)) (leading : ℂ)
    (coefficient : Fin (2*Q+1) → Orbital Q → Orbital Q → ℂ) :
    selectedCertificateRow (ι := Fin (2*Q+1) × Orbital Q × Orbital Q) Q N t leading
      (fun a => a.1) (fun a => a.2.1) (fun a => a.2.2)
      (fun a => coefficient a.1 a.2.1 a.2.2)=certificateRow Q N t leading coefficient := by
  simp only [selectedCertificateRow, certificateRow, Fintype.sum_prod_type]

theorem selectedCertificateRow_annihilates_kernel {Q N : ℕ} {ι : Type*} [Fintype ι]
    (t : Fin (2*Q+1)) (leading : ℂ) (p : ι → Fin (2*Q+1))
    (i j : ι → Orbital Q) (α : ι → ℂ) (ψ : State Q (N+2))
    (hψ : IsBosonic ψ) (hH : hamiltonian ψ=0) :
    selectedCertificateRow Q N t leading p i j α ψ=0 := by
  have hB := (hamiltonian_zero_iff_v0PairAnnihilate_zero ψ hψ).mp hH
  have h0 (a : ι) : orbitalTransfer (i a) (j a) (0 : State Q N)=0 :=
    (orbitalTransferLinear Q N (i a) (j a)).map_zero
  rw [selectedCertificateRow_apply]
  simp [hB, h0]

def certificateRowTwoForm {Q N : ℕ} (t : Fin (2*Q+1)) (leading : ℂ)
    (ψ φ : State Q (N+2)) : ℂ :=
  star leading*leading*inner (v0PairAnnihilate t ψ) (v0PairAnnihilate t φ)

def certificateRowThreeForm {Q N : ℕ} {ι : Type*} [Fintype ι]
    (t : Fin (2*Q+1)) (leading : ℂ) (p : ι → Fin (2*Q+1))
    (i j : ι → Orbital Q) (α : ι → ℂ) (ψ φ : State Q (N+3)) : ℂ :=
  (∑ a,
    (star leading*α a*inner
      (annihilate (Pi.single (i a) 1) (v0PairAnnihilate t ψ))
      (annihilate (Pi.single (j a) 1) (v0PairAnnihilate (p a) φ)) +
    star (α a)*leading*inner
      (annihilate (Pi.single (j a) 1) (v0PairAnnihilate (p a) ψ))
      (annihilate (Pi.single (i a) 1) (v0PairAnnihilate t φ)))) +
  ∑ a, ∑ b, star (α a)*α b*(if i a=i b then inner
    (annihilate (Pi.single (j a) 1) (v0PairAnnihilate (p a) ψ))
    (annihilate (Pi.single (j b) 1) (v0PairAnnihilate (p b) φ)) else 0)

def certificateRowFourForm {Q N : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → Fin (2*Q+1)) (i j : ι → Orbital Q) (α : ι → ℂ)
    (ψ φ : State Q (N+4)) : ℂ :=
  ∑ a, ∑ b, star (α a)*α b*inner
    (annihilate (Pi.single (i b) 1) (annihilate (Pi.single (j a) 1) (v0PairAnnihilate (p a) ψ)))
    (annihilate (Pi.single (i a) 1) (annihilate (Pi.single (j b) 1) (v0PairAnnihilate (p b) φ)))

theorem selectedCertificateRow_normal_order_three {Q : ℕ} {ι : Type*} [Fintype ι]
    (t : Fin (2*Q+1)) (leading : ℂ) (p : ι → Fin (2*Q+1))
    (i j : ι → Orbital Q) (α : ι → ℂ) (ψ φ : State Q 3) :
    inner (selectedCertificateRow Q 1 t leading p i j α ψ) (selectedCertificateRow Q 1 t leading p i j α φ) =
      certificateRowTwoForm t leading ψ φ + certificateRowThreeForm t leading p i j α ψ φ := by
  rw [selectedCertificateRow_apply, selectedCertificateRow_apply, stateInner_row_expansion]
  simp only [orbitalTransfer_gram_one]
  simp only [orbitalTransfer_inner_one, orbitalTransfer_inner_one_left,
    certificateRowTwoForm, certificateRowThreeForm]
  ring

theorem selectedCertificateRow_normal_order_four {Q : ℕ} {ι : Type*} [Fintype ι]
    (t : Fin (2*Q+1)) (leading : ℂ) (p : ι → Fin (2*Q+1))
    (i j : ι → Orbital Q) (α : ι → ℂ) (ψ φ : State Q 4)
    (hψ : IsBosonic ψ) (hφ : IsBosonic φ) :
    inner (selectedCertificateRow Q 2 t leading p i j α ψ) (selectedCertificateRow Q 2 t leading p i j α φ) =
      certificateRowTwoForm t leading ψ φ + certificateRowThreeForm t leading p i j α ψ φ +
        certificateRowFourForm p i j α ψ φ := by
  rw [selectedCertificateRow_apply, selectedCertificateRow_apply, stateInner_row_expansion]
  have hu (a : Fin (2*Q+1)) := v0PairAnnihilate_isBosonic a ψ hψ
  have hv (a : Fin (2*Q+1)) := v0PairAnnihilate_isBosonic a φ hφ
  simp only [orbitalTransfer_inner_two _ _ _ _ (hu _) (hv _),
    orbitalTransfer_inner_two_left _ _ _ _ (hu _) (hv _),
    orbitalTransfer_gram_two _ _ _ _ _ _ (hu _) (hv _),
    certificateRowTwoForm, certificateRowThreeForm, certificateRowFourForm,
    mul_add, Finset.sum_add_distrib]
  ring

theorem certificateRow_three_parts_nonneg {Q : ℕ} {ι : Type*} [Fintype ι]
    (t : Fin (2*Q+1)) (leading : ℂ) (p : ι → Fin (2*Q+1))
    (i j : ι → Orbital Q) (α : ι → ℂ) (ψ : State Q 3) :
    0≤(certificateRowTwoForm t leading ψ ψ+certificateRowThreeForm t leading p i j α ψ ψ).re := by
  rw [← selectedCertificateRow_normal_order_three t leading p i j α ψ ψ]
  exact stateNormSq_nonneg _

theorem certificateRow_four_parts_nonneg {Q : ℕ} {ι : Type*} [Fintype ι]
    (t : Fin (2*Q+1)) (leading : ℂ) (p : ι → Fin (2*Q+1))
    (i j : ι → Orbital Q) (α : ι → ℂ) (ψ : State Q 4) (hψ : IsBosonic ψ) :
    0≤(certificateRowTwoForm t leading ψ ψ+certificateRowThreeForm t leading p i j α ψ ψ+
      certificateRowFourForm p i j α ψ ψ).re := by
  rw [← selectedCertificateRow_normal_order_four t leading p i j α ψ ψ hψ hψ]
  exact stateNormSq_nonneg _

end
end BosonicLaughlin

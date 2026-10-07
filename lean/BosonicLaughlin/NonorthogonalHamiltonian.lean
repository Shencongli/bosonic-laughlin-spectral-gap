import BosonicLaughlin.PhysicalComparisonForms

/-! The inverse metric in the Hamiltonian square is forced by the actual
physical coordinate map, rather than inserted as a convention. -/
namespace BosonicLaughlin
noncomputable section
open Finset
open scoped Matrix ComplexOrder

def physicalFrameMetric {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) : Matrix I I ℂ :=
  (physicalFrameMatrix P)ᴴ * physicalFrameMatrix P

theorem physicalFrameMetric_eq_form {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) :
    physicalFrameMetric P=physicalFormMatrix P LinearMap.id := by
  simp [physicalFrameMetric, physicalFormMatrix]

theorem physicalFrameMetric_apply {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (i j : I) :
    physicalFrameMetric P i j=inner (P (Pi.single i 1)) (P (Pi.single j 1)) := by
  rw [physicalFrameMetric_eq_form, physicalFormMatrix_apply]
  rfl

theorem physical_coordinate_action {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (A : State Q N →ₗ[ℂ] State Q N)
    (R : Matrix I I ℂ) (hR : R * physicalFrameMetric P=1)
    (hclosed : ∀ v, ∃ w, P w=A (P v)) (v : I → ℂ) :
    P ((R * physicalFormMatrix P A) *ᵥ v)=A (P v) := by
  obtain ⟨w,hw⟩ := hclosed v
  have hf : physicalFormMatrix P A *ᵥ v=physicalFrameMetric P *ᵥ w := by
    simp only [physicalFormMatrix, physicalFrameMetric, ← Matrix.mulVec_mulVec,
      physicalFrameMatrix_mulVec, LinearMap.toMatrix'_mulVec, hw]
  rw [← Matrix.mulVec_mulVec, hf, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec, hw]

theorem physicalFormMatrix_square {I : Type*} [Fintype I] [DecidableEq I] {Q N : ℕ}
    (P : (I → ℂ) →ₗ[ℂ] State Q N) (A : State Q N →ₗ[ℂ] State Q N)
    (R : Matrix I I ℂ) (hR : R * physicalFrameMetric P=1)
    (hclosed : ∀ v, ∃ w, P w=A (P v)) :
    physicalFormMatrix P (A.comp A)=physicalFormMatrix P A * R * physicalFormMatrix P A := by
  have ha : LinearMap.toMatrix' A * physicalFrameMatrix P =
      physicalFrameMatrix P * (R * physicalFormMatrix P A) := by
    apply Matrix.ext
    intro i j
    have h := congrFun (physical_coordinate_action P A R hR hclosed (Pi.single j 1)) i
    simpa only [← physicalFrameMatrix_mulVec, ← LinearMap.toMatrix'_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, physicalFrameMatrix] using h.symm
  simp only [physicalFormMatrix, LinearMap.toMatrix'_comp]
  calc
    _ = (physicalFrameMatrix P)ᴴ * LinearMap.toMatrix' A *
        (LinearMap.toMatrix' A * physicalFrameMatrix P) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha]; simp only [physicalFormMatrix, Matrix.mul_assoc]

def certificateMetricMatrix (Q N d : ℕ) : Matrix (WeightOccupation Q N d) (WeightOccupation Q N d) ℂ :=
  Matrix.diagonal (fun A => (certificateMetricWeight A.val : ℂ))

def certificateInverseMetric (Q N d : ℕ) : Matrix (WeightOccupation Q N d) (WeightOccupation Q N d) ℂ :=
  Matrix.diagonal (fun A => (certificateMetricWeight A.val : ℂ)⁻¹)

theorem certificateMetricMatrix_physical {Q N d : ℕ} (hQ : 0<Q) :
    certificateMetricMatrix Q N d = physicalFrameMetric (certificateWeightCoordinates Q N d) := by
  ext i j
  rw [physicalFrameMetric_apply, certificateWeightCoordinates_inner hQ]
  by_cases hij : i=j
  · subst j; simp [certificateMetricMatrix, certificateInner, Pi.single_apply, Matrix.diagonal_apply, mul_ite]
  · simp [certificateMetricMatrix, certificateInner, Pi.single_apply, Matrix.diagonal_apply, mul_ite, hij, Ne.symm hij]

theorem certificateInverseMetric_mul {Q N d : ℕ} (hQ : 0<Q) :
    certificateInverseMetric Q N d * certificateMetricMatrix Q N d=1 := by
  rw [certificateInverseMetric, certificateMetricMatrix, Matrix.diagonal_mul_diagonal]
  have hn (A : WeightOccupation Q N d) : (certificateMetricWeight A.val : ℂ)≠0 := by
    exact_mod_cast (certificateMetricWeight_pos hQ A.val).ne'
  simp [hn]

theorem certificate_hamiltonian_closed {Q N d : ℕ} (hQ : 0<Q) (v : WeightOccupationState Q N d) :
    ∃ w, certificateWeightCoordinates Q N d w=hamiltonian (certificateWeightCoordinates Q N d v) := by
  apply certificateWeightCoordinates_surjective_bosonic_weight hQ
  · exact hamiltonian_isBosonic _ (certificateWeightCoordinates_isBosonic Q N d v)
  · exact hamiltonian_weightSupported d _ (certificateWeightCoordinates_weightSupported hQ N d v)

theorem certificateHamiltonian_coordinate_action {Q N d : ℕ} (hQ : 0<Q)
    (v : WeightOccupationState Q N d) :
    certificateWeightCoordinates Q N d
      ((certificateInverseMetric Q N d * certificateHamiltonianFormMatrix Q N d) *ᵥ v) =
      hamiltonian (certificateWeightCoordinates Q N d v) := by
  rw [certificateHamiltonianFormMatrix_eq_pullback]
  apply physical_coordinate_action
  · rw [← certificateMetricMatrix_physical hQ]
    exact certificateInverseMetric_mul hQ
  · exact certificate_hamiltonian_closed hQ

theorem certificateHamiltonian_square_form {Q N d : ℕ} (hQ : 0<Q) :
    physicalFormMatrix (certificateWeightCoordinates Q N d)
      ((hamiltonianLinear Q N).comp (hamiltonianLinear Q N)) =
      certificateHamiltonianFormMatrix Q N d * certificateInverseMetric Q N d *
        certificateHamiltonianFormMatrix Q N d := by
  rw [certificateHamiltonianFormMatrix_eq_pullback]
  apply physicalFormMatrix_square
  · rw [← certificateMetricMatrix_physical hQ]
    exact certificateInverseMetric_mul hQ
  · exact certificate_hamiltonian_closed hQ

theorem certificateThreeBody_target_form {Q d : ℕ} (hQ : 0<Q) :
    physicalFormMatrix (certificateWeightCoordinates Q 3 d) (normalThreeBodyLinear Q 3) =
      certificateHamiltonianFormMatrix Q 3 d * certificateInverseMetric Q 3 d *
        certificateHamiltonianFormMatrix Q 3 d - certificateHamiltonianFormMatrix Q 3 d := by
  have h : normalThreeBodyLinear Q 3=
      (hamiltonianLinear Q 3).comp (hamiltonianLinear Q 3)-hamiltonianLinear Q 3 := by
    apply LinearMap.ext
    intro ψ
    funext a
    have he := congrFun (three_particle_square ψ) a
    change normalThreeBodyApply ψ a = hamiltonian (hamiltonian ψ) a - hamiltonian ψ a
    exact eq_sub_of_add_eq' he.symm
  rw [h, physicalFormMatrix_sub, certificateHamiltonian_square_form hQ,
    ← certificateHamiltonianFormMatrix_eq_pullback]

end
end BosonicLaughlin

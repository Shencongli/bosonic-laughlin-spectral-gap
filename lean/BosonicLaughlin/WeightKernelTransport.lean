import BosonicLaughlin.PolynomialWeightCoordinates
import BosonicLaughlin.OrbitalCapKernel

/-! Exact transport of the physical bosonic zero space at fixed total weight.
The transport is a linear equivalence of kernels, not a spectral equivalence. -/
namespace BosonicLaughlin
noncomputable section

/-- Convert physical coefficients to polynomial coefficients, remove the inactive
orbital cap, and convert back using the target physical normalization. -/
def weightKernelTransport {Q N d : ℕ} (hd : d ≤ Q) :
    WeightState Q N d ≃ₗ[ℂ] WeightState d N d :=
  (polynomialWeightCoordinates Q N d).trans
    ((capWeightStateEquiv hd).trans (polynomialWeightCoordinates d N d).symm)

theorem weightKernelTransport_polynomial {Q N d : ℕ} (hd : d ≤ Q)
    (φ : WeightState Q N d) :
    polynomialWeightCoordinates d N d (weightKernelTransport hd φ) =
      capWeightStateEquiv hd (polynomialWeightCoordinates Q N d φ) := by
  exact (polynomialWeightCoordinates d N d).apply_symm_apply _

theorem weightKernelTransport_bosonic_iff {Q N d : ℕ} (hd : d ≤ Q)
    (φ : WeightState Q N d) :
    WeightIsBosonic (weightKernelTransport hd φ) ↔ WeightIsBosonic φ := by
  rw [← polynomialWeightCoordinates_bosonic_iff, weightKernelTransport_polynomial,
    capWeightStateEquiv_bosonic_iff, polynomialWeightCoordinates_bosonic_iff]

/-- The actual physical block has the same zero condition after transport. -/
theorem weightKernelTransport_kernel_iff {Q N d : ℕ} (hd : d ≤ Q)
    (φ : WeightState Q (N+2) d) (hφ : WeightIsBosonic φ) :
    weightHamiltonian d (N+2) d (weightKernelTransport hd φ) = 0 ↔
      weightHamiltonian Q (N+2) d φ = 0 := by
  rw [weightHamiltonian_zero_iff_polynomialChannels _
      ((weightKernelTransport_bosonic_iff hd φ).mpr hφ),
    weightHamiltonian_zero_iff_polynomialChannels φ hφ,
    weightKernelTransport_polynomial]
  exact (capWeightStateEquiv_pairKernel_iff hd _).symm

/-- Physical bosonic zero modes in the total-weight block, as a subspace of
the ordered tensor coefficient space. -/
def physicalWeightKernel (Q N d : ℕ) : Submodule ℂ (WeightState Q N d) :=
  (bosonicSubspace Q N).comap (weightIncludeLinear Q N d) ⊓
    LinearMap.ker (weightHamiltonian Q N d)

theorem mem_physicalWeightKernel {Q N d : ℕ} (φ : WeightState Q N d) :
    φ ∈ physicalWeightKernel Q N d ↔
      WeightIsBosonic φ ∧ weightHamiltonian Q N d φ = 0 := Iff.rfl

theorem weightKernelTransport_mem_iff {Q N d : ℕ} (hd : d ≤ Q)
    (φ : WeightState Q (N+2) d) :
    weightKernelTransport hd φ ∈ physicalWeightKernel d (N+2) d ↔
      φ ∈ physicalWeightKernel Q (N+2) d := by
  rw [mem_physicalWeightKernel, mem_physicalWeightKernel]
  constructor
  · rintro ⟨hB, hH⟩
    have hφ := (weightKernelTransport_bosonic_iff hd φ).mp hB
    exact ⟨hφ, (weightKernelTransport_kernel_iff hd φ hφ).mp hH⟩
  · rintro ⟨hφ, hH⟩
    exact ⟨(weightKernelTransport_bosonic_iff hd φ).mpr hφ,
      (weightKernelTransport_kernel_iff hd φ hφ).mpr hH⟩

/-- The kernel equivalence is explicit; neither a stable-rank assumption nor
a dimension formula is used to construct its inverse. -/
def physicalWeightKernelEquiv {Q N d : ℕ} (hd : d ≤ Q) :
    physicalWeightKernel Q (N+2) d ≃ₗ[ℂ] physicalWeightKernel d (N+2) d where
  toFun φ := ⟨weightKernelTransport hd φ.val,
    (weightKernelTransport_mem_iff hd φ.val).mpr φ.property⟩
  invFun χ := ⟨(weightKernelTransport hd).symm χ.val, by
    apply (weightKernelTransport_mem_iff hd _).mp
    simpa only [LinearEquiv.apply_symm_apply] using χ.property⟩
  left_inv φ := by apply Subtype.ext; exact (weightKernelTransport hd).symm_apply_apply φ.val
  right_inv χ := by apply Subtype.ext; exact (weightKernelTransport hd).apply_symm_apply χ.val
  map_add' φ χ := by apply Subtype.ext; exact (weightKernelTransport hd).map_add φ.val χ.val
  map_smul' c φ := by
    apply Subtype.ext
    exact (weightKernelTransport hd).map_smul c φ.val

theorem physicalWeightKernel_finrank_stable {Q N d : ℕ} (hd : d ≤ Q) :
    Module.finrank ℂ (physicalWeightKernel Q (N+2) d) =
      Module.finrank ℂ (physicalWeightKernel d (N+2) d) :=
  (physicalWeightKernelEquiv (N := N) hd).finrank_eq

end
end BosonicLaughlin

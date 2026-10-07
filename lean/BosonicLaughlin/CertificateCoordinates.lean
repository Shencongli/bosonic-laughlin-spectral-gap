import BosonicLaughlin.CertificateNormalization
import BosonicLaughlin.OccupationPairBlocks

/-!
Actual physical coordinates for the polynomial certificate basis.
The normalization is alpha = sqrt(Q^d/N!), in addition to the inverse spherical
diagonal and the occupation factorial. For Q>0 the map is complete and injective
on every bosonic weight sector. Its metric is not asserted to be Euclidean.
-/
namespace BosonicLaughlin
noncomputable section

theorem certificateSectorScale_complex_ne_zero {Q N d : ℕ} (hQ : 0<Q) :
    (certificateSectorScale Q N d : ℂ) ≠ 0 := by
  exact_mod_cast (certificateSectorScale_pos hQ N d).ne'

def certificateCoordinates (Q N d : ℕ) : OccupationState Q N →ₗ[ℂ] State Q N :=
  (certificateSectorScale Q N d : ℂ) •
    ((polynomialCoordinates Q N).symm.toLinearMap.comp (polynomialOccupationIncludeLinear Q N))

theorem certificateCoordinates_apply (Q N d : ℕ) (c : OccupationState Q N) :
    certificateCoordinates Q N d c = (certificateSectorScale Q N d : ℂ) •
      (polynomialCoordinates Q N).symm (polynomialOccupationInclude c) := rfl

theorem certificateCoordinates_polynomial (Q N d : ℕ) (c : OccupationState Q N) :
    polynomialCoordinates Q N (certificateCoordinates Q N d c) =
      (certificateSectorScale Q N d : ℂ) • polynomialOccupationInclude c := by
  rw [certificateCoordinates_apply, map_smul, LinearEquiv.apply_symm_apply]

theorem certificateCoordinates_isBosonic (Q N d : ℕ) (c : OccupationState Q N) :
    IsBosonic (certificateCoordinates Q N d c) := by
  apply (polynomialCoordinates_bosonic_iff _).mp
  rw [certificateCoordinates_polynomial]
  exact (bosonicSubspace Q N).smul_mem _ (polynomialOccupationInclude_isBosonic c)

theorem certificateCoordinates_injective {Q : ℕ} (hQ : 0<Q) (N d : ℕ) :
    Function.Injective (certificateCoordinates Q N d) := by
  intro c e h
  apply polynomialOccupationInclude_injective Q N
  have he := congrArg (polynomialCoordinates Q N) h
  rw [certificateCoordinates_polynomial, certificateCoordinates_polynomial] at he
  exact smul_right_injective (State Q N) (certificateSectorScale_complex_ne_zero hQ) he

theorem certificateCoordinates_surjective_bosonic {Q : ℕ} (hQ : 0<Q) (N d : ℕ)
    (ψ : State Q N) (hψ : IsBosonic ψ) : ∃ c, certificateCoordinates Q N d c = ψ := by
  have hs := certificateSectorScale_complex_ne_zero (N:=N) (d:=d) hQ
  have hp : IsBosonic ((certificateSectorScale Q N d : ℂ)⁻¹ • polynomialCoordinates Q N ψ) :=
    (bosonicSubspace Q N).smul_mem _ ((polynomialCoordinates_bosonic_iff ψ).mpr hψ)
  obtain ⟨c,hc⟩ := polynomialOccupationInclude_surjective_bosonic _ hp
  refine ⟨c, ?_⟩
  rw [certificateCoordinates_apply, hc, map_smul, LinearEquiv.symm_apply_apply,
    smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem certificateCoordinates_weightSupported_iff {Q : ℕ} (hQ : 0<Q) (N d : ℕ)
    (c : OccupationState Q N) :
    WeightSupported d (certificateCoordinates Q N d c) ↔ OccupationWeightSupported d c := by
  constructor
  · intro hc A hA
    have hw : configurationWeight (occupationRepresentative A) ≠ d := by
      rw [← occupationOfConfiguration_weight, occupationOfConfiguration_representative]
      exact hA
    have hz := hc (occupationRepresentative A) hw
    have hz' : polynomialCoordinates Q N (certificateCoordinates Q N d c)
        (occupationRepresentative A) = 0 := by
      rw [polynomialCoordinates_apply, hz, mul_zero]
    rw [certificateCoordinates_polynomial] at hz'
    simp only [Pi.smul_apply, smul_eq_mul, polynomialOccupationInclude,
      occupationOfConfiguration_representative] at hz'
    have hf : (occupationFactorial A : ℂ) ≠ 0 := by exact_mod_cast (occupationFactorial_pos A).ne'
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left
      (certificateSectorScale_complex_ne_zero hQ))).resolve_left hf
  · intro hc a ha
    have hw : occupationWeight (occupationOfConfiguration a) ≠ d := by
      simpa only [occupationOfConfiguration_weight] using ha
    simp [certificateCoordinates_apply, polynomialCoordinates_symm_apply,
      polynomialOccupationInclude, hc _ hw]

def certificateWeightCoordinates (Q N d : ℕ) :
    WeightOccupationState Q N d →ₗ[ℂ] State Q N :=
  (certificateCoordinates Q N d).comp (occupationWeightExtendLinear Q N d)

theorem certificateWeightCoordinates_apply (Q N d : ℕ) (c : WeightOccupationState Q N d) :
    certificateWeightCoordinates Q N d c =
      certificateCoordinates Q N d (occupationWeightExtend d c) := rfl

theorem certificateWeightCoordinates_polynomial (Q N d : ℕ) (c : WeightOccupationState Q N d) :
    polynomialCoordinates Q N (certificateWeightCoordinates Q N d c) =
      (certificateSectorScale Q N d : ℂ) • weightInclude d (polynomialWeightOccupationInclude c) := by
  rw [certificateWeightCoordinates_apply, certificateCoordinates_polynomial,
    polynomialWeightOccupationInclude_include]

theorem certificateWeightCoordinates_isBosonic (Q N d : ℕ) (c : WeightOccupationState Q N d) :
    IsBosonic (certificateWeightCoordinates Q N d c) :=
  certificateCoordinates_isBosonic Q N d _

theorem certificateWeightCoordinates_weightSupported {Q : ℕ} (hQ : 0<Q) (N d : ℕ)
    (c : WeightOccupationState Q N d) : WeightSupported d (certificateWeightCoordinates Q N d c) :=
  (certificateCoordinates_weightSupported_iff hQ N d _).mpr (occupationWeightExtend_supported c)

theorem certificateWeightCoordinates_injective {Q : ℕ} (hQ : 0<Q) (N d : ℕ) :
    Function.Injective (certificateWeightCoordinates Q N d) := by
  intro c e h
  have he : occupationWeightExtend d c = occupationWeightExtend d e :=
    certificateCoordinates_injective hQ N d h
  have hr := congrArg (occupationWeightRestrict d) he
  simpa only [occupationWeightRestrict_extend] using hr

theorem certificateWeightCoordinates_surjective_bosonic_weight {Q : ℕ} (hQ : 0<Q) (N d : ℕ)
    (ψ : State Q N) (hψ : IsBosonic ψ) (hw : WeightSupported d ψ) :
    ∃ c, certificateWeightCoordinates Q N d c = ψ := by
  obtain ⟨c,hc⟩ := certificateCoordinates_surjective_bosonic hQ N d ψ hψ
  have hs : OccupationWeightSupported d c :=
    (certificateCoordinates_weightSupported_iff hQ N d c).mp (by rw [hc]; exact hw)
  refine ⟨occupationWeightRestrict d c, ?_⟩
  rw [certificateWeightCoordinates_apply, occupationWeightExtend_restrict_supported d c hs, hc]

theorem certificateCoordinates_hamiltonian_kernel {Q N d : ℕ} (hQ : 0<Q)
    (c : OccupationState Q (N+2)) :
    hamiltonian (certificateCoordinates Q (N+2) d c) = 0 ↔
      ∀ p : Fin (2*Q+1), (occupationPairMatrix Q N p.val).mulVec c = 0 := by
  rw [certificateCoordinates_apply, hamiltonian_smul,
    smul_eq_zero, or_iff_right (certificateSectorScale_complex_ne_zero hQ)]
  have h := polynomialHamiltonian_occupation_kernel c
  rw [polynomialHamiltonian_apply, (polynomialCoordinates Q (N+2)).map_eq_zero_iff] at h
  exact h

theorem certificateWeightCoordinates_hamiltonian_kernel {Q N d : ℕ} (hQ : 0<Q)
    (c : WeightOccupationState Q (N+2) d) :
    hamiltonian (certificateWeightCoordinates Q (N+2) d c) = 0 ↔
      ∀ p : Fin (2*Q+1), (occupationPairBlockMatrix Q N d p.val).mulVec c = 0 := by
  rw [certificateWeightCoordinates_apply, certificateCoordinates_hamiltonian_kernel hQ]
  simp only [occupationPairMatrix_mulVec, occupationPairBlockMatrix_mulVec]
  exact forall_congr' (fun p => (occupationPairBlock_zero_iff Q N d p.val c).symm)

end
end BosonicLaughlin

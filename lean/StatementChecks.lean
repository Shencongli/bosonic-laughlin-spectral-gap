import BosonicLaughlin
open scoped Matrix

/-! These contracts keep the physical model, quantifiers, and hypotheses of
the published results explicit. They must elaborate without assuming an
occupation inequality, a normal-order identity, or a spectral-gap estimate. -/
open BosonicLaughlin
open scoped ComplexOrder

example (Q N : ℕ) (u v : ℂ) (h : Complex.normSq u + Complex.normSq v = 1)
    (ψ : State Q N) :
    modeOccupation (coherentOrbital Q u v) ψ ≤ energy ψ + normSq ψ :=
  coherent_occupation_bound u v h ψ

example (Q N : ℕ) (u v : ℂ) (h : Complex.normSq u + Complex.normSq v = 1)
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    normSq (pairAnnihilate (coherentOrbital Q u v) ψ) ≤ energy ψ :=
  coherent_pairAnnihilation_bound u v h ψ hψ

example (Q N : ℕ) (α : Orbital Q → ℂ) (u v : ℂ)
    (h : Complex.normSq u + Complex.normSq v = 1) (ψ : State Q (N+2)) :
    modeOccupation (coherentOrbital Q u v) (pairAnnihilate α ψ) ≤
      energy (pairAnnihilate α ψ) + normSq (pairAnnihilate α ψ) :=
  coherent_occupation_pair_lift α u v h ψ

example (Q N : ℕ) (α : Orbital Q → ℂ) (u v : ℂ)
    (h : Complex.normSq u + Complex.normSq v = 1)
    (ψ : State Q (N+3)) (hψ : IsBosonic ψ) :
    normSq (annihilate (coherentOrbital Q u v) (pairAnnihilate α ψ)) ≤
      energy (pairAnnihilate α ψ) + normSq (pairAnnihilate α ψ) :=
  coherent_annihilation_pair_lift α u v h ψ hψ

example (Q N : ℕ) (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    energy ψ = ∑ p : Fin (2*Q+1), normSq (v0PairAnnihilate p ψ) :=
  energy_eq_sum_v0PairAnnihilate_normSq ψ hψ

example (Q N : ℕ) (ψ : State Q N) :
    hamiltonian (hamiltonian ψ) =
      hamiltonian ψ + normalThreeBodyApply ψ + normalFourBodyApply ψ :=
  hamiltonian_normal_order ψ

example (Q N : ℕ) (ψ : State Q N) :
    0 ≤ (BosonicLaughlin.inner ψ (normalFourBodyApply ψ)).re :=
  normalFourBody_nonneg ψ

example (Q N : ℕ) (ψ : State Q (N+4)) (hψ : IsBosonic ψ) :
    normSq (hamiltonian ψ) = energy ψ +
      (BosonicLaughlin.inner ψ (normalThreeBodyApply ψ)).re +
      ∑ p : Fin (2*Q+1), ∑ q : Fin (2*Q+1),
        normSq (v0PairAnnihilate q (v0PairAnnihilate p ψ)) :=
  normal_order_fock_quadratic_form ψ hψ

example (Q : ℕ) (φ : ThreeBodyAux Q) :
    threeBodyAdjoint (threeBodyMap φ) = φ + (2 : ℂ) • compressedSwap φ :=
  threeBody_gram φ

example (Q : ℕ) (ψ : State Q 3) (hψ : IsBosonic ψ) :
    threeBodyMap (threeBodyAdjoint ψ) = hamiltonian ψ :=
  threeBody_hamiltonian ψ hψ

example (Q : ℕ) (ψ : State Q 3) (hψ : IsBosonic ψ) :
    normalThreeBodyApply ψ =
      (2 : ℂ) • threeBodyMap (compressedSwap (threeBodyAdjoint ψ)) :=
  threeBody_normal_coefficient ψ hψ

example (Q : ℕ) (φ : ThreeBodyAux Q) (ψ : State Q 3) (hψ : IsBosonic ψ) :
    BosonicLaughlin.inner (threeBodyMap φ) ψ =
      ∑ p : Fin (2*Q+1), ∑ k : Orbital Q, star (φ p k) * threeBodyAdjoint ψ p k :=
  threeBody_adjoint_inner φ ψ hψ

example (Q : ℕ) (hQ : 0 < Q) :
    threeBodyDeficitOne Q hQ ≠ 0 ∧
    threeBodyMap (threeBodyDeficitOne Q hQ) = 0 ∧
    compressedSwap (threeBodyDeficitOne Q hQ) =
      (-1 / 2 : ℂ) • threeBodyDeficitOne Q hQ :=
  ⟨threeBodyDeficitOne_nonzero Q hQ, threeBodyDeficitOne_kernel Q hQ,
    threeBodyDeficitOne_swap Q hQ⟩

example (Q N : ℕ) (u v : ℂ) (h : Complex.normSq u + Complex.normSq v = 1)
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    (∑ p : Fin (2*Q+1),
      modeOccupation (coherentOrbital Q u v) (v0PairAnnihilate p ψ)) ≤
        (BosonicLaughlin.inner ψ (normalFourBodyApply ψ)).re + energy ψ :=
  coherent_occupation_v0_sum_lift u v h ψ hψ

example (Q : ℕ) (φ : ThreeBodyAux Q) :
    compressedSwap (auxRaise φ) = auxRaise (compressedSwap φ) :=
  compressedSwap_auxRaise φ

example (Q : ℕ) (φ : ThreeBodyAux Q) :
    compressedSwap (auxLower φ) = auxLower (compressedSwap φ) :=
  compressedSwap_auxLower φ

example (Q : ℕ) :
    spectrum ℂ (compressedSwapMatrix Q) =
      {μ : ℂ | ∃ z ≤ Q, μ = (recouplingEigenvalue Q z : ℂ)} :=
  compressedSwap_spectrum Q

example (Q : ℕ) : ∑ z, compressedSwapProjector Q z = 1 :=
  compressedSwapProjector_sum Q

example (Q : ℕ) (z w : Fin (Q+1)) :
    compressedSwapProjector Q z * compressedSwapProjector Q w =
      if z=w then compressedSwapProjector Q z else 0 :=
  compressedSwapProjector_mul Q z w

example (Q : ℕ) (z : Fin (Q+1)) :
    (compressedSwapProjector Q z).IsHermitian :=
  compressedSwapProjector_hermitian Q z

example (Q : ℕ) :
    compressedSwapMatrix Q = ∑ z : Fin (Q+1),
      (recouplingEigenvalue Q z.val : ℂ) • compressedSwapProjector Q z :=
  compressedSwap_projector_resolution Q

example (Q : ℕ) (z : Fin (Q+1)) :
    Module.finrank ℂ (LinearMap.range (compressedSwapProjectorLinear Q z)) =
      3*Q - 2*z.val + 1 :=
  compressedSwapProjector_rank Q z

example (Q : ℕ) :
    threeBodyGramMatrix Q = ∑ z : Fin (Q+1),
      ((1 + 2 * recouplingEigenvalue Q z.val : ℝ) : ℂ) • compressedSwapProjector Q z :=
  threeBodyGram_projector_resolution Q

example (Q : ℕ) (ψ : State Q 3) (hψ : IsBosonic ψ) :
    normalThreeBodyApply ψ = ∑ z : Fin (Q+1),
      ((2 : ℂ) * (recouplingEigenvalue Q z.val : ℂ)) •
        threeBodyMap (auxSpectralProject z (threeBodyAdjoint ψ)) :=
  threeBody_normal_spectral_resolution ψ hψ

example (Q M : ℕ) (ψ : State Q M) (hψ : IsBosonic ψ) :
    threeBodyLift Q M LinearMap.id ψ = (M.choose 3 : ℂ) • ψ :=
  threeBodyLift_id Q M ψ hψ

example (Q M : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3)
    (hA : ∀ χ, IsBosonic χ → 0 ≤ (BosonicLaughlin.inner χ (A χ)).re)
    (ψ : State Q M) :
    0 ≤ (BosonicLaughlin.inner ψ (threeBodyLift Q M A ψ)).re :=
  threeBodyLift_nonneg Q M A hA ψ

example (Q M : ℕ) (A B : State Q 3 →ₗ[ℂ] State Q 3)
    (hAB : ∀ χ, IsBosonic χ →
      (BosonicLaughlin.inner χ (A χ)).re ≤ (BosonicLaughlin.inner χ (B χ)).re)
    (ψ : State Q M) :
    (BosonicLaughlin.inner ψ (threeBodyLift Q M A ψ)).re ≤
      (BosonicLaughlin.inner ψ (threeBodyLift Q M B ψ)).re :=
  threeBodyLift_mono Q M A B hAB ψ

example (Q M : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3)
    (hA : ∀ χ η, IsBosonic χ → IsBosonic η →
      BosonicLaughlin.inner χ (A η) = BosonicLaughlin.inner (A χ) η)
    (ψ φ : State Q M) :
    BosonicLaughlin.inner ψ (threeBodyLift Q M A φ) =
      BosonicLaughlin.inner (threeBodyLift Q M A ψ) φ :=
  threeBodyLift_hermitian Q M A hA ψ φ

example (Q N : ℕ) (w w' : State Q 3) (ψ : State Q (N+3)) :
    threeBodyLiftAbove Q N (rankOneThree w w') ψ =
      threeCreate w (threeAnnihilate w' ψ) :=
  threeBodyLiftAbove_rankOne Q N w w' ψ

example (Q N : ℕ) (w : State Q 3) (χ : State Q N) (ψ : State Q (N+3)) :
    BosonicLaughlin.inner (threeCreate w χ) ψ =
      BosonicLaughlin.inner χ (threeAnnihilate w ψ) :=
  threeCreate_inner w χ ψ

example (Q : ℕ) (w : State Q 3) (hw : IsBosonic w) :
    threeCreate (N := 0) w (fun _ => 1) = w :=
  threeCreate_vacuum w hw

example (Q M : ℕ) (ψ : State Q M) (hψ : IsBosonic ψ) :
    normalThreeBodyApply ψ = threeBodyLift Q M (normalThreeBodyLinear Q 3) ψ :=
  normalThreeBody_eq_lift ψ hψ

example (Q M : ℕ) (ψ : State Q M) (hψ : IsBosonic ψ) :
    normalThreeBodyApply ψ = threeBodyLift Q M
      ((2 : ℂ) • threeBodyAuxCoefficient Q (compressedSwapLinear Q)) ψ :=
  normalThreeBody_eq_recoupling_lift ψ hψ

example (Q M : ℕ) (ψ : State Q M) (hψ : IsBosonic ψ) :
    normalThreeBodyApply ψ = ∑ z : Fin (Q+1),
      ((2 : ℂ) * (recouplingEigenvalue Q z.val : ℂ)) •
        threeBodyLift Q M (threeBodySpectralBlock Q z) ψ :=
  normalThreeBody_spectral_lift ψ hψ

example (Q M : ℕ) (z : Fin (Q+1)) (ψ : State Q M) :
    0 ≤ (BosonicLaughlin.inner ψ (threeBodyLift Q M (threeBodySpectralBlock Q z) ψ)).re :=
  threeBodySpectralBlock_lift_nonneg Q M z ψ

example (Q M : ℕ) (z : Fin (Q+1)) (ψ φ : State Q M) :
    BosonicLaughlin.inner ψ (threeBodyLift Q M (threeBodySpectralBlock Q z) φ) =
      BosonicLaughlin.inner (threeBodyLift Q M (threeBodySpectralBlock Q z) ψ) φ :=
  threeBodySpectralBlock_lift_hermitian Q M z ψ φ

example (Q M : ℕ) (ψ : State Q M) (hψ : IsBosonic ψ) :
    hamiltonian (hamiltonian ψ) = hamiltonian ψ +
      (∑ z : Fin (Q+1), ((2 : ℂ) * (recouplingEigenvalue Q z.val : ℂ)) •
        threeBodyLift Q M (threeBodySpectralBlock Q z) ψ) + normalFourBodyApply ψ :=
  hamiltonian_square_lifted_recoupling ψ hψ

example (Q N : ℕ) (ψ : State Q (N+2)) (hψ : IsBosonic ψ) :
    hamiltonian ψ = 0 ↔ ∀ p : Fin (2*Q+1), v0PairAnnihilate p ψ = 0 :=
  hamiltonian_zero_iff_v0PairAnnihilate_zero ψ hψ

example (Q N : ℕ) :
    bosonicSubspace Q (N+2) ⊓ LinearMap.ker (hamiltonianLinear Q (N+2)) =
      bosonicSubspace Q (N+2) ⊓
        ⨅ p : Fin (2*Q+1), LinearMap.ker (v0PairAnnihilateLinear Q N p) :=
  physicalHamiltonian_kernel_eq_common_pair_kernel Q N

example (Q N d : ℕ) (ψ : State Q N) :
    hamiltonian (weightProjection d ψ) = weightProjection d (hamiltonian ψ) :=
  hamiltonian_weightProjection d ψ

example (Q N d : ℕ) (φ χ : WeightState Q N d) :
    BosonicLaughlin.inner (weightInclude d φ) (weightInclude d χ) = weightInner φ χ :=
  weightInclude_inner φ χ

example (Q N d : ℕ) (φ : WeightState Q N d) :
    (weightHamiltonianMatrix Q N d).mulVec φ = weightHamiltonian Q N d φ :=
  weightHamiltonianMatrix_mulVec φ

example (Q N d : ℕ) : (weightHamiltonianMatrix Q N d).PosSemidef :=
  weightHamiltonianMatrix_posSemidef Q N d

example (Q N : ℕ) (p : Fin (2*Q+1)) (ψ : State Q (N+2)) :
    (Real.sqrt ((N+2).choose 2) : ℂ) •
        polynomialPairChannel p.val (polynomialCoordinates Q (N+2) ψ) =
      (binomialRoot (2*Q) p.val : ℂ) •
        polynomialCoordinates Q N (v0PairAnnihilate p ψ) :=
  polynomialPairChannel_annihilate p ψ

example (Q N : ℕ) (χ η : State Q N) :
    polynomialInner χ η = ∑ a : Configuration Q N,
      star (χ a) * η a / (polynomialScale a : ℂ)^2 :=
  polynomialInner_diagonal χ η

example (Q N : ℕ) (χ η : State Q N) :
    polynomialInner χ (polynomialHamiltonian Q N η) =
      polynomialInner (polynomialHamiltonian Q N χ) η :=
  polynomialHamiltonian_hermitian χ η

example (Q N d : ℕ) (φ : WeightState Q (N+2) d) (hφ : WeightIsBosonic φ) :
    (weightHamiltonianMatrix Q (N+2) d).mulVec φ = 0 ↔ ∀ p : Fin (2*Q+1),
      (polynomialPairMatrix Q N d p.val).mulVec
        (polynomialWeightCoordinates Q (N+2) d φ) = 0 :=
  weightHamiltonianMatrix_zero_iff_polynomialPairMatrices φ hφ

example (Q N d : ℕ) (hd : d ≤ Q) (φ : WeightState Q N d) :
    polynomialWeightCoordinates d N d (weightKernelTransport hd φ) =
      capWeightStateEquiv hd (polynomialWeightCoordinates Q N d φ) :=
  weightKernelTransport_polynomial hd φ

example (Q N d : ℕ) (hd : d ≤ Q)
    (φ : WeightState Q (N+2) d) (hφ : WeightIsBosonic φ) :
    weightHamiltonian d (N+2) d (weightKernelTransport hd φ) = 0 ↔
      weightHamiltonian Q (N+2) d φ = 0 :=
  weightKernelTransport_kernel_iff hd φ hφ

example (Q N d : ℕ) (hd : d ≤ Q) :
    Module.finrank ℂ (physicalWeightKernel Q (N+2) d) =
      Module.finrank ℂ (physicalWeightKernel d (N+2) d) :=
  physicalWeightKernel_finrank_stable hd

example (Q N : ℕ) (t : Fin (2*Q+1)) (leading : ℂ)
    (coefficient : Fin (2*Q+1) → Orbital Q → Orbital Q → ℂ)
    (ψ : State Q (N+2)) (hψ : IsBosonic ψ) (hH : hamiltonian ψ = 0) :
    certificateRow Q N t leading coefficient ψ = 0 :=
  certificateRow_annihilates_kernel Q N t leading coefficient ψ hψ hH

example (Q N : ℕ) (ψ : State Q N) (hH : hamiltonian ψ = 0) :
    normalThreeBodyApply ψ = 0 := normalThreeBody_kernel_zero ψ hH

example (Q N : ℕ) (ψ : State Q N) (hH : hamiltonian ψ = 0) :
    normalFourBodyApply ψ = 0 := normalFourBody_kernel_zero ψ hH

example (Q : ℕ) (z : Fin (Q+1)) (ψ : State Q 3)
    (hψ : IsBosonic ψ) (hH : hamiltonian ψ = 0) :
    threeBodySpectralBlock Q z ψ = 0 := threeBodySpectralBlock_kernel_zero z ψ hψ hH

example (Q N : ℕ) (A : Occupation Q N) :
    occupationOrbitMultiplicity A * multisetOccupationFactorial A.val = N.factorial :=
  occupationOrbitMultiplicity_mul_factorial A

example (Q N : ℕ) (ψ : State Q N) (hψ : IsBosonic ψ) :
    occupationInclude (occupationRestrict ψ) = ψ := occupationInclude_restrict ψ hψ

example (Q N : ℕ) (x y : Orbital Q) (A : Occupation Q (N+2)) (B : Occupation Q N) :
    occupationAnnihilate y (occupationAnnihilate x (Pi.single A 1)) B =
      if Sym.cons x (Sym.cons y B) = A then
        ((A.val.count x * (A.val.erase x).count y : ℕ) : ℂ) else 0 :=
  occupationAnnihilate_twice_single x y A B

example (Q N d p : ℕ) (c : WeightOccupationState Q (N+2) d) :
    (polynomialPairMatrix Q N d p).mulVec (polynomialWeightOccupationInclude c) =
      polynomialWeightOccupationInclude ((occupationPairBlockMatrix Q N d p).mulVec c) :=
  polynomialWeightOccupationInclude_pairMatrix Q N d p c

example (Q N : ℕ) (hQ : 0<Q) (A : Occupation Q N) :
    (Q : ℝ)^(occupationWeight A) * (occupationFactorial A : ℝ) /
      occupationBinomialProduct A = occupationPlanarMetric A / occupationSphereProduct A :=
  occupation_metric_script_factor hQ A

example (Q p : ℕ) (hQ : 0<Q) (hp : p≤2*Q) :
    (Q : ℝ)^p / (2 * ((2*Q).choose p : ℝ)) = planarPairFactor p / sphereFactor (2*Q) p :=
  sphere_pair_factor hQ hp

example (Q N d : ℕ) (c : WeightOccupationState Q N d) :
    certificateWeightCoordinates Q N d c = (certificateSectorScale Q N d : ℂ) •
      (polynomialCoordinates Q N).symm (polynomialOccupationInclude (occupationWeightExtend d c)) := rfl

example (Q N d : ℕ) (hQ : 0<Q) (c e : WeightOccupationState Q N d) :
    BosonicLaughlin.inner (certificateWeightCoordinates Q N d c)
      (certificateWeightCoordinates Q N d e) = certificateInner c e :=
  certificateWeightCoordinates_inner hQ c e

example (Q N d : ℕ) (hQ : 0<Q) (c e : WeightOccupationState Q (N+2) d) :
    BosonicLaughlin.inner (certificateWeightCoordinates Q (N+2) d c)
      (hamiltonian (certificateWeightCoordinates Q (N+2) d e)) =
      ∑ p : Fin (2*Q+1), (planarPairFactor p.val / sphereFactor (2*Q) p.val : ℝ) *
        certificateInner (occupationPairBlock Q N d p.val c) (occupationPairBlock Q N d p.val e) :=
  certificateWeightCoordinates_hamiltonian_inner hQ c e

example (Q N d : ℕ) (hQ : 0<Q) (A B : WeightOccupation Q (N+2) d) :
    certificateHamiltonianFormMatrix Q (N+2) d A B =
      ∑ p : Fin (2*Q+1), (planarPairFactor p.val / sphereFactor (2*Q) p.val : ℝ) *
        ∑ C : WeightOccupation Q N (d-p.val), (certificateMetricWeight C.val : ℂ) *
          star (occupationPairBlockMatrix Q N d p.val C A) *
            occupationPairBlockMatrix Q N d p.val C B :=
  certificateHamiltonianFormMatrix_apply hQ A B

example (Q N d : ℕ) (hQ : 0<Q) (c : WeightOccupationState Q (N+2) d) :
    hamiltonian (certificateWeightCoordinates Q (N+2) d c)=0 ↔
      ∀ p : Fin (2*Q+1), (occupationPairBlockMatrix Q N d p.val).mulVec c=0 :=
  certificateWeightCoordinates_hamiltonian_kernel hQ c

example (Q N : ℕ) (ψ : State Q N) :
    polynomialCoordinates Q N (tensorRaise ψ) = polynomialCM (polynomialCoordinates Q N ψ) :=
  polynomialCoordinates_tensorRaise ψ

example (Q N d : ℕ) (hd : 0<d) (c : WeightOccupationState Q N d) :
    tensorRaise (certificateWeightCoordinates Q N d c) =
      (Real.sqrt Q : ℂ) • certificateWeightCoordinates Q N (d-1) (occupationCMBlock Q N d c) :=
  tensorRaise_certificateWeightCoordinates hd c

example (Q N d : ℕ) (hQ : 0<Q) (c : WeightOccupationState Q N d) :
    tensorRaise (certificateWeightCoordinates Q N d c)=0 ↔
      (occupationCMBlockMatrix Q N d).mulVec c=0 :=
  tensorRaise_certificateWeightCoordinates_zero_iff hQ c

example (Q N d : ℕ) (hQ : 0<Q) (ψ : State Q N) (hψ : IsBosonic ψ)
    (hw : WeightSupported d ψ) (hE : tensorRaise ψ=0) :
    ∃ c : WeightOccupationState Q N d,
      (occupationCMBlockMatrix Q N d).mulVec c=0 ∧ certificateWeightCoordinates Q N d c=ψ :=
  certificateWeightCoordinates_highest_surjective hQ ψ hψ hw hE

example (Q N d : ℕ) (hd : d≤Q) : Nonempty (SortedDegreeTuple N d ≃ WeightOccupation Q N d) :=
  ⟨sortedDegreeOccupationEquiv hd⟩

/- Concrete retained highest-weight spaces in the spherical V0 model. -/

example (Q : ℕ) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 0)=1 :=
  retainedCM_3_0_physical_finrank Q

example (Q : ℕ) (hd : 1≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 1)=0 :=
  retainedCM_3_1_physical_finrank Q hd

example (Q : ℕ) (hd : 2≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 2)=1 :=
  retainedCM_3_2_physical_finrank Q hd

example (Q : ℕ) (hd : 3≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 3)=1 :=
  retainedCM_3_3_physical_finrank Q hd

example (Q : ℕ) (hd : 4≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 4)=1 :=
  retainedCM_3_4_physical_finrank Q hd

example (Q : ℕ) (hd : 5≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 5)=1 :=
  retainedCM_3_5_physical_finrank Q hd

example (Q : ℕ) (hd : 6≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 6)=2 :=
  retainedCM_3_6_physical_finrank Q hd

example (Q : ℕ) (hd : 7≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 7)=1 :=
  retainedCM_3_7_physical_finrank Q hd

example (Q : ℕ) (hd : 8≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 3 8)=2 :=
  retainedCM_3_8_physical_finrank Q hd

example (Q : ℕ) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 0)=1 :=
  retainedCM_4_0_physical_finrank Q

example (Q : ℕ) (hd : 1≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 1)=0 :=
  retainedCM_4_1_physical_finrank Q hd

example (Q : ℕ) (hd : 2≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 2)=1 :=
  retainedCM_4_2_physical_finrank Q hd

example (Q : ℕ) (hd : 3≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 3)=1 :=
  retainedCM_4_3_physical_finrank Q hd

example (Q : ℕ) (hd : 4≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 4)=2 :=
  retainedCM_4_4_physical_finrank Q hd

example (Q : ℕ) (hd : 5≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 5)=1 :=
  retainedCM_4_5_physical_finrank Q hd

example (Q : ℕ) (hd : 6≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 6)=3 :=
  retainedCM_4_6_physical_finrank Q hd

example (Q : ℕ) (hd : 7≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 7)=2 :=
  retainedCM_4_7_physical_finrank Q hd

example (Q : ℕ) (hd : 8≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 8)=4 :=
  retainedCM_4_8_physical_finrank Q hd

example (Q : ℕ) (hd : 9≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 9)=3 :=
  retainedCM_4_9_physical_finrank Q hd

example (Q : ℕ) (hd : 10≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 10)=5 :=
  retainedCM_4_10_physical_finrank Q hd

example (Q : ℕ) (hd : 11≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 11)=4 :=
  retainedCM_4_11_physical_finrank Q hd

example (Q : ℕ) (hd : 12≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 12)=7 :=
  retainedCM_4_12_physical_finrank Q hd

example (Q : ℕ) (hd : 13≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 13)=5 :=
  retainedCM_4_13_physical_finrank Q hd

example (Q : ℕ) (hd : 14≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 14)=8 :=
  retainedCM_4_14_physical_finrank Q hd

example (Q : ℕ) (hd : 15≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 15)=7 :=
  retainedCM_4_15_physical_finrank Q hd

example (Q : ℕ) (hd : 16≤Q) :
    Module.finrank ℂ (physicalHighestWeightSubspace Q 4 16)=10 :=
  retainedCM_4_16_physical_finrank Q hd

example (Q : ℕ) (hd : 16≤Q) :
    indexedOccupationCMMatrix hd retainedEnum_4_16 retainedEnum_4_15 =
      retainedCM_4_16C.map (Rat.castHom ℂ) := retainedCM_4_16_physical_matrix Q hd

example (Q : ℕ) (hd : 16≤Q) (c : Fin 10 → ℂ) :
    (retainedCM_4_16_physicalEquiv Q hd c).val =
      (polynomialWeightCoordinates Q 4 16).symm
        (polynomialWeightOccupationInclude
          (((retainedCM_4_16U.map (Rat.castHom ℂ)) *ᵥ c) ∘ (retainedEnum_4_16.occupationEquiv hd).symm)) :=
  retainedCM_4_16_physical_apply Q hd c

example (Q : ℕ) : Function.Bijective (fun c : Fin 1 → ℂ => zeroDegreePhysicalHighestEquiv Q 4
    ((retainedCM_4_0U.map (Rat.castHom ℂ)) *ᵥ c)) := retainedCM_4_0_columns_complete Q

/- Planar-certificate extension contracts: physical form identities and
exact exported arrays have separate statements. -/
example {Q N d : ℕ} (hQ : 0<Q) :
    certificateMetricMatrix Q N d=physicalFrameMetric (certificateWeightCoordinates Q N d) :=
  certificateMetricMatrix_physical hQ

example {Q N d : ℕ} (hQ : 0<Q) :
    physicalFormMatrix (certificateWeightCoordinates Q N d)
      ((hamiltonianLinear Q N).comp (hamiltonianLinear Q N)) =
      certificateHamiltonianFormMatrix Q N d * certificateInverseMetric Q N d *
        certificateHamiltonianFormMatrix Q N d := certificateHamiltonian_square_form hQ

example {Q d : ℕ} (hQ : 0<Q) :
    physicalFormMatrix (certificateWeightCoordinates Q 3 d) (normalThreeBodyLinear Q 3) =
      certificateHamiltonianFormMatrix Q 3 d * certificateInverseMetric Q 3 d *
        certificateHamiltonianFormMatrix Q 3 d - certificateHamiltonianFormMatrix Q 3 d :=
  certificateThreeBody_target_form hQ

example (Q : ℕ) (hd : 16≤Q) (A : State Q 4 →ₗ[ℂ] State Q 4) :
    (∀ v, 0 ≤ (star v ⬝ᵥ (physicalFormMatrix
      (highestWeightPhysicalFrame (retainedCM_4_16_physicalEquiv Q hd)) A *ᵥ v)).re) ↔
      ∀ φ ∈ physicalHighestWeightSubspace Q 4 16,
        0 ≤ (inner (weightInclude 16 φ) (A (weightInclude 16 φ))).re :=
  highestWeightPhysicalFrame_nonneg_iff (retainedCM_4_16_physicalEquiv Q hd) A

example (Q : ℕ) (A : State Q 3 →ₗ[ℂ] State Q 3) :
    (∀ v, 0 ≤ (star v ⬝ᵥ (physicalFormMatrix
      (highestWeightPhysicalFrame (zeroDegreePhysicalHighestEquiv Q 3)) A *ᵥ v)).re) ↔
      ∀ φ ∈ physicalHighestWeightSubspace Q 3 0,
        0 ≤ (inner (weightInclude 0 φ) (A (weightInclude 0 φ))).re :=
  highestWeightPhysicalFrame_nonneg_iff (zeroDegreePhysicalHighestEquiv Q 3) A

example : (planar_3_6A.map (Rat.castHom ℂ)).PosSemidef := planar_3_6A_posSemidef

example : Module.finrank ℂ (LinearMap.ker (planar_3_6A.map (Rat.castHom ℂ)).mulVecLin)=1 :=
  planar_3_6A_kernel_finrank

example : (planar_4_16A.map (Rat.castHom ℂ)).PosSemidef := planar_4_16A_posSemidef

example (v : Fin 10 → ℂ) :
    (planar_4_16A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_16H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  planar_4_16_same_kernel v

example : ((planar_4_16W.map (Rat.castHom ℂ))ᴴ * (planar_4_16A.map (Rat.castHom ℂ)) *
    (planar_4_16W.map (Rat.castHom ℂ))).PosDef := planar_4_16A_active_posDef

example : Module.finrank ℂ (LinearMap.ker (planar_4_16A.map (Rat.castHom ℂ)).mulVecLin)=2 :=
  planar_4_16A_kernel_finrank

example : (planar_4_1A.map (Rat.castHom ℂ)).PosSemidef := planar_4_1A_posSemidef

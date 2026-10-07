import BosonicLaughlin

/-! These contracts keep the physical model, quantifiers, and hypotheses of
the published results explicit. They must elaborate without assuming an
occupation inequality, a normal-order identity, or a spectral-gap estimate. -/
open BosonicLaughlin

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

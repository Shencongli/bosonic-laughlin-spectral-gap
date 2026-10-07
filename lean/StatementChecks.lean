import BosonicLaughlin

/-! These contracts keep the physical model, quantifiers, and hypotheses of
the published occupation results explicit. They must elaborate without any
assumption of an occupation or spectral-gap inequality. -/
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

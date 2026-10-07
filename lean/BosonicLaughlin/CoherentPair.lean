import BosonicLaughlin.Model
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-!
Spin-coherent orbitals in the same orthonormal spherical basis as `Model`.
A spinor `(u,v)` is normalized when `normSq u + normSq v = 1`.
The two copies of its degree-Q coherent orbital lie exactly in the V₀
pair space; their pair-space coordinates are its degree-2Q coherent vector.
-/
namespace BosonicLaughlin
noncomputable section
open Finset

/-- Homogeneous spin-coherent coefficient; physical labels satisfy `i ≤ Q`. -/
def coherentCoefficient (Q i : ℕ) (u v : ℂ) : ℂ :=
  (Real.sqrt (Q.choose i : ℝ) : ℂ) * u^(Q-i) * v^i

def coherentOrbital (Q : ℕ) (u v : ℂ) : Orbital Q → ℂ :=
  fun i => coherentCoefficient Q i.val u v

theorem coherentCoefficient_normSq (Q i : ℕ) (u v : ℂ) :
    Complex.normSq (coherentCoefficient Q i u v) =
      (Q.choose i : ℝ) * Complex.normSq u^(Q-i) * Complex.normSq v^i := by
  simp only [coherentCoefficient, map_mul, map_pow, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (by positivity)]

/-- Exact normalization in the physical orthonormal orbital basis. -/
theorem coherentOrbital_normalized (Q : ℕ) (u v : ℂ)
    (hspinor : Complex.normSq u + Complex.normSq v = 1) :
    ∑ i : Orbital Q, Complex.normSq (coherentOrbital Q u v i) = 1 := by
  simp only [coherentOrbital, coherentCoefficient_normSq]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    (Q.choose i : ℝ) * Complex.normSq u^(Q-i) * Complex.normSq v^i)]
  have h := add_pow (Complex.normSq v) (Complex.normSq u) Q
  rw [add_comm, hspinor, one_pow] at h
  calc
    _ = ∑ i ∈ range (Q+1), Complex.normSq v^i *
        Complex.normSq u^(Q-i) * (Q.choose i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 1 := h.symm

theorem pairCoefficient_sqrt_choose (Q x y : ℕ) (hx : x ≤ Q) (hy : y ≤ Q) :
    pairCoefficient Q (x+y) x * Real.sqrt ((2*Q).choose (x+y) : ℝ) =
      Real.sqrt (Q.choose x : ℝ) * Real.sqrt (Q.choose y : ℝ) := by
  have hp : x+y ≤ 2*Q := by omega
  have hpos : (0 : ℝ) < ((2*Q).choose (x+y) : ℝ) := by
    exact_mod_cast Nat.choose_pos hp
  have hn : Real.sqrt ((2*Q).choose (x+y) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  unfold pairCoefficient pairWeight
  rw [Nat.add_sub_cancel_left]
  rw [Real.sqrt_div (by positivity), div_mul_cancel₀ _ hn]
  exact Real.sqrt_mul (by positivity) _

/-- The coherent product has exactly the normalized V₀ pair coefficients. -/
theorem coherentCoefficient_pair_factorization (Q x y : ℕ)
    (hx : x ≤ Q) (hy : y ≤ Q) (u v : ℂ) :
    coherentCoefficient Q x u v * coherentCoefficient Q y u v =
      (pairCoefficient Q (x+y) x : ℂ) *
        coherentCoefficient (2*Q) (x+y) u v := by
  have he : Q-x+(Q-y) = 2*Q-(x+y) := by omega
  have hc := congrArg Complex.ofReal (pairCoefficient_sqrt_choose Q x y hx hy)
  simp only [Complex.ofReal_mul] at hc
  unfold coherentCoefficient
  calc
    _ = ((Real.sqrt (Q.choose x : ℝ) : ℂ) *
          (Real.sqrt (Q.choose y : ℝ) : ℂ)) *
          (u^(Q-x) * u^(Q-y)) * (v^x * v^y) := by ring
    _ = _ := by rw [← hc, ← pow_add, ← pow_add, he]; ring

/-- Explicit membership in the full pair space, with no restriction on flux. -/
theorem coherentOrbital_pair_expansion (Q : ℕ) (u v : ℂ) (x y : Orbital Q) :
    coherentOrbital Q u v x * coherentOrbital Q u v y =
      ∑ p : Fin (2*Q+1), (pairVector Q p.val x y : ℂ) *
        coherentCoefficient (2*Q) p.val u v := by
  let p₀ : Fin (2*Q+1) := ⟨x.val+y.val, by have hx := x.isLt; have hy := y.isLt; omega⟩
  rw [Finset.sum_eq_single p₀]
  · simp only [p₀, pairVector, coherentOrbital]
    exact coherentCoefficient_pair_factorization Q x.val y.val
      (Nat.le_of_lt_succ x.isLt) (Nat.le_of_lt_succ y.isLt) u v
  · intro p hp hne
    have h : x.val+y.val ≠ p.val := by
      intro heq
      apply hne
      exact Fin.ext heq.symm
    simp [pairVector, h]
  · simp

/-- A normalized coherent product has normalized coordinates in the V₀ pair frame. -/
theorem coherentOrbital_pair_witness (Q : ℕ) (u v : ℂ)
    (hspinor : Complex.normSq u + Complex.normSq v = 1) :
    ∃ c : Fin (2*Q+1) → ℂ,
      (∑ p, Complex.normSq (c p)) = 1 ∧
      ∀ x y : Orbital Q, coherentOrbital Q u v x * coherentOrbital Q u v y =
        ∑ p : Fin (2*Q+1), (pairVector Q p.val x y : ℂ) * c p := by
  refine ⟨coherentOrbital (2*Q) u v, coherentOrbital_normalized (2*Q) u v hspinor, ?_⟩
  exact coherentOrbital_pair_expansion Q u v

end
end BosonicLaughlin

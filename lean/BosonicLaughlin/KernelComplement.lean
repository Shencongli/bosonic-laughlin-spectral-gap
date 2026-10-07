import BosonicLaughlin.KernelFrameTransport
import BosonicLaughlin.SparseGramCertificate

/-! Kernel reconstruction and positivity on a complementary coordinate frame.
The complement need not be orthogonal. All matrix identities are hypotheses
to be checked for each concrete frame. -/
namespace BosonicLaughlin
open scoped Matrix ComplexOrder

def HasComplement {K : Type*} [Field K] {n k r : ℕ}
    (U : Matrix (Fin n) (Fin k) K) (L : Matrix (Fin k) (Fin n) K)
    (W : Matrix (Fin n) (Fin r) K) (R : Matrix (Fin r) (Fin n) K) : Prop :=
  W*R+U*L=1 ∧ L*W=0 ∧ R*W=1

theorem HasComplement.map {K F : Type*} [Field K] [Field F] {n k r : ℕ}
    {U : Matrix (Fin n) (Fin k) K} {L : Matrix (Fin k) (Fin n) K}
    {W : Matrix (Fin n) (Fin r) K} {R : Matrix (Fin r) (Fin n) K}
    (h : HasComplement U L W R) (f : K →+* F) :
    HasComplement (U.map f) (L.map f) (W.map f) (R.map f) := by
  refine ⟨?_,?_,?_⟩
  · have he := congrArg (fun M : Matrix (Fin n) (Fin n) K => M.map f) h.1
    rw [Matrix.map_add f f.map_add] at he
    simpa using he
  · simpa using congrArg (fun M : Matrix (Fin k) (Fin r) K => M.map f) h.2.1
  · simpa using congrArg (fun M : Matrix (Fin r) (Fin r) K => M.map f) h.2.2

theorem HasKernelFrame.scale_matrix {K : Type*} [Field K] {m n k : ℕ}
    {C : Matrix (Fin m) (Fin n) K} {U : Matrix (Fin n) (Fin k) K}
    {L : Matrix (Fin k) (Fin n) K} {V : Matrix (Fin n) (Fin m) K}
    (h : HasKernelFrame C U L V) {a : K} (ha : a≠0) :
    HasKernelFrame (a • C) U L (a⁻¹ • V) := by
  refine ⟨?_,h.2.1,?_⟩
  · rw [Matrix.smul_mul, h.1, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]
    exact h.2.2

theorem kernelFrame_same_kernel {K : Type*} [Field K] {m p n k : ℕ}
    {A : Matrix (Fin m) (Fin n) K} {B : Matrix (Fin p) (Fin n) K}
    {U : Matrix (Fin n) (Fin k) K} {L J : Matrix (Fin k) (Fin n) K}
    {V : Matrix (Fin n) (Fin m) K} {Z : Matrix (Fin n) (Fin p) K}
    (hA : HasKernelFrame A U L V) (hB : HasKernelFrame B U J Z) (v : Fin n → K) :
    A *ᵥ v=0 ↔ B *ᵥ v=0 := by
  constructor
  · intro h
    rw [← kernelFrame_reconstruction hA v h]
    exact kernelFrame_columns_in_kernel hB _
  · intro h
    rw [← kernelFrame_reconstruction hB v h]
    exact kernelFrame_columns_in_kernel hA _

theorem complement_form_reconstruction {n k r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin k) ℂ)
    (L : Matrix (Fin k) (Fin n) ℂ) (W : Matrix (Fin n) (Fin r) ℂ)
    (R : Matrix (Fin r) (Fin n) ℂ)
    (hA : A.IsHermitian) (hAU : A*U=0) (hspan : W*R+U*L=1) :
    A=Rᴴ*(Wᴴ*A*W)*R := by
  have har : A*(W*R)=A := by
    have h := congrArg (fun B => A*B) hspan
    simpa only [Matrix.mul_add, ← Matrix.mul_assoc, hAU, Matrix.zero_mul,
      add_zero, Matrix.mul_one] using h
  have hleft : (W*R)ᴴ*A=A := by
    have h := congrArg Matrix.conjTranspose har
    simpa only [Matrix.conjTranspose_mul, hA.eq] using h
  calc
    A = (W*R)ᴴ*A*(W*R) := by rw [hleft, har]
    _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem complement_posSemidef_iff {n k r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin k) ℂ)
    (L : Matrix (Fin k) (Fin n) ℂ) (W : Matrix (Fin n) (Fin r) ℂ)
    (R : Matrix (Fin r) (Fin n) ℂ)
    (hA : A.IsHermitian) (hAU : A*U=0) (hspan : W*R+U*L=1) :
    A.PosSemidef ↔ (Wᴴ*A*W).PosSemidef := by
  constructor
  · exact fun h => h.conjTranspose_mul_mul_same W
  · intro h
    rw [complement_form_reconstruction A U L W R hA hAU hspan]
    exact h.conjTranspose_mul_mul_same R

theorem kernelFrame_complement_posDef {n k r : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} {U : Matrix (Fin n) (Fin k) ℂ}
    {L : Matrix (Fin k) (Fin n) ℂ} {V : Matrix (Fin n) (Fin n) ℂ}
    (h : HasKernelFrame A U L V) (hA : A.PosSemidef)
    (W : Matrix (Fin n) (Fin r) ℂ) (R : Matrix (Fin r) (Fin n) ℂ)
    (hLW : L*W=0) (hRW : R*W=1) : (Wᴴ*A*W).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_conjTranspose_mul_mul W hA.isHermitian)
  intro x hx
  have hw : A *ᵥ (W *ᵥ x)≠0 := by
    intro hz
    have hv := kernelFrame_reconstruction h (W *ᵥ x) hz
    rw [Matrix.mulVec_mulVec x L W, hLW, Matrix.zero_mulVec, Matrix.mulVec_zero] at hv
    have he := congrArg (fun v => R *ᵥ v) hv
    simp only [Matrix.mulVec_zero, Matrix.mulVec_mulVec, hRW, Matrix.one_mulVec] at he
    exact hx he.symm
  have hp : 0 < star (W *ᵥ x) ⬝ᵥ (A *ᵥ (W *ᵥ x)) :=
    lt_of_le_of_ne (hA.dotProduct_mulVec_nonneg _) (fun he => hw (hA.dotProduct_mulVec_zero_iff.mp he.symm))
  simpa only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec] using hp

end BosonicLaughlin

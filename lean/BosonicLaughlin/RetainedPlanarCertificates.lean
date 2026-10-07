import BosonicLaughlin.KernelComplement

/-!
Exact exported planar comparison and Hamiltonian arrays.
Their Gram decompositions, common kernels, and complement identities
are checked by Lean kernel reduction. Operator-to-array identification
and finite-sphere interval estimates are not asserted here.
-/
namespace BosonicLaughlin
open scoped Matrix ComplexOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- N=3, d=0, A; dimension=1, rank=1. -/
def planar_3_0AD : ℤ := 3189375000000000000000000000
def planar_3_0AS : ℤ := 3189375000000000000000000000
def planar_3_0AM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 7528001429986150065178711171)]
  | _ => []

def planar_3_0AR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_0AT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_0Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 24009619560762077364129351941008125000000000000000000000
  | _ => 0

def planar_3_0A : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_0AD planar_3_0AM

theorem planar_3_0A_gram_check : SparseGramCheck planar_3_0AS planar_3_0AM planar_3_0AR planar_3_0AT planar_3_0Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_0A_posSemidef : (planar_3_0A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_0A_gram_check

/- N=3, d=0, H; dimension=1, rank=1. -/
def planar_3_0HD : ℤ := 1
def planar_3_0HS : ℤ := 1
def planar_3_0HM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 18)]
  | _ => []

def planar_3_0HR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_0HT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_0Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 18
  | _ => 0

def planar_3_0H : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_0HD planar_3_0HM

theorem planar_3_0H_gram_check : SparseGramCheck planar_3_0HS planar_3_0HM planar_3_0HR planar_3_0HT planar_3_0Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_0H_posSemidef : (planar_3_0H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_0H_gram_check

def planar_3_0KD : ℤ := 135504025739750701173216801078
def planar_3_0KU : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_0KL : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def planar_3_0KVA : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 18)]
  | _ => []

def planar_3_0KVH : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 7528001429986150065178711171)]
  | _ => []

def planar_3_0U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix planar_3_0KD planar_3_0KU
def planar_3_0L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix planar_3_0KL

def planar_3_0AV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_0AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_0KD planar_3_0KVA

theorem planar_3_0A_kernel_check : SparseScaledFrameCheck planar_3_0KD planar_3_0AM planar_3_0KU planar_3_0KL planar_3_0KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_0A_kernel_frame : HasKernelFrame planar_3_0A planar_3_0U planar_3_0L planar_3_0AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_0KD≠0) planar_3_0A_kernel_check).scale_matrix
    (by norm_num [planar_3_0AD])

theorem planar_3_0A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_0A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_0A_kernel_frame.ratCast

def planar_3_0HV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_0HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_0KD planar_3_0KVH

theorem planar_3_0H_kernel_check : SparseScaledFrameCheck planar_3_0KD planar_3_0HM planar_3_0KU planar_3_0KL planar_3_0KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_0H_kernel_frame : HasKernelFrame planar_3_0H planar_3_0U planar_3_0L planar_3_0HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_0KD≠0) planar_3_0H_kernel_check).scale_matrix
    (by norm_num [planar_3_0HD])

theorem planar_3_0H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_0H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_0H_kernel_frame.ratCast

theorem planar_3_0_same_kernel (v : Fin 1 → ℂ) :
    (planar_3_0A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_3_0H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_3_0A_kernel_frame.ratCast planar_3_0H_kernel_frame.ratCast v

def planar_3_0WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_0RS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_0W : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix planar_3_0WS
def planar_3_0R : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix 1 planar_3_0RS

theorem planar_3_0_complement : HasComplement planar_3_0U planar_3_0L planar_3_0W planar_3_0R := by
  unfold HasComplement
  decide +kernel

theorem planar_3_0A_active_posDef :
    ((planar_3_0W.map (Rat.castHom ℂ))ᴴ * (planar_3_0A.map (Rat.castHom ℂ)) * (planar_3_0W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_0A_kernel_frame.ratCast planar_3_0A_posSemidef _ _
    ((planar_3_0_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_0_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_3_0H_active_posDef :
    ((planar_3_0W.map (Rat.castHom ℂ))ᴴ * (planar_3_0H.map (Rat.castHom ℂ)) * (planar_3_0W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_0H_kernel_frame.ratCast planar_3_0H_posSemidef _ _
    ((planar_3_0_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_0_complement.map (Rat.castHom ℂ)).2.2)

/- N=3, d=1, A; dimension=0, rank=0. -/
def planar_3_1AD : ℤ := 1
def planar_3_1AS : ℤ := 1
def planar_3_1AM : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1AR : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1AT : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1Aw : Fin 0 → ℤ := fun i =>
  match i.val with
  | _ => 0

def planar_3_1A : Matrix (Fin 0) (Fin 0) ℚ := sparseRatScaledMatrix planar_3_1AD planar_3_1AM

theorem planar_3_1A_gram_check : SparseGramCheck planar_3_1AS planar_3_1AM planar_3_1AR planar_3_1AT planar_3_1Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_1A_posSemidef : (planar_3_1A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_1A_gram_check

/- N=3, d=1, H; dimension=0, rank=0. -/
def planar_3_1HD : ℤ := 1
def planar_3_1HS : ℤ := 1
def planar_3_1HM : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1HR : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1HT : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1Hw : Fin 0 → ℤ := fun i =>
  match i.val with
  | _ => 0

def planar_3_1H : Matrix (Fin 0) (Fin 0) ℚ := sparseRatScaledMatrix planar_3_1HD planar_3_1HM

theorem planar_3_1H_gram_check : SparseGramCheck planar_3_1HS planar_3_1HM planar_3_1HR planar_3_1HT planar_3_1Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_1H_posSemidef : (planar_3_1H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_1H_gram_check

def planar_3_1KD : ℤ := 1
def planar_3_1KU : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1KL : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1KVA : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1KVH : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1U : Matrix (Fin 0) (Fin 0) ℚ := sparseRatScaledMatrix planar_3_1KD planar_3_1KU
def planar_3_1L : Matrix (Fin 0) (Fin 0) ℚ := sparseRatMatrix planar_3_1KL

def planar_3_1AV : Matrix (Fin 0) (Fin 0) ℚ :=
  ((planar_3_1AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_1KD planar_3_1KVA

theorem planar_3_1A_kernel_check : SparseScaledFrameCheck planar_3_1KD planar_3_1AM planar_3_1KU planar_3_1KL planar_3_1KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_1A_kernel_frame : HasKernelFrame planar_3_1A planar_3_1U planar_3_1L planar_3_1AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_1KD≠0) planar_3_1A_kernel_check).scale_matrix
    (by norm_num [planar_3_1AD])

theorem planar_3_1A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_1A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_1A_kernel_frame.ratCast

def planar_3_1HV : Matrix (Fin 0) (Fin 0) ℚ :=
  ((planar_3_1HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_1KD planar_3_1KVH

theorem planar_3_1H_kernel_check : SparseScaledFrameCheck planar_3_1KD planar_3_1HM planar_3_1KU planar_3_1KL planar_3_1KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_1H_kernel_frame : HasKernelFrame planar_3_1H planar_3_1U planar_3_1L planar_3_1HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_1KD≠0) planar_3_1H_kernel_check).scale_matrix
    (by norm_num [planar_3_1HD])

theorem planar_3_1H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_1H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_1H_kernel_frame.ratCast

theorem planar_3_1_same_kernel (v : Fin 0 → ℂ) :
    (planar_3_1A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_3_1H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_3_1A_kernel_frame.ratCast planar_3_1H_kernel_frame.ratCast v

def planar_3_1WS : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1RS : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_1W : Matrix (Fin 0) (Fin 0) ℚ := sparseRatMatrix planar_3_1WS
def planar_3_1R : Matrix (Fin 0) (Fin 0) ℚ := sparseRatScaledMatrix 1 planar_3_1RS

theorem planar_3_1_complement : HasComplement planar_3_1U planar_3_1L planar_3_1W planar_3_1R := by
  unfold HasComplement
  decide +kernel

theorem planar_3_1A_active_posDef :
    ((planar_3_1W.map (Rat.castHom ℂ))ᴴ * (planar_3_1A.map (Rat.castHom ℂ)) * (planar_3_1W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_1A_kernel_frame.ratCast planar_3_1A_posSemidef _ _
    ((planar_3_1_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_1_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_3_1H_active_posDef :
    ((planar_3_1W.map (Rat.castHom ℂ))ᴴ * (planar_3_1H.map (Rat.castHom ℂ)) * (planar_3_1W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_1H_kernel_frame.ratCast planar_3_1H_posSemidef _ _
    ((planar_3_1_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_1_complement.map (Rat.castHom ℂ)).2.2)

/- N=3, d=2, A; dimension=1, rank=1. -/
def planar_3_2AD : ℤ := 1366875000000000000000000000
def planar_3_2AS : ℤ := 1366875000000000000000000000
def planar_3_2AM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 147180477684153814807687489)]
  | _ => []

def planar_3_2AR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_2AT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_2Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 201177315434527745615257836526875000000000000000000000
  | _ => 0

def planar_3_2A : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_2AD planar_3_2AM

theorem planar_3_2A_gram_check : SparseGramCheck planar_3_2AS planar_3_2AM planar_3_2AR planar_3_2AT planar_3_2Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_2A_posSemidef : (planar_3_2A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_2A_gram_check

/- N=3, d=2, H; dimension=1, rank=1. -/
def planar_3_2HD : ℤ := 1
def planar_3_2HS : ℤ := 1
def planar_3_2HM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 9)]
  | _ => []

def planar_3_2HR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_2HT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_2Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 9
  | _ => 0

def planar_3_2H : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_2HD planar_3_2HM

theorem planar_3_2H_gram_check : SparseGramCheck planar_3_2HS planar_3_2HM planar_3_2HR planar_3_2HT planar_3_2Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_2H_posSemidef : (planar_3_2H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_2H_gram_check

def planar_3_2KD : ℤ := 1324624299157384333269187401
def planar_3_2KU : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_2KL : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def planar_3_2KVA : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 9)]
  | _ => []

def planar_3_2KVH : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 147180477684153814807687489)]
  | _ => []

def planar_3_2U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix planar_3_2KD planar_3_2KU
def planar_3_2L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix planar_3_2KL

def planar_3_2AV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_2AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_2KD planar_3_2KVA

theorem planar_3_2A_kernel_check : SparseScaledFrameCheck planar_3_2KD planar_3_2AM planar_3_2KU planar_3_2KL planar_3_2KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_2A_kernel_frame : HasKernelFrame planar_3_2A planar_3_2U planar_3_2L planar_3_2AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_2KD≠0) planar_3_2A_kernel_check).scale_matrix
    (by norm_num [planar_3_2AD])

theorem planar_3_2A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_2A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_2A_kernel_frame.ratCast

def planar_3_2HV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_2HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_2KD planar_3_2KVH

theorem planar_3_2H_kernel_check : SparseScaledFrameCheck planar_3_2KD planar_3_2HM planar_3_2KU planar_3_2KL planar_3_2KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_2H_kernel_frame : HasKernelFrame planar_3_2H planar_3_2U planar_3_2L planar_3_2HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_2KD≠0) planar_3_2H_kernel_check).scale_matrix
    (by norm_num [planar_3_2HD])

theorem planar_3_2H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_2H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_2H_kernel_frame.ratCast

theorem planar_3_2_same_kernel (v : Fin 1 → ℂ) :
    (planar_3_2A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_3_2H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_3_2A_kernel_frame.ratCast planar_3_2H_kernel_frame.ratCast v

def planar_3_2WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_2RS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_2W : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix planar_3_2WS
def planar_3_2R : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix 1 planar_3_2RS

theorem planar_3_2_complement : HasComplement planar_3_2U planar_3_2L planar_3_2W planar_3_2R := by
  unfold HasComplement
  decide +kernel

theorem planar_3_2A_active_posDef :
    ((planar_3_2W.map (Rat.castHom ℂ))ᴴ * (planar_3_2A.map (Rat.castHom ℂ)) * (planar_3_2W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_2A_kernel_frame.ratCast planar_3_2A_posSemidef _ _
    ((planar_3_2_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_2_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_3_2H_active_posDef :
    ((planar_3_2W.map (Rat.castHom ℂ))ᴴ * (planar_3_2H.map (Rat.castHom ℂ)) * (planar_3_2W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_2H_kernel_frame.ratCast planar_3_2H_posSemidef _ _
    ((planar_3_2_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_2_complement.map (Rat.castHom ℂ)).2.2)

/- N=3, d=3, A; dimension=1, rank=1. -/
def planar_3_3AD : ℤ := 5062500000000000000000000
def planar_3_3AS : ℤ := 5062500000000000000000000
def planar_3_3AM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 70623296092351361639099)]
  | _ => []

def planar_3_3AR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_3AT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_3Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 357530436467528768297938687500000000000000000000
  | _ => 0

def planar_3_3A : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_3AD planar_3_3AM

theorem planar_3_3A_gram_check : SparseGramCheck planar_3_3AS planar_3_3AM planar_3_3AR planar_3_3AT planar_3_3Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_3A_posSemidef : (planar_3_3A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_3A_gram_check

/- N=3, d=3, H; dimension=1, rank=1. -/
def planar_3_3HD : ℤ := 8
def planar_3_3HS : ℤ := 8
def planar_3_3HM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 81)]
  | _ => []

def planar_3_3HR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_3HT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_3Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 648
  | _ => 0

def planar_3_3H : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_3HD planar_3_3HM

theorem planar_3_3H_gram_check : SparseGramCheck planar_3_3HS planar_3_3HM planar_3_3HR planar_3_3HT planar_3_3Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_3H_posSemidef : (planar_3_3H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_3H_gram_check

def planar_3_3KD : ℤ := 5720486983480460292767019
def planar_3_3KU : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_3KL : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def planar_3_3KVA : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 81)]
  | _ => []

def planar_3_3KVH : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 70623296092351361639099)]
  | _ => []

def planar_3_3U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix planar_3_3KD planar_3_3KU
def planar_3_3L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix planar_3_3KL

def planar_3_3AV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_3AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_3KD planar_3_3KVA

theorem planar_3_3A_kernel_check : SparseScaledFrameCheck planar_3_3KD planar_3_3AM planar_3_3KU planar_3_3KL planar_3_3KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_3A_kernel_frame : HasKernelFrame planar_3_3A planar_3_3U planar_3_3L planar_3_3AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_3KD≠0) planar_3_3A_kernel_check).scale_matrix
    (by norm_num [planar_3_3AD])

theorem planar_3_3A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_3A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_3A_kernel_frame.ratCast

def planar_3_3HV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_3HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_3KD planar_3_3KVH

theorem planar_3_3H_kernel_check : SparseScaledFrameCheck planar_3_3KD planar_3_3HM planar_3_3KU planar_3_3KL planar_3_3KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_3H_kernel_frame : HasKernelFrame planar_3_3H planar_3_3U planar_3_3L planar_3_3HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_3KD≠0) planar_3_3H_kernel_check).scale_matrix
    (by norm_num [planar_3_3HD])

theorem planar_3_3H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_3H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_3H_kernel_frame.ratCast

theorem planar_3_3_same_kernel (v : Fin 1 → ℂ) :
    (planar_3_3A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_3_3H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_3_3A_kernel_frame.ratCast planar_3_3H_kernel_frame.ratCast v

def planar_3_3WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_3RS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_3W : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix planar_3_3WS
def planar_3_3R : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix 1 planar_3_3RS

theorem planar_3_3_complement : HasComplement planar_3_3U planar_3_3L planar_3_3W planar_3_3R := by
  unfold HasComplement
  decide +kernel

theorem planar_3_3A_active_posDef :
    ((planar_3_3W.map (Rat.castHom ℂ))ᴴ * (planar_3_3A.map (Rat.castHom ℂ)) * (planar_3_3W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_3A_kernel_frame.ratCast planar_3_3A_posSemidef _ _
    ((planar_3_3_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_3_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_3_3H_active_posDef :
    ((planar_3_3W.map (Rat.castHom ℂ))ᴴ * (planar_3_3H.map (Rat.castHom ℂ)) * (planar_3_3W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_3H_kernel_frame.ratCast planar_3_3H_posSemidef _ _
    ((planar_3_3_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_3_complement.map (Rat.castHom ℂ)).2.2)

/- N=3, d=4, A; dimension=1, rank=1. -/
def planar_3_4AD : ℤ := 45562500000000000000000000
def planar_3_4AS : ℤ := 45562500000000000000000000
def planar_3_4AM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1824664982067046470251)]
  | _ => []

def planar_3_4AR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_4AT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_4Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 83136298245429804800811187500000000000000000000
  | _ => 0

def planar_3_4A : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_4AD planar_3_4AM

theorem planar_3_4A_gram_check : SparseGramCheck planar_3_4AS planar_3_4AM planar_3_4AR planar_3_4AT planar_3_4Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_4A_posSemidef : (planar_3_4A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_4A_gram_check

/- N=3, d=4, H; dimension=1, rank=1. -/
def planar_3_4HD : ℤ := 1
def planar_3_4HS : ℤ := 1
def planar_3_4HM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 27)]
  | _ => []

def planar_3_4HR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_4HT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_4Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 27
  | _ => 0

def planar_3_4H : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_4HD planar_3_4HM

theorem planar_3_4H_gram_check : SparseGramCheck planar_3_4HS planar_3_4HM planar_3_4HR planar_3_4HT planar_3_4Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_4H_posSemidef : (planar_3_4H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_4H_gram_check

def planar_3_4KD : ℤ := 49265954515810254696777
def planar_3_4KU : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_4KL : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def planar_3_4KVA : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 27)]
  | _ => []

def planar_3_4KVH : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1824664982067046470251)]
  | _ => []

def planar_3_4U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix planar_3_4KD planar_3_4KU
def planar_3_4L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix planar_3_4KL

def planar_3_4AV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_4AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_4KD planar_3_4KVA

theorem planar_3_4A_kernel_check : SparseScaledFrameCheck planar_3_4KD planar_3_4AM planar_3_4KU planar_3_4KL planar_3_4KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_4A_kernel_frame : HasKernelFrame planar_3_4A planar_3_4U planar_3_4L planar_3_4AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_4KD≠0) planar_3_4A_kernel_check).scale_matrix
    (by norm_num [planar_3_4AD])

theorem planar_3_4A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_4A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_4A_kernel_frame.ratCast

def planar_3_4HV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_4HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_4KD planar_3_4KVH

theorem planar_3_4H_kernel_check : SparseScaledFrameCheck planar_3_4KD planar_3_4HM planar_3_4KU planar_3_4KL planar_3_4KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_4H_kernel_frame : HasKernelFrame planar_3_4H planar_3_4U planar_3_4L planar_3_4HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_4KD≠0) planar_3_4H_kernel_check).scale_matrix
    (by norm_num [planar_3_4HD])

theorem planar_3_4H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_4H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_4H_kernel_frame.ratCast

theorem planar_3_4_same_kernel (v : Fin 1 → ℂ) :
    (planar_3_4A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_3_4H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_3_4A_kernel_frame.ratCast planar_3_4H_kernel_frame.ratCast v

def planar_3_4WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_4RS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_4W : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix planar_3_4WS
def planar_3_4R : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix 1 planar_3_4RS

theorem planar_3_4_complement : HasComplement planar_3_4U planar_3_4L planar_3_4W planar_3_4R := by
  unfold HasComplement
  decide +kernel

theorem planar_3_4A_active_posDef :
    ((planar_3_4W.map (Rat.castHom ℂ))ᴴ * (planar_3_4A.map (Rat.castHom ℂ)) * (planar_3_4W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_4A_kernel_frame.ratCast planar_3_4A_posSemidef _ _
    ((planar_3_4_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_4_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_3_4H_active_posDef :
    ((planar_3_4W.map (Rat.castHom ℂ))ᴴ * (planar_3_4H.map (Rat.castHom ℂ)) * (planar_3_4W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_4H_kernel_frame.ratCast planar_3_4H_posSemidef _ _
    ((planar_3_4_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_4_complement.map (Rat.castHom ℂ)).2.2)

/- N=3, d=5, A; dimension=1, rank=1. -/
def planar_3_5AD : ℤ := 60750000000000000000000000
def planar_3_5AS : ℤ := 60750000000000000000000000
def planar_3_5AM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 353336390103844300252699)]
  | _ => []

def planar_3_5AR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_5AT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_5Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 21465185698808541240351464250000000000000000000000
  | _ => 0

def planar_3_5A : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_5AD planar_3_5AM

theorem planar_3_5A_gram_check : SparseGramCheck planar_3_5AS planar_3_5AM planar_3_5AR planar_3_5AT planar_3_5Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_5A_posSemidef : (planar_3_5A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_5A_gram_check

/- N=3, d=5, H; dimension=1, rank=1. -/
def planar_3_5HD : ℤ := 8
def planar_3_5HS : ℤ := 8
def planar_3_5HM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 405)]
  | _ => []

def planar_3_5HR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_5HT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_5Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 3240
  | _ => 0

def planar_3_5H : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_5HD planar_3_5HM

theorem planar_3_5H_gram_check : SparseGramCheck planar_3_5HS planar_3_5HM planar_3_5HR planar_3_5HT planar_3_5Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_5H_posSemidef : (planar_3_5H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_5H_gram_check

def planar_3_5KD : ℤ := 143101237992056941602343095
def planar_3_5KU : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_5KL : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def planar_3_5KVA : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 405)]
  | _ => []

def planar_3_5KVH : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 353336390103844300252699)]
  | _ => []

def planar_3_5U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix planar_3_5KD planar_3_5KU
def planar_3_5L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix planar_3_5KL

def planar_3_5AV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_5AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_5KD planar_3_5KVA

theorem planar_3_5A_kernel_check : SparseScaledFrameCheck planar_3_5KD planar_3_5AM planar_3_5KU planar_3_5KL planar_3_5KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_5A_kernel_frame : HasKernelFrame planar_3_5A planar_3_5U planar_3_5L planar_3_5AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_5KD≠0) planar_3_5A_kernel_check).scale_matrix
    (by norm_num [planar_3_5AD])

theorem planar_3_5A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_5A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_5A_kernel_frame.ratCast

def planar_3_5HV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_5HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_5KD planar_3_5KVH

theorem planar_3_5H_kernel_check : SparseScaledFrameCheck planar_3_5KD planar_3_5HM planar_3_5KU planar_3_5KL planar_3_5KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_5H_kernel_frame : HasKernelFrame planar_3_5H planar_3_5U planar_3_5L planar_3_5HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_5KD≠0) planar_3_5H_kernel_check).scale_matrix
    (by norm_num [planar_3_5HD])

theorem planar_3_5H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_5H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_5H_kernel_frame.ratCast

theorem planar_3_5_same_kernel (v : Fin 1 → ℂ) :
    (planar_3_5A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_3_5H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_3_5A_kernel_frame.ratCast planar_3_5H_kernel_frame.ratCast v

def planar_3_5WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_5RS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_5W : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix planar_3_5WS
def planar_3_5R : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix 1 planar_3_5RS

theorem planar_3_5_complement : HasComplement planar_3_5U planar_3_5L planar_3_5W planar_3_5R := by
  unfold HasComplement
  decide +kernel

theorem planar_3_5A_active_posDef :
    ((planar_3_5W.map (Rat.castHom ℂ))ᴴ * (planar_3_5A.map (Rat.castHom ℂ)) * (planar_3_5W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_5A_kernel_frame.ratCast planar_3_5A_posSemidef _ _
    ((planar_3_5_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_5_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_3_5H_active_posDef :
    ((planar_3_5W.map (Rat.castHom ℂ))ᴴ * (planar_3_5H.map (Rat.castHom ℂ)) * (planar_3_5W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_5H_kernel_frame.ratCast planar_3_5H_posSemidef _ _
    ((planar_3_5_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_5_complement.map (Rat.castHom ℂ)).2.2)

/- N=3, d=6, A; dimension=2, rank=1. -/
def planar_3_6AD : ℤ := 250000000000000000000000
def planar_3_6AS : ℤ := 250000000000000000000000
def planar_3_6AM : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 2215052568130295867007), (⟨1, by decide⟩, -2215052568130295867007)]
  | 1 => [(⟨0, by decide⟩, -2215052568130295867007), (⟨1, by decide⟩, 2215052568130295867007)]
  | _ => []

def planar_3_6AR : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1), (⟨1, by decide⟩, -1)]
  | _ => []

def planar_3_6AT : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨0, by decide⟩, -1)]
  | _ => []

def planar_3_6Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 553763142032573966751750000000000000000000000
  | _ => 0

def planar_3_6A : Matrix (Fin 2) (Fin 2) ℚ := sparseRatScaledMatrix planar_3_6AD planar_3_6AM

theorem planar_3_6A_gram_check : SparseGramCheck planar_3_6AS planar_3_6AM planar_3_6AR planar_3_6AT planar_3_6Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_6A_posSemidef : (planar_3_6A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_6A_gram_check

/- N=3, d=6, H; dimension=2, rank=1. -/
def planar_3_6HD : ℤ := 40
def planar_3_6HS : ℤ := 40
def planar_3_6HM : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 6561), (⟨1, by decide⟩, -6561)]
  | 1 => [(⟨0, by decide⟩, -6561), (⟨1, by decide⟩, 6561)]
  | _ => []

def planar_3_6HR : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1), (⟨1, by decide⟩, -1)]
  | _ => []

def planar_3_6HT : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨0, by decide⟩, -1)]
  | _ => []

def planar_3_6Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 262440
  | _ => 0

def planar_3_6H : Matrix (Fin 2) (Fin 2) ℚ := sparseRatScaledMatrix planar_3_6HD planar_3_6HM

theorem planar_3_6H_gram_check : SparseGramCheck planar_3_6HS planar_3_6HM planar_3_6HR planar_3_6HT planar_3_6Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_6H_posSemidef : (planar_3_6H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_6H_gram_check

def planar_3_6KD : ℤ := 4844319966500957061144309
def planar_3_6KU : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 4844319966500957061144309)]
  | 1 => [(⟨0, by decide⟩, 4844319966500957061144309)]
  | _ => []

def planar_3_6KL : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨1, by decide⟩, 1)]
  | _ => []

def planar_3_6KVA : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 2187)]
  | _ => []

def planar_3_6KVH : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 738350856043431955669)]
  | _ => []

def planar_3_6U : Matrix (Fin 2) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_6KD planar_3_6KU
def planar_3_6L : Matrix (Fin 1) (Fin 2) ℚ := sparseRatMatrix planar_3_6KL

def planar_3_6AV : Matrix (Fin 2) (Fin 2) ℚ :=
  ((planar_3_6AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_6KD planar_3_6KVA

theorem planar_3_6A_kernel_check : SparseScaledFrameCheck planar_3_6KD planar_3_6AM planar_3_6KU planar_3_6KL planar_3_6KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_6A_kernel_frame : HasKernelFrame planar_3_6A planar_3_6U planar_3_6L planar_3_6AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_6KD≠0) planar_3_6A_kernel_check).scale_matrix
    (by norm_num [planar_3_6AD])

theorem planar_3_6A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_6A.map (Rat.castHom ℂ)).mulVecLin)=1 :=
  kernelFrame_finrank planar_3_6A_kernel_frame.ratCast

def planar_3_6HV : Matrix (Fin 2) (Fin 2) ℚ :=
  ((planar_3_6HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_6KD planar_3_6KVH

theorem planar_3_6H_kernel_check : SparseScaledFrameCheck planar_3_6KD planar_3_6HM planar_3_6KU planar_3_6KL planar_3_6KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_6H_kernel_frame : HasKernelFrame planar_3_6H planar_3_6U planar_3_6L planar_3_6HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_6KD≠0) planar_3_6H_kernel_check).scale_matrix
    (by norm_num [planar_3_6HD])

theorem planar_3_6H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_6H.map (Rat.castHom ℂ)).mulVecLin)=1 :=
  kernelFrame_finrank planar_3_6H_kernel_frame.ratCast

theorem planar_3_6_same_kernel (v : Fin 2 → ℂ) :
    (planar_3_6A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_3_6H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_3_6A_kernel_frame.ratCast planar_3_6H_kernel_frame.ratCast v

def planar_3_6WS : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_6RS : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1), (⟨1, by decide⟩, -1)]
  | _ => []

def planar_3_6W : Matrix (Fin 2) (Fin 1) ℚ := sparseRatMatrix planar_3_6WS
def planar_3_6R : Matrix (Fin 1) (Fin 2) ℚ := sparseRatScaledMatrix 1 planar_3_6RS

theorem planar_3_6_complement : HasComplement planar_3_6U planar_3_6L planar_3_6W planar_3_6R := by
  unfold HasComplement
  decide +kernel

theorem planar_3_6A_active_posDef :
    ((planar_3_6W.map (Rat.castHom ℂ))ᴴ * (planar_3_6A.map (Rat.castHom ℂ)) * (planar_3_6W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_6A_kernel_frame.ratCast planar_3_6A_posSemidef _ _
    ((planar_3_6_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_6_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_3_6H_active_posDef :
    ((planar_3_6W.map (Rat.castHom ℂ))ᴴ * (planar_3_6H.map (Rat.castHom ℂ)) * (planar_3_6W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_6H_kernel_frame.ratCast planar_3_6H_posSemidef _ _
    ((planar_3_6_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_6_complement.map (Rat.castHom ℂ)).2.2)

/- N=3, d=7, A; dimension=1, rank=1. -/
def planar_3_7AD : ℤ := 6250000000000000000000000
def planar_3_7AS : ℤ := 6250000000000000000000000
def planar_3_7AM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 5015494973490863806537)]
  | _ => []

def planar_3_7AR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_7AT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_7Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 31346843584317898790856250000000000000000000000
  | _ => 0

def planar_3_7A : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_7AD planar_3_7AM

theorem planar_3_7A_gram_check : SparseGramCheck planar_3_7AS planar_3_7AM planar_3_7AR planar_3_7AT planar_3_7Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_7A_posSemidef : (planar_3_7A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_7A_gram_check

/- N=3, d=7, H; dimension=1, rank=1. -/
def planar_3_7HD : ℤ := 320
def planar_3_7HS : ℤ := 320
def planar_3_7HM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 137781)]
  | _ => []

def planar_3_7HR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_7HT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_7Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 44089920
  | _ => 0

def planar_3_7H : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_7HD planar_3_7HM

theorem planar_3_7H_gram_check : SparseGramCheck planar_3_7HS planar_3_7HM planar_3_7HR planar_3_7HT planar_3_7Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_7H_posSemidef : (planar_3_7H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_7H_gram_check

def planar_3_7KD : ℤ := 691039912942544706128474397
def planar_3_7KU : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def planar_3_7KL : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def planar_3_7KVA : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 137781)]
  | _ => []

def planar_3_7KVH : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 5015494973490863806537)]
  | _ => []

def planar_3_7U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix planar_3_7KD planar_3_7KU
def planar_3_7L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix planar_3_7KL

def planar_3_7AV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_7AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_7KD planar_3_7KVA

theorem planar_3_7A_kernel_check : SparseScaledFrameCheck planar_3_7KD planar_3_7AM planar_3_7KU planar_3_7KL planar_3_7KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_7A_kernel_frame : HasKernelFrame planar_3_7A planar_3_7U planar_3_7L planar_3_7AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_7KD≠0) planar_3_7A_kernel_check).scale_matrix
    (by norm_num [planar_3_7AD])

theorem planar_3_7A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_7A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_7A_kernel_frame.ratCast

def planar_3_7HV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_3_7HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_7KD planar_3_7KVH

theorem planar_3_7H_kernel_check : SparseScaledFrameCheck planar_3_7KD planar_3_7HM planar_3_7KU planar_3_7KL planar_3_7KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_7H_kernel_frame : HasKernelFrame planar_3_7H planar_3_7U planar_3_7L planar_3_7HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_7KD≠0) planar_3_7H_kernel_check).scale_matrix
    (by norm_num [planar_3_7HD])

theorem planar_3_7H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_7H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_3_7H_kernel_frame.ratCast

theorem planar_3_7_same_kernel (v : Fin 1 → ℂ) :
    (planar_3_7A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_3_7H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_3_7A_kernel_frame.ratCast planar_3_7H_kernel_frame.ratCast v

def planar_3_7WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_7RS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_7W : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix planar_3_7WS
def planar_3_7R : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix 1 planar_3_7RS

theorem planar_3_7_complement : HasComplement planar_3_7U planar_3_7L planar_3_7W planar_3_7R := by
  unfold HasComplement
  decide +kernel

theorem planar_3_7A_active_posDef :
    ((planar_3_7W.map (Rat.castHom ℂ))ᴴ * (planar_3_7A.map (Rat.castHom ℂ)) * (planar_3_7W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_7A_kernel_frame.ratCast planar_3_7A_posSemidef _ _
    ((planar_3_7_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_7_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_3_7H_active_posDef :
    ((planar_3_7W.map (Rat.castHom ℂ))ᴴ * (planar_3_7H.map (Rat.castHom ℂ)) * (planar_3_7W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_7H_kernel_frame.ratCast planar_3_7H_posSemidef _ _
    ((planar_3_7_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_7_complement.map (Rat.castHom ℂ)).2.2)

/- N=3, d=8, A; dimension=2, rank=1. -/
def planar_3_8AD : ℤ := 1914062500000000000000000
def planar_3_8AS : ℤ := 1914062500000000000000000
def planar_3_8AM : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 691798755440651671869279), (⟨1, by decide⟩, -691798755440651671869279)]
  | 1 => [(⟨0, by decide⟩, -691798755440651671869279), (⟨1, by decide⟩, 691798755440651671869279)]
  | _ => []

def planar_3_8AR : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1), (⟨1, by decide⟩, -1)]
  | _ => []

def planar_3_8AT : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨0, by decide⟩, -1)]
  | _ => []

def planar_3_8Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 1324146055335622340687291835937500000000000000000
  | _ => 0

def planar_3_8A : Matrix (Fin 2) (Fin 2) ℚ := sparseRatScaledMatrix planar_3_8AD planar_3_8AM

theorem planar_3_8A_gram_check : SparseGramCheck planar_3_8AS planar_3_8AM planar_3_8AR planar_3_8AT planar_3_8Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_8A_posSemidef : (planar_3_8A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_8A_gram_check

/- N=3, d=8, H; dimension=2, rank=1. -/
def planar_3_8HD : ℤ := 35
def planar_3_8HS : ℤ := 35
def planar_3_8HM : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 59049), (⟨1, by decide⟩, -59049)]
  | 1 => [(⟨0, by decide⟩, -59049), (⟨1, by decide⟩, 59049)]
  | _ => []

def planar_3_8HR : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1), (⟨1, by decide⟩, -1)]
  | _ => []

def planar_3_8HT : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨0, by decide⟩, -1)]
  | _ => []

def planar_3_8Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 2066715
  | _ => 0

def planar_3_8H : Matrix (Fin 2) (Fin 2) ℚ := sparseRatScaledMatrix planar_3_8HD planar_3_8HM

theorem planar_3_8H_gram_check : SparseGramCheck planar_3_8HS planar_3_8HM planar_3_8HR planar_3_8HT planar_3_8Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_3_8H_posSemidef : (planar_3_8H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_3_8H_gram_check

def planar_3_8KD : ℤ := 13616674903338346857403018557
def planar_3_8KU : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 13616674903338346857403018557)]
  | 1 => [(⟨0, by decide⟩, 13616674903338346857403018557)]
  | _ => []

def planar_3_8KL : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨1, by decide⟩, 1)]
  | _ => []

def planar_3_8KVA : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 19683)]
  | _ => []

def planar_3_8KVH : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 230599585146883890623093)]
  | _ => []

def planar_3_8U : Matrix (Fin 2) (Fin 1) ℚ := sparseRatScaledMatrix planar_3_8KD planar_3_8KU
def planar_3_8L : Matrix (Fin 1) (Fin 2) ℚ := sparseRatMatrix planar_3_8KL

def planar_3_8AV : Matrix (Fin 2) (Fin 2) ℚ :=
  ((planar_3_8AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_8KD planar_3_8KVA

theorem planar_3_8A_kernel_check : SparseScaledFrameCheck planar_3_8KD planar_3_8AM planar_3_8KU planar_3_8KL planar_3_8KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_8A_kernel_frame : HasKernelFrame planar_3_8A planar_3_8U planar_3_8L planar_3_8AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_8KD≠0) planar_3_8A_kernel_check).scale_matrix
    (by norm_num [planar_3_8AD])

theorem planar_3_8A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_8A.map (Rat.castHom ℂ)).mulVecLin)=1 :=
  kernelFrame_finrank planar_3_8A_kernel_frame.ratCast

def planar_3_8HV : Matrix (Fin 2) (Fin 2) ℚ :=
  ((planar_3_8HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_3_8KD planar_3_8KVH

theorem planar_3_8H_kernel_check : SparseScaledFrameCheck planar_3_8KD planar_3_8HM planar_3_8KU planar_3_8KL planar_3_8KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_3_8H_kernel_frame : HasKernelFrame planar_3_8H planar_3_8U planar_3_8L planar_3_8HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_3_8KD≠0) planar_3_8H_kernel_check).scale_matrix
    (by norm_num [planar_3_8HD])

theorem planar_3_8H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_3_8H.map (Rat.castHom ℂ)).mulVecLin)=1 :=
  kernelFrame_finrank planar_3_8H_kernel_frame.ratCast

theorem planar_3_8_same_kernel (v : Fin 2 → ℂ) :
    (planar_3_8A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_3_8H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_3_8A_kernel_frame.ratCast planar_3_8H_kernel_frame.ratCast v

def planar_3_8WS : SparseIntMatrix 2 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_3_8RS : SparseIntMatrix 1 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1), (⟨1, by decide⟩, -1)]
  | _ => []

def planar_3_8W : Matrix (Fin 2) (Fin 1) ℚ := sparseRatMatrix planar_3_8WS
def planar_3_8R : Matrix (Fin 1) (Fin 2) ℚ := sparseRatScaledMatrix 1 planar_3_8RS

theorem planar_3_8_complement : HasComplement planar_3_8U planar_3_8L planar_3_8W planar_3_8R := by
  unfold HasComplement
  decide +kernel

theorem planar_3_8A_active_posDef :
    ((planar_3_8W.map (Rat.castHom ℂ))ᴴ * (planar_3_8A.map (Rat.castHom ℂ)) * (planar_3_8W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_8A_kernel_frame.ratCast planar_3_8A_posSemidef _ _
    ((planar_3_8_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_8_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_3_8H_active_posDef :
    ((planar_3_8W.map (Rat.castHom ℂ))ᴴ * (planar_3_8H.map (Rat.castHom ℂ)) * (planar_3_8W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_3_8H_kernel_frame.ratCast planar_3_8H_posSemidef _ _
    ((planar_3_8_complement.map (Rat.castHom ℂ)).2.1) ((planar_3_8_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=0, A; dimension=1, rank=1. -/
def planar_4_0AD : ℤ := 134811438777630720000000000000000000000000
def planar_4_0AS : ℤ := 134811438777630720000000000000000000000000
def planar_4_0AM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 473644590916212189999960985930176534687917)]
  | _ => []

def planar_4_0AR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_0AT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_0Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 63852708770656887105303505439591327695928020391115872010240000000000000000000000000
  | _ => 0

def planar_4_0A : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_4_0AD planar_4_0AM

theorem planar_4_0A_gram_check : SparseGramCheck planar_4_0AS planar_4_0AM planar_4_0AR planar_4_0AT planar_4_0Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_0A_posSemidef : (planar_4_0A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_0A_gram_check

/- N=4, d=0, H; dimension=1, rank=1. -/
def planar_4_0HD : ℤ := 1
def planar_4_0HS : ℤ := 1
def planar_4_0HM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 144)]
  | _ => []

def planar_4_0HR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_0HT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_0Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 144
  | _ => 0

def planar_4_0H : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_4_0HD planar_4_0HM

theorem planar_4_0H_gram_check : SparseGramCheck planar_4_0HS planar_4_0HM planar_4_0HR planar_4_0HT planar_4_0Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_0H_posSemidef : (planar_4_0H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_0H_gram_check

def planar_4_0KD : ℤ := 68204821091934555359994381973945420995060048
def planar_4_0KU : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_0KL : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def planar_4_0KVA : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 144)]
  | _ => []

def planar_4_0KVH : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 473644590916212189999960985930176534687917)]
  | _ => []

def planar_4_0U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_0KD planar_4_0KU
def planar_4_0L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix planar_4_0KL

def planar_4_0AV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_4_0AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_0KD planar_4_0KVA

theorem planar_4_0A_kernel_check : SparseScaledFrameCheck planar_4_0KD planar_4_0AM planar_4_0KU planar_4_0KL planar_4_0KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_0A_kernel_frame : HasKernelFrame planar_4_0A planar_4_0U planar_4_0L planar_4_0AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_0KD≠0) planar_4_0A_kernel_check).scale_matrix
    (by norm_num [planar_4_0AD])

theorem planar_4_0A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_0A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_0A_kernel_frame.ratCast

def planar_4_0HV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_4_0HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_0KD planar_4_0KVH

theorem planar_4_0H_kernel_check : SparseScaledFrameCheck planar_4_0KD planar_4_0HM planar_4_0KU planar_4_0KL planar_4_0KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_0H_kernel_frame : HasKernelFrame planar_4_0H planar_4_0U planar_4_0L planar_4_0HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_0KD≠0) planar_4_0H_kernel_check).scale_matrix
    (by norm_num [planar_4_0HD])

theorem planar_4_0H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_0H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_0H_kernel_frame.ratCast

theorem planar_4_0_same_kernel (v : Fin 1 → ℂ) :
    (planar_4_0A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_0H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_0A_kernel_frame.ratCast planar_4_0H_kernel_frame.ratCast v

def planar_4_0WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_0RS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_0W : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix planar_4_0WS
def planar_4_0R : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix 1 planar_4_0RS

theorem planar_4_0_complement : HasComplement planar_4_0U planar_4_0L planar_4_0W planar_4_0R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_0A_active_posDef :
    ((planar_4_0W.map (Rat.castHom ℂ))ᴴ * (planar_4_0A.map (Rat.castHom ℂ)) * (planar_4_0W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_0A_kernel_frame.ratCast planar_4_0A_posSemidef _ _
    ((planar_4_0_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_0_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_0H_active_posDef :
    ((planar_4_0W.map (Rat.castHom ℂ))ᴴ * (planar_4_0H.map (Rat.castHom ℂ)) * (planar_4_0W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_0H_kernel_frame.ratCast planar_4_0H_posSemidef _ _
    ((planar_4_0_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_0_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=1, A; dimension=0, rank=0. -/
def planar_4_1AD : ℤ := 1
def planar_4_1AS : ℤ := 1
def planar_4_1AM : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1AR : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1AT : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1Aw : Fin 0 → ℤ := fun i =>
  match i.val with
  | _ => 0

def planar_4_1A : Matrix (Fin 0) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_1AD planar_4_1AM

theorem planar_4_1A_gram_check : SparseGramCheck planar_4_1AS planar_4_1AM planar_4_1AR planar_4_1AT planar_4_1Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_1A_posSemidef : (planar_4_1A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_1A_gram_check

/- N=4, d=1, H; dimension=0, rank=0. -/
def planar_4_1HD : ℤ := 1
def planar_4_1HS : ℤ := 1
def planar_4_1HM : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1HR : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1HT : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1Hw : Fin 0 → ℤ := fun i =>
  match i.val with
  | _ => 0

def planar_4_1H : Matrix (Fin 0) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_1HD planar_4_1HM

theorem planar_4_1H_gram_check : SparseGramCheck planar_4_1HS planar_4_1HM planar_4_1HR planar_4_1HT planar_4_1Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_1H_posSemidef : (planar_4_1H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_1H_gram_check

def planar_4_1KD : ℤ := 1
def planar_4_1KU : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1KL : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1KVA : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1KVH : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1U : Matrix (Fin 0) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_1KD planar_4_1KU
def planar_4_1L : Matrix (Fin 0) (Fin 0) ℚ := sparseRatMatrix planar_4_1KL

def planar_4_1AV : Matrix (Fin 0) (Fin 0) ℚ :=
  ((planar_4_1AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_1KD planar_4_1KVA

theorem planar_4_1A_kernel_check : SparseScaledFrameCheck planar_4_1KD planar_4_1AM planar_4_1KU planar_4_1KL planar_4_1KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_1A_kernel_frame : HasKernelFrame planar_4_1A planar_4_1U planar_4_1L planar_4_1AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_1KD≠0) planar_4_1A_kernel_check).scale_matrix
    (by norm_num [planar_4_1AD])

theorem planar_4_1A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_1A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_1A_kernel_frame.ratCast

def planar_4_1HV : Matrix (Fin 0) (Fin 0) ℚ :=
  ((planar_4_1HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_1KD planar_4_1KVH

theorem planar_4_1H_kernel_check : SparseScaledFrameCheck planar_4_1KD planar_4_1HM planar_4_1KU planar_4_1KL planar_4_1KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_1H_kernel_frame : HasKernelFrame planar_4_1H planar_4_1U planar_4_1L planar_4_1HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_1KD≠0) planar_4_1H_kernel_check).scale_matrix
    (by norm_num [planar_4_1HD])

theorem planar_4_1H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_1H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_1H_kernel_frame.ratCast

theorem planar_4_1_same_kernel (v : Fin 0 → ℂ) :
    (planar_4_1A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_1H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_1A_kernel_frame.ratCast planar_4_1H_kernel_frame.ratCast v

def planar_4_1WS : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1RS : SparseIntMatrix 0 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_1W : Matrix (Fin 0) (Fin 0) ℚ := sparseRatMatrix planar_4_1WS
def planar_4_1R : Matrix (Fin 0) (Fin 0) ℚ := sparseRatScaledMatrix 1 planar_4_1RS

theorem planar_4_1_complement : HasComplement planar_4_1U planar_4_1L planar_4_1W planar_4_1R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_1A_active_posDef :
    ((planar_4_1W.map (Rat.castHom ℂ))ᴴ * (planar_4_1A.map (Rat.castHom ℂ)) * (planar_4_1W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_1A_kernel_frame.ratCast planar_4_1A_posSemidef _ _
    ((planar_4_1_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_1_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_1H_active_posDef :
    ((planar_4_1W.map (Rat.castHom ℂ))ᴴ * (planar_4_1H.map (Rat.castHom ℂ)) * (planar_4_1W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_1H_kernel_frame.ratCast planar_4_1H_posSemidef _ _
    ((planar_4_1_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_1_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=2, A; dimension=1, rank=1. -/
def planar_4_2AD : ℤ := 606651474499338240000000000000000000000000
def planar_4_2AS : ℤ := 606651474499338240000000000000000000000000
def planar_4_2AM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3533566795909849901084351539799683827600341)]
  | _ => []

def planar_4_2AR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_2AT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_2Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 2143643506980612638403639708225282048172572825583051698339840000000000000000000000000
  | _ => 0

def planar_4_2A : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_4_2AD planar_4_2AM

theorem planar_4_2A_gram_check : SparseGramCheck planar_4_2AS planar_4_2AM planar_4_2AR planar_4_2AT planar_4_2Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_2A_posSemidef : (planar_4_2A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_2A_gram_check

/- N=4, d=2, H; dimension=1, rank=1. -/
def planar_4_2HD : ℤ := 1
def planar_4_2HS : ℤ := 1
def planar_4_2HM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 64)]
  | _ => []

def planar_4_2HR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_2HT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_2Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 64
  | _ => 0

def planar_4_2H : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_4_2HD planar_4_2HM

theorem planar_4_2H_gram_check : SparseGramCheck planar_4_2HS planar_4_2HM planar_4_2HR planar_4_2HT planar_4_2Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_2H_posSemidef : (planar_4_2H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_2H_gram_check

def planar_4_2KD : ℤ := 226148274938230393669398498547179764966421824
def planar_4_2KU : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_2KL : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def planar_4_2KVA : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 64)]
  | _ => []

def planar_4_2KVH : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3533566795909849901084351539799683827600341)]
  | _ => []

def planar_4_2U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_2KD planar_4_2KU
def planar_4_2L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix planar_4_2KL

def planar_4_2AV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_4_2AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_2KD planar_4_2KVA

theorem planar_4_2A_kernel_check : SparseScaledFrameCheck planar_4_2KD planar_4_2AM planar_4_2KU planar_4_2KL planar_4_2KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_2A_kernel_frame : HasKernelFrame planar_4_2A planar_4_2U planar_4_2L planar_4_2AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_2KD≠0) planar_4_2A_kernel_check).scale_matrix
    (by norm_num [planar_4_2AD])

theorem planar_4_2A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_2A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_2A_kernel_frame.ratCast

def planar_4_2HV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_4_2HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_2KD planar_4_2KVH

theorem planar_4_2H_kernel_check : SparseScaledFrameCheck planar_4_2KD planar_4_2HM planar_4_2KU planar_4_2KL planar_4_2KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_2H_kernel_frame : HasKernelFrame planar_4_2H planar_4_2U planar_4_2L planar_4_2HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_2KD≠0) planar_4_2H_kernel_check).scale_matrix
    (by norm_num [planar_4_2HD])

theorem planar_4_2H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_2H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_2H_kernel_frame.ratCast

theorem planar_4_2_same_kernel (v : Fin 1 → ℂ) :
    (planar_4_2A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_2H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_2A_kernel_frame.ratCast planar_4_2H_kernel_frame.ratCast v

def planar_4_2WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_2RS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_2W : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix planar_4_2WS
def planar_4_2R : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix 1 planar_4_2RS

theorem planar_4_2_complement : HasComplement planar_4_2U planar_4_2L planar_4_2W planar_4_2R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_2A_active_posDef :
    ((planar_4_2W.map (Rat.castHom ℂ))ᴴ * (planar_4_2A.map (Rat.castHom ℂ)) * (planar_4_2W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_2A_kernel_frame.ratCast planar_4_2A_posSemidef _ _
    ((planar_4_2_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_2_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_2H_active_posDef :
    ((planar_4_2W.map (Rat.castHom ℂ))ᴴ * (planar_4_2H.map (Rat.castHom ℂ)) * (planar_4_2W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_2H_kernel_frame.ratCast planar_4_2H_posSemidef _ _
    ((planar_4_2_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_2_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=3, A; dimension=1, rank=1. -/
def planar_4_3AD : ℤ := 4697620480000000000000000000000000
def planar_4_3AS : ℤ := 4697620480000000000000000000000000
def planar_4_3AM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 9582815795973647481442642956689811)]
  | _ => []

def planar_4_3AR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_3AT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_3Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 45016431739233307949125379498673809160929280000000000000000000000000
  | _ => 0

def planar_4_3A : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_4_3AD planar_4_3AM

theorem planar_4_3A_gram_check : SparseGramCheck planar_4_3AS planar_4_3AM planar_4_3AR planar_4_3AT planar_4_3Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_3A_posSemidef : (planar_4_3A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_3A_gram_check

/- N=4, d=3, H; dimension=1, rank=1. -/
def planar_4_3HD : ℤ := 1
def planar_4_3HS : ℤ := 1
def planar_4_3HM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 72)]
  | _ => []

def planar_4_3HR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_3HT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_3Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 72
  | _ => 0

def planar_4_3H : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_4_3HD planar_4_3HM

theorem planar_4_3H_gram_check : SparseGramCheck planar_4_3HS planar_4_3HM planar_4_3HR planar_4_3HT planar_4_3Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_3H_posSemidef : (planar_4_3H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_3H_gram_check

def planar_4_3KD : ℤ := 229987579103367539554623430960555464
def planar_4_3KU : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_3KL : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def planar_4_3KVA : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 24)]
  | _ => []

def planar_4_3KVH : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3194271931991215827147547652229937)]
  | _ => []

def planar_4_3U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_3KD planar_4_3KU
def planar_4_3L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix planar_4_3KL

def planar_4_3AV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_4_3AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_3KD planar_4_3KVA

theorem planar_4_3A_kernel_check : SparseScaledFrameCheck planar_4_3KD planar_4_3AM planar_4_3KU planar_4_3KL planar_4_3KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_3A_kernel_frame : HasKernelFrame planar_4_3A planar_4_3U planar_4_3L planar_4_3AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_3KD≠0) planar_4_3A_kernel_check).scale_matrix
    (by norm_num [planar_4_3AD])

theorem planar_4_3A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_3A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_3A_kernel_frame.ratCast

def planar_4_3HV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_4_3HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_3KD planar_4_3KVH

theorem planar_4_3H_kernel_check : SparseScaledFrameCheck planar_4_3KD planar_4_3HM planar_4_3KU planar_4_3KL planar_4_3KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_3H_kernel_frame : HasKernelFrame planar_4_3H planar_4_3U planar_4_3L planar_4_3HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_3KD≠0) planar_4_3H_kernel_check).scale_matrix
    (by norm_num [planar_4_3HD])

theorem planar_4_3H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_3H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_3H_kernel_frame.ratCast

theorem planar_4_3_same_kernel (v : Fin 1 → ℂ) :
    (planar_4_3A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_3H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_3A_kernel_frame.ratCast planar_4_3H_kernel_frame.ratCast v

def planar_4_3WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_3RS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_3W : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix planar_4_3WS
def planar_4_3R : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix 1 planar_4_3RS

theorem planar_4_3_complement : HasComplement planar_4_3U planar_4_3L planar_4_3W planar_4_3R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_3A_active_posDef :
    ((planar_4_3W.map (Rat.castHom ℂ))ᴴ * (planar_4_3A.map (Rat.castHom ℂ)) * (planar_4_3W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_3A_kernel_frame.ratCast planar_4_3A_posSemidef _ _
    ((planar_4_3_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_3_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_3H_active_posDef :
    ((planar_4_3W.map (Rat.castHom ℂ))ᴴ * (planar_4_3H.map (Rat.castHom ℂ)) * (planar_4_3W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_3H_kernel_frame.ratCast planar_4_3H_posSemidef _ _
    ((planar_4_3_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_3_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=4, A; dimension=2, rank=2. -/
def planar_4_4AD : ℤ := 28436787867156480000000000000000000000000
def planar_4_4AS : ℤ := 8101833911373024608756993594397329470708943960975701574669649017952727929465553315578191991385702560649815878497651013875160359488269844480000000000000000000000000000
def planar_4_4AM : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 658012684930060424142188294807402683786385), (⟨1, by decide⟩, 254227895324566219387242490855503609896419)]
  | 1 => [(⟨0, by decide⟩, 254227895324566219387242490855503609896419), (⟨1, by decide⟩, 392009540874123364847188836264381120405449)]
  | _ => []

def planar_4_4AR : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 658012684930060424142188294807402683786385), (⟨1, by decide⟩, 254227895324566219387242490855503609896419)]
  | 1 => [(⟨1, by decide⟩, 658012684930060424142188294807402683786385)]
  | _ => []

def planar_4_4AT : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 658012684930060424142188294807402683786385)]
  | 1 => [(⟨0, by decide⟩, 254227895324566219387242490855503609896419), (⟨1, by decide⟩, 658012684930060424142188294807402683786385)]
  | _ => []

def planar_4_4Aw : Fin 2 → ℤ := fun i =>
  match i.val with
  | 0 => 12312580132454682451807434609833009993652811498738985895121633125239236572652331139490590848974848000000000000000000000000000
  | 1 => 5497269810307787433086873654469294068213003261998423810426623184192954572444040554854384660297809920000000000000000000000000
  | _ => 0

def planar_4_4A : Matrix (Fin 2) (Fin 2) ℚ := sparseRatScaledMatrix planar_4_4AD planar_4_4AM

theorem planar_4_4A_gram_check : SparseGramCheck planar_4_4AS planar_4_4AM planar_4_4AR planar_4_4AT planar_4_4Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_4A_posSemidef : (planar_4_4A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_4A_gram_check

/- N=4, d=4, H; dimension=2, rank=2. -/
def planar_4_4HD : ℤ := 3
def planar_4_4HS : ℤ := 1500
def planar_4_4HM : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 520), (⟨1, by decide⟩, -364)]
  | 1 => [(⟨0, by decide⟩, -364), (⟨1, by decide⟩, 562)]
  | _ => []

def planar_4_4HR : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 10), (⟨1, by decide⟩, -7)]
  | 1 => [(⟨1, by decide⟩, 10)]
  | _ => []

def planar_4_4HT : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 10)]
  | 1 => [(⟨0, by decide⟩, -7), (⟨1, by decide⟩, 10)]
  | _ => []

def planar_4_4Hw : Fin 2 → ℤ := fun i =>
  match i.val with
  | 0 => 7800
  | 1 => 4608
  | _ => 0

def planar_4_4H : Matrix (Fin 2) (Fin 2) ℚ := sparseRatScaledMatrix planar_4_4HD planar_4_4HM

theorem planar_4_4H_gram_check : SparseGramCheck planar_4_4HS planar_4_4HM planar_4_4HR planar_4_4HT planar_4_4Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_4H_posSemidef : (planar_4_4H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_4H_gram_check

def planar_4_4KD : ℤ := 321676871772045641633075380954880957754222630101810593620221053386788420638638188537856
def planar_4_4KU : SparseIntMatrix 2 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_4KL : SparseIntMatrix 0 2 := fun i =>
  match i.val with
  | _ => []

def planar_4_4KVA : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 652303876014541279105722223543930184354667136), (⟨1, by decide⟩, -423035217820078189060371504783558006867641216)]
  | 1 => [(⟨0, by decide⟩, -423035217820078189060371504783558006867641216), (⟨1, by decide⟩, 1094933107723620545772601322559518065820544640)]
  | _ => []

def planar_4_4KVH : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1131700733272546390460914739186718113092655236611187610267454377024333260710353202363), (⟨1, by decide⟩, 732987663543072751117033745665418849049335420153865284941909952378749656403146913986)]
  | 1 => [(⟨0, by decide⟩, 732987663543072751117033745665418849049335420153865284941909952378749656403146913986), (⟨1, by decide⟩, 1047125233632961073024333922379169784356193457362664692774157074826785223433067019980)]
  | _ => []

def planar_4_4U : Matrix (Fin 2) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_4KD planar_4_4KU
def planar_4_4L : Matrix (Fin 0) (Fin 2) ℚ := sparseRatMatrix planar_4_4KL

def planar_4_4AV : Matrix (Fin 2) (Fin 2) ℚ :=
  ((planar_4_4AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_4KD planar_4_4KVA

theorem planar_4_4A_kernel_check : SparseScaledFrameCheck planar_4_4KD planar_4_4AM planar_4_4KU planar_4_4KL planar_4_4KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_4A_kernel_frame : HasKernelFrame planar_4_4A planar_4_4U planar_4_4L planar_4_4AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_4KD≠0) planar_4_4A_kernel_check).scale_matrix
    (by norm_num [planar_4_4AD])

theorem planar_4_4A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_4A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_4A_kernel_frame.ratCast

def planar_4_4HV : Matrix (Fin 2) (Fin 2) ℚ :=
  ((planar_4_4HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_4KD planar_4_4KVH

theorem planar_4_4H_kernel_check : SparseScaledFrameCheck planar_4_4KD planar_4_4HM planar_4_4KU planar_4_4KL planar_4_4KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_4H_kernel_frame : HasKernelFrame planar_4_4H planar_4_4U planar_4_4L planar_4_4HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_4KD≠0) planar_4_4H_kernel_check).scale_matrix
    (by norm_num [planar_4_4HD])

theorem planar_4_4H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_4H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_4H_kernel_frame.ratCast

theorem planar_4_4_same_kernel (v : Fin 2 → ℂ) :
    (planar_4_4A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_4H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_4A_kernel_frame.ratCast planar_4_4H_kernel_frame.ratCast v

def planar_4_4WS : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | _ => []

def planar_4_4RS : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | _ => []

def planar_4_4W : Matrix (Fin 2) (Fin 2) ℚ := sparseRatMatrix planar_4_4WS
def planar_4_4R : Matrix (Fin 2) (Fin 2) ℚ := sparseRatScaledMatrix 1 planar_4_4RS

theorem planar_4_4_complement : HasComplement planar_4_4U planar_4_4L planar_4_4W planar_4_4R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_4A_active_posDef :
    ((planar_4_4W.map (Rat.castHom ℂ))ᴴ * (planar_4_4A.map (Rat.castHom ℂ)) * (planar_4_4W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_4A_kernel_frame.ratCast planar_4_4A_posSemidef _ _
    ((planar_4_4_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_4_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_4H_active_posDef :
    ((planar_4_4W.map (Rat.castHom ℂ))ᴴ * (planar_4_4H.map (Rat.castHom ℂ)) * (planar_4_4W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_4H_kernel_frame.ratCast planar_4_4H_posSemidef _ _
    ((planar_4_4_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_4_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=5, A; dimension=1, rank=1. -/
def planar_4_5AD : ℤ := 73400320000000000000000000000000
def planar_4_5AS : ℤ := 73400320000000000000000000000000
def planar_4_5AM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 297961458431951777633181877225579)]
  | _ => []

def planar_4_5AR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_5AT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_5Aw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 21870466396571958702844392406558210785280000000000000000000000000
  | _ => 0

def planar_4_5A : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_4_5AD planar_4_5AM

theorem planar_4_5A_gram_check : SparseGramCheck planar_4_5AS planar_4_5AM planar_4_5AR planar_4_5AT planar_4_5Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_5A_posSemidef : (planar_4_5A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_5A_gram_check

/- N=4, d=5, H; dimension=1, rank=1. -/
def planar_4_5HD : ℤ := 1
def planar_4_5HS : ℤ := 1
def planar_4_5HM : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 256)]
  | _ => []

def planar_4_5HR : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_5HT : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_5Hw : Fin 1 → ℤ := fun i =>
  match i.val with
  | 0 => 256
  | _ => 0

def planar_4_5H : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix planar_4_5HD planar_4_5HM

theorem planar_4_5H_gram_check : SparseGramCheck planar_4_5HS planar_4_5HM planar_4_5HR planar_4_5HT planar_4_5Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_5H_posSemidef : (planar_4_5H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_5H_gram_check

def planar_4_5KD : ℤ := 76278133358579655074094560569748224
def planar_4_5KU : SparseIntMatrix 1 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_5KL : SparseIntMatrix 0 1 := fun i =>
  match i.val with
  | _ => []

def planar_4_5KVA : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 256)]
  | _ => []

def planar_4_5KVH : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 297961458431951777633181877225579)]
  | _ => []

def planar_4_5U : Matrix (Fin 1) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_5KD planar_4_5KU
def planar_4_5L : Matrix (Fin 0) (Fin 1) ℚ := sparseRatMatrix planar_4_5KL

def planar_4_5AV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_4_5AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_5KD planar_4_5KVA

theorem planar_4_5A_kernel_check : SparseScaledFrameCheck planar_4_5KD planar_4_5AM planar_4_5KU planar_4_5KL planar_4_5KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_5A_kernel_frame : HasKernelFrame planar_4_5A planar_4_5U planar_4_5L planar_4_5AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_5KD≠0) planar_4_5A_kernel_check).scale_matrix
    (by norm_num [planar_4_5AD])

theorem planar_4_5A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_5A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_5A_kernel_frame.ratCast

def planar_4_5HV : Matrix (Fin 1) (Fin 1) ℚ :=
  ((planar_4_5HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_5KD planar_4_5KVH

theorem planar_4_5H_kernel_check : SparseScaledFrameCheck planar_4_5KD planar_4_5HM planar_4_5KU planar_4_5KL planar_4_5KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_5H_kernel_frame : HasKernelFrame planar_4_5H planar_4_5U planar_4_5L planar_4_5HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_5KD≠0) planar_4_5H_kernel_check).scale_matrix
    (by norm_num [planar_4_5HD])

theorem planar_4_5H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_5H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_5H_kernel_frame.ratCast

theorem planar_4_5_same_kernel (v : Fin 1 → ℂ) :
    (planar_4_5A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_5H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_5A_kernel_frame.ratCast planar_4_5H_kernel_frame.ratCast v

def planar_4_5WS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_5RS : SparseIntMatrix 1 1 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | _ => []

def planar_4_5W : Matrix (Fin 1) (Fin 1) ℚ := sparseRatMatrix planar_4_5WS
def planar_4_5R : Matrix (Fin 1) (Fin 1) ℚ := sparseRatScaledMatrix 1 planar_4_5RS

theorem planar_4_5_complement : HasComplement planar_4_5U planar_4_5L planar_4_5W planar_4_5R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_5A_active_posDef :
    ((planar_4_5W.map (Rat.castHom ℂ))ᴴ * (planar_4_5A.map (Rat.castHom ℂ)) * (planar_4_5W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_5A_kernel_frame.ratCast planar_4_5A_posSemidef _ _
    ((planar_4_5_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_5_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_5H_active_posDef :
    ((planar_4_5W.map (Rat.castHom ℂ))ᴴ * (planar_4_5H.map (Rat.castHom ℂ)) * (planar_4_5W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_5H_kernel_frame.ratCast planar_4_5H_posSemidef _ _
    ((planar_4_5_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_5_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=6, A; dimension=3, rank=3. -/
def planar_4_6AD : ℤ := 5924330805657600000000000000000000000000
def planar_4_6AS : ℤ := 6375781140103448573805356904911364742812400146500948803240778295908272751212752773979204898868296609428501053631459278025460929508540770579499305903729433164831365961234408794864602574698606152247365653554607470413296198689417801931482738718442204895780997413073246350039690677843202330196528466778545182920736634748835815292684440403943967948800000000000000000000000000
def planar_4_6AM : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 832011554355178672059851082668946396843753), (⟨1, by decide⟩, -672737294913873234036513066057071594117133), (⟨2, by decide⟩, 398981678018050474950981416360438464667247)]
  | 1 => [(⟨0, by decide⟩, -672737294913873234036513066057071594117133), (⟨1, by decide⟩, 553906427856423783735858285237245541480033), (⟨2, by decide⟩, -315278287385466953151262210518357554977707)]
  | 2 => [(⟨0, by decide⟩, 398981678018050474950981416360438464667247), (⟨1, by decide⟩, -315278287385466953151262210518357554977707), (⟨2, by decide⟩, 330059067075860099885045279085506405600633)]
  | _ => []

def planar_4_6AR : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 588101067891669554340477515893459674895587980951181622653743528437477015263443442934930542978809421481205722893), (⟨1, by decide⟩, -475519263498722501436958548086949140096948023263972460388175652560599669705124159981674830686782473359810260673), (⟨2, by decide⟩, 282017178347332491134405764306808737714905099957102644094351419587485260803688232061262298149528689824040968107)]
  | 1 => [(⟨1, by decide⟩, 588101067891669554340477515893459674895587980951181622653743528437477015263443442934930542978809421481205722893), (⟨2, by decide⟩, 432828320149712336493029759429195513245816055245360671166658560837611823009871412655497936413815877929651270104)]
  | 2 => [(⟨2, by decide⟩, 588101067891669554340477515893459674895587980951181622653743528437477015263443442934930542978809421481205722893)]
  | _ => []

def planar_4_6AT : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 588101067891669554340477515893459674895587980951181622653743528437477015263443442934930542978809421481205722893)]
  | 1 => [(⟨0, by decide⟩, -475519263498722501436958548086949140096948023263972460388175652560599669705124159981674830686782473359810260673), (⟨1, by decide⟩, 588101067891669554340477515893459674895587980951181622653743528437477015263443442934930542978809421481205722893)]
  | 2 => [(⟨0, by decide⟩, 282017178347332491134405764306808737714905099957102644094351419587485260803688232061262298149528689824040968107), (⟨1, by decide⟩, 432828320149712336493029759429195513245816055245360671166658560837611823009871412655497936413815877929651270104), (⟨2, by decide⟩, 588101067891669554340477515893459674895587980951181622653743528437477015263443442934930542978809421481205722893)]
  | _ => []

def planar_4_6Aw : Fin 3 → ℤ := fun i =>
  match i.val with
  | 0 => 15337649968347258470792301382943231627815782867184778186411889041325404505469678021175643928958007226011699667732102306928387044548355569106291899624661337025419673600000000000000000000000000
  | 1 => 183479306316236316140894980371630234441889860440587515981248839103509828533300431381695318071754962657692760623187850346218836484665706849541866520029076168638464000000000000000000000000000
  | 2 => 2458059246342870698569891890821699177768866432629122440755276627362073074612466759347739340403633474730012540280327960433185156677011196082421652605700512447201280000000000000000000000000000
  | _ => 0

def planar_4_6A : Matrix (Fin 3) (Fin 3) ℚ := sparseRatScaledMatrix planar_4_6AD planar_4_6AM

theorem planar_4_6A_gram_check : SparseGramCheck planar_4_6AS planar_4_6AM planar_4_6AR planar_4_6AT planar_4_6Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_6A_posSemidef : (planar_4_6A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_6A_gram_check

/- N=4, d=6, H; dimension=3, rank=3. -/
def planar_4_6HD : ℤ := 15
def planar_4_6HS : ℤ := 1896222163129921316385
def planar_4_6HM : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 17631), (⟨1, by decide⟩, -10881), (⟨2, by decide⟩, -8136)]
  | 1 => [(⟨0, by decide⟩, -10881), (⟨1, by decide⟩, 12591), (⟨2, by decide⟩, 10056)]
  | 2 => [(⟨0, by decide⟩, -8136), (⟨1, by decide⟩, 10056), (⟨2, by decide⟩, 12496)]
  | _ => []

def planar_4_6HR : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 10439511), (⟨1, by decide⟩, -6442761), (⟨2, by decide⟩, -4817416)]
  | 1 => [(⟨1, by decide⟩, 10439511), (⟨2, by decide⟩, 8945447)]
  | 2 => [(⟨2, by decide⟩, 10439511)]
  | _ => []

def planar_4_6HT : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 10439511)]
  | 1 => [(⟨0, by decide⟩, -6442761), (⟨1, by decide⟩, 10439511)]
  | 2 => [(⟨0, by decide⟩, -4817416), (⟨1, by decide⟩, 8945447), (⟨2, by decide⟩, 10439511)]
  | _ => []

def planar_4_6Hw : Fin 3 → ℤ := fun i =>
  match i.val with
  | 0 => 306765030735
  | 1 => 102233667600
  | 2 => 77031014400
  | _ => 0

def planar_4_6H : Matrix (Fin 3) (Fin 3) ℚ := sparseRatScaledMatrix planar_4_6HD planar_4_6HM

theorem planar_4_6H_gram_check : SparseGramCheck planar_4_6HS planar_4_6HM planar_4_6HR planar_4_6HT planar_4_6Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_6H_posSemidef : (planar_4_6H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_6H_gram_check

def planar_4_6KD : ℤ := 5211697601689055037599532409448915614971698764805614457557211172406613659634234327061419527276456803946392807014400
def planar_4_6KU : SparseIntMatrix 3 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_6KL : SparseIntMatrix 0 3 := fun i =>
  match i.val with
  | _ => []

def planar_4_6KVA : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 393737725925237521323961548889049437481646353329730212614180704836045830144), (⟨1, by decide⟩, 454299902507427801648727512728791915187672903909896850264457419920383574016), (⟨2, by decide⟩, -42002310342681120743233932284831673659121589677337925510416607440296364032)]
  | 1 => [(⟨0, by decide⟩, 454299902507427801648727512728791915187672903909896850264457419920383574016), (⟨1, by decide⟩, 544797574421467802039062412309359824803880018142397811007686581923673391104), (⟨2, by decide⟩, -28766036560090138715646527519089941035589662387129020346986110302578556928)]
  | 2 => [(⟨0, by decide⟩, -42002310342681120743233932284831673659121589677337925510416607440296364032), (⟨1, by decide⟩, -28766036560090138715646527519089941035589662387129020346986110302578556928), (⟨2, by decide⟩, 39085558944359807236807066593643441957769547132315461414565924056140363776)]
  | _ => []

def planar_4_6KVH : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 638770727859109277388621346536838997168074527100297509925401573472586363295477164759569724741663936674823868375), (⟨1, by decide⟩, 615355270630383427220369866629206167070155483916678534921796074871516338681302900967806823016263460379423984785), (⟨2, by decide⟩, -79303293821816794437757370630567792501442797197351056851833716960227724872533591521159261503950669717439228385)]
  | 1 => [(⟨0, by decide⟩, 615355270630383427220369866629206167070155483916678534921796074871516338681302900967806823016263460379423984785), (⟨1, by decide⟩, 1751324024781211307185794387682730949661234264445246041333609163188835918548402771838216275484801032605521901255), (⟨2, by decide⟩, -1008705498667658558034204475643591633683625699913196033252804167723453670407463017872201228730380895505292469495)]
  | 2 => [(⟨0, by decide⟩, -79303293821816794437757370630567792501442797197351056851833716960227724872533591521159261503950669717439228385), (⟨1, by decide⟩, -1008705498667658558034204475643591633683625699913196033252804167723453670407463017872201228730380895505292469495), (⟨2, by decide⟩, 1177178977093208071194454117243163694262363972882127526360506623067001520461647657984004748062822058284773392935)]
  | _ => []

def planar_4_6U : Matrix (Fin 3) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_6KD planar_4_6KU
def planar_4_6L : Matrix (Fin 0) (Fin 3) ℚ := sparseRatMatrix planar_4_6KL

def planar_4_6AV : Matrix (Fin 3) (Fin 3) ℚ :=
  ((planar_4_6AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_6KD planar_4_6KVA

theorem planar_4_6A_kernel_check : SparseScaledFrameCheck planar_4_6KD planar_4_6AM planar_4_6KU planar_4_6KL planar_4_6KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_6A_kernel_frame : HasKernelFrame planar_4_6A planar_4_6U planar_4_6L planar_4_6AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_6KD≠0) planar_4_6A_kernel_check).scale_matrix
    (by norm_num [planar_4_6AD])

theorem planar_4_6A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_6A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_6A_kernel_frame.ratCast

def planar_4_6HV : Matrix (Fin 3) (Fin 3) ℚ :=
  ((planar_4_6HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_6KD planar_4_6KVH

theorem planar_4_6H_kernel_check : SparseScaledFrameCheck planar_4_6KD planar_4_6HM planar_4_6KU planar_4_6KL planar_4_6KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_6H_kernel_frame : HasKernelFrame planar_4_6H planar_4_6U planar_4_6L planar_4_6HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_6KD≠0) planar_4_6H_kernel_check).scale_matrix
    (by norm_num [planar_4_6HD])

theorem planar_4_6H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_6H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_6H_kernel_frame.ratCast

theorem planar_4_6_same_kernel (v : Fin 3 → ℂ) :
    (planar_4_6A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_6H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_6A_kernel_frame.ratCast planar_4_6H_kernel_frame.ratCast v

def planar_4_6WS : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | _ => []

def planar_4_6RS : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | _ => []

def planar_4_6W : Matrix (Fin 3) (Fin 3) ℚ := sparseRatMatrix planar_4_6WS
def planar_4_6R : Matrix (Fin 3) (Fin 3) ℚ := sparseRatScaledMatrix 1 planar_4_6RS

theorem planar_4_6_complement : HasComplement planar_4_6U planar_4_6L planar_4_6W planar_4_6R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_6A_active_posDef :
    ((planar_4_6W.map (Rat.castHom ℂ))ᴴ * (planar_4_6A.map (Rat.castHom ℂ)) * (planar_4_6W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_6A_kernel_frame.ratCast planar_4_6A_posSemidef _ _
    ((planar_4_6_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_6_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_6H_active_posDef :
    ((planar_4_6W.map (Rat.castHom ℂ))ᴴ * (planar_4_6H.map (Rat.castHom ℂ)) * (planar_4_6W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_6H_kernel_frame.ratCast planar_4_6H_posSemidef _ _
    ((planar_4_6_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_6_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=7, A; dimension=2, rank=2. -/
def planar_4_7AD : ℤ := 58982400000000000000000000000000
def planar_4_7AS : ℤ := 3121396127489072691378018395084536221697897027699213384877884198235333109054621713992241266650768998400000000000000000000000000
def planar_4_7AM : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1013691752903476340672294336075037), (⟨1, by decide⟩, -1216254614499566088089636645855316)]
  | 1 => [(⟨0, by decide⟩, -1216254614499566088089636645855316), (⟨1, by decide⟩, 1512907135197521840745450247079888)]
  | _ => []

def planar_4_7AR : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 37544138996425049654529419854631), (⟨1, by decide⟩, -45046467203687632892208764661308)]
  | 1 => [(⟨1, by decide⟩, 37544138996425049654529419854631)]
  | _ => []

def planar_4_7AT : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 37544138996425049654529419854631)]
  | 1 => [(⟨0, by decide⟩, -45046467203687632892208764661308), (⟨1, by decide⟩, 37544138996425049654529419854631)]
  | _ => []

def planar_4_7Aw : Fin 2 → ℤ := fun i =>
  match i.val with
  | 0 => 2244763036122092959934192691764181451322679760361302253429270230617292800000000000000000000000000
  | 1 => 118721082309704564878678963343860859216504594033843138425205764915200000000000000000000000000000
  | _ => 0

def planar_4_7A : Matrix (Fin 2) (Fin 2) ℚ := sparseRatScaledMatrix planar_4_7AD planar_4_7AM

theorem planar_4_7A_gram_check : SparseGramCheck planar_4_7AS planar_4_7AM planar_4_7AR planar_4_7AT planar_4_7Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_7A_posSemidef : (planar_4_7A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_7A_gram_check

/- N=4, d=7, H; dimension=2, rank=2. -/
def planar_4_7HD : ℤ := 15
def planar_4_7HS : ℤ := 694721205
def planar_4_7HM : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 26892), (⟨1, by decide⟩, -31896)]
  | 1 => [(⟨0, by decide⟩, -31896), (⟨1, by decide⟩, 48688)]
  | _ => []

def planar_4_7HR : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 747), (⟨1, by decide⟩, -886)]
  | 1 => [(⟨1, by decide⟩, 747)]
  | _ => []

def planar_4_7HT : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 747)]
  | 1 => [(⟨0, by decide⟩, -886), (⟨1, by decide⟩, 747)]
  | _ => []

def planar_4_7Hw : Fin 2 → ℤ := fun i =>
  match i.val with
  | 0 => 33480540
  | 1 => 13516800
  | _ => 0

def planar_4_7H : Matrix (Fin 2) (Fin 2) ℚ := sparseRatScaledMatrix planar_4_7HD planar_4_7HM

theorem planar_4_7H_gram_check : SparseGramCheck planar_4_7HS planar_4_7HM planar_4_7HR planar_4_7HT planar_4_7Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_7H_posSemidef : (planar_4_7H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_7H_gram_check

def planar_4_7KD : ℤ := 114779171373640155497941575889084229125331589935063190469681354752000
def planar_4_7KU : SparseIntMatrix 2 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_7KL : SparseIntMatrix 0 2 := fun i =>
  match i.val with
  | _ => []

def planar_4_7KVA : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3195259869537166127654390921832723456), (⟨1, by decide⟩, 2568729745823083578045312596046427392)]
  | 1 => [(⟨0, by decide⟩, 2568729745823083578045312596046427392), (⟨1, by decide⟩, 2140916982132142031499885637790478144)]
  | _ => []

def planar_4_7KVH : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 19140680814765876713107431488851366816405374720095775934214122700), (⟨1, by decide⟩, 12539253106879978714288420858700361402728923596618774014083422150)]
  | 1 => [(⟨0, by decide⟩, 12539253106879978714288420858700361402728923596618774014083422150), (⟨1, by decide⟩, 10572033939999259706064842416985519151059261768255332041219318675)]
  | _ => []

def planar_4_7U : Matrix (Fin 2) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_7KD planar_4_7KU
def planar_4_7L : Matrix (Fin 0) (Fin 2) ℚ := sparseRatMatrix planar_4_7KL

def planar_4_7AV : Matrix (Fin 2) (Fin 2) ℚ :=
  ((planar_4_7AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_7KD planar_4_7KVA

theorem planar_4_7A_kernel_check : SparseScaledFrameCheck planar_4_7KD planar_4_7AM planar_4_7KU planar_4_7KL planar_4_7KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_7A_kernel_frame : HasKernelFrame planar_4_7A planar_4_7U planar_4_7L planar_4_7AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_7KD≠0) planar_4_7A_kernel_check).scale_matrix
    (by norm_num [planar_4_7AD])

theorem planar_4_7A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_7A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_7A_kernel_frame.ratCast

def planar_4_7HV : Matrix (Fin 2) (Fin 2) ℚ :=
  ((planar_4_7HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_7KD planar_4_7KVH

theorem planar_4_7H_kernel_check : SparseScaledFrameCheck planar_4_7KD planar_4_7HM planar_4_7KU planar_4_7KL planar_4_7KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_7H_kernel_frame : HasKernelFrame planar_4_7H planar_4_7U planar_4_7L planar_4_7HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_7KD≠0) planar_4_7H_kernel_check).scale_matrix
    (by norm_num [planar_4_7HD])

theorem planar_4_7H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_7H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_7H_kernel_frame.ratCast

theorem planar_4_7_same_kernel (v : Fin 2 → ℂ) :
    (planar_4_7A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_7H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_7A_kernel_frame.ratCast planar_4_7H_kernel_frame.ratCast v

def planar_4_7WS : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | _ => []

def planar_4_7RS : SparseIntMatrix 2 2 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | _ => []

def planar_4_7W : Matrix (Fin 2) (Fin 2) ℚ := sparseRatMatrix planar_4_7WS
def planar_4_7R : Matrix (Fin 2) (Fin 2) ℚ := sparseRatScaledMatrix 1 planar_4_7RS

theorem planar_4_7_complement : HasComplement planar_4_7U planar_4_7L planar_4_7W planar_4_7R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_7A_active_posDef :
    ((planar_4_7W.map (Rat.castHom ℂ))ᴴ * (planar_4_7A.map (Rat.castHom ℂ)) * (planar_4_7W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_7A_kernel_frame.ratCast planar_4_7A_posSemidef _ _
    ((planar_4_7_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_7_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_7H_active_posDef :
    ((planar_4_7W.map (Rat.castHom ℂ))ᴴ * (planar_4_7H.map (Rat.castHom ℂ)) * (planar_4_7W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_7H_kernel_frame.ratCast planar_4_7H_posSemidef _ _
    ((planar_4_7_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_7_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=8, A; dimension=4, rank=4. -/
def planar_4_8AD : ℤ := 17999268940800000000000000000000000000
def planar_4_8AS : ℤ := 2155656938445217238262182959608111297795468879990633439209308380355683562515188139176044940879120969202299269331833967343609149553516210525499510300562018059044592993341051416383168178416679002473230714827610655851731324854990776108797835168521103704074407650544124937640288939883230988577281004816109833764920544301318587186137120130983941245150063253234062391618828452260153200782432513145654652180491833065007781444256331678316710092729788341750753857872446868465379032739100014675544714894954646949010797934660091676847050116278595208044141867898700315135842534929463986578133115756777428564941843368894049888303920000000000000000000000000000000
def planar_4_8AM : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 13318271805918536837520345014528422953694), (⟨1, by decide⟩, -10449957734665672809664323111559881667294), (⟨2, by decide⟩, 6347319990890477303111463378753559662810), (⟨3, by decide⟩, 6029265981483050212567908862048177882574)]
  | 1 => [(⟨0, by decide⟩, -10449957734665672809664323111559881667294), (⟨1, by decide⟩, 8458847888741617768047579094056456711769), (⟨2, by decide⟩, -4867485459861754822507655964625344876870), (⟨3, by decide⟩, -5157422975512324820144856901893249202934)]
  | 2 => [(⟨0, by decide⟩, 6347319990890477303111463378753559662810), (⟨1, by decide⟩, -4867485459861754822507655964625344876870), (⟨2, by decide⟩, 5281175894859156477998583720282095220798), (⟨3, by decide⟩, 1261379689890224723748307504914796969098)]
  | 3 => [(⟨0, by decide⟩, 6029265981483050212567908862048177882574), (⟨1, by decide⟩, -5157422975512324820144856901893249202934), (⟨2, by decide⟩, 1261379689890224723748307504914796969098), (⟨3, by decide⟩, 4360707049998829679690686756563245129782)]
  | _ => []

def planar_4_8AR : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1753257739283743444175897931779613174701133504549223321370745767532695990586316024481211030687043695618351930664699444832778316649369571362871989139337771280532782947382212632340261559861298448360403603325), (⟨1, by decide⟩, -1375664165777776617316068363762633772658968870553079839630138456640895719494859523659574811388464970967706730774813902522777352673168228752892619229858252726873408360190908073258620386691512015955182483325), (⟨2, by decide⟩, 835580476199151862893227849594285694779375391671941922390182490867325745386734729972550204526135660026759612673187655722291688296208944648624635441384103058668802627399712752497504927060801990812013532375), (⟨3, by decide⟩, 793710880681812342371090223784091222005725767886858535924383320556441469084008489447587548387467725801728121156738710790789545647606152636213029642553433002341259731813249599895820611943671652087723732325)]
  | 1 => [(⟨1, by decide⟩, 1753257739283743444175897931779613174701133504549223321370745767532695990586316024481211030687043695618351930664699444832778316649369571362871989139337771280532782947382212632340261559861298448360403603325), (⟨2, by decide⟩, 762432276338777988424027627759014597345546989471227177116437333777341623508190784642632558102661605462621106616965485364317656476387284287231713780185036424514727072881881279383727890090993220611021504652), (⟨3, by decide⟩, -2883040259669482587569009458267228485026777291754019073008372281460589690409779777180697798047364744276917415575202739004729500843857615257693631107828758897804101420699472516647664332523457749794390051608)]
  | 2 => [(⟨2, by decide⟩, 1753257739283743444175897931779613174701133504549223321370745767532695990586316024481211030687043695618351930664699444832778316649369571362871989139337771280532782947382212632340261559861298448360403603325), (⟨3, by decide⟩, -1133234779326061230520557373203378368589588470875210262677607552713781779271850713135870366948657471609025802884392769266162295119137060168238665231817775866541579851407156350364112102955504843989840375175)]
  | 3 => [(⟨3, by decide⟩, 1753257739283743444175897931779613174701133504549223321370745767532695990586316024481211030687043695618351930664699444832778316649369571362871989139337771280532782947382212632340261559861298448360403603325)]
  | _ => []

def planar_4_8AT : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1753257739283743444175897931779613174701133504549223321370745767532695990586316024481211030687043695618351930664699444832778316649369571362871989139337771280532782947382212632340261559861298448360403603325)]
  | 1 => [(⟨0, by decide⟩, -1375664165777776617316068363762633772658968870553079839630138456640895719494859523659574811388464970967706730774813902522777352673168228752892619229858252726873408360190908073258620386691512015955182483325), (⟨1, by decide⟩, 1753257739283743444175897931779613174701133504549223321370745767532695990586316024481211030687043695618351930664699444832778316649369571362871989139337771280532782947382212632340261559861298448360403603325)]
  | 2 => [(⟨0, by decide⟩, 835580476199151862893227849594285694779375391671941922390182490867325745386734729972550204526135660026759612673187655722291688296208944648624635441384103058668802627399712752497504927060801990812013532375), (⟨1, by decide⟩, 762432276338777988424027627759014597345546989471227177116437333777341623508190784642632558102661605462621106616965485364317656476387284287231713780185036424514727072881881279383727890090993220611021504652), (⟨2, by decide⟩, 1753257739283743444175897931779613174701133504549223321370745767532695990586316024481211030687043695618351930664699444832778316649369571362871989139337771280532782947382212632340261559861298448360403603325)]
  | 3 => [(⟨0, by decide⟩, 793710880681812342371090223784091222005725767886858535924383320556441469084008489447587548387467725801728121156738710790789545647606152636213029642553433002341259731813249599895820611943671652087723732325), (⟨1, by decide⟩, -2883040259669482587569009458267228485026777291754019073008372281460589690409779777180697798047364744276917415575202739004729500843857615257693631107828758897804101420699472516647664332523457749794390051608), (⟨2, by decide⟩, -1133234779326061230520557373203378368589588470875210262677607552713781779271850713135870366948657471609025802884392769266162295119137060168238665231817775866541579851407156350364112102955504843989840375175), (⟨3, by decide⟩, 1753257739283743444175897931779613174701133504549223321370745767532695990586316024481211030687043695618351930664699444832778316649369571362871989139337771280532782947382212632340261559861298448360403603325)]
  | _ => []

def planar_4_8Aw : Fin 4 → ℤ := fun i =>
  match i.val with
  | 0 => 9339765902649339648083091101348661352191725219307446648589318293243791604793951963777499308217732618635953584215092011593194636181358378312673499782361217102139206628309536608253392312759936622374802806563744355112769519564247672210963659442742831456512000000000000000000000000000
  | 1 => 181955864426913200876249526301175891961870172228104135965254813790291310565775525674553048182589002607577330485666566202590733861751181039453018626014356867382766841920464482136577701404492877880042628160113687940042237267739225970214970064543642512000000000000000000000000000000
  | 2 => 1547752680678286656827590690775083999478258849923422107185426303771813880053876695170568800638651760040174676027893095368264489618510335295208689113049934255011836316226959440928035040683187711731308398300816928978010373289633681512482831408131212192972800000000000000000000000000
  | 3 => 5299977040927448192111398321909887562215290600218121580129002856597362519673165434842100592184628968784261778249176913546603329882718527951180070129305009176757139860415440778368783501810296847834542368390333960496709801328117491256330629855877350400000000000000000000000000000
  | _ => 0

def planar_4_8A : Matrix (Fin 4) (Fin 4) ℚ := sparseRatScaledMatrix planar_4_8AD planar_4_8AM

theorem planar_4_8A_gram_check : SparseGramCheck planar_4_8AS planar_4_8AM planar_4_8AR planar_4_8AT planar_4_8Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_8A_posSemidef : (planar_4_8A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_8A_gram_check

/- N=4, d=8, H; dimension=4, rank=4. -/
def planar_4_8HD : ℤ := 70
def planar_4_8HS : ℤ := 7697911160670315540673260031356828376201308127290000
def planar_4_8HM : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1080720), (⟨1, by decide⟩, -438120), (⟨2, by decide⟩, -329004), (⟨3, by decide⟩, 505416)]
  | 1 => [(⟨0, by decide⟩, -438120), (⟨1, by decide⟩, 460800), (⟨2, by decide⟩, 382554), (⟨3, by decide⟩, -681396)]
  | 2 => [(⟨0, by decide⟩, -329004), (⟨1, by decide⟩, 382554), (⟨2, by decide⟩, 444861), (⟨3, by decide⟩, -704118)]
  | 3 => [(⟨0, by decide⟩, 505416), (⟨1, by decide⟩, -681396), (⟨2, by decide⟩, -704118), (⟨3, by decide⟩, 1267428)]
  | _ => []

def planar_4_8HR : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 199313072349404940), (⟨1, by decide⟩, -80800802481420990), (⟨2, by decide⟩, -60676954303837833), (⟨3, by decide⟩, 93211947381881382)]
  | 1 => [(⟨1, by decide⟩, 199313072349404940), (⟨2, by decide⟩, 175375628664871260), (⟨3, by decide⟩, -335371565955964480)]
  | 2 => [(⟨2, by decide⟩, 199313072349404940), (⟨3, by decide⟩, -208096278852790560)]
  | 3 => [(⟨3, by decide⟩, 199313072349404940)]
  | _ => []

def planar_4_8HT : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 199313072349404940)]
  | 1 => [(⟨0, by decide⟩, -80800802481420990), (⟨1, by decide⟩, 199313072349404940)]
  | 2 => [(⟨0, by decide⟩, -60676954303837833), (⟨1, by decide⟩, 175375628664871260), (⟨2, by decide⟩, 199313072349404940)]
  | 3 => [(⟨0, by decide⟩, 93211947381881382), (⟨1, by decide⟩, -335371565955964480), (⟨2, by decide⟩, -208096278852790560), (⟨3, by decide⟩, 199313072349404940)]
  | _ => []

def planar_4_8Hw : Fin 4 → ℤ := fun i =>
  match i.val with
  | 0 => 209418245117519770458000
  | 1 => 54875154595572142429500
  | 2 => 24309527706193471956480
  | 3 => 17930216174709637120000
  | _ => 0

def planar_4_8H : Matrix (Fin 4) (Fin 4) ℚ := sparseRatScaledMatrix planar_4_8HD planar_4_8HM

theorem planar_4_8H_gram_check : SparseGramCheck planar_4_8HS planar_4_8HM planar_4_8HR planar_4_8HT planar_4_8Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_8H_posSemidef : (planar_4_8H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_8H_gram_check

def planar_4_8KD : ℤ := 63194716811871206643181739548612627643579328483491614479787940772835855043635369383180097825922456825485225921210726866041844641395682731622400
def planar_4_8KU : SparseIntMatrix 4 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_8KL : SparseIntMatrix 0 4 := fun i =>
  match i.val with
  | _ => []

def planar_4_8KVA : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 971944158940325873066205579484861169282489104554453600591298758009376265607328382964698433602737506877440), (⟨1, by decide⟩, 3723144333847431260100105515304520414118232895541621928614356822604513885943359221790037401748462382350336), (⟨2, by decide⟩, 1646332629246288278936468339594626586626204814222987107716172342031786450814830504803270667382381326106624), (⟨3, by decide⟩, 2583312661143195030307657674054191412083333280747913755464277527471896382700190634093995659289380903714816)]
  | 1 => [(⟨0, by decide⟩, 3723144333847431260100105515304520414118232895541621928614356822604513885943359221790037401748462382350336), (⟨1, by decide⟩, 15790172867820405477175102513438829862375227207661174448617066156056297076085586546070181547262172515532800), (⟨2, by decide⟩, 7355789994325423708060146641515485212957131509423524917542425862861468942693443027036060205097205011316736), (⟨3, by decide⟩, 11399602905603146490475884802878661691767653362196459229871422279990986388817215164939022710341335403986944)]
  | 2 => [(⟨0, by decide⟩, 1646332629246288278936468339594626586626204814222987107716172342031786450814830504803270667382381326106624), (⟨1, by decide⟩, 7355789994325423708060146641515485212957131509423524917542425862861468942693443027036060205097205011316736), (⟨2, by decide⟩, 3521991564580249504167387540865123562444708898546623142711856307786188779934993464824295539283960438980608), (⟨3, by decide⟩, 5404668120629090050278634744755121081504259007123460098331327699584901892929363208113912509373197217431552)]
  | 3 => [(⟨0, by decide⟩, 2583312661143195030307657674054191412083333280747913755464277527471896382700190634093995659289380903714816), (⟨1, by decide⟩, 11399602905603146490475884802878661691767653362196459229871422279990986388817215164939022710341335403986944), (⟨2, by decide⟩, 5404668120629090050278634744755121081504259007123460098331327699584901892929363208113912509373197217431552), (⟨3, by decide⟩, 8361706138588823378808709220062490569555064990827969043048715402799976961901690254769061592393378837823488)]
  | _ => []

def planar_4_8KVH : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 113985212862311114424190301411118523379823606831897165294528396531062520991776896161032930642781404342841564857775730933900089258925318505), (⟨1, by decide⟩, 197060174098128815292580186519963614639792723373681254639893467842920223483570723615019237625852073916287862648832223639305930872931810640), (⟨2, by decide⟩, 87674453016742531950691061121692912398770790268403363393036039494143537049775294984291589084181295230504782466650811041249090495821857040), (⟨3, by decide⟩, 109196912609626318914639010634796941239231708442286594518728665778007375970583675121588329980344965344014680545292780972159904674616893110)]
  | 1 => [(⟨0, by decide⟩, 197060174098128815292580186519963614639792723373681254639893467842920223483570723615019237625852073916287862648832223639305930872931810640), (⟨1, by decide⟩, 1011764386193216435945752796754322172116876060287056902594755769544149099469799076743233857216806924369258285465571965311952192944163049728), (⟨2, by decide⟩, 101509356913947416863853889139949639214464392549190904710259972102020814102569114927859112457769279885341693534724715544741828396349971712), (⟨3, by decide⟩, 521756980368169127197064084003570412362182025370812497158149130710019301841543338883706464520063710965315264348633598904830930697513681888)]
  | 2 => [(⟨0, by decide⟩, 87674453016742531950691061121692912398770790268403363393036039494143537049775294984291589084181295230504782466650811041249090495821857040), (⟨1, by decide⟩, 101509356913947416863853889139949639214464392549190904710259972102020814102569114927859112457769279885341693534724715544741828396349971712), (⟨2, by decide⟩, 1248220030630556845569030232749128904798454033698169856965526972891549115692153528109280376021998899072454365564983957588552030964205648128), (⟨3, by decide⟩, 713058406430465947983906415764346949521487531276444180450605890127019684721824602305498260893369409184292840654859976432142126825648114272)]
  | 3 => [(⟨0, by decide⟩, 109196912609626318914639010634796941239231708442286594518728665778007375970583675121588329980344965344014680545292780972159904674616893110), (⟨1, by decide⟩, 521756980368169127197064084003570412362182025370812497158149130710019301841543338883706464520063710965315264348633598904830930697513681888), (⟨2, by decide⟩, 713058406430465947983906415764346949521487531276444180450605890127019684721824602305498260893369409184292840654859976432142126825648114272), (⟨3, by decide⟩, 682962052631250141231473066389943576199455855666990447416819004033144003189663484557759718897173835416388598311739418194185311647016037828)]
  | _ => []

def planar_4_8U : Matrix (Fin 4) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_8KD planar_4_8KU
def planar_4_8L : Matrix (Fin 0) (Fin 4) ℚ := sparseRatMatrix planar_4_8KL

def planar_4_8AV : Matrix (Fin 4) (Fin 4) ℚ :=
  ((planar_4_8AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_8KD planar_4_8KVA

theorem planar_4_8A_kernel_check : SparseScaledFrameCheck planar_4_8KD planar_4_8AM planar_4_8KU planar_4_8KL planar_4_8KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_8A_kernel_frame : HasKernelFrame planar_4_8A planar_4_8U planar_4_8L planar_4_8AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_8KD≠0) planar_4_8A_kernel_check).scale_matrix
    (by norm_num [planar_4_8AD])

theorem planar_4_8A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_8A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_8A_kernel_frame.ratCast

def planar_4_8HV : Matrix (Fin 4) (Fin 4) ℚ :=
  ((planar_4_8HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_8KD planar_4_8KVH

theorem planar_4_8H_kernel_check : SparseScaledFrameCheck planar_4_8KD planar_4_8HM planar_4_8KU planar_4_8KL planar_4_8KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_8H_kernel_frame : HasKernelFrame planar_4_8H planar_4_8U planar_4_8L planar_4_8HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_8KD≠0) planar_4_8H_kernel_check).scale_matrix
    (by norm_num [planar_4_8HD])

theorem planar_4_8H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_8H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_8H_kernel_frame.ratCast

theorem planar_4_8_same_kernel (v : Fin 4 → ℂ) :
    (planar_4_8A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_8H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_8A_kernel_frame.ratCast planar_4_8H_kernel_frame.ratCast v

def planar_4_8WS : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | _ => []

def planar_4_8RS : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | _ => []

def planar_4_8W : Matrix (Fin 4) (Fin 4) ℚ := sparseRatMatrix planar_4_8WS
def planar_4_8R : Matrix (Fin 4) (Fin 4) ℚ := sparseRatScaledMatrix 1 planar_4_8RS

theorem planar_4_8_complement : HasComplement planar_4_8U planar_4_8L planar_4_8W planar_4_8R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_8A_active_posDef :
    ((planar_4_8W.map (Rat.castHom ℂ))ᴴ * (planar_4_8A.map (Rat.castHom ℂ)) * (planar_4_8W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_8A_kernel_frame.ratCast planar_4_8A_posSemidef _ _
    ((planar_4_8_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_8_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_8H_active_posDef :
    ((planar_4_8W.map (Rat.castHom ℂ))ᴴ * (planar_4_8H.map (Rat.castHom ℂ)) * (planar_4_8W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_8H_kernel_frame.ratCast planar_4_8H_posSemidef _ _
    ((planar_4_8_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_8_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=9, A; dimension=3, rank=3. -/
def planar_4_9AD : ℤ := 10035200000000000000000000000000
def planar_4_9AS : ℤ := 10269752910523703219611562164374115553739081645494590137042341668221627193565633173544196611204207366021666752260016187086497578784467183904699289314700230002420174405914466010526302286062575789595510211505355086565793916133529033636122435027952107064626338040298086119741644800000000000000000000000000
def planar_4_9AM : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1622443332933953944709071875790512), (⟨1, by decide⟩, -1383504249605399075238230042726220), (⟨2, by decide⟩, -810165018589290309951316718064300)]
  | 1 => [(⟨0, by decide⟩, -1383504249605399075238230042726220), (⟨1, by decide⟩, 1233610519036966422561796813695963), (⟨2, by decide⟩, 788951027126598060618400690735731)]
  | 2 => [(⟨0, by decide⟩, -810165018589290309951316718064300), (⟨1, by decide⟩, 788951027126598060618400690735731), (⟨2, by decide⟩, 602045682657050633646359496569547)]
  | _ => []

def planar_4_9AR : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 5813598882003748162462633148647468912425878442723541350125000962628351198458844430833636052), (⟨1, by decide⟩, -4957423532449993353566828662859479398443883171051887736521633942111202504844450670849959245), (⟨2, by decide⟩, -2903013221295030934027432184535614706344395634918406721644171177242777167413048642592535925)]
  | 1 => [(⟨1, by decide⟩, 5813598882003748162462633148647468912425878442723541350125000962628351198458844430833636052), (⟨2, by decide⟩, 10589500969089590431307783510152331354870148621130401605445266724663762627172139949927865924)]
  | 2 => [(⟨2, by decide⟩, 5813598882003748162462633148647468912425878442723541350125000962628351198458844430833636052)]
  | _ => []

def planar_4_9AT : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 5813598882003748162462633148647468912425878442723541350125000962628351198458844430833636052)]
  | 1 => [(⟨0, by decide⟩, -4957423532449993353566828662859479398443883171051887736521633942111202504844450670849959245), (⟨1, by decide⟩, 5813598882003748162462633148647468912425878442723541350125000962628351198458844430833636052)]
  | 2 => [(⟨0, by decide⟩, -2903013221295030934027432184535614706344395634918406721644171177242777167413048642592535925), (⟨1, by decide⟩, 10589500969089590431307783510152331354870148621130401605445266724663762627172139949927865924), (⟨2, by decide⟩, 5813598882003748162462633148647468912425878442723541350125000962628351198458844430833636052)]
  | _ => []

def planar_4_9Aw : Fin 3 → ℤ := fun i =>
  match i.val with
  | 0 => 492991469414937825158316505811353646174611974855400828546877977216839882391632489952400022499065290506883691747363672889805414400000000000000000000000000
  | 1 => 16364704312625959636922463329108893567901055127225945341820542406040994066738488118732241454921117446244061280652101447418265600000000000000000000000000
  | 2 => 5712902159439232922630414171414322305113270577859047969876363598657976778438780555752116741796605266087834741398405675008000000000000000000000000000000
  | _ => 0

def planar_4_9A : Matrix (Fin 3) (Fin 3) ℚ := sparseRatScaledMatrix planar_4_9AD planar_4_9AM

theorem planar_4_9A_gram_check : SparseGramCheck planar_4_9AS planar_4_9AM planar_4_9AR planar_4_9AT planar_4_9Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_9A_posSemidef : (planar_4_9A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_9A_gram_check

/- N=4, d=9, H; dimension=3, rank=3. -/
def planar_4_9HD : ℤ := 35
def planar_4_9HS : ℤ := 35715467134373040
def planar_4_9HM : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 801792), (⟨1, by decide⟩, -808704), (⟨2, by decide⟩, -695808)]
  | 1 => [(⟨0, by decide⟩, -808704), (⟨1, by decide⟩, 1112940), (⟨2, by decide⟩, 931500)]
  | 2 => [(⟨0, by decide⟩, -695808), (⟨1, by decide⟩, 931500), (⟨2, by decide⟩, 1012140)]
  | _ => []

def planar_4_9HR : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 440916), (⟨1, by decide⟩, -444717), (⟨2, by decide⟩, -382634)]
  | 1 => [(⟨1, by decide⟩, 440916), (⟨2, by decide⟩, 340692)]
  | 2 => [(⟨2, by decide⟩, 440916)]
  | _ => []

def planar_4_9HT : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 440916)]
  | 1 => [(⟨0, by decide⟩, -444717), (⟨1, by decide⟩, 440916)]
  | 2 => [(⟨0, by decide⟩, -382634), (⟨1, by decide⟩, 340692), (⟨2, by decide⟩, 440916)]
  | _ => []

def planar_4_9Hw : Fin 3 → ℤ := fun i =>
  match i.val with
  | 0 => 147301217280
  | 1 => 54611931780
  | 2 => 42405888000
  | _ => 0

def planar_4_9H : Matrix (Fin 3) (Fin 3) ℚ := sparseRatScaledMatrix planar_4_9HD planar_4_9HM

theorem planar_4_9H_gram_check : SparseGramCheck planar_4_9HS planar_4_9HM planar_4_9HR planar_4_9HT planar_4_9Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_9H_posSemidef : (planar_4_9H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_9H_gram_check

def planar_4_9KD : ℤ := 253317430814200490071709897305071536347417060359533301877317313502617816161897966690064465920000
def planar_4_9KU : SparseIntMatrix 3 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_9KL : SparseIntMatrix 0 3 := fun i =>
  match i.val with
  | _ => []

def planar_4_9KVA : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 18541358600100262454717366567337304501681651866854913895231411200), (⟨1, by decide⟩, 29875628358525188331137721024349887898722117052501973635349329920), (⟨2, by decide⟩, -14199665890569649145655865736357743654883399941052345205934172160)]
  | 1 => [(⟨0, by decide⟩, 29875628358525188331137721024349887898722117052501973635349329920), (⟨1, by decide⟩, 49406802650774606723335756219105305467335025247920347766584092672), (⟨2, by decide⟩, -24541922846634052939565414207318103901431989735980004813816825856)]
  | 2 => [(⟨0, by decide⟩, -14199665890569649145655865736357743654883399941052345205934172160), (⟨1, by decide⟩, -24541922846634052939565414207318103901431989735980004813816825856), (⟨2, by decide⟩, 13473429544969418320701232537821522514421301372585828270167205888)]
  | _ => []

def planar_4_9KVH : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1191445242510996825273205410368202429402826803243954887813983110416126789915034136569061875), (⟨1, by decide⟩, 784492179872695726124606586496130056002608464869754368136815232919203614493089749293636500), (⟨2, by decide⟩, 97084065198169828397877245100809224841911521415410485368257919485630626728404144713995500)]
  | 1 => [(⟨0, by decide⟩, 784492179872695726124606586496130056002608464869754368136815232919203614493089749293636500), (⟨1, by decide⟩, 1507394859703110397406027272603097426560966409834008894282334143406630872698998590259556400), (⟨2, by decide⟩, -847987805165872969530306227096138865013216768467094707885720474436571451899845272936817200)]
  | 2 => [(⟨0, by decide⟩, 97084065198169828397877245100809224841911521415410485368257919485630626728404144713995500), (⟨1, by decide⟩, -847987805165872969530306227096138865013216768467094707885720474436571451899845272936817200), (⟨2, by decide⟩, 1097446934775445405919201215251080635313325480743420832370998816252437210987848785302295600)]
  | _ => []

def planar_4_9U : Matrix (Fin 3) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_9KD planar_4_9KU
def planar_4_9L : Matrix (Fin 0) (Fin 3) ℚ := sparseRatMatrix planar_4_9KL

def planar_4_9AV : Matrix (Fin 3) (Fin 3) ℚ :=
  ((planar_4_9AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_9KD planar_4_9KVA

theorem planar_4_9A_kernel_check : SparseScaledFrameCheck planar_4_9KD planar_4_9AM planar_4_9KU planar_4_9KL planar_4_9KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_9A_kernel_frame : HasKernelFrame planar_4_9A planar_4_9U planar_4_9L planar_4_9AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_9KD≠0) planar_4_9A_kernel_check).scale_matrix
    (by norm_num [planar_4_9AD])

theorem planar_4_9A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_9A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_9A_kernel_frame.ratCast

def planar_4_9HV : Matrix (Fin 3) (Fin 3) ℚ :=
  ((planar_4_9HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_9KD planar_4_9KVH

theorem planar_4_9H_kernel_check : SparseScaledFrameCheck planar_4_9KD planar_4_9HM planar_4_9KU planar_4_9KL planar_4_9KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_9H_kernel_frame : HasKernelFrame planar_4_9H planar_4_9U planar_4_9L planar_4_9HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_9KD≠0) planar_4_9H_kernel_check).scale_matrix
    (by norm_num [planar_4_9HD])

theorem planar_4_9H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_9H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_9H_kernel_frame.ratCast

theorem planar_4_9_same_kernel (v : Fin 3 → ℂ) :
    (planar_4_9A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_9H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_9A_kernel_frame.ratCast planar_4_9H_kernel_frame.ratCast v

def planar_4_9WS : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | _ => []

def planar_4_9RS : SparseIntMatrix 3 3 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | _ => []

def planar_4_9W : Matrix (Fin 3) (Fin 3) ℚ := sparseRatMatrix planar_4_9WS
def planar_4_9R : Matrix (Fin 3) (Fin 3) ℚ := sparseRatScaledMatrix 1 planar_4_9RS

theorem planar_4_9_complement : HasComplement planar_4_9U planar_4_9L planar_4_9W planar_4_9R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_9A_active_posDef :
    ((planar_4_9W.map (Rat.castHom ℂ))ᴴ * (planar_4_9A.map (Rat.castHom ℂ)) * (planar_4_9W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_9A_kernel_frame.ratCast planar_4_9A_posSemidef _ _
    ((planar_4_9_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_9_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_9H_active_posDef :
    ((planar_4_9W.map (Rat.castHom ℂ))ᴴ * (planar_4_9H.map (Rat.castHom ℂ)) * (planar_4_9W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_9H_kernel_frame.ratCast planar_4_9H_posSemidef _ _
    ((planar_4_9_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_9_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=10, A; dimension=5, rank=5. -/
def planar_4_10AD : ℤ := 40498355116800000000000000000000000000
def planar_4_10AS : ℤ := 363638793452129503393326145916932896327228285049372556438239111301588069270787127116785708608676039515095377318723418952106329546806652123907550142996446869997214296087591333074950378902330303323058398121640346849898401530883210141548263801866581276089629476098269703990292449578361876031090561352905476370859783678521335566874425214176169650178980343902864385892315673167541476463488606435858151612656843368642699986452486746113376949689499908795956060315862395919763157652888048951523759207955118178093763162963959778794866278097629188877577927516099483100569875850466673062012360849415328522107216880295033287488629359533145770315963158506199786879595460242355266181845613111335899185750787647986354339977516174390046419687172982392796625969992559119379928685932324608946607849491209103767834903661075776083437941550917297344267875027873977189258337462721804329397600312462381774064457136201726021263252635373071367498549854946244955065587375173210907904000000000000000000000000000000
def planar_4_10AM : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 209945557905293792238435347441389839977500), (⟨1, by decide⟩, -159447122869720476967437880495535177062900), (⟨2, by decide⟩, 116436219027782710324508147582935487720900), (⟨3, by decide⟩, -109492467822338412788796556365922497092250), (⟨4, by decide⟩, 95346474841032027496905264547258826012850)]
  | 1 => [(⟨0, by decide⟩, -159447122869720476967437880495535177062900), (⟨1, by decide⟩, 126305845496022857001003000172743490620460), (⟨2, by decide⟩, -95058933989317411651649821087221274810604), (⟨3, by decide⟩, 88892068980967640492909880937129420873278), (⟨4, by decide⟩, -76723485202457441395632239555002254851526)]
  | 2 => [(⟨0, by decide⟩, 116436219027782710324508147582935487720900), (⟨1, by decide⟩, -95058933989317411651649821087221274810604), (⟨2, by decide⟩, 79559126960385093797950511945591460953692), (⟨3, by decide⟩, -75229119877715277218377932340279740809526), (⟨4, by decide⟩, 56609930289488289221226966889935255196638)]
  | 3 => [(⟨0, by decide⟩, -109492467822338412788796556365922497092250), (⟨1, by decide⟩, 88892068980967640492909880937129420873278), (⟨2, by decide⟩, -75229119877715277218377932340279740809526), (⟨3, by decide⟩, 71382651819371860761885949793673045662511), (⟨4, by decide⟩, -52445108920906838663553869493363154066419)]
  | 4 => [(⟨0, by decide⟩, 95346474841032027496905264547258826012850), (⟨1, by decide⟩, -76723485202457441395632239555002254851526), (⟨2, by decide⟩, 56609930289488289221226966889935255196638), (⟨3, by decide⟩, -52445108920906838663553869493363154066419), (⟨4, by decide⟩, 47608570826670771473912067240853537538727)]
  | _ => []

def planar_4_10AR : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 670693401686603974649470631884726761819115630112182812863979630903520378929695704073550937761432398556786776927087360135843862783058194720499334306846563351753858800279550474077650150814191422935122288286355934917641389413301937110950011988202882386578737844809325919693865600122909302434951177513789368774536851665200), (⟨1, by decide⟩, -509370783043074958184892847512786046605599004784048449676603611019263832338963516562489186232357720912824770993894361281812373921246660475741796937168885834782908495452418526534094844027527607363116008012096070204857291741296947124252144860080389367156974693729178417186967365566286127922674176433642675499547677223952), (⟨2, by decide⟩, 371967878713098266438222425100763070442399513423422983949853239504045097816323757451460346518986698603245109749050297404970275783744914281010271021545727304235480042774840385599652821098208819784363466911501292349991895669221271317820069763192377455942541568469056648498544031031632182600748799741280788382961758374992), (⟨3, by decide⟩, -349785327374976037042794056350642095135428155486258941297137557132993930790435716389551265593878265347014517472513068753026405412865085262575672956604235923535373893942536802211487034154436887993494720277033746562055382677725719054815727320640448353123710935246744465337673329666302153814113433868022971556802142252680), (⟨4, by decide⟩, 304594449094297859092770868799812646719966567810892496249069248401932397690270356124538733046836483608411794672046104778620259096824172410174755743696655104855683363661643309524437607299469442372819885268172034009496110038610312531747304823396435792031100530140574666242751880690052960259134288737091629076956364783208)]
  | 1 => [(⟨1, by decide⟩, 670693401686603974649470631884726761819115630112182812863979630903520378929695704073550937761432398556786776927087360135843862783058194720499334306846563351753858800279550474077650150814191422935122288286355934917641389413301937110950011988202882386578737844809325919693865600122909302434951177513789368774536851665200), (⟨2, by decide⟩, -853278828963759343140331603528881902073024028191093452893639485421054553428444367147781371555007374952546276068615019113560537720767104355968339435844879104580878270174057194686039341693841883537899600249165787921448921405861233346548477018761979789715987058032890654281687318227622964998370880370492994483599077064000), (⟨3, by decide⟩, 738298097198623186410365484827872931733328829560636427906348642314918868957430234941142665470233400465924155468344454371359543824671946320624084862472063691846624870825707979217854499525094531306405569504244714552696507717484533129008443673069145352279180730317475988397593448684605823383408928955645596321873561865600), (⟨4, by decide⟩, -554861936646907122210331646588175400495150300862245369853888082043538407025234969546023345743558909294951731508551674153181308777079573321758683093809595169878738036087237987130255708334521274696874104762898427171677021579804080463630047850038430978680186076172524390668252101446568223016061678000554536944102190352000)]
  | 2 => [(⟨2, by decide⟩, 670693401686603974649470631884726761819115630112182812863979630903520378929695704073550937761432398556786776927087360135843862783058194720499334306846563351753858800279550474077650150814191422935122288286355934917641389413301937110950011988202882386578737844809325919693865600122909302434951177513789368774536851665200), (⟨3, by decide⟩, -738024681855978665499134176365818492518511574342152061956480567338467531693684328437548672613662108746765231422299110643992893606508517259751903140613605812632735478455100673337485841346514387282524191886791257585346476381697328313449501701085564763703401156128663948136517210799604841230702815309338299716268847692275), (⟨4, by decide⟩, -179593880299770571854095394567021623510224295441450202149061659015042086333850040405081787143558582162497394979445491399312905622088175177030648790673680780581326252443558256783396075438736166174128809953665486923450165459196489674252955553834175964894881035039157091985390911496741832280723099956565580376451405658825)]
  | 3 => [(⟨3, by decide⟩, 670693401686603974649470631884726761819115630112182812863979630903520378929695704073550937761432398556786776927087360135843862783058194720499334306846563351753858800279550474077650150814191422935122288286355934917641389413301937110950011988202882386578737844809325919693865600122909302434951177513789368774536851665200), (⟨4, by decide⟩, 1858539600886965687293775891001933353096901479694907591401540567305438718795996266536993353425620649277833980198790341113261914386096882150213146802235184326386132928897885981765613214475300451961709648121710762550908843727013986977415132948662625276131631669231935992192707588760243346006914776005658823984736168310800)]
  | 4 => [(⟨4, by decide⟩, 670693401686603974649470631884726761819115630112182812863979630903520378929695704073550937761432398556786776927087360135843862783058194720499334306846563351753858800279550474077650150814191422935122288286355934917641389413301937110950011988202882386578737844809325919693865600122909302434951177513789368774536851665200)]
  | _ => []

def planar_4_10AT : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 670693401686603974649470631884726761819115630112182812863979630903520378929695704073550937761432398556786776927087360135843862783058194720499334306846563351753858800279550474077650150814191422935122288286355934917641389413301937110950011988202882386578737844809325919693865600122909302434951177513789368774536851665200)]
  | 1 => [(⟨0, by decide⟩, -509370783043074958184892847512786046605599004784048449676603611019263832338963516562489186232357720912824770993894361281812373921246660475741796937168885834782908495452418526534094844027527607363116008012096070204857291741296947124252144860080389367156974693729178417186967365566286127922674176433642675499547677223952), (⟨1, by decide⟩, 670693401686603974649470631884726761819115630112182812863979630903520378929695704073550937761432398556786776927087360135843862783058194720499334306846563351753858800279550474077650150814191422935122288286355934917641389413301937110950011988202882386578737844809325919693865600122909302434951177513789368774536851665200)]
  | 2 => [(⟨0, by decide⟩, 371967878713098266438222425100763070442399513423422983949853239504045097816323757451460346518986698603245109749050297404970275783744914281010271021545727304235480042774840385599652821098208819784363466911501292349991895669221271317820069763192377455942541568469056648498544031031632182600748799741280788382961758374992), (⟨1, by decide⟩, -853278828963759343140331603528881902073024028191093452893639485421054553428444367147781371555007374952546276068615019113560537720767104355968339435844879104580878270174057194686039341693841883537899600249165787921448921405861233346548477018761979789715987058032890654281687318227622964998370880370492994483599077064000), (⟨2, by decide⟩, 670693401686603974649470631884726761819115630112182812863979630903520378929695704073550937761432398556786776927087360135843862783058194720499334306846563351753858800279550474077650150814191422935122288286355934917641389413301937110950011988202882386578737844809325919693865600122909302434951177513789368774536851665200)]
  | 3 => [(⟨0, by decide⟩, -349785327374976037042794056350642095135428155486258941297137557132993930790435716389551265593878265347014517472513068753026405412865085262575672956604235923535373893942536802211487034154436887993494720277033746562055382677725719054815727320640448353123710935246744465337673329666302153814113433868022971556802142252680), (⟨1, by decide⟩, 738298097198623186410365484827872931733328829560636427906348642314918868957430234941142665470233400465924155468344454371359543824671946320624084862472063691846624870825707979217854499525094531306405569504244714552696507717484533129008443673069145352279180730317475988397593448684605823383408928955645596321873561865600), (⟨2, by decide⟩, -738024681855978665499134176365818492518511574342152061956480567338467531693684328437548672613662108746765231422299110643992893606508517259751903140613605812632735478455100673337485841346514387282524191886791257585346476381697328313449501701085564763703401156128663948136517210799604841230702815309338299716268847692275), (⟨3, by decide⟩, 670693401686603974649470631884726761819115630112182812863979630903520378929695704073550937761432398556786776927087360135843862783058194720499334306846563351753858800279550474077650150814191422935122288286355934917641389413301937110950011988202882386578737844809325919693865600122909302434951177513789368774536851665200)]
  | 4 => [(⟨0, by decide⟩, 304594449094297859092770868799812646719966567810892496249069248401932397690270356124538733046836483608411794672046104778620259096824172410174755743696655104855683363661643309524437607299469442372819885268172034009496110038610312531747304823396435792031100530140574666242751880690052960259134288737091629076956364783208), (⟨1, by decide⟩, -554861936646907122210331646588175400495150300862245369853888082043538407025234969546023345743558909294951731508551674153181308777079573321758683093809595169878738036087237987130255708334521274696874104762898427171677021579804080463630047850038430978680186076172524390668252101446568223016061678000554536944102190352000), (⟨2, by decide⟩, -179593880299770571854095394567021623510224295441450202149061659015042086333850040405081787143558582162497394979445491399312905622088175177030648790673680780581326252443558256783396075438736166174128809953665486923450165459196489674252955553834175964894881035039157091985390911496741832280723099956565580376451405658825), (⟨3, by decide⟩, 1858539600886965687293775891001933353096901479694907591401540567305438718795996266536993353425620649277833980198790341113261914386096882150213146802235184326386132928897885981765613214475300451961709648121710762550908843727013986977415132948662625276131631669231935992192707588760243346006914776005658823984736168310800), (⟨4, by decide⟩, 670693401686603974649470631884726761819115630112182812863979630903520378929695704073550937761432398556786776927087360135843862783058194720499334306846563351753858800279550474077650150814191422935122288286355934917641389413301937110950011988202882386578737844809325919693865600122909302434951177513789368774536851665200)]
  | _ => []

def planar_4_10Aw : Fin 5 → ℤ := fun i =>
  match i.val with
  | 0 => 169718361657628754900731685889057321480665098321785673024331519875717786536568566954944585311369182030261914248687629741412002816259664077937016622449066532477654831943540234205170023671166830614878609400880992085564950829523184975891118048839875405166765229426865256483723839314082290745602802689641329755029730592716381605321856382715910470021428542553261404204000000000000000000000000000000
  | 1 => 4212300615663962392517479615665624263107422091569008158040951205845843137585187201989158718671015313694604789363857553004592531996649502367747446954663563592278578185272976773432711974873968211034909898519009976185481274452687440311684564007558681739128782766632991606764389560436322167240647780434461659248558310429944584303543715079140907256288751044845670938905600000000000000000000000000
  | 2 => 5294500142910674124383992754745116105579980987035244090667056220585145196186946809847414320180725725535000307907236831207640585388893039652443844839423798148588694383572368983447529460295285801399205893195898297971434880166955181548488377812654760298659904828632143541580485674336650027897285740396345326886383557108478237919726850503667473790155769350975502978252800000000000000000000000000
  | 3 => 28075850881340930200412374077246113725523490438112003897203591419200829846461683740874857030930052095755282130081549106070713359602904481327993600597825805111917484477843115197991347000120895723887481915064926320069796319556028521774022849240537821858607668604220439268628683735579743657543767084657461350784230930311776046169746822365184613817137043956502068032000000000000000000000000000
  | 4 => 3634506943126180150457998266547670105851727938537502541172684440608500288800100338173125855927848593724350247653351666793868833125595043494724706040397398336019442176393495119237211698561519566880842610320802535577471747529195248598485963602555416930888098746621320820735521299095681599943053050283830043170232957713106625268184211302963761548022308849051084800000000000000000000000000000
  | _ => 0

def planar_4_10A : Matrix (Fin 5) (Fin 5) ℚ := sparseRatScaledMatrix planar_4_10AD planar_4_10AM

theorem planar_4_10A_gram_check : SparseGramCheck planar_4_10AS planar_4_10AM planar_4_10AR planar_4_10AT planar_4_10Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_10A_posSemidef : (planar_4_10A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_10A_gram_check

/- N=4, d=10, H; dimension=5, rank=5. -/
def planar_4_10HD : ℤ := 560
def planar_4_10HS : ℤ := 184726409127132379509311907794147232375900303973325129896061771215225917659838234634192612092712352000
def planar_4_10HM : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 191146000), (⟨1, by decide⟩, -52798000), (⟨2, by decide⟩, -40050400), (⟨3, by decide⟩, 48709500), (⟨4, by decide⟩, 41323200)]
  | 1 => [(⟨0, by decide⟩, -52798000), (⟨1, by decide⟩, 47389072), (⟨2, by decide⟩, 39554464), (⟨3, by decide⟩, -58245684), (⟨4, by decide⟩, -57031872)]
  | 2 => [(⟨0, by decide⟩, -40050400), (⟨1, by decide⟩, 39554464), (⟨2, by decide⟩, 45173056), (⟨3, by decide⟩, -60991368), (⟨4, by decide⟩, -58645248)]
  | 3 => [(⟨0, by decide⟩, 48709500), (⟨1, by decide⟩, -58245684), (⟨2, by decide⟩, -60991368), (⟨3, by decide⟩, 95234193), (⟨4, by decide⟩, 94370544)]
  | 4 => [(⟨0, by decide⟩, 41323200), (⟨1, by decide⟩, -57031872), (⟨2, by decide⟩, -58645248), (⟨3, by decide⟩, 94370544), (⟨4, by decide⟩, 100643904)]
  | _ => []

def planar_4_10HR : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 7502113728915680416631110002763760), (⟨1, by decide⟩, -2072220191159062154778490504252880), (⟨2, by decide⟩, -1571901351263246769266647526261024), (⟨3, by decide⟩, 1911754411175846396230593644018820), (⟨4, by decide⟩, 1621856309013677738443549354243392)]
  | 1 => [(⟨1, by decide⟩, 7502113728915680416631110002763760), (⟨2, by decide⟩, 6515679171269742533397107672187120), (⟨3, by decide⟩, -10243128064575565010529684617138220), (⟨4, by decide⟩, -10432118363692887331478975453004760)]
  | 2 => [(⟨2, by decide⟩, 7502113728915680416631110002763760), (⟨3, by decide⟩, -7407209108005299716806392171372075), (⟨4, by decide⟩, -6462118786274922836563570219299680)]
  | 3 => [(⟨3, by decide⟩, 7502113728915680416631110002763760), (⟨4, by decide⟩, 8550008791921176280966535065375040)]
  | 4 => [(⟨4, by decide⟩, 7502113728915680416631110002763760)]
  | _ => []

def planar_4_10HT : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 7502113728915680416631110002763760)]
  | 1 => [(⟨0, by decide⟩, -2072220191159062154778490504252880), (⟨1, by decide⟩, 7502113728915680416631110002763760)]
  | 2 => [(⟨0, by decide⟩, -1571901351263246769266647526261024), (⟨1, by decide⟩, 6515679171269742533397107672187120), (⟨2, by decide⟩, 7502113728915680416631110002763760)]
  | 3 => [(⟨0, by decide⟩, 1911754411175846396230593644018820), (⟨1, by decide⟩, -10243128064575565010529684617138220), (⟨2, by decide⟩, -7407209108005299716806392171372075), (⟨3, by decide⟩, 7502113728915680416631110002763760)]
  | 4 => [(⟨0, by decide⟩, 1621856309013677738443549354243392), (⟨1, by decide⟩, -10432118363692887331478975453004760), (⟨2, by decide⟩, -6462118786274922836563570219299680), (⟨3, by decide⟩, 8550008791921176280966535065375040), (⟨4, by decide⟩, 7502113728915680416631110002763760)]
  | _ => []

def planar_4_10Hw : Fin 5 → ℤ := fun i =>
  match i.val with
  | 0 => 627374575986951033901349441757373230170000
  | 1 => 107672742624543905175818030876339952733440
  | 2 => 39503886283079571983008410324295890370560
  | 3 => 32598242385621763039269007050613660262400
  | 4 => 21156834258619967473146826564923555840000
  | _ => 0

def planar_4_10H : Matrix (Fin 5) (Fin 5) ℚ := sparseRatScaledMatrix planar_4_10HD planar_4_10HM

theorem planar_4_10H_gram_check : SparseGramCheck planar_4_10HS planar_4_10HM planar_4_10HR planar_4_10HT planar_4_10Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_10H_posSemidef : (planar_4_10H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_10H_gram_check

def planar_4_10KD : ℤ := 8421953965194450621081426478584038164328243508710206646886341847212851495464398843171441397386376728755293622872435881266922275721264418327531551874523661693091840000
def planar_4_10KU : SparseIntMatrix 5 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_10KL : SparseIntMatrix 0 5 := fun i =>
  match i.val with
  | _ => []

def planar_4_10KVA : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 24299416790473371106492194437832099788798635744662555918145241189478105223168228349895311739940719590106597539324595135188041728), (⟨1, by decide⟩, -51093420920754996960353684821623662179203355772776529009163273957650800262408543148251692888496337566666219202372475724255723520), (⟨2, by decide⟩, 554721964534809654434777536132716191817650258210162187780640750647640001428671363207756101837754335989591024809435331940340203520), (⟨3, by decide⟩, 548885269095639863026645226777570698425221150499689960117884472163055994731178671154793229898681020640993122245201995862103818240), (⟨4, by decide⟩, -185961328421621944229674189823334900828895810008116403844408027235641437698596112392839184412961125816172487081202961961199861760)]
  | 1 => [(⟨0, by decide⟩, -51093420920754996960353684821623662179203355772776529009163273957650800262408543148251692888496337566666219202372475724255723520), (⟨1, by decide⟩, 240651827553233983045127345586361814667998336964635186011104935627390386360902706359404233166800899770374434504501981815421009920), (⟨2, by decide⟩, -1684761936736399456632411366998127137916391362488898082125347843452384538548519484889356267490002051321669406532510194533421547520), (⟨3, by decide⟩, -1687066537520497943534333643012487138303315852502046911100748420752377858258365335547383812460367339933322948312608064651122442240), (⟨4, by decide⟩, 634992637955923341073389373065018042203585899704095760039071217442437630316558325001375680661408152348996231212614683684566466560)]
  | 2 => [(⟨0, by decide⟩, 554721964534809654434777536132716191817650258210162187780640750647640001428671363207756101837754335989591024809435331940340203520), (⟨1, by decide⟩, -1684761936736399456632411366998127137916391362488898082125347843452384538548519484889356267490002051321669406532510194533421547520), (⟨2, by decide⟩, 14787430137561989729222456182032599565991952619583016923324969160077641208145625000690481788644158995222896334821018407623584645120), (⟨3, by decide⟩, 14705085224571846889875328927147281082365314784841331269157122622332233632284810531291338297213275445515679188795784402912086589440), (⟨4, by decide⟩, -5210347212803853894767120217899298354237301650381057376333001852637756619927460604373687757881834927649732187756065060145709711360)]
  | 3 => [(⟨0, by decide⟩, 548885269095639863026645226777570698425221150499689960117884472163055994731178671154793229898681020640993122245201995862103818240), (⟨1, by decide⟩, -1687066537520497943534333643012487138303315852502046911100748420752377858258365335547383812460367339933322948312608064651122442240), (⟨2, by decide⟩, 14705085224571846889875328927147281082365314784841331269157122622332233632284810531291338297213275445515679188795784402912086589440), (⟨3, by decide⟩, 14626673375542324676811713268557233722924535602012161539239471626173097137098820809835959157294388474344368554402593308531784417280), (⟨4, by decide⟩, -5190835743848104438663571557257979634526402620022995426412824729191339657239739400956401624127457936332932600915646875746770616320)]
  | 4 => [(⟨0, by decide⟩, -185961328421621944229674189823334900828895810008116403844408027235641437698596112392839184412961125816172487081202961961199861760), (⟨1, by decide⟩, 634992637955923341073389373065018042203585899704095760039071217442437630316558325001375680661408152348996231212614683684566466560), (⟨2, by decide⟩, -5210347212803853894767120217899298354237301650381057376333001852637756619927460604373687757881834927649732187756065060145709711360), (⟨3, by decide⟩, -5190835743848104438663571557257979634526402620022995426412824729191339657239739400956401624127457936332932600915646875746770616320), (⟨4, by decide⟩, 1873223083853803194090759053479666152652467122535244069965186816294201588707960224118599142691646190985837401606233512742045614080)]
  | _ => []

def planar_4_10KVH : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 73264315961130135270757684803755053113021162495025804782623663470729651027116485059613879588231935575303744024577663416809007119409296552752731222778696335135), (⟨1, by decide⟩, 132165913817396965226658380138252555951547484320572860184450841226655025560197731305334360860057113459006193966726476614291380493653675253387949313582227647915), (⟨2, by decide⟩, 43449793842288337628898916735506989874351853480633973736759730272951950041314966764380256851373320155543243244392574617818157364610226672596959342092278589735), (⟨3, by decide⟩, 23891134512312801581339175637088102320274453404664396044328719215537288507085087205670564572805233813830329659061770656826865727914589258955498170096292259120), (⟨4, by decide⟩, 47729250178903840539950918920943669861260440723852280088451202646850071755365772667195547010993246718300951119779915271413158267518282763738513952017478656220)]
  | 1 => [(⟨0, by decide⟩, 132165913817396965226658380138252555951547484320572860184450841226655025560197731305334360860057113459006193966726476614291380493653675253387949313582227647915), (⟨1, by decide⟩, 1008535720152135334808237800046280448287570691503396191368889258233063546009052460998465199131743260623724205665312875907842603029456651063253713091001831570855), (⟨2, by decide⟩, -204496602259556966419100409683421434449310323695382738247900602366158863987182994894403749765374297106437460601734446859601665525242143967091697230332017221805), (⟨3, by decide⟩, 335827794744945423621481344750948172364193913622485184834514023776978532108114679603440086460584375631395995869580588835809293060866339093804374226224869107440), (⟨4, by decide⟩, 83185922261276998205086054003704462111605594637687624589990500080069859316410889835369260167323011565586559749976989702232407790512350109001798194688129984140)]
  | 2 => [(⟨0, by decide⟩, 43449793842288337628898916735506989874351853480633973736759730272951950041314966764380256851373320155543243244392574617818157364610226672596959342092278589735), (⟨1, by decide⟩, -204496602259556966419100409683421434449310323695382738247900602366158863987182994894403749765374297106437460601734446859601665525242143967091697230332017221805), (⟨2, by decide⟩, 1617372698091395192285380404844635892035055404956771955115998144606965547943947642103602162132675457129262280673984793856748780198177568452247662588032616086255), (⟨3, by decide⟩, 1230185072122047382744411000251654376158893378473753407751537449710703984684211711844967681538800086647414684787622831095347122080559125838909211016746342230960), (⟨4, by decide⟩, -344783128188702430549707283544325160871577706565916276125640626147027623804395790606373732089008462205724468598762731263532290349039400560585197880974972852740)]
  | 3 => [(⟨0, by decide⟩, 23891134512312801581339175637088102320274453404664396044328719215537288507085087205670564572805233813830329659061770656826865727914589258955498170096292259120), (⟨1, by decide⟩, 335827794744945423621481344750948172364193913622485184834514023776978532108114679603440086460584375631395995869580588835809293060866339093804374226224869107440), (⟨2, by decide⟩, 1230185072122047382744411000251654376158893378473753407751537449710703984684211711844967681538800086647414684787622831095347122080559125838909211016746342230960), (⟨3, by decide⟩, 2545000554302564288560976920813102991886865091912725901914943339903018720409845221070008586649362887216703407441483676657333851142394413787690619839215095576320), (⟨4, by decide⟩, -1489041487054023478590569777413977198233088972982385601669530507678705654555742301587160860475061900400026230694661715410618777477193842488250936156400163446080)]
  | 4 => [(⟨0, by decide⟩, 47729250178903840539950918920943669861260440723852280088451202646850071755365772667195547010993246718300951119779915271413158267518282763738513952017478656220), (⟨1, by decide⟩, 83185922261276998205086054003704462111605594637687624589990500080069859316410889835369260167323011565586559749976989702232407790512350109001798194688129984140), (⟨2, by decide⟩, -344783128188702430549707283544325160871577706565916276125640626147027623804395790606373732089008462205724468598762731263532290349039400560585197880974972852740), (⟨3, by decide⟩, -1489041487054023478590569777413977198233088972982385601669530507678705654555742301587160860475061900400026230694661715410618777477193842488250936156400163446080), (⟨4, by decide⟩, 1306543519991271204875276772256441209432756309615835693085115958406651047174567135322103989599145476396658922972847488878535273561840013512199261400588159201520)]
  | _ => []

def planar_4_10U : Matrix (Fin 5) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_10KD planar_4_10KU
def planar_4_10L : Matrix (Fin 0) (Fin 5) ℚ := sparseRatMatrix planar_4_10KL

def planar_4_10AV : Matrix (Fin 5) (Fin 5) ℚ :=
  ((planar_4_10AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_10KD planar_4_10KVA

theorem planar_4_10A_kernel_check : SparseScaledFrameCheck planar_4_10KD planar_4_10AM planar_4_10KU planar_4_10KL planar_4_10KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_10A_kernel_frame : HasKernelFrame planar_4_10A planar_4_10U planar_4_10L planar_4_10AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_10KD≠0) planar_4_10A_kernel_check).scale_matrix
    (by norm_num [planar_4_10AD])

theorem planar_4_10A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_10A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_10A_kernel_frame.ratCast

def planar_4_10HV : Matrix (Fin 5) (Fin 5) ℚ :=
  ((planar_4_10HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_10KD planar_4_10KVH

theorem planar_4_10H_kernel_check : SparseScaledFrameCheck planar_4_10KD planar_4_10HM planar_4_10KU planar_4_10KL planar_4_10KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_10H_kernel_frame : HasKernelFrame planar_4_10H planar_4_10U planar_4_10L planar_4_10HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_10KD≠0) planar_4_10H_kernel_check).scale_matrix
    (by norm_num [planar_4_10HD])

theorem planar_4_10H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_10H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_10H_kernel_frame.ratCast

theorem planar_4_10_same_kernel (v : Fin 5 → ℂ) :
    (planar_4_10A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_10H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_10A_kernel_frame.ratCast planar_4_10H_kernel_frame.ratCast v

def planar_4_10WS : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 1)]
  | _ => []

def planar_4_10RS : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 1)]
  | _ => []

def planar_4_10W : Matrix (Fin 5) (Fin 5) ℚ := sparseRatMatrix planar_4_10WS
def planar_4_10R : Matrix (Fin 5) (Fin 5) ℚ := sparseRatScaledMatrix 1 planar_4_10RS

theorem planar_4_10_complement : HasComplement planar_4_10U planar_4_10L planar_4_10W planar_4_10R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_10A_active_posDef :
    ((planar_4_10W.map (Rat.castHom ℂ))ᴴ * (planar_4_10A.map (Rat.castHom ℂ)) * (planar_4_10W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_10A_kernel_frame.ratCast planar_4_10A_posSemidef _ _
    ((planar_4_10_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_10_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_10H_active_posDef :
    ((planar_4_10W.map (Rat.castHom ℂ))ᴴ * (planar_4_10H.map (Rat.castHom ℂ)) * (planar_4_10W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_10H_kernel_frame.ratCast planar_4_10H_posSemidef _ _
    ((planar_4_10_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_10_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=11, A; dimension=4, rank=4. -/
def planar_4_11AD : ℤ := 313600000000000000000000000000
def planar_4_11AS : ℤ := 1424422689470773928488289513871730722653750917878196549401283251934723979518836502824873125635014763921645637174772649574140731797573411180002347480077966999913544804298458225698446709101496489695082275994162227795930357222552302399575136774982493872209604059238588062515686527160984519943682330227854579490336620926857961731149332002079109371121492832028405880324945283047471832297622094736913053024507498536794077810569357517433505918325305977644658142341114814564625588537255549113451098259696144000000000000000000000000000000
def planar_4_11AM : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 306222097563705929185469973982500), (⟨1, by decide⟩, -163139238701778316967952357683400), (⟨2, by decide⟩, -109629559903083371368378237973400), (⟨3, by decide⟩, 81698224801443337096120726676250)]
  | 1 => [(⟨0, by decide⟩, -163139238701778316967952357683400), (⟨1, by decide⟩, 96808010610809359344678417223632), (⟨2, by decide⟩, 66638009754003204494222109242544), (⟨3, by decide⟩, -55178419480017586485101622213300)]
  | 2 => [(⟨0, by decide⟩, -109629559903083371368378237973400), (⟨1, by decide⟩, 66638009754003204494222109242544), (⟨2, by decide⟩, 46743877912619410020480344487696), (⟨3, by decide⟩, -41233951484875452735158079207420)]
  | 3 => [(⟨0, by decide⟩, 81698224801443337096120726676250), (⟨1, by decide⟩, -55178419480017586485101622213300), (⟨2, by decide⟩, -41233951484875452735158079207420), (⟨3, by decide⟩, 43749698807406761079048686030625)]
  | _ => []

def planar_4_11AR : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 175987312123790076331473057324141600164557753154299190856803963576156161571448863248642154729953427315201682884418826103627833335830391896011412874227497757821715594700), (⟨1, by decide⟩, -93756905035484853217642256238940335773792096466097028913962070505366608720177671852328428756862024488012516953978617870665671973826869557838911896819483850640238590744), (⟨2, by decide⟩, -63004635296262072638527018241590016871620419147182831999917740954125540006852306452212229884956887171660113831178281985570028855137981118772733653468038660249284027144), (⟨3, by decide⟩, 46952362688652905617429727388510009632355036646031641794215410694107963444667089561425687006307902242437214241958343779704188242533893896277489444728188599671499781950)]
  | 1 => [(⟨1, by decide⟩, 175987312123790076331473057324141600164557753154299190856803963576156161571448863248642154729953427315201682884418826103627833335830391896011412874227497757821715594700), (⟨2, by decide⟩, 146415902279211983687433127679058762070121319832970514691407630498777808862346540799060336940844567239696715755999259421826051678385280536415578097133331170950270339800), (⟨3, by decide⟩, -207250542578309897058581960831701858467871439282673719959830389610172915036649844299509553828475520140711849032218723528819766612798613873591797203076934697732634857500)]
  | 2 => [(⟨2, by decide⟩, 175987312123790076331473057324141600164557753154299190856803963576156161571448863248642154729953427315201682884418826103627833335830391896011412874227497757821715594700), (⟨3, by decide⟩, -623700841002751115222875762578579994897816312934691964204064932227142207931275895393579553555481761046710440578448682895589638327156594724884072359300068613658577136625)]
  | 3 => [(⟨3, by decide⟩, 175987312123790076331473057324141600164557753154299190856803963576156161571448863248642154729953427315201682884418826103627833335830391896011412874227497757821715594700)]
  | _ => []

def planar_4_11AT : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 175987312123790076331473057324141600164557753154299190856803963576156161571448863248642154729953427315201682884418826103627833335830391896011412874227497757821715594700)]
  | 1 => [(⟨0, by decide⟩, -93756905035484853217642256238940335773792096466097028913962070505366608720177671852328428756862024488012516953978617870665671973826869557838911896819483850640238590744), (⟨1, by decide⟩, 175987312123790076331473057324141600164557753154299190856803963576156161571448863248642154729953427315201682884418826103627833335830391896011412874227497757821715594700)]
  | 2 => [(⟨0, by decide⟩, -63004635296262072638527018241590016871620419147182831999917740954125540006852306452212229884956887171660113831178281985570028855137981118772733653468038660249284027144), (⟨1, by decide⟩, 146415902279211983687433127679058762070121319832970514691407630498777808862346540799060336940844567239696715755999259421826051678385280536415578097133331170950270339800), (⟨2, by decide⟩, 175987312123790076331473057324141600164557753154299190856803963576156161571448863248642154729953427315201682884418826103627833335830391896011412874227497757821715594700)]
  | 3 => [(⟨0, by decide⟩, 46952362688652905617429727388510009632355036646031641794215410694107963444667089561425687006307902242437214241958343779704188242533893896277489444728188599671499781950), (⟨1, by decide⟩, -207250542578309897058581960831701858467871439282673719959830389610172915036649844299509553828475520140711849032218723528819766612798613873591797203076934697732634857500), (⟨2, by decide⟩, -623700841002751115222875762578579994897816312934691964204064932227142207931275895393579553555481761046710440578448682895589638327156594724884072359300068613658577136625), (⟨3, by decide⟩, 175987312123790076331473057324141600164557753154299190856803963576156161571448863248642154729953427315201682884418826103627833335830391896011412874227497757821715594700)]
  | _ => []

def planar_4_11Aw : Fin 4 → ℤ := fun i =>
  match i.val with
  | 0 => 14083567942902053287001598334720525026871486358117872854957958570375210149567350063091936478815069991046367527331581289579271143807089150112066345448258871405757932878816850294174192120552811891972000000000000000000000000000000
  | 1 => 455125450545410164385313927873386361338484229153615217327945160315270212980013977039576336200377150056817961793201178819195484410914108451900576751158379698575423269119974868467172710421970705725542400000000000000000000000000
  | 2 => 29715302849990242807756000708962007248213207329211326241369082048395351112348633399768127613005907067468095895809021281888442085883048913340622136756675111789954694402754893900953672992528324576870400000000000000000000000000
  | 3 => 5238813354984749425700979779662127436401915395041336968534005939721388472908044298480480081755145791071948592384645056831880559328346825634808531913941553367085857402681823165455874801322021783040000000000000000000000000000
  | _ => 0

def planar_4_11A : Matrix (Fin 4) (Fin 4) ℚ := sparseRatScaledMatrix planar_4_11AD planar_4_11AM

theorem planar_4_11A_gram_check : SparseGramCheck planar_4_11AS planar_4_11AM planar_4_11AR planar_4_11AT planar_4_11Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_11A_posSemidef : (planar_4_11A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_11A_gram_check

/- N=4, d=11, H; dimension=4, rank=4. -/
def planar_4_11HD : ℤ := 35
def planar_4_11HS : ℤ := 8083052519291605479824268590122800761625336000
def planar_4_11HM : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 16828500), (⟨1, by decide⟩, -12520800), (⟨2, by decide⟩, -10593000), (⟨3, by decide⟩, 15973650)]
  | 1 => [(⟨0, by decide⟩, -12520800), (⟨1, by decide⟩, 16222464), (⟨2, by decide⟩, 13065408), (⟨3, by decide⟩, -22072176)]
  | 2 => [(⟨0, by decide⟩, -10593000), (⟨1, by decide⟩, 13065408), (⟨2, by decide⟩, 13685328), (⟨3, by decide⟩, -23857092)]
  | 3 => [(⟨0, by decide⟩, 15973650), (⟨1, by decide⟩, -22072176), (⟨2, by decide⟩, -23857092), (⟨3, by decide⟩, 44117325)]
  | _ => []

def planar_4_11HR : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3026190062396280), (⟨1, by decide⟩, -2251556617241664), (⟨2, by decide⟩, -1904889403747440), (⟨3, by decide⟩, 2872466404622892)]
  | 1 => [(⟨1, by decide⟩, 3026190062396280), (⟨2, by decide⟩, 2271371545592760), (⟨3, by decide⟩, -4463643758309320)]
  | 2 => [(⟨2, by decide⟩, 3026190062396280), (⟨3, by decide⟩, -5958434917354725)]
  | 3 => [(⟨3, by decide⟩, 3026190062396280)]
  | _ => []

def planar_4_11HT : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 3026190062396280)]
  | 1 => [(⟨0, by decide⟩, -2251556617241664), (⟨1, by decide⟩, 3026190062396280)]
  | 2 => [(⟨0, by decide⟩, -1904889403747440), (⟨1, by decide⟩, 2271371545592760), (⟨2, by decide⟩, 3026190062396280)]
  | 3 => [(⟨0, by decide⟩, 2872466404622892), (⟨1, by decide⟩, -4463643758309320), (⟨2, by decide⟩, -5958434917354725), (⟨3, by decide⟩, 3026190062396280)]
  | _ => []

def planar_4_11Hw : Fin 4 → ℤ := fun i =>
  match i.val with
  | 0 => 14853486510635441077500
  | 1 => 6096116031606410664960
  | 2 => 2759515387670241607680
  | 3 => 1595897294765335511040
  | _ => 0

def planar_4_11H : Matrix (Fin 4) (Fin 4) ℚ := sparseRatScaledMatrix planar_4_11HD planar_4_11HM

theorem planar_4_11H_gram_check : SparseGramCheck planar_4_11HS planar_4_11HM planar_4_11HR planar_4_11HT planar_4_11Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_11H_posSemidef : (planar_4_11H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_11H_gram_check

def planar_4_11KD : ℤ := 12434069791403187310425212075958436081230205289313805081881970371059283790884041669503333282750339284541292854546268160000
def planar_4_11KU : SparseIntMatrix 4 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_11KL : SparseIntMatrix 0 4 := fun i =>
  match i.val with
  | _ => []

def planar_4_11KVA : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 911366362351314389425921278684197776162428232601851643503826038057136567863202665610870784), (⟨1, by decide⟩, -9286571699375204971311567877793891599920274164409746258581494608307217849421566709379891200), (⟨2, by decide⟩, 21015477369746126968002721861417288800031809004919168984457223463482301477716686653079552000), (⟨3, by decide⟩, 6392633988625880389041400735112703663024674936325527953294945674624202209880295920584622080)]
  | 1 => [(⟨0, by decide⟩, -9286571699375204971311567877793891599920274164409746258581494608307217849421566709379891200), (⟨1, by decide⟩, 356891390304098774379039700162223451249296778151878472116506701337749758637491594432675840000), (⟨2, by decide⟩, -701082223132479816250597011490829773042312321557906898162244502833303729781635265940684800000), (⟨3, by decide⟩, -193303984730176533176340464674780270984235352880626135192698735242237234140373380010672128000)]
  | 2 => [(⟨0, by decide⟩, 21015477369746126968002721861417288800031809004919168984457223463482301477716686653079552000), (⟨1, by decide⟩, -701082223132479816250597011490829773042312321557906898162244502833303729781635265940684800000), (⟨2, by decide⟩, 1390273121678659561046056411799369320285046800514055038495234708625963327140604820174848000000), (⟨3, by decide⟩, 386857937744440114067414975008475941303249753624385905999740831715616115143002526673764352000)]
  | 3 => [(⟨0, by decide⟩, 6392633988625880389041400735112703663024674936325527953294945674624202209880295920584622080), (⟨1, by decide⟩, -193303984730176533176340464674780270984235352880626135192698735242237234140373380010672128000), (⟨2, by decide⟩, 386857937744440114067414975008475941303249753624385905999740831715616115143002526673764352000), (⟨3, by decide⟩, 109158244083714848406813589410140624524572347827428732451313492122722186801015349604017766400)]
  | _ => []

def planar_4_11KVH : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 2326239248473819861092007427725769720162729140950980292222563142675555309213462588732302052906799063247685680748060), (⟨1, by decide⟩, 1121823239101487051407639714005422506346602731441281758435624356751637465641445448016352776537413884216824781148750), (⟨2, by decide⟩, 4183168275007733573964871621792984797212027051396780824699131583681587335086778966754307282224283451503794784223250), (⟨3, by decide⟩, 1981098781290458386174294885592679345034056961063772722657203133691965098156210149550873787173235773411795816558000)]
  | 1 => [(⟨0, by decide⟩, 1121823239101487051407639714005422506346602731441281758435624356751637465641445448016352776537413884216824781148750), (⟨1, by decide⟩, 4040860734081166513814494717780030895864226657664771256609508335538911490828699629018743339766225369214809426354375), (⟨2, by decide⟩, -3023496701996317594521027021774021444798490554549522205842098855539951435321195400966562397464583779734096293844375), (⟨3, by decide⟩, -19513001986577735032768259377928712089435124415123083863921251355453115007309242994813744370087671033316242985000)]
  | 2 => [(⟨0, by decide⟩, 4183168275007733573964871621792984797212027051396780824699131583681587335086778966754307282224283451503794784223250), (⟨1, by decide⟩, -3023496701996317594521027021774021444798490554549522205842098855539951435321195400966562397464583779734096293844375), (⟨2, by decide⟩, 30637269576068966665208548074529086237350163298571315168123278670392832428236777954465956211041467251252892624214375), (⟨3, by decide⟩, 13540271121313877923806232923089913585582177026035474536663367718025689652173091663659268832012492319513424180825000)]
  | 3 => [(⟨0, by decide⟩, 1981098781290458386174294885592679345034056961063772722657203133691965098156210149550873787173235773411795816558000), (⟨1, by decide⟩, -19513001986577735032768259377928712089435124415123083863921251355453115007309242994813744370087671033316242985000), (⟨2, by decide⟩, 13540271121313877923806232923089913585582177026035474536663367718025689652173091663659268832012492319513424180825000), (⟨3, by decide⟩, 6876878656528588481051420248351245985472135320465592359616927007774650031067680831978683098700330808316906307160000)]
  | _ => []

def planar_4_11U : Matrix (Fin 4) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_11KD planar_4_11KU
def planar_4_11L : Matrix (Fin 0) (Fin 4) ℚ := sparseRatMatrix planar_4_11KL

def planar_4_11AV : Matrix (Fin 4) (Fin 4) ℚ :=
  ((planar_4_11AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_11KD planar_4_11KVA

theorem planar_4_11A_kernel_check : SparseScaledFrameCheck planar_4_11KD planar_4_11AM planar_4_11KU planar_4_11KL planar_4_11KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_11A_kernel_frame : HasKernelFrame planar_4_11A planar_4_11U planar_4_11L planar_4_11AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_11KD≠0) planar_4_11A_kernel_check).scale_matrix
    (by norm_num [planar_4_11AD])

theorem planar_4_11A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_11A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_11A_kernel_frame.ratCast

def planar_4_11HV : Matrix (Fin 4) (Fin 4) ℚ :=
  ((planar_4_11HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_11KD planar_4_11KVH

theorem planar_4_11H_kernel_check : SparseScaledFrameCheck planar_4_11KD planar_4_11HM planar_4_11KU planar_4_11KL planar_4_11KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_11H_kernel_frame : HasKernelFrame planar_4_11H planar_4_11U planar_4_11L planar_4_11HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_11KD≠0) planar_4_11H_kernel_check).scale_matrix
    (by norm_num [planar_4_11HD])

theorem planar_4_11H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_11H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_11H_kernel_frame.ratCast

theorem planar_4_11_same_kernel (v : Fin 4 → ℂ) :
    (planar_4_11A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_11H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_11A_kernel_frame.ratCast planar_4_11H_kernel_frame.ratCast v

def planar_4_11WS : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | _ => []

def planar_4_11RS : SparseIntMatrix 4 4 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | _ => []

def planar_4_11W : Matrix (Fin 4) (Fin 4) ℚ := sparseRatMatrix planar_4_11WS
def planar_4_11R : Matrix (Fin 4) (Fin 4) ℚ := sparseRatScaledMatrix 1 planar_4_11RS

theorem planar_4_11_complement : HasComplement planar_4_11U planar_4_11L planar_4_11W planar_4_11R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_11A_active_posDef :
    ((planar_4_11W.map (Rat.castHom ℂ))ᴴ * (planar_4_11A.map (Rat.castHom ℂ)) * (planar_4_11W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_11A_kernel_frame.ratCast planar_4_11A_posSemidef _ _
    ((planar_4_11_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_11_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_11H_active_posDef :
    ((planar_4_11W.map (Rat.castHom ℂ))ᴴ * (planar_4_11H.map (Rat.castHom ℂ)) * (planar_4_11W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_11H_kernel_frame.ratCast planar_4_11H_posSemidef _ _
    ((planar_4_11_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_11_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=12, A; dimension=7, rank=6. -/
def planar_4_12AD : ℤ := 116010913095000000000000000000000000
def planar_4_12AS : ℤ := 31411481169985358271214437469841267436919720543376062160816588646302931319609515422663711916174109851819194000330194575863696509800429598678325973699185902038642135336316006482566596095370787134672092291824395884225928639351454043273580073859143993295152113399579313045067133691510578298657280663019009370401255656190100796505127990445560399761666188038177642524090161040522619480878617810912145972644107555159792228468111760883414643659819473353274682786699937670226892996596467118989030348565087878744891257750016203785401469612983091273519211530486003792913960015597286981194998283395249701776528901821576455097905369715336732710722240044605374446457189322201301289462700142228134470719451456673112249234706128070925067438392801984087073417266795267462593267003149970950309354211804423038769422943538882588797099362811484702451370277993623826069679033327800834388200449114607285672883188015587613259704623730328558872648840985927088254169016072114153889210436687055656487292786546883423221870285384829943623172409445972420275161150597985881837391070682567053438167512094858323548007713178471310396521737860991349283064656568207209801238438378913840294719558325799130570822587993456307289646507102857028307265947921326860565176048746332352745017657974994194801622135018947482319927923129039963718387688585047865234375000000000000000000000000
def planar_4_12AM : SparseIntMatrix 7 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 5420938365019035797302553404396476819375), (⟨1, by decide⟩, -4184250599004837725402488721373364335375), (⟨2, by decide⟩, 5708168891236237090126986875316212100135), (⟨3, by decide⟩, 3267843556759750513941886345413552190125), (⟨4, by decide⟩, -3251294938783744923846113584106211224955), (⟨5, by decide⟩, 2704959079610859029457512251644033068745), (⟨6, by decide⟩, 2053705533428279669017326725097684955800)]
  | 1 => [(⟨0, by decide⟩, -4184250599004837725402488721373364335375), (⟨1, by decide⟩, 3524223511596073981941283678470380662875), (⟨2, by decide⟩, -4873507464935388608703438362249595433335), (⟨3, by decide⟩, -2854082167943857743508410158336957488125), (⟨4, by decide⟩, 2787429179721791938750650137105234378415), (⟨5, by decide⟩, -2313956942179804681962126918138658509465), (⟨6, by decide⟩, -1756103202659236078792917881514067529700)]
  | 2 => [(⟨0, by decide⟩, 5708168891236237090126986875316212100135), (⟨1, by decide⟩, -4873507464935388608703438362249595433335), (⟨2, by decide⟩, 6758210082311663308464128548437315145179), (⟨3, by decide⟩, 3980467695258786495227651755558650174585), (⟨4, by decide⟩, -3872903354020770906897399296642272487811), (⟨5, by decide⟩, 3209743925271110605569189131517616643577), (⟨6, by decide⟩, 2440297704887919412758647892395997869304)]
  | 3 => [(⟨0, by decide⟩, 3267843556759750513941886345413552190125), (⟨1, by decide⟩, -2854082167943857743508410158336957488125), (⟨2, by decide⟩, 3980467695258786495227651755558650174585), (⟨3, by decide⟩, 2375454992447724707762993347136771496875), (⟨4, by decide⟩, -2294037431158519023397200618990570368265), (⟨5, by decide⟩, 1890921567397982265358846645670491785715), (⟨6, by decide⟩, 1448083829786259825391802842395570140400)]
  | 4 => [(⟨0, by decide⟩, -3251294938783744923846113584106211224955), (⟨1, by decide⟩, 2787429179721791938750650137105234378415), (⟨2, by decide⟩, -3872903354020770906897399296642272487811), (⟨3, by decide⟩, -2294037431158519023397200618990570368265), (⟨4, by decide⟩, 2226616896945513201697972278917950717107), (⟨5, by decide⟩, -1838892417340115674507047209979925743213), (⟨6, by decide⟩, -1405778119691370673638445888402443432132)]
  | 5 => [(⟨0, by decide⟩, 2704959079610859029457512251644033068745), (⟨1, by decide⟩, -2313956942179804681962126918138658509465), (⟨2, by decide⟩, 3209743925271110605569189131517616643577), (⟨3, by decide⟩, 1890921567397982265358846645670491785715), (⟨4, by decide⟩, -1838892417340115674507047209979925743213), (⟨5, by decide⟩, 1524878976358250768599789326971072365295), (⟨6, by decide⟩, 1157771274015304238662520660697245469528)]
  | 6 => [(⟨0, by decide⟩, 2053705533428279669017326725097684955800), (⟨1, by decide⟩, -1756103202659236078792917881514067529700), (⟨2, by decide⟩, 2440297704887919412758647892395997869304), (⟨3, by decide⟩, 1448083829786259825391802842395570140400), (⟨4, by decide⟩, -1405778119691370673638445888402443432132), (⟨5, by decide⟩, 1157771274015304238662520660697245469528), (⟨6, by decide⟩, 889895637809860617188298284594001593940)]
  | _ => []

def planar_4_12AR : SparseIntMatrix 6 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125), (⟨1, by decide⟩, -76849123502553459400343707749229331590286904101869981397817143650139465161303752769941465099134843014813205894972926344610852951305392983770468367600549655854095166343277402589364008899874951069759964428534675856665484814194735939969271335733296206976617403950556736616862482655874613639557099063296070666242278687357613165527116363951393379386206003557148326685852766354211841173158763877191975221782878439394928157181532618554556138725), (⟨2, by decide⟩, 104837835525524663411409209668556548699308581125965952143314244155035215455737732249834622800854433887933933050840732356221240575340872680784043352979281943704503911666266465154971631510336166719507827397199468269017411203950124942921328376586140108288596314674190011747952528521832046115476712984560075417318818337461317385041969768693783760752934701624756651351480327410747213396949990345320702645231920845635642932499721236202952313581), (⟨3, by decide⟩, 60018133985612959142119758531940286537484587362858129489848989365950884907680342096216616481628054234023873268450348385401838409743528488021695643960954469045976042635383484470270619236283397921032376069019561044198315748397956136088513109081102696618461068944280066997012772682280125019959399043669206183416562475638107139062573336536135193383541414025061660053230323588582554700799625422893331276345694067484747973732884840219198326575), (⟨4, by decide⟩, -59714197412851973921689572027570934589814428829582436878627997170556703538088189209752995348605227257661117010372959347409164790593584913656106449691358608515932727248661876015057625985921135050551988610165444889944940013305383343763273669838268797509288122784471885410744239482339286424208940239412266561993342187948210351803876402650182268636616175703798478434820922020337763383215189442883573591214267948275273583000274546029377550473), (⟨5, by decide⟩, 49680039342721953995691591147809411527617713594746985852762120994925732457702036186166273858417082969657480257984255936629689179728362820795489926426818513709621042248041358241298980655889816333031439148847526971404266527220577099479363798268649359746157167729253123326441401059872632683848319610122152026878842847593039651566181414364559887888286666233265612709035374074086767666393011886474231715170796296364138192923796521930363195747), (⟨6, by decide⟩, 37718933520340238716633296294719388223548233725655729160141984485132540005227979617016258058884908184761607650179120384397189615750758215508602314373676522126677114936887971884153274690130271496788024971128594176639224140747622454910727473179629439965936919619043855629124351088483247620529775746297179664767818702768978132493851459142059837368132969216878008773003707434541576623028968044528311614361087938942375774662056347557589753480)]
  | 1 => [(⟨1, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125), (⟨2, by decide⟩, -158049197539415107638922702395921690089569018152105370984920835006927770380243351300601059497444421420588058494544662127708314220202910645459964397202241973461718225883168797996055441688443790456431735129063859189833774355934799323172126370182975628834881210753688331922428292220292235230759651649107533595169198262861233251648188023742852231155163135642038888939439760673188531441763166264839477638872806826867362045726581054090697896260), (⟨3, by decide⟩, -112138809204620725971742946231594604886583238309039870786287822663555062131644762263313499507326118181046946748893794621355669263436018360755620064867439990789437766326276131032845074410500599229083081905378536605231415556549043869473542961869178558519421684257727731312848401808759912196634249162442870281908345855471884192025732407115975886578723621283944721854183080678819226594841525209801431322227437872758079911019499648544461544500), (⟨4, by decide⟩, 93925605516336201255934679639359098908920865717832429372972755768713157964731234777580757538647065966347640449122203643277743719634594370698811894407069512574655011342488696926923837709617356611924782957495953539317661462851029982426332481900615906675449212473701242790386587170057758932405459342633976505673485770355656315905216491104706650243569750355927663960722539085845546157166435373030337648052999901782405611472878499738092397355), (⟨5, by decide⟩, -76424553579479392127237373789391670983022846182116069039078290834215988271921956649809588978427619571363190979166158981887449718048694243170048017214150833091667896203384510570889753925999125994219580307337199533772945401931738268898892523821694956526926600311206255603938707885941850775114734961462182713398219693214995182395081246414630559751769303993576136224481942680386474429989482089742924866663468127475326735191416841610925842420), (⟨6, by decide⟩, -57774566902961019392283143216653197638255666061145836264427880422738099775218030138139945150429287798990078008665180910246662112599506690060964466401842554261830521333340187661993650775408100337040685217881892941928281310587090755141108352338299638489362641045239271186435751848816687486680394148044438684958732370380320323550173928417170383476128542888665109903774691820890524984603562217373800230370393063528979838842780368775087274925)]
  | 2 => [(⟨2, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125), (⟨3, by decide⟩, 238019378338580840154520454961840071455131408496025970246410490405270730485158663223496785410422016917394949352238161131707279441773029807707271620031392037012006113073161273765429077612361864669014378599202997941029143491735438035635820058164486149338488938084514486257366817191646687870421681079803356935366236955784263371091988900508132566314901556338196876492394165491177094687635958368456120067376040051257441093675032869841512071875), (⟨4, by decide⟩, -152752886498800867466521031530784099202767996062840001618787608914555460717203379195840136141871253314545896126591751082089437158532703917960317299766622974224841377257193441570599368952758550005079604227282927633817306908768377028253344913600246859964623966901894537732969479002544928176327410883275902251691697804760212774901615953991535363227521655182151034140919593718351748565328594909484803999682701342885322988622100407206406319000), (⟨5, by decide⟩, 47481714062616804284946707132475089110962994837889809140969712513077924170622525898923469955551425212014333564531572982869663823005085160008038948673460541934727859282345896781559613242610589713904001281991384604407861423320642151676535888639213819238769588264529757105289981456995368241006570982066415715970699386090726736031604621588595483959433937760484469021582659122379391230048073754500776800393046831983536749031273476937800752750), (⟨6, by decide⟩, 119567159481430463153103499404253452238990587827232677491267367534607202909546641073759557856324592301565632992477702950375951617675172961076279668361340989971040846864025075178384685046315323747178782186829609909734063915049660263705581376351828040002058117541662391503260764373337102878367761767108026778297331152150781628167271809890831378016388984453328971646307486487930408959634625189994707647313823369199454918156535662269907842500)]
  | 3 => [(⟨3, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125), (⟨4, by decide⟩, -122272534535263136829474772294860884306315777869510233983594818990361422089375332847504194861205079687495101945550204340891468114954930671123494512860862139003025724165360536254392186532115427279865016564374052026839334037396289841287817909608371941141662202424867024368525743743672720087719489984425560931797918502498076458442007066443081653286448078164679372420964848776302887965168883216254794168263714873065457820374542133983842824029), (⟨5, by decide⟩, -39754848337577130857784548699068946543683974197795984041191059934369469018527386738556587549303251263256742775845158046014391099050884169449223019491676770371687769133049921009485252721782579389601740950541478829611335527276464758087849452421337587865214498349128455980444251541089206799044196548960823442002644011578710645343496993146407364868119234743769197323989019958700829122418334057701899156929995563893198302660106800833851820132), (⟨6, by decide⟩, 184737438523077031857205494851790300756766530901347998367308345291247377066356980629065436333157882836363823010881631827023306763572865418825256407680453427909647152758625630934094987790242755829393820465831445695753548589500058046152237775683047181498470193111944945317517134011545344337341984455385950379347609132069517376739877702028081969605334222885419693287473593846523207306094632996229490977739917743354327159790549874165129439065)]
  | 4 => [(⟨4, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125), (⟨5, by decide⟩, 132172960762459737989832553482351025605390717093368500694943450643878648135706295991494837649628351741733601828985320314077871231026523920321325177318402011018718925658860768217488978495791909039567222438608385271540419148143179482098782407074854179881631108455306366728227472919509794716177383740733259453749880176369855198639112444890617199897778393364044886091794962054039538209941902250027471676610349502915544140337987914869706695500), (⟨6, by decide⟩, -331297918532512483308889750356351854404488715164305407977088155891568520397548439600493919526739407345499849141113190115625912361802284106063236452384297251954903055069151493385838254487333265279443129665524659646613329173281152271121277398984922757181768528629141485528184682953288399990459767865585249306251623945380547569614379292899594603569140729739461383848685209383606333703264837237991464708045364636255117707575270304142522753750)]
  | 5 => [(⟨5, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125), (⟨6, by decide⟩, -99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125)]
  | _ => []

def planar_4_12AT : SparseIntMatrix 7 6 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125)]
  | 1 => [(⟨0, by decide⟩, -76849123502553459400343707749229331590286904101869981397817143650139465161303752769941465099134843014813205894972926344610852951305392983770468367600549655854095166343277402589364008899874951069759964428534675856665484814194735939969271335733296206976617403950556736616862482655874613639557099063296070666242278687357613165527116363951393379386206003557148326685852766354211841173158763877191975221782878439394928157181532618554556138725), (⟨1, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125)]
  | 2 => [(⟨0, by decide⟩, 104837835525524663411409209668556548699308581125965952143314244155035215455737732249834622800854433887933933050840732356221240575340872680784043352979281943704503911666266465154971631510336166719507827397199468269017411203950124942921328376586140108288596314674190011747952528521832046115476712984560075417318818337461317385041969768693783760752934701624756651351480327410747213396949990345320702645231920845635642932499721236202952313581), (⟨1, by decide⟩, -158049197539415107638922702395921690089569018152105370984920835006927770380243351300601059497444421420588058494544662127708314220202910645459964397202241973461718225883168797996055441688443790456431735129063859189833774355934799323172126370182975628834881210753688331922428292220292235230759651649107533595169198262861233251648188023742852231155163135642038888939439760673188531441763166264839477638872806826867362045726581054090697896260), (⟨2, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125)]
  | 3 => [(⟨0, by decide⟩, 60018133985612959142119758531940286537484587362858129489848989365950884907680342096216616481628054234023873268450348385401838409743528488021695643960954469045976042635383484470270619236283397921032376069019561044198315748397956136088513109081102696618461068944280066997012772682280125019959399043669206183416562475638107139062573336536135193383541414025061660053230323588582554700799625422893331276345694067484747973732884840219198326575), (⟨1, by decide⟩, -112138809204620725971742946231594604886583238309039870786287822663555062131644762263313499507326118181046946748893794621355669263436018360755620064867439990789437766326276131032845074410500599229083081905378536605231415556549043869473542961869178558519421684257727731312848401808759912196634249162442870281908345855471884192025732407115975886578723621283944721854183080678819226594841525209801431322227437872758079911019499648544461544500), (⟨2, by decide⟩, 238019378338580840154520454961840071455131408496025970246410490405270730485158663223496785410422016917394949352238161131707279441773029807707271620031392037012006113073161273765429077612361864669014378599202997941029143491735438035635820058164486149338488938084514486257366817191646687870421681079803356935366236955784263371091988900508132566314901556338196876492394165491177094687635958368456120067376040051257441093675032869841512071875), (⟨3, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125)]
  | 4 => [(⟨0, by decide⟩, -59714197412851973921689572027570934589814428829582436878627997170556703538088189209752995348605227257661117010372959347409164790593584913656106449691358608515932727248661876015057625985921135050551988610165444889944940013305383343763273669838268797509288122784471885410744239482339286424208940239412266561993342187948210351803876402650182268636616175703798478434820922020337763383215189442883573591214267948275273583000274546029377550473), (⟨1, by decide⟩, 93925605516336201255934679639359098908920865717832429372972755768713157964731234777580757538647065966347640449122203643277743719634594370698811894407069512574655011342488696926923837709617356611924782957495953539317661462851029982426332481900615906675449212473701242790386587170057758932405459342633976505673485770355656315905216491104706650243569750355927663960722539085845546157166435373030337648052999901782405611472878499738092397355), (⟨2, by decide⟩, -152752886498800867466521031530784099202767996062840001618787608914555460717203379195840136141871253314545896126591751082089437158532703917960317299766622974224841377257193441570599368952758550005079604227282927633817306908768377028253344913600246859964623966901894537732969479002544928176327410883275902251691697804760212774901615953991535363227521655182151034140919593718351748565328594909484803999682701342885322988622100407206406319000), (⟨3, by decide⟩, -122272534535263136829474772294860884306315777869510233983594818990361422089375332847504194861205079687495101945550204340891468114954930671123494512860862139003025724165360536254392186532115427279865016564374052026839334037396289841287817909608371941141662202424867024368525743743672720087719489984425560931797918502498076458442007066443081653286448078164679372420964848776302887965168883216254794168263714873065457820374542133983842824029), (⟨4, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125)]
  | 5 => [(⟨0, by decide⟩, 49680039342721953995691591147809411527617713594746985852762120994925732457702036186166273858417082969657480257984255936629689179728362820795489926426818513709621042248041358241298980655889816333031439148847526971404266527220577099479363798268649359746157167729253123326441401059872632683848319610122152026878842847593039651566181414364559887888286666233265612709035374074086767666393011886474231715170796296364138192923796521930363195747), (⟨1, by decide⟩, -76424553579479392127237373789391670983022846182116069039078290834215988271921956649809588978427619571363190979166158981887449718048694243170048017214150833091667896203384510570889753925999125994219580307337199533772945401931738268898892523821694956526926600311206255603938707885941850775114734961462182713398219693214995182395081246414630559751769303993576136224481942680386474429989482089742924866663468127475326735191416841610925842420), (⟨2, by decide⟩, 47481714062616804284946707132475089110962994837889809140969712513077924170622525898923469955551425212014333564531572982869663823005085160008038948673460541934727859282345896781559613242610589713904001281991384604407861423320642151676535888639213819238769588264529757105289981456995368241006570982066415715970699386090726736031604621588595483959433937760484469021582659122379391230048073754500776800393046831983536749031273476937800752750), (⟨3, by decide⟩, -39754848337577130857784548699068946543683974197795984041191059934369469018527386738556587549303251263256742775845158046014391099050884169449223019491676770371687769133049921009485252721782579389601740950541478829611335527276464758087849452421337587865214498349128455980444251541089206799044196548960823442002644011578710645343496993146407364868119234743769197323989019958700829122418334057701899156929995563893198302660106800833851820132), (⟨4, by decide⟩, 132172960762459737989832553482351025605390717093368500694943450643878648135706295991494837649628351741733601828985320314077871231026523920321325177318402011018718925658860768217488978495791909039567222438608385271540419148143179482098782407074854179881631108455306366728227472919509794716177383740733259453749880176369855198639112444890617199897778393364044886091794962054039538209941902250027471676610349502915544140337987914869706695500), (⟨5, by decide⟩, 99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125)]
  | 6 => [(⟨0, by decide⟩, 37718933520340238716633296294719388223548233725655729160141984485132540005227979617016258058884908184761607650179120384397189615750758215508602314373676522126677114936887971884153274690130271496788024971128594176639224140747622454910727473179629439965936919619043855629124351088483247620529775746297179664767818702768978132493851459142059837368132969216878008773003707434541576623028968044528311614361087938942375774662056347557589753480), (⟨1, by decide⟩, -57774566902961019392283143216653197638255666061145836264427880422738099775218030138139945150429287798990078008665180910246662112599506690060964466401842554261830521333340187661993650775408100337040685217881892941928281310587090755141108352338299638489362641045239271186435751848816687486680394148044438684958732370380320323550173928417170383476128542888665109903774691820890524984603562217373800230370393063528979838842780368775087274925), (⟨2, by decide⟩, 119567159481430463153103499404253452238990587827232677491267367534607202909546641073759557856324592301565632992477702950375951617675172961076279668361340989971040846864025075178384685046315323747178782186829609909734063915049660263705581376351828040002058117541662391503260764373337102878367761767108026778297331152150781628167271809890831378016388984453328971646307486487930408959634625189994707647313823369199454918156535662269907842500), (⟨3, by decide⟩, 184737438523077031857205494851790300756766530901347998367308345291247377066356980629065436333157882836363823010881631827023306763572865418825256407680453427909647152758625630934094987790242755829393820465831445695753548589500058046152237775683047181498470193111944945317517134011545344337341984455385950379347609132069517376739877702028081969605334222885419693287473593846523207306094632996229490977739917743354327159790549874165129439065), (⟨4, by decide⟩, -331297918532512483308889750356351854404488715164305407977088155891568520397548439600493919526739407345499849141113190115625912361802284106063236452384297251954903055069151493385838254487333265279443129665524659646613329173281152271121277398984922757181768528629141485528184682953288399990459767865585249306251623945380547569614379292899594603569140729739461383848685209383606333703264837237991464708045364636255117707575270304142522753750), (⟨5, by decide⟩, -99562478885026372659528598437000414399548999035468453641072352623844936130921071804499540938555527801883123656063934900774020565387880092870955637532947620468092064705145362584174637995770678119937953613458137187536455012568986394511247495955034288650068710086917559399978605016889302637141192062425994926250871884505346185487633424004488701835681168187708248878445123664783397746661467493981996515717507566669786783618641194636408029125)]
  | _ => []

def planar_4_12Aw : Fin 6 → ℤ := fun i =>
  match i.val with
  | 0 => 17177955877262633656581881702274536859110269402151296680915229327693659260902064588445250232025091338437216019651266891539592379050209656135100605240883008426098765254011981176258072561694334098318398820303975555693607321563470467295517094149179523139448399031994010326664506930427278147466117506778510286814487239323309598469015006050750502850893150353538885655195729685526068014730729178489343867604270741357951769711437652481570591044047039473460944852915219034150602339538366640625000000000000000000000000
  | 1 => 933320937732335244884806328454469811218631866162831963413396328289922330983904998448911915269694846311129718902936873443251683324981109613684826751497776946045930793140674770214209421810605079664177353709365545400999719633441238016012431035456587546006187825334336680127041842467674208833323742932033740669905007790994757996461154844917469854313204194738765370383882597593356328300063485281067586388273681338479649147299804919033638174076840336467094838987364070262167039523842212500000000000000000000000000
  | 2 => 17051369436092788131285783008343635629754627983684149458563070820551027655870501472741292331154475113739775024570922084176781535798797749997086840792773473931834358844455424911759589967440012871280480704083724446628489246985770473836125783369172545976201218841807244394840797663867165121466460627153559057135958958408044077346803361601054695470789097173180031223456465577757561050788510087676729766299919832207549675591715108096289224229773015351669031619431693681022345326965352900000000000000000000000000
  | 3 => 3621773049724621122510683591124123325119544751771817282654506323497808945803253614499727316523851168536153338324070023487013516057918082074112728978179630058471330613923446219932787006344655801530860695659250762442744502377159284324067962177443434660409974012388865768746747894757729987707439843920442026574265682054662523492267434055373551361781683002492207963034545439757246244595464927448144236687409005717308559941657624257008438472742132792295196260892443737087574257016875000000000000000000000000000
  | 4 => 266403883983329876264811707470473462256558670477724240894283012873591884020573044096876116694990721262413414525587088539619086762886168913951909101402123727646233883217667069975905607617270069536635064094459794737612082313885121902805983098941338225738098384682747493214953478227040176343144882463151019619667628989949047409202813319853788915720692536990794326440571353667197234548896383233487424256612555406683070927756145990086948439209082719190269662314708510776097676768505080000000000000000000000000
  | 5 => 162040336819201132918688143277035219806958473628717059149902614274571765168237040944199845419384526260464866834281348629912421460007670353262090782870927046996362976877970845270948818517904790624357733565161622638960329811792071123268313587385975861410305888741140973861199550951929816848000024003219971664114247289327672663160535281154038922293774463140886934151222529987659404302568267432777325415829795284492371764379732117720979459892325633833936172862964048027327705599160000000000000000000000000000
  | _ => 0

def planar_4_12A : Matrix (Fin 7) (Fin 7) ℚ := sparseRatScaledMatrix planar_4_12AD planar_4_12AM

theorem planar_4_12A_gram_check : SparseGramCheck planar_4_12AS planar_4_12AM planar_4_12AR planar_4_12AT planar_4_12Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_12A_posSemidef : (planar_4_12A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_12A_gram_check

/- N=4, d=12, H; dimension=7, rank=6. -/
def planar_4_12HD : ℤ := 1540
def planar_4_12HS : ℤ := 15066818166109356351913185246669981768524270325654819870186114800632096727678703307288810794190224622870608656075451904865158843339646299237953197305923112500
def planar_4_12HM : SparseIntMatrix 7 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 17770657500), (⟨1, by decide⟩, -3421845000), (⟨2, by decide⟩, 3758656500), (⟨3, by decide⟩, -2665658250), (⟨4, by decide⟩, 2283219900), (⟨5, by decide⟩, 1920454200), (⟨6, by decide⟩, -3484424250)]
  | 1 => [(⟨0, by decide⟩, -3421845000), (⟨1, by decide⟩, 2632353000), (⟨2, by decide⟩, -3320789400), (⟨3, by decide⟩, 2213830500), (⟨4, by decide⟩, -2600524800), (⟨5, by decide⟩, -2492694000), (⟨6, by decide⟩, 4791476700)]
  | 2 => [(⟨0, by decide⟩, 3758656500), (⟨1, by decide⟩, -3320789400), (⟨2, by decide⟩, 4838487804), (⟨3, by decide⟩, -2715072750), (⟨4, by decide⟩, 3819133908), (⟨5, by decide⟩, 3594417768), (⟨6, by decide⟩, -6999914430)]
  | 3 => [(⟨0, by decide⟩, -2665658250), (⟨1, by decide⟩, 2213830500), (⟨2, by decide⟩, -2715072750), (⟨3, by decide⟩, 2486758375), (⟨4, by decide⟩, -2684478450), (⟨5, by decide⟩, -2555854900), (⟨6, by decide⟩, 4936811175)]
  | 4 => [(⟨0, by decide⟩, 2283219900), (⟨1, by decide⟩, -2600524800), (⟨2, by decide⟩, 3819133908), (⟨3, by decide⟩, -2684478450), (⟨4, by decide⟩, 3933289620), (⟨5, by decide⟩, 3855827928), (⟨6, by decide⟩, -7819319610)]
  | 5 => [(⟨0, by decide⟩, 1920454200), (⟨1, by decide⟩, -2492694000), (⟨2, by decide⟩, 3594417768), (⟨3, by decide⟩, -2555854900), (⟨4, by decide⟩, 3855827928), (⟨5, by decide⟩, 4036283632), (⟨6, by decide⟩, -8090360820)]
  | 6 => [(⟨0, by decide⟩, -3484424250), (⟨1, by decide⟩, 4791476700), (⟨2, by decide⟩, -6999914430), (⟨3, by decide⟩, 4936811175), (⟨4, by decide⟩, -7819319610), (⟨5, by decide⟩, -8090360820), (⟨6, by decide⟩, 16583751135)]
  | _ => []

def planar_4_12HR : SparseIntMatrix 6 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 57861364644296431857766682005185086604038081774488350), (⟨1, by decide⟩, -11141547311981142164848972638521256890500235566952100), (⟨2, by decide⟩, 12238207523787736696236580711896673461144060781612170), (⟨3, by decide⟩, -8679398835992821257582539220186319436015161284625485), (⟨4, by decide⟩, 7434177334013332636490622697061743096312737368627982), (⟨5, by decide⟩, 6253010095370449214175774142117258258232069978488956), (⟨6, by decide⟩, -11345305715597698698186872242679008444198558216459365)]
  | 1 => [(⟨1, by decide⟩, 57861364644296431857766682005185086604038081774488350), (⟨2, by decide⟩, -76144649562460454176633590963627143275938182796222480), (⟨3, by decide⟩, 49859570755831467581939433161469277914332115162352950), (⟨4, by decide⟩, -63356505824679965929948372580475817135698160319211630), (⟨5, by decide⟩, -62242994593370279106635257040479856333353459693400760), (⟨6, by decide⟩, 120813150568734721065725660081520156018517564147736940)]
  | 2 => [(⟨2, by decide⟩, 57861364644296431857766682005185086604038081774488350), (⟨3, by decide⟩, 8008897539057739144276523687999308071575571738758125), (⟨4, by decide⟩, 45536715191069972985440129474946525620532670006678950), (⟨5, by decide⟩, 36475321863141584748729734523315057861574482616875950), (⟨6, by decide⟩, -77696285140042838006119835156022330570177312594503625)]
  | 3 => [(⟨3, by decide⟩, 57861364644296431857766682005185086604038081774488350), (⟨4, by decide⟩, -52030719220763165937806455428021301785598258957119945), (⟨5, by decide⟩, -46805275573533562811967642601900151733730894213065660), (⟨6, by decide⟩, 93005349370763462829813871452757668700889330352817200)]
  | 4 => [(⟨4, by decide⟩, 57861364644296431857766682005185086604038081774488350), (⟨5, by decide⟩, 78068563108697248998869860970101043699316553824907800), (⟨6, by decide⟩, -193791292397290112714403224980471216907392717373884500)]
  | 5 => [(⟨5, by decide⟩, 57861364644296431857766682005185086604038081774488350), (⟨6, by decide⟩, -57861364644296431857766682005185086604038081774488350)]
  | _ => []

def planar_4_12HT : SparseIntMatrix 7 6 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 57861364644296431857766682005185086604038081774488350)]
  | 1 => [(⟨0, by decide⟩, -11141547311981142164848972638521256890500235566952100), (⟨1, by decide⟩, 57861364644296431857766682005185086604038081774488350)]
  | 2 => [(⟨0, by decide⟩, 12238207523787736696236580711896673461144060781612170), (⟨1, by decide⟩, -76144649562460454176633590963627143275938182796222480), (⟨2, by decide⟩, 57861364644296431857766682005185086604038081774488350)]
  | 3 => [(⟨0, by decide⟩, -8679398835992821257582539220186319436015161284625485), (⟨1, by decide⟩, 49859570755831467581939433161469277914332115162352950), (⟨2, by decide⟩, 8008897539057739144276523687999308071575571738758125), (⟨3, by decide⟩, 57861364644296431857766682005185086604038081774488350)]
  | 4 => [(⟨0, by decide⟩, 7434177334013332636490622697061743096312737368627982), (⟨1, by decide⟩, -63356505824679965929948372580475817135698160319211630), (⟨2, by decide⟩, 45536715191069972985440129474946525620532670006678950), (⟨3, by decide⟩, -52030719220763165937806455428021301785598258957119945), (⟨4, by decide⟩, 57861364644296431857766682005185086604038081774488350)]
  | 5 => [(⟨0, by decide⟩, 6253010095370449214175774142117258258232069978488956), (⟨1, by decide⟩, -62242994593370279106635257040479856333353459693400760), (⟨2, by decide⟩, 36475321863141584748729734523315057861574482616875950), (⟨3, by decide⟩, -46805275573533562811967642601900151733730894213065660), (⟨4, by decide⟩, 78068563108697248998869860970101043699316553824907800), (⟨5, by decide⟩, 57861364644296431857766682005185086604038081774488350)]
  | 6 => [(⟨0, by decide⟩, -11345305715597698698186872242679008444198558216459365), (⟨1, by decide⟩, 120813150568734721065725660081520156018517564147736940), (⟨2, by decide⟩, -77696285140042838006119835156022330570177312594503625), (⟨3, by decide⟩, 93005349370763462829813871452757668700889330352817200), (⟨4, by decide⟩, -193791292397290112714403224980471216907392717373884500), (⟨5, by decide⟩, -57861364644296431857766682005185086604038081774488350)]
  | _ => []

def planar_4_12Hw : Fin 6 → ℤ := fun i =>
  match i.val with
  | 0 => 79973793944831205923502477175321130967082134191110810434787500
  | 1 => 8881202465624341523923005125410438399449774963311751786015000
  | 2 => 2816469273266713414801364811609494725489418001264652367646720
  | 3 => 2743132083315356058509669004224937682230803982923128930304000
  | 4 => 1770128897628486879989617236663209415824427234206751648645120
  | 5 => 816756418427681063538544310621051719725948077146382952038400
  | _ => 0

def planar_4_12H : Matrix (Fin 7) (Fin 7) ℚ := sparseRatScaledMatrix planar_4_12HD planar_4_12HM

theorem planar_4_12H_gram_check : SparseGramCheck planar_4_12HS planar_4_12HM planar_4_12HR planar_4_12HT planar_4_12Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_12H_posSemidef : (planar_4_12H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_12H_gram_check

def planar_4_12KD : ℤ := 99032139724623950196003610052302589842127533006578761136744958553114990702437329272876458336222646828644347143301021390922422376413652614565041457101780577703182480220344652824313856000
def planar_4_12KU : SparseIntMatrix 7 1 := fun i =>
  match i.val with
  | 1 => [(⟨0, by decide⟩, -99032139724623950196003610052302589842127533006578761136744958553114990702437329272876458336222646828644347143301021390922422376413652614565041457101780577703182480220344652824313856000)]
  | 2 => [(⟨0, by decide⟩, -99032139724623950196003610052302589842127533006578761136744958553114990702437329272876458336222646828644347143301021390922422376413652614565041457101780577703182480220344652824313856000)]
  | 3 => [(⟨0, by decide⟩, 99032139724623950196003610052302589842127533006578761136744958553114990702437329272876458336222646828644347143301021390922422376413652614565041457101780577703182480220344652824313856000)]
  | 4 => [(⟨0, by decide⟩, 198064279449247900392007220104605179684255066013157522273489917106229981404874658545752916672445293657288694286602042781844844752827305229130082914203561155406364960440689305648627712000)]
  | 5 => [(⟨0, by decide⟩, 99032139724623950196003610052302589842127533006578761136744958553114990702437329272876458336222646828644347143301021390922422376413652614565041457101780577703182480220344652824313856000)]
  | 6 => [(⟨0, by decide⟩, 99032139724623950196003610052302589842127533006578761136744958553114990702437329272876458336222646828644347143301021390922422376413652614565041457101780577703182480220344652824313856000)]
  | _ => []

def planar_4_12KL : SparseIntMatrix 1 7 := fun i =>
  match i.val with
  | 0 => [(⟨6, by decide⟩, 1)]
  | _ => []

def planar_4_12KVA : SparseIntMatrix 7 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 4918251370380919999554305149081639470299033296500466029957818206416622643325555085277926433559825301287283976365305050655755408923188742677401174016), (⟨1, by decide⟩, 153434764040900582881734706252132061030793251173112643437876969105376406110496209537744869134635975431411420877087442619124142673570633498955677171712), (⟨2, by decide⟩, 111747123381040174594383385183900060448307341745515231233263558157462174122716177600568856931868026993325651207518926741753611956939460258254353858560), (⟨3, by decide⟩, -97579544536290316041841369023904740916969460281384457982517419998463510903449217996454710587886360668433664308487098759861336756151941605376946864128), (⟨4, by decide⟩, -75375106160098222165961403828190218037649744381033170215122998342679166379948451802132940356139097159938075220531727021706616059714747457554895339520), (⟨5, by decide⟩, 18996046808211645952603329917847802526635646157381023947986366536645202538436503739287478048518999795037356582002740746734035540011957839240772976640)]
  | 1 => [(⟨0, by decide⟩, 153434764040900582881734706252132061030793251173112643437876969105376406110496209537744869134635975431411420877087442619124142673570633498955677171712), (⟨1, by decide⟩, 7767177437786374133724461695212390979070082638442558412979450906865316233853090412877915144047068468880131978540458866339916882679144306424245429207040), (⟨2, by decide⟩, 4623264119503595129959994629353700103820526542435181431967199574289672132246152302703614495431420594369013510046731981416400414675693175598146618654720), (⟨3, by decide⟩, -5949037574914448659097316995263011882550124292416957441536616400693723790385907580631617132230486792125214822733276969575751257639864693019348136099840), (⟨4, by decide⟩, -5483828391259448802616602946655829999122748094528756178778651643451796537253156070871846987708634511344554774691482801749571327005566030606987889213440), (⟨5, by decide⟩, 2546679796810389856226104754869457791425352729959590538207199800661098713132701281760980060528672125965122828760816190290252570783152539614126255636480)]
  | 2 => [(⟨0, by decide⟩, 111747123381040174594383385183900060448307341745515231233263558157462174122716177600568856931868026993325651207518926741753611956939460258254353858560), (⟨1, by decide⟩, 4623264119503595129959994629353700103820526542435181431967199574289672132246152302703614495431420594369013510046731981416400414675693175598146618654720), (⟨2, by decide⟩, 3185092042049752556304674740218421003158851887942965839628781093571079933172273099622730266211914325569142865068926199996440359709005175103793240473600), (⟨3, by decide⟩, -3258566177862062832115874190145804677499661529023253858586577449481306766084855642777265707908738799741179745143521580260568148496911499461502728929280), (⟨4, by decide⟩, -2755021826576259642797662411389022279226852189069463104692527402864868942167041415981361496623029829061806618171792649970258612026277605700980126515200), (⟨5, by decide⟩, 831500212883226202291921328788874416349462068880577852919200858326188376980349179962258543816161782052109189379038616785528277059365827589936932454400)]
  | 3 => [(⟨0, by decide⟩, -97579544536290316041841369023904740916969460281384457982517419998463510903449217996454710587886360668433664308487098759861336756151941605376946864128), (⟨1, by decide⟩, -5949037574914448659097316995263011882550124292416957441536616400693723790385907580631617132230486792125214822733276969575751257639864693019348136099840), (⟨2, by decide⟩, -3258566177862062832115874190145804677499661529023253858586577449481306766084855642777265707908738799741179745143521580260568148496911499461502728929280), (⟨3, by decide⟩, 4798248651193990371118665022795220586917354914043533395927168289464655553006491594264225752022246131685280928839128808366547473999275645664283601141760), (⟨4, by decide⟩, 4611654806289561382852828826889734747993386689850697466736564616682252005422309250859450955361931031631849501545077134151092415608552179279552955023360), (⟨5, by decide⟩, -2384110469268035131495373192286521042491654658864810019069280290626158845527537226485645504690614195826795212101566898494051459913419211443976609464320)]
  | 4 => [(⟨0, by decide⟩, -75375106160098222165961403828190218037649744381033170215122998342679166379948451802132940356139097159938075220531727021706616059714747457554895339520), (⟨1, by decide⟩, -5483828391259448802616602946655829999122748094528756178778651643451796537253156070871846987708634511344554774691482801749571327005566030606987889213440), (⟨2, by decide⟩, -2755021826576259642797662411389022279226852189069463104692527402864868942167041415981361496623029829061806618171792649970258612026277605700980126515200), (⟨3, by decide⟩, 4611654806289561382852828826889734747993386689850697466736564616682252005422309250859450955361931031631849501545077134151092415608552179279552955023360), (⟨4, by decide⟩, 4591025257338514324848007261805946453074536938706370121909197855288117114001378479220500822559820458906459347170065858081769026488271409955373213286400), (⟨5, by decide⟩, -2570969688679313018524556053476694878693420068678403799372713531689620270663244780350907710368595007059678620291401467480698548896257099587189001420800)]
  | 5 => [(⟨0, by decide⟩, 18996046808211645952603329917847802526635646157381023947986366536645202538436503739287478048518999795037356582002740746734035540011957839240772976640), (⟨1, by decide⟩, 2546679796810389856226104754869457791425352729959590538207199800661098713132701281760980060528672125965122828760816190290252570783152539614126255636480), (⟨2, by decide⟩, 831500212883226202291921328788874416349462068880577852919200858326188376980349179962258543816161782052109189379038616785528277059365827589936932454400), (⟨3, by decide⟩, -2384110469268035131495373192286521042491654658864810019069280290626158845527537226485645504690614195826795212101566898494051459913419211443976609464320), (⟨4, by decide⟩, -2570969688679313018524556053476694878693420068678403799372713531689620270663244780350907710368595007059678620291401467480698548896257099587189001420800), (⟨5, by decide⟩, 1936645088878716359273882936921733001913360390033764112055533313039968794530433238805993738399557522412454526712657797871754916957855423180599564697600)]
  | _ => []

def planar_4_12KVH : SparseIntMatrix 7 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 8131819857444672094629734975950168937107915891914168117960899129400933985289367802079854132892833731685330574030844603908505133302476754579718144459270465589401383676911952029), (⟨1, by decide⟩, 20210521571520729558291523756509309294140209767908166720603825620916554565091119130581211936797604317602024644491195377345581154902502223841061090508118014535846142243286458364), (⟨2, by decide⟩, 4202131142262105572535266941744170751375233509527547554357559815686574478572328270366821813822661502311362843540707455624771192887584082856216960441525109682702314142228478685), (⟨3, by decide⟩, -34934592841401242647644875318689359446541687586426812991895296937944909259289295799174645232747783217493372989075044159719593431763112024804554026675535279212688746676985988), (⟨4, by decide⟩, -3380191593161584668684138945431852514780615124252960468087882392646905759889207655633463521767820170469615541901327689791925255998631091317171285654559523744296930137284758020), (⟨5, by decide⟩, 8077180839387620955020819276660533434695175328149405008169520020446762811581394991098537334656743761946869953163391774129410849387514201521785490064188340202545428053789501765)]
  | 1 => [(⟨0, by decide⟩, 20210521571520729558291523756509309294140209767908166720603825620916554565091119130581211936797604317602024644491195377345581154902502223841061090508118014535846142243286458364), (⟨1, by decide⟩, 884763116716791070719316567060163413215413256821408424322956714882565773815844404583535108423362173920436009949722101569347612878983958381174139921938327355093833821871273732944), (⟨2, by decide⟩, 589969253584977428163590981835125532262845819156105428581718943133857131478333612696221904449512278419796454234425302128868084549696394206264500237935969037767770423878685281020), (⟨3, by decide⟩, -498478391703702651825390342102907983532500404544140756393972449284976463671809750441271176964863905710121595581839992204743001473121546567021009311363416237662858180193617570480), (⟨4, by decide⟩, -654476824708287662520438328184806835598462532337261899439298273652397153434386667561588693420620304184794645079198666185489910453505556455678345459368997623803677299772489432240), (⟨5, by decide⟩, 320974951426415243925405854564670619539285248818162488606834313301870269921745152625270282564936740607059807575618043640248031275344880625146970005513508486951290903415305487580)]
  | 2 => [(⟨0, by decide⟩, 4202131142262105572535266941744170751375233509527547554357559815686574478572328270366821813822661502311362843540707455624771192887584082856216960441525109682702314142228478685), (⟨1, by decide⟩, 589969253584977428163590981835125532262845819156105428581718943133857131478333612696221904449512278419796454234425302128868084549696394206264500237935969037767770423878685281020), (⟨2, by decide⟩, 500159024170113642078631400506322310854365842878040696430272007258582323872185136152365239650199092153270979331657624766674118638481315305802724266885934847267183685793596631325), (⟨3, by decide⟩, -336394021329533042340857315694870993954474114634493656941903822284461538893355375562288130045286611328984491474694601229709209633758060659542410728122959704556735897686848320900), (⟨4, by decide⟩, -588340471962762633921694287774945565249557148663890453911141712437061994624682667974182537808120561733811008584656267886852837183072666172209779777994047166117469155618535216900), (⟨5, by decide⟩, 265969329212138810475916450929582418257129638701162214412449121189297394830470097499882667471321958151124651439587654242569565291184773393959265451354256049590090909077907137925)]
  | 3 => [(⟨0, by decide⟩, -34934592841401242647644875318689359446541687586426812991895296937944909259289295799174645232747783217493372989075044159719593431763112024804554026675535279212688746676985988), (⟨1, by decide⟩, -498478391703702651825390342102907983532500404544140756393972449284976463671809750441271176964863905710121595581839992204743001473121546567021009311363416237662858180193617570480), (⟨2, by decide⟩, -336394021329533042340857315694870993954474114634493656941903822284461538893355375562288130045286611328984491474694601229709209633758060659542410728122959704556735897686848320900), (⟨3, by decide⟩, 455277828284758904694542047431179992937263401578352172518957237571377587723846514685826596001133441735117804204824392406124120043284052941641267436559549665047062253792371244880), (⟨4, by decide⟩, 524102887585938803818208769361461382824766421361212843911753888523054928469832628085194843154996134427368247988547330955522429642258558820181935421955827395611020147496334552400), (⟨5, by decide⟩, -220641788967427293643872926288432354078307161456075854046042280295118232098148271419286516616582336093242270577652215063622587262573229878929061030077199337336952952373797281700)]
  | 4 => [(⟨0, by decide⟩, -3380191593161584668684138945431852514780615124252960468087882392646905759889207655633463521767820170469615541901327689791925255998631091317171285654559523744296930137284758020), (⟨1, by decide⟩, -654476824708287662520438328184806835598462532337261899439298273652397153434386667561588693420620304184794645079198666185489910453505556455678345459368997623803677299772489432240), (⟨2, by decide⟩, -588340471962762633921694287774945565249557148663890453911141712437061994624682667974182537808120561733811008584656267886852837183072666172209779777994047166117469155618535216900), (⟨3, by decide⟩, 524102887585938803818208769361461382824766421361212843911753888523054928469832628085194843154996134427368247988547330955522429642258558820181935421955827395611020147496334552400), (⟨4, by decide⟩, 1245127900523611655813635397337847933221995459256763822975575971549061177203050537722142981591422327411745417668724516564991245256291384128466581704003643996262037055028633086800), (⟨5, by decide⟩, -736233073603120239648734700751074759751835352733936374741431579427915006059271830646915400865124671368971412318647021483911148978840772690885519831267015862217359618491661432100)]
  | 5 => [(⟨0, by decide⟩, 8077180839387620955020819276660533434695175328149405008169520020446762811581394991098537334656743761946869953163391774129410849387514201521785490064188340202545428053789501765), (⟨1, by decide⟩, 320974951426415243925405854564670619539285248818162488606834313301870269921745152625270282564936740607059807575618043640248031275344880625146970005513508486951290903415305487580), (⟨2, by decide⟩, 265969329212138810475916450929582418257129638701162214412449121189297394830470097499882667471321958151124651439587654242569565291184773393959265451354256049590090909077907137925), (⟨3, by decide⟩, -220641788967427293643872926288432354078307161456075854046042280295118232098148271419286516616582336093242270577652215063622587262573229878929061030077199337336952952373797281700), (⟨4, by decide⟩, -736233073603120239648734700751074759751835352733936374741431579427915006059271830646915400865124671368971412318647021483911148978840772690885519831267015862217359618491661432100), (⟨5, by decide⟩, 545667149984927428314957316137768090304683587170466988497829107625163504854589857864264298377342360336249777786021495153532102443149931331966659669974231833076966375613266945325)]
  | _ => []

def planar_4_12U : Matrix (Fin 7) (Fin 1) ℚ := sparseRatScaledMatrix planar_4_12KD planar_4_12KU
def planar_4_12L : Matrix (Fin 1) (Fin 7) ℚ := sparseRatMatrix planar_4_12KL

def planar_4_12AV : Matrix (Fin 7) (Fin 7) ℚ :=
  ((planar_4_12AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_12KD planar_4_12KVA

theorem planar_4_12A_kernel_check : SparseScaledFrameCheck planar_4_12KD planar_4_12AM planar_4_12KU planar_4_12KL planar_4_12KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_12A_kernel_frame : HasKernelFrame planar_4_12A planar_4_12U planar_4_12L planar_4_12AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_12KD≠0) planar_4_12A_kernel_check).scale_matrix
    (by norm_num [planar_4_12AD])

theorem planar_4_12A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_12A.map (Rat.castHom ℂ)).mulVecLin)=1 :=
  kernelFrame_finrank planar_4_12A_kernel_frame.ratCast

def planar_4_12HV : Matrix (Fin 7) (Fin 7) ℚ :=
  ((planar_4_12HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_12KD planar_4_12KVH

theorem planar_4_12H_kernel_check : SparseScaledFrameCheck planar_4_12KD planar_4_12HM planar_4_12KU planar_4_12KL planar_4_12KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_12H_kernel_frame : HasKernelFrame planar_4_12H planar_4_12U planar_4_12L planar_4_12HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_12KD≠0) planar_4_12H_kernel_check).scale_matrix
    (by norm_num [planar_4_12HD])

theorem planar_4_12H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_12H.map (Rat.castHom ℂ)).mulVecLin)=1 :=
  kernelFrame_finrank planar_4_12H_kernel_frame.ratCast

theorem planar_4_12_same_kernel (v : Fin 7 → ℂ) :
    (planar_4_12A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_12H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_12A_kernel_frame.ratCast planar_4_12H_kernel_frame.ratCast v

def planar_4_12WS : SparseIntMatrix 7 6 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 1)]
  | 5 => [(⟨5, by decide⟩, 1)]
  | _ => []

def planar_4_12RS : SparseIntMatrix 6 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1), (⟨6, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1), (⟨6, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1), (⟨6, by decide⟩, -1)]
  | 4 => [(⟨4, by decide⟩, 1), (⟨6, by decide⟩, -2)]
  | 5 => [(⟨5, by decide⟩, 1), (⟨6, by decide⟩, -1)]
  | _ => []

def planar_4_12W : Matrix (Fin 7) (Fin 6) ℚ := sparseRatMatrix planar_4_12WS
def planar_4_12R : Matrix (Fin 6) (Fin 7) ℚ := sparseRatScaledMatrix 1 planar_4_12RS

theorem planar_4_12_complement : HasComplement planar_4_12U planar_4_12L planar_4_12W planar_4_12R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_12A_active_posDef :
    ((planar_4_12W.map (Rat.castHom ℂ))ᴴ * (planar_4_12A.map (Rat.castHom ℂ)) * (planar_4_12W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_12A_kernel_frame.ratCast planar_4_12A_posSemidef _ _
    ((planar_4_12_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_12_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_12H_active_posDef :
    ((planar_4_12W.map (Rat.castHom ℂ))ᴴ * (planar_4_12H.map (Rat.castHom ℂ)) * (planar_4_12W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_12H_kernel_frame.ratCast planar_4_12H_posSemidef _ _
    ((planar_4_12_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_12_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=13, A; dimension=5, rank=5. -/
def planar_4_13AD : ℤ := 2156000000000000000000000000
def planar_4_13AS : ℤ := 9970409342168293063661257241830404221497512839324193262776605700025829635877520244497930180709664776466642320057484970383438599040813859573282376117246295983595490115669941917096135123820026792051507919164806093236510939715088338300087397727668927391451160754307990461873661306929132412629528044356754627113811849550626559467644044403183835547957031703306348539190077920642930416068435637975825414489333479911857290191065131538127669095584605673079318265541587370978597078230685084695482129593377436432550509836301408736310220671152093576329436566248850028282196013153861181441644943620006704627132443680184234675328852711983904926194145904246259616573917770957823477468579558304487948458876297926187635307019563121634012660394155276689412500000000000000000000000000
def planar_4_13AM : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 6537776254068386337681387701700), (⟨1, by decide⟩, -685597986902787445665409214250), (⟨2, by decide⟩, -396439637958160043918307712650), (⟨3, by decide⟩, -137674378094781342970978331040), (⟨4, by decide⟩, -106456255616217898401865313760)]
  | 1 => [(⟨0, by decide⟩, -685597986902787445665409214250), (⟨1, by decide⟩, 154733868594802520859401912025), (⟨2, by decide⟩, 121387055013074844714168794025), (⟨3, by decide⟩, -35376784888443476570762861520), (⟨4, by decide⟩, -39728181279798215280841479120)]
  | 2 => [(⟨0, by decide⟩, -396439637958160043918307712650), (⟨1, by decide⟩, 121387055013074844714168794025), (⟨2, by decide⟩, 105977505393570826903850800825), (⟨3, by decide⟩, -42916083665883165052631636880), (⟨4, by decide⟩, -47446426034246597416945792080)]
  | 3 => [(⟨0, by decide⟩, -137674378094781342970978331040), (⟨1, by decide⟩, -35376784888443476570762861520), (⟨2, by decide⟩, -42916083665883165052631636880), (⟨3, by decide⟩, 71385109855426528262591740992), (⟨4, by decide⟩, 70527855813067958826121187328)]
  | 4 => [(⟨0, by decide⟩, -106456255616217898401865313760), (⟨1, by decide⟩, -39728181279798215280841479120), (⟨2, by decide⟩, -47446426034246597416945792080), (⟨3, by decide⟩, 70527855813067958826121187328), (⟨4, by decide⟩, 73640549485153023893465960448)]
  | _ => []

def planar_4_13AR : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 22671917769815206662595446988444758286596896606470831860727063780876839385182398301597992527251121360895198257864278472203251972115345465059239143099329985759581870193368278198649129607725080808900322315099347271333119653622999370043799866817365050), (⟨1, by decide⟩, -2377539484092636369654950291162380307393575012410958781822198294373333464759397336605971411669840340644433893075285287172568611655220398941693580075500866344203780830725470239994724260200618693332527250210987666934495417127773198167993900728352625), (⟨2, by decide⟩, -1374786551755966409533461809865405866197488090603090338567094947428220360320882619900698345324639950532975846785459279647345626701879828491023594761234864515875704098539212727292262216279133391279406748552002341555386924116241234277247063019600225), (⟨3, by decide⟩, -477431783816852652262245912769820061168733154617905132631617200469773487552943438842023181710217379724943137954101889148282652716337130374026907170566721890077539627259032052602482648655830368492584014582597661119855641799851131683714514113596560), (⟨4, by decide⟩, -369172541184991447421017672345457553728024483578131236305418526469778419887452891961145078955684042609481184833632601637214602722561449735383758587290345383039275026984587364859044725477987150531526735933104063084207323244891622812729241733870640)]
  | 1 => [(⟨1, by decide⟩, 22671917769815206662595446988444758286596896606470831860727063780876839385182398301597992527251121360895198257864278472203251972115345465059239143099329985759581870193368278198649129607725080808900322315099347271333119653622999370043799866817365050), (⟨2, by decide⟩, 21844380655686201841881750816474475522202271097512526306166896575696901333992185773222251417087021981058824613011877233157584643578449519193552387191422308912808405290939720081832547988558393772098256167210739802744792615626594873902909738429374550), (⟨3, by decide⟩, -13633806846848265363824543880269674502154803749062089060763115722619429655621731199934132537042186444202763179185157943519679308681241880416230251009826243025676102494635654048316731809096580084170209985518019440635780012402945021003907444367974540), (⟨4, by decide⟩, -13928749148134748168602515679091817516222790770095847669545419209749635490026423631674294395041908206625265357253121576521293105931292698996736962766147927931788577047821668198545359993697527904977927029183358139844175205545163899506102661559173840)]
  | 2 => [(⟨2, by decide⟩, 22671917769815206662595446988444758286596896606470831860727063780876839385182398301597992527251121360895198257864278472203251972115345465059239143099329985759581870193368278198649129607725080808900322315099347271333119653622999370043799866817365050), (⟨3, by decide⟩, -14708954351807520294519504797641317753632435724969363191956304457784108096867387771570248170277115279335239401595397531960164400608700234237083286277604179895873830523289828568753083558807954349328317175294621789917741347659650053057224061472410909), (⟨4, by decide⟩, -21905190348658458835568857107464930706767172446289871078816491426253858723900013822404604119671535626054293403113154185789419763316231635167232505373633660755992133100853474788435760149432611773395393938813277776422469837966333000238703091000231183)]
  | 3 => [(⟨3, by decide⟩, 22671917769815206662595446988444758286596896606470831860727063780876839385182398301597992527251121360895198257864278472203251972115345465059239143099329985759581870193368278198649129607725080808900322315099347271333119653622999370043799866817365050), (⟨4, by decide⟩, 21497957663119076947597903515568408818119102543338754986234167719514433380108118197896222215145155403216912367789756129097849152780644947381448127424250071562567233454948683511715424276503036496027604187836176163204419826137220415856612400110333350)]
  | 4 => [(⟨4, by decide⟩, 22671917769815206662595446988444758286596896606470831860727063780876839385182398301597992527251121360895198257864278472203251972115345465059239143099329985759581870193368278198649129607725080808900322315099347271333119653622999370043799866817365050)]
  | _ => []

def planar_4_13AT : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 22671917769815206662595446988444758286596896606470831860727063780876839385182398301597992527251121360895198257864278472203251972115345465059239143099329985759581870193368278198649129607725080808900322315099347271333119653622999370043799866817365050)]
  | 1 => [(⟨0, by decide⟩, -2377539484092636369654950291162380307393575012410958781822198294373333464759397336605971411669840340644433893075285287172568611655220398941693580075500866344203780830725470239994724260200618693332527250210987666934495417127773198167993900728352625), (⟨1, by decide⟩, 22671917769815206662595446988444758286596896606470831860727063780876839385182398301597992527251121360895198257864278472203251972115345465059239143099329985759581870193368278198649129607725080808900322315099347271333119653622999370043799866817365050)]
  | 2 => [(⟨0, by decide⟩, -1374786551755966409533461809865405866197488090603090338567094947428220360320882619900698345324639950532975846785459279647345626701879828491023594761234864515875704098539212727292262216279133391279406748552002341555386924116241234277247063019600225), (⟨1, by decide⟩, 21844380655686201841881750816474475522202271097512526306166896575696901333992185773222251417087021981058824613011877233157584643578449519193552387191422308912808405290939720081832547988558393772098256167210739802744792615626594873902909738429374550), (⟨2, by decide⟩, 22671917769815206662595446988444758286596896606470831860727063780876839385182398301597992527251121360895198257864278472203251972115345465059239143099329985759581870193368278198649129607725080808900322315099347271333119653622999370043799866817365050)]
  | 3 => [(⟨0, by decide⟩, -477431783816852652262245912769820061168733154617905132631617200469773487552943438842023181710217379724943137954101889148282652716337130374026907170566721890077539627259032052602482648655830368492584014582597661119855641799851131683714514113596560), (⟨1, by decide⟩, -13633806846848265363824543880269674502154803749062089060763115722619429655621731199934132537042186444202763179185157943519679308681241880416230251009826243025676102494635654048316731809096580084170209985518019440635780012402945021003907444367974540), (⟨2, by decide⟩, -14708954351807520294519504797641317753632435724969363191956304457784108096867387771570248170277115279335239401595397531960164400608700234237083286277604179895873830523289828568753083558807954349328317175294621789917741347659650053057224061472410909), (⟨3, by decide⟩, 22671917769815206662595446988444758286596896606470831860727063780876839385182398301597992527251121360895198257864278472203251972115345465059239143099329985759581870193368278198649129607725080808900322315099347271333119653622999370043799866817365050)]
  | 4 => [(⟨0, by decide⟩, -369172541184991447421017672345457553728024483578131236305418526469778419887452891961145078955684042609481184833632601637214602722561449735383758587290345383039275026984587364859044725477987150531526735933104063084207323244891622812729241733870640), (⟨1, by decide⟩, -13928749148134748168602515679091817516222790770095847669545419209749635490026423631674294395041908206625265357253121576521293105931292698996736962766147927931788577047821668198545359993697527904977927029183358139844175205545163899506102661559173840), (⟨2, by decide⟩, -21905190348658458835568857107464930706767172446289871078816491426253858723900013822404604119671535626054293403113154185789419763316231635167232505373633660755992133100853474788435760149432611773395393938813277776422469837966333000238703091000231183), (⟨3, by decide⟩, 21497957663119076947597903515568408818119102543338754986234167719514433380108118197896222215145155403216912367789756129097849152780644947381448127424250071562567233454948683511715424276503036496027604187836176163204419826137220415856612400110333350), (⟨4, by decide⟩, 22671917769815206662595446988444758286596896606470831860727063780876839385182398301597992527251121360895198257864278472203251972115345465059239143099329985759581870193368278198649129607725080808900322315099347271333119653622999370043799866817365050)]
  | _ => []

def planar_4_13Aw : Fin 5 → ℤ := fun i =>
  match i.val with
  | 0 => 126813803038733875604121069028077822713493684790358799187206907124646889843396883913279925058955124025762694440312924055905214310150876417219035404820675956480271871785871761882724850667651358243155713404271785798422418811215542127317219872702360009065939919752238536226047000500000000000000000000000000
  | 1 => 1606799434334924816351739154645815049586606193226946453289966488736698446078638205000617340040345216554139827385547964486463350802727014579255938780984126107993599064161711604761266296108407987914725232813862149774501750142800197516283531609870204304465766309953075787845346000000000000000000000000000
  | 2 => 97717833510549818318870457589643596976334655278298518854634436839371975263648224276744519765733733210229758016714631404443761455346991058034214707270305454658824202506918104154378220321365589599390567812233561116113762937049935661934430631105581420933428730590738358218720000000000000000000000000000
  | 3 => 706239151914878858468625187992042726111577147597922883718557844801214312411411278803385009148596548939232233330210960752405004410583281703737199785157223310860677821492026006270907816166637207009736830015374730386771353479336450458886145598124106787247936353886813773410851392000000000000000000000000
  | 4 => 62103604107533835087575293279058093773896456865070492459912641612701462119440502802627571070340272970223271994534601938914211906008604120996970559802409148791445330273816268664965205243174416050640684690457876567137606403985628521025310743717092110372094621931584719280048640000000000000000000000000
  | _ => 0

def planar_4_13A : Matrix (Fin 5) (Fin 5) ℚ := sparseRatScaledMatrix planar_4_13AD planar_4_13AM

theorem planar_4_13A_gram_check : SparseGramCheck planar_4_13AS planar_4_13AM planar_4_13AR planar_4_13AT planar_4_13Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_13A_posSemidef : (planar_4_13A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_13A_gram_check

/- N=4, d=13, H; dimension=5, rank=5. -/
def planar_4_13HD : ℤ := 385
def planar_4_13HS : ℤ := 2106837326194439410699380914740863368355922272064732337229754590161186485610314695722172714975066000
def planar_4_13HM : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 5863914000), (⟨1, by decide⟩, -3272332500), (⟨2, by decide⟩, -2744464500), (⟨3, by decide⟩, 3753226800), (⟨4, by decide⟩, 3093589800)]
  | 1 => [(⟨0, by decide⟩, -3272332500), (⟨1, by decide⟩, 3755264625), (⟨2, by decide⟩, 2938613625), (⟨3, by decide⟩, -4716265500), (⟨4, by decide⟩, -4224953250)]
  | 2 => [(⟨0, by decide⟩, -2744464500), (⟨1, by decide⟩, 2938613625), (⟨2, by decide⟩, 3039186625), (⟨3, by decide⟩, -4608527100), (⟨4, by decide⟩, -4477878450)]
  | 3 => [(⟨0, by decide⟩, 3753226800), (⟨1, by decide⟩, -4716265500), (⟨2, by decide⟩, -4608527100), (⟨3, by decide⟩, 7584029712), (⟨4, by decide⟩, 7391382840)]
  | 4 => [(⟨0, by decide⟩, 3093589800), (⟨1, by decide⟩, -4224953250), (⟨2, by decide⟩, -4477878450), (⟨3, by decide⟩, 7391382840), (⟨4, by decide⟩, 7778094660)]
  | _ => []

def planar_4_13HR : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 994979790943363007444517572514420), (⟨1, by decide⟩, -555244279971904845220860469536225), (⟨2, by decide⟩, -465676460204136910013467830086185), (⟨3, by decide⟩, 636841675513492749325682959578204), (⟨4, by decide⟩, 524915497135278617238875540850594)]
  | 1 => [(⟨1, by decide⟩, 994979790943363007444517572514420), (⟨2, by decide⟩, 725713701998345120165338890231540), (⟨3, by decide⟩, -1352215607374369225498340482150320), (⟨4, by decide⟩, -1288671620933426010437350651355640)]
  | 2 => [(⟨2, by decide⟩, 994979790943363007444517572514420), (⟨3, by decide⟩, -1283507428497152441579826479264916), (⟨4, by decide⟩, -1649500135962260886296657757783054)]
  | 3 => [(⟨3, by decide⟩, 994979790943363007444517572514420), (⟨4, by decide⟩, 1120682277197229394324852279959150)]
  | 4 => [(⟨4, by decide⟩, 994979790943363007444517572514420)]
  | _ => []

def planar_4_13HT : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 994979790943363007444517572514420)]
  | 1 => [(⟨0, by decide⟩, -555244279971904845220860469536225), (⟨1, by decide⟩, 994979790943363007444517572514420)]
  | 2 => [(⟨0, by decide⟩, -465676460204136910013467830086185), (⟨1, by decide⟩, 725713701998345120165338890231540), (⟨2, by decide⟩, 994979790943363007444517572514420)]
  | 3 => [(⟨0, by decide⟩, 636841675513492749325682959578204), (⟨1, by decide⟩, -1352215607374369225498340482150320), (⟨2, by decide⟩, -1283507428497152441579826479264916), (⟨3, by decide⟩, 994979790943363007444517572514420)]
  | 4 => [(⟨0, by decide⟩, 524915497135278617238875540850594), (⟨1, by decide⟩, -1288671620933426010437350651355640), (⟨2, by decide⟩, -1649500135962260886296657757783054), (⟨3, by decide⟩, 1120682277197229394324852279959150), (⟨4, by decide⟩, 994979790943363007444517572514420)]
  | _ => []

def planar_4_13Hw : Fin 5 → ℤ := fun i =>
  match i.val with
  | 0 => 12479295730247199585432578691303495646410000
  | 1 => 4105529865891178443664067125904808457935000
  | 2 => 1550185098336823813320720772052130037760000
  | 3 => 865117030900852382980181095329457778196480
  | 4 => 834745074864318938672722312436641274265600
  | _ => 0

def planar_4_13H : Matrix (Fin 5) (Fin 5) ℚ := sparseRatScaledMatrix planar_4_13HD planar_4_13HM

theorem planar_4_13H_gram_check : SparseGramCheck planar_4_13HS planar_4_13HM planar_4_13HR planar_4_13HT planar_4_13Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_13H_posSemidef : (planar_4_13H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_13H_gram_check

def planar_4_13KD : ℤ := 1154869698916839010214753658443896825674492875117416203437855661584728700446582109586975836363487803305317536594258830741073830084608000
def planar_4_13KU : SparseIntMatrix 5 0 := fun i =>
  match i.val with
  | _ => []

def planar_4_13KL : SparseIntMatrix 0 5 := fun i =>
  match i.val with
  | _ => []

def planar_4_13KVA : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 873703158627966431916785861947069620115930621818625164607831290759624587438081541293157057419385765888000), (⟨1, by decide⟩, 11745836482052514969401692908721199790350835869662671267778966437035114970182591937045288686371105281146880), (⟨2, by decide⟩, -9745761576951602301199789427019317303107965592649314241252264909565887001901043138062215158896839087882240), (⟨3, by decide⟩, 6363851483177445161320432964048664185541363546426070660709524382958783217825910938400120478134107111424000), (⟨4, by decide⟩, -4774251010592906774662799981406533583369675965473849938958400360660544786762303154971281405308530537267200)]
  | 1 => [(⟨0, by decide⟩, 11745836482052514969401692908721199790350835869662671267778966437035114970182591937045288686371105281146880), (⟨1, by decide⟩, 257959401500902998988533332199571523220119679492165573473091643673603864863877936636611871511512696833966080), (⟨2, by decide⟩, -258591933513645146825634469014050862226864313347256807867548364424622602790449163930816003766853835570544640), (⟨3, by decide⟩, 99817573089969372727537452671752486838055755765500123232627389461883153164772901239136428926836389026201600), (⟨4, by decide⟩, -106062581919851275707270262381983438869260201140807911053142491373124280857545874883911651115324146922291200)]
  | 2 => [(⟨0, by decide⟩, -9745761576951602301199789427019317303107965592649314241252264909565887001901043138062215158896839087882240), (⟨1, by decide⟩, -258591933513645146825634469014050862226864313347256807867548364424622602790449163930816003766853835570544640), (⟨2, by decide⟩, 287033061096552249751309708541887854865047439040691533060172019576315834303492416310357903258300711163658240), (⟨3, by decide⟩, -99473849999267633696802077248357730963170978788754513218304339936941019895626980521118788767271219940556800), (⟨4, by decide⟩, 126608041630182280500173623395366120269517739064851183453814975151560330634417861754718144639386863324364800)]
  | 3 => [(⟨0, by decide⟩, 6363851483177445161320432964048664185541363546426070660709524382958783217825910938400120478134107111424000), (⟨1, by decide⟩, 99817573089969372727537452671752486838055755765500123232627389461883153164772901239136428926836389026201600), (⟨2, by decide⟩, -99473849999267633696802077248357730963170978788754513218304339936941019895626980521118788767271219940556800), (⟨3, by decide⟩, 356036488960046774282893744960189388442023549833543106580393767767557615152658853406562561566396733980672000), (⟨4, by decide⟩, -342027952821707526542610437214183561145624640116500179149161297577367985892551417684317225864877020020736000)]
  | 4 => [(⟨0, by decide⟩, -4774251010592906774662799981406533583369675965473849938958400360660544786762303154971281405308530537267200), (⟨1, by decide⟩, -106062581919851275707270262381983438869260201140807911053142491373124280857545874883911651115324146922291200), (⟨2, by decide⟩, 126608041630182280500173623395366120269517739064851183453814975151560330634417861754718144639386863324364800), (⟨3, by decide⟩, -342027952821707526542610437214183561145624640116500179149161297577367985892551417684317225864877020020736000), (⟨4, by decide⟩, 360705409456412525950022117218855473549368666084126938462566143647514334645127873380697523384749727940608000)]
  | _ => []

def planar_4_13KVH : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 515866776680775259420811085104474185963422665888115756129685093333777001266723928517202174148932093721389790582168422546613052), (⟨1, by decide⟩, 413274074185044843085808156079292532219992217226393280838952497295526548032802884676697264460609398674972915780295985294797056), (⟨2, by decide⟩, 863697116050069354205185231345681304229432469477167001159049558311669852435704903550739062368522443970278698207698113154433872), (⟨3, by decide⟩, 313061206256988604014268452302341393700447137982749205498175460060005138258347116160399941832701615180416437883682752755176950), (⟨4, by decide⟩, 219045793904039552659384450008453241066821721562123238710365488267810312234114166279014872212674371180032267232619653595503580)]
  | 1 => [(⟨0, by decide⟩, 413274074185044843085808156079292532219992217226393280838952497295526548032802884676697264460609398674972915780295985294797056), (⟨1, by decide⟩, 2375216921636218784693463570081635052896377788256143775494138178446839131150933915011105801872493534637864735025742133978939392), (⟨2, by decide⟩, 143833371497314608704528708561176888525992471472532913059413331214567781705557884541874207648294686872825209710019425944325120), (⟨3, by decide⟩, 2464670187070782233266198785085211513658403926602968482182460687774145770596722126245406310673138508370632579742513715261763200), (⟨4, by decide⟩, -1133513150164883762441073814710549744183754184547691516730718803882480523054439295348711390947023644845865588231772097693351680)]
  | 2 => [(⟨0, by decide⟩, 863697116050069354205185231345681304229432469477167001159049558311669852435704903550739062368522443970278698207698113154433872), (⟨1, by decide⟩, 143833371497314608704528708561176888525992471472532913059413331214567781705557884541874207648294686872825209710019425944325120), (⟨2, by decide⟩, 6436492206489267332435215410741286246450454607519478969945538279872681920737923364322227825267412381232198896695791715864210880), (⟨3, by decide⟩, 2985358790746290488384802897758483358442927380339230840958269897491953020744986719166750714088093758930923716720635113839219400), (⟨4, by decide⟩, 603189456391892756105248322054257823911488315027677185297936469984051086510675322727011984831879321925515252474904110089221840)]
  | 3 => [(⟨0, by decide⟩, 313061206256988604014268452302341393700447137982749205498175460060005138258347116160399941832701615180416437883682752755176950), (⟨1, by decide⟩, 2464670187070782233266198785085211513658403926602968482182460687774145770596722126245406310673138508370632579742513715261763200), (⟨2, by decide⟩, 2985358790746290488384802897758483358442927380339230840958269897491953020744986719166750714088093758930923716720635113839219400), (⟨3, by decide⟩, 6576166903364931373575987133879849627869549411625516627072965342237987296036139777093879693100493682498783722010471016337588375), (⟨4, by decide⟩, -3316269751507000194397658796346216126644717084257444226170202778338646223194766494362247988840434316619469517190546275737360250)]
  | 4 => [(⟨0, by decide⟩, 219045793904039552659384450008453241066821721562123238710365488267810312234114166279014872212674371180032267232619653595503580), (⟨1, by decide⟩, -1133513150164883762441073814710549744183754184547691516730718803882480523054439295348711390947023644845865588231772097693351680), (⟨2, by decide⟩, 603189456391892756105248322054257823911488315027677185297936469984051086510675322727011984831879321925515252474904110089221840), (⟨3, by decide⟩, -3316269751507000194397658796346216126644717084257444226170202778338646223194766494362247988840434316619469517190546275737360250), (⟨4, by decide⟩, 2944296926260333412724986437665930698792445411842426310788229251384716363580692633504362895919616360961351586124632764341496700)]
  | _ => []

def planar_4_13U : Matrix (Fin 5) (Fin 0) ℚ := sparseRatScaledMatrix planar_4_13KD planar_4_13KU
def planar_4_13L : Matrix (Fin 0) (Fin 5) ℚ := sparseRatMatrix planar_4_13KL

def planar_4_13AV : Matrix (Fin 5) (Fin 5) ℚ :=
  ((planar_4_13AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_13KD planar_4_13KVA

theorem planar_4_13A_kernel_check : SparseScaledFrameCheck planar_4_13KD planar_4_13AM planar_4_13KU planar_4_13KL planar_4_13KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_13A_kernel_frame : HasKernelFrame planar_4_13A planar_4_13U planar_4_13L planar_4_13AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_13KD≠0) planar_4_13A_kernel_check).scale_matrix
    (by norm_num [planar_4_13AD])

theorem planar_4_13A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_13A.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_13A_kernel_frame.ratCast

def planar_4_13HV : Matrix (Fin 5) (Fin 5) ℚ :=
  ((planar_4_13HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_13KD planar_4_13KVH

theorem planar_4_13H_kernel_check : SparseScaledFrameCheck planar_4_13KD planar_4_13HM planar_4_13KU planar_4_13KL planar_4_13KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_13H_kernel_frame : HasKernelFrame planar_4_13H planar_4_13U planar_4_13L planar_4_13HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_13KD≠0) planar_4_13H_kernel_check).scale_matrix
    (by norm_num [planar_4_13HD])

theorem planar_4_13H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_13H.map (Rat.castHom ℂ)).mulVecLin)=0 :=
  kernelFrame_finrank planar_4_13H_kernel_frame.ratCast

theorem planar_4_13_same_kernel (v : Fin 5 → ℂ) :
    (planar_4_13A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_13H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_13A_kernel_frame.ratCast planar_4_13H_kernel_frame.ratCast v

def planar_4_13WS : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 1)]
  | _ => []

def planar_4_13RS : SparseIntMatrix 5 5 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 1)]
  | _ => []

def planar_4_13W : Matrix (Fin 5) (Fin 5) ℚ := sparseRatMatrix planar_4_13WS
def planar_4_13R : Matrix (Fin 5) (Fin 5) ℚ := sparseRatScaledMatrix 1 planar_4_13RS

theorem planar_4_13_complement : HasComplement planar_4_13U planar_4_13L planar_4_13W planar_4_13R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_13A_active_posDef :
    ((planar_4_13W.map (Rat.castHom ℂ))ᴴ * (planar_4_13A.map (Rat.castHom ℂ)) * (planar_4_13W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_13A_kernel_frame.ratCast planar_4_13A_posSemidef _ _
    ((planar_4_13_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_13_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_13H_active_posDef :
    ((planar_4_13W.map (Rat.castHom ℂ))ᴴ * (planar_4_13H.map (Rat.castHom ℂ)) * (planar_4_13W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_13H_kernel_frame.ratCast planar_4_13H_posSemidef _ _
    ((planar_4_13_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_13_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=14, A; dimension=8, rank=7. -/
def planar_4_14AD : ℤ := 37703546755875000000000000000000000
def planar_4_14AS : ℤ := 112249752254809462639615047314524432789647375431652464335987764466800327630961592007218093412442939233872541126500190445004214310240382441187226384047715179127705378548812455609344795009035908155115511605101253994972402094260325427415597985703767396050872059228136181648272480198586645612203944793779574594607750622304592050972097523452221462715861423381207656493115284022993113304272962449209984403019899630773009250318887418917835777396990424882607559559687425830283990388877014204196703839850092414624152803505292271086983472088762268667087379666117782126783681513431397599944450911030576454959093983221346144267825149947646519823561386992889071173951703580661461244812259936417148974947778193713346729274332266490752056638790775951775132553367815184411056896110095513600320892190003980386954539168465367534556005726730420491451259154039128687197767989858260829911194371954455692120551912278982869684721061543669007325099236024014901549849838310387683795140130761535213037427157320445625910976709239144466172017205232813851549358462075674756838308094936656706195166652992386317216250045150300954795571007216690529623910272114651511486595543225510857049201110938545969814417363047591728331185002401085192955309529234396493398761487718621235841247363241871079071021085869561149222250734361407553933585201203173650684664674807120313641064353189470372571981971040611873191658127869320834603421831355407117843522798594808853025625575828860548545907587534023787663895411899907785052388189290156891274067639387948574857656370609082678491890096760029763017625699245149842512900582976298430159928772625761281089189427259034534379794328236730921802884080142397025000000000000000000000000000
def planar_4_14AM : SparseIntMatrix 8 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 19024811474575496071841066408523832111725), (⟨1, by decide⟩, -15325982043675691868329661946622998812925), (⟨2, by decide⟩, 20142456298116104905459751596591377642000), (⟨3, by decide⟩, 12722660072050386342775420176374453677875), (⟨4, by decide⟩, -12580213117776988630978259823161579772900), (⟨5, by decide⟩, 10787628254215163960067952626277777117800), (⟨6, by decide⟩, -10069379433613425995325176950451862215160), (⟨7, by decide⟩, 8625352689748880884635479815967256843360)]
  | 1 => [(⟨0, by decide⟩, -15325982043675691868329661946622998812925), (⟨1, by decide⟩, 14859001699458108411695656637817169483725), (⟨2, by decide⟩, -19760825825055726974835998115381569281200), (⟨3, by decide⟩, -12663314021564340824737113344470359547875), (⟨4, by decide⟩, 12346511543250293933701724436303773118900), (⟨5, by decide⟩, -10586044282010627289486689255835812255400), (⟨6, by decide⟩, 9879327965500638523575565415933914143000), (⟨7, by decide⟩, -8465227176939485882442435368747650450080)]
  | 2 => [(⟨0, by decide⟩, 20142456298116104905459751596591377642000), (⟨1, by decide⟩, -19760825825055726974835998115381569281200), (⟨2, by decide⟩, 26312112172207166923410128274105206510800), (⟨3, by decide⟩, 16887540025831535644574705729363314534800), (⟨4, by decide⟩, -16441263939619391122995498024160788845800), (⟨5, by decide⟩, 14095603651718408769067590837298773420000), (⟨6, by decide⟩, -13154821331761829835617706754452608459600), (⟨7, by decide⟩, 11272309483980145526615069015944240440480)]
  | 3 => [(⟨0, by decide⟩, 12722660072050386342775420176374453677875), (⟨1, by decide⟩, -12663314021564340824737113344470359547875), (⟨2, by decide⟩, 16887540025831535644574705729363314534800), (⟨3, by decide⟩, 10864395990673869902398399486418802958125), (⟨4, by decide⟩, -10558847546388498500582949304948046205900), (⟨5, by decide⟩, 9045833376993226096255567746597191806200), (⟨6, by decide⟩, -8439893205172912886945347495791547445160), (⟨7, by decide⟩, 7241592908837945289179904938557793596800)]
  | 4 => [(⟨0, by decide⟩, -12580213117776988630978259823161579772900), (⟨1, by decide⟩, 12346511543250293933701724436303773118900), (⟨2, by decide⟩, -16441263939619391122995498024160788845800), (⟨3, by decide⟩, -10558847546388498500582949304948046205900), (⟨4, by decide⟩, 10279522220540317325791906295718939992500), (⟨5, by decide⟩, -8806471188327320392142082336310114772400), (⟨6, by decide⟩, 8215851575138717231157922821914654285000), (⟨7, by decide⟩, -7051171540702781414105200935930688087440)]
  | 5 => [(⟨0, by decide⟩, 10787628254215163960067952626277777117800), (⟨1, by decide⟩, -10586044282010627289486689255835812255400), (⟨2, by decide⟩, 14095603651718408769067590837298773420000), (⟨3, by decide⟩, 9045833376993226096255567746597191806200), (⟨4, by decide⟩, -8806471188327320392142082336310114772400), (⟨5, by decide⟩, 7551951227805555425250069214585718872800), (⟨6, by decide⟩, -7048802092620897640863131434541310439200), (⟨7, by decide⟩, 6036448538100703625039575667172073878720)]
  | 6 => [(⟨0, by decide⟩, -10069379433613425995325176950451862215160), (⟨1, by decide⟩, 9879327965500638523575565415933914143000), (⟨2, by decide⟩, -13154821331761829835617706754452608459600), (⟨3, by decide⟩, -8439893205172912886945347495791547445160), (⟨4, by decide⟩, 8215851575138717231157922821914654285000), (⟨5, by decide⟩, -7048802092620897640863131434541310439200), (⟨6, by decide⟩, 6580942145782363967421129816019149375760), (⟨7, by decide⟩, -5629301791100400612046219402496230615200)]
  | 7 => [(⟨0, by decide⟩, 8625352689748880884635479815967256843360), (⟨1, by decide⟩, -8465227176939485882442435368747650450080), (⟨2, by decide⟩, 11272309483980145526615069015944240440480), (⟨3, by decide⟩, 7241592908837945289179904938557793596800), (⟨4, by decide⟩, -7051171540702781414105200935930688087440), (⟨5, by decide⟩, 6036448538100703625039575667172073878720), (⟨6, by decide⟩, -5629301791100400612046219402496230615200), (⟨7, by decide⟩, 4839931195087186180538576203934911045536)]
  | _ => []

def planar_4_14AR : SparseIntMatrix 7 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800), (⟨1, by decide⟩, -306914916484836806203953558047637096917889448877084100644694531356895289359309080491393666704196199132748338440685505874961869844992373757099156334348579268746134931930409694381132131159111326013914926593744448025597806390248300064577106362297829701030930196857366801634620547304246299716888348604942360118468608418607296131360273527029658895568114078602397529469131168356064958957048080528261391209049568273049566176121227533285321023387778096784748870366845332108339579415207709410026564449793915502255563714836548241092109572676799809158587814357400), (⟨2, by decide⟩, 403368624269451427846064734913031755993254073490449606061949988701436336007610500829166731067566490142189300615123867230200858262100535763288897670599213460640722624964992607004560137312017530826648347398264531349068373414356486093351914670288564359179855483313671205532926685696609716891697356817568085155643725417833875378491941472050416176126118070456653636693177432808008879228084485923551439799733983269767401685966533476306223005251739458080271150001574099266096129242915246075593708186653380881864768090378437211436394366399694238231485285296000), (⟨3, by decide⟩, 254781334230365212504137914573862507509901576223613422191035830338187927956727459967413038634246111051836445501599141106404542617816738240850449316049141246865421470813239536946345951961237875006050365052465031174209340028739314634779909095694984424557858956407309564360999072546114453897528201187538194140524034119711071934907552609533265690115040038598646235913601702302090328229991192547502844378780248905038791631139741224027653361733786390726321334354963107728137437980438412651647420730233019440562171450709506747376280408359154556474060891553000), (⟨4, by decide⟩, -251928721265678879109712044909599003549073585400491203029656913906428618659674612853614514478569106134427290156288690384437935562118244499960574687533189992110163966651515098711129411982508362443470090476886729682397816151431837441126576797548900671768391132712183772293442175904612025606454561729017330416457542417970962478879151537547471207961984543534325594901410049263577494604011575609107975553816014214723642434383758125459843839232334743735797831202267357203771809134176476947066201801905765233137281775433844491037876853493940009948226669375200), (⟨5, by decide⟩, 216030791062955617296336343706213791340106702506626270232793977903343929114771565945392398453823962624403075307972777798318778433801204818074818896341437609810141575729503473345906922333269677476744844809106379214589784372476674661843835670063390630633093112725849950526203666624189682232104367887778736236775202220855336898041337146415465480401003538915902345004126528495169489670778490423068977425454417907572858360864869290793554493512802484777539737302243265304382233741534935449230157566129394033291989477840643844509574549806024438635546049886400), (⟨6, by decide⟩, -201647290145226131050511897273309178479415572770591672232882642492847284433315475751481374771668212916374734962035621750558188965643259344398393547649414997975488755065787425688601432746080879926361693786760002503761296492823850370083566049841919203526714601180294840836436527768830803632124749631310895257802796952700821110465781503418796439734944870895796764268672251595185473003869175442704246989778627833464795446039935043978641983165767358759671911603179604347037954829943853009920253359698837301507628235419805921570459097718093835962752485078080), (⟨7, by decide⟩, 172729512071882855040802443097309653568629233763922097980464433505797981582600804751897313195460914430955291145649169792368220793318078511722709310410044500316024759235682191933831834017562636275920413613777644666090306968321965726820157440570106483273633408843704004686100219499311209954745976892871606047245475128081428306789778579993928371687796475364275465886504306473493804206061652633497104563503811746315791344198564250226489475843824692653329405981559785791245391876928595388843487069654469430534249216811113793763892983119564715734574395239680)]
  | 1 => [(⟨1, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800), (⟨2, by decide⟩, -535911984871829379644050410409734443771140229908154493035878688555996941562198702781462568172044680448904291602407993623148879326799260014397515847883935149772597004831482652801196452834201018146723433556625332922667865048416990784269118869447564978009764931927209286823940610851234080058251935069121185373624631366065930657482138490991779846212983573813951340908587184678673710499048068717067481163415271451918549706593882173152560527831085279363357232240003909756213091541399691215338607809143535578333383979475035398249965660280860964495451279228300), (⟨3, by decide⟩, -366050922278508900288198073978866382337547447096300542461087735060018142511387564827566539643978710521022743241596677640103757590053662644884082077154529379887236049830647779882805149320519561173664546126716288457474285406633448164076299799459595307679299662171201734614105422305358458124802062407193734999495242584125300260278846972035289417820072023634108471480617294500045344169811913245870260547951108099796455445485764133384194783449280327260888901116134725096925703706748997212091832616387477626727280937923399413635924067075941183315746781847000), (⟨4, by decide⟩, 335415367806549331460622307211538543434764122755034794312303137269738791652325914998067338446359904706389039221279006992643468141886238948374413773470943615192367360474219194607570863718980906782631730725041961645376114364589097356063315531192565185358002025288351541638462175305285791252785413535801138200953810859843841767810452705269107290506718327966448280335078126107101512588865682768569601714809050706060026966868400979189954413687948299308584384649242670717339536787560783733407953688358038660340908205601537921867431521408546354774252685105550), (⟨5, by decide⟩, -287441838914651559480651904016927682086185522423742956594249328988799299722958582253261416981243071176119327166168085786763233207718636044122983255417167619922279081958582809377225407674317556484126065528386772464522907864135967065393150402139519311393630947576179535378159956196623661841246921512673533630671102089187489309179794642283590631506460737641509972429155162600993051380473437578747764665518582026928018200147475907237482844984876484703888817197559207320682498422162361398280466931296768925243615883051295099687337956219165592594144131205000), (⟨6, by decide⟩, 268017299656962003275346037506992944212394544184255932595299590648353808231286877009124827945198425580316435169443846539872670695283142673427423414852879379031317549746342445483084880585009688911282461014385437091148643644706069591767698361805838645189101427243616711940050115349589508417394786475534446095885089507817307073932479418164604303567876004814764490801843457682793666989770703035217910826181251674366375684132380839663593175118006073287499544583739754641617688331542928265251670963341672680311665013802175935523857628399284992339951463779980), (⟨7, by decide⟩, -229986552388607608818588315378765363912658925102955110691514790396581688840483629421115053529665268773698116651299045927909114012508599342732526984627820372193831034739152881334956040407898090137403351152707497109518296428152228388057967931423112512647344226431948333134822155905058727916659681328484432258898690748802999380576662458974325691042965538392842478910331908686496263740942108043601227683807083490584942645810098773426160300439603861590793416214643278285331670302244643890597698667979854010743436272131433214293485226817416909019244349921400)]
  | 2 => [(⟨2, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800), (⟨3, by decide⟩, 562441614788156107049963049471536555511256557878470508933566131082787297749614954295936967140288128884962509351859455330876146956417706849602537515552946182156609744836445592028129328676438500048778846951458709312203171993080740396817350036818501163917210809341878648389489919840534918485260923927709912588465948832595745246569123351756166877834917891080984998351407488342574732567342718103854733705767597758191662981621901739783779743367879019982128062073663778004023672403677378293925543619888372925230739576806286300012918443057497947531657000709400), (⟨4, by decide⟩, -268681701062205675771848083098760960900224093790219538650959541081488468702463266391140185724403310095654277733342927424877670574355602037743802220780883729194450142630618674572498351236559010140940498359007434287445250836817108346054095174097779885139659674328676631761150371710176330159037385620333513376939381636933659056488734332786676767541934637749705901420834574067583776882641969799527295240186401154991930296399912433162368956243402582916180013025025224373674254477663206255608023845748987243997593603757617581003069323277178846005526029387675), (⟨5, by decide⟩, 197992739984390482237903331283758066474144176045991631008682585484734949274246561128714487802165582454387347379506398851943375012534686435109393610263051137464365068427116622018610809674984839091879589260120118240334912119389702167879934639580448363789950860139643771165338600985069993147986084252640003751050165325938071877330764834243095757253796672732779679578842383900044910557279196412990796246740433409097851183270817060604974120608553816058422044296599482752534651940744543155960773129056042210827334943481250613775981550375133087905689985909500), (⟨6, by decide⟩, -194510179359034903082178110433709780071679829056784599245054944308745020913618798774164214099783096650184335889093867350554261673206424290522971285624588782848747808372218304240301226975713344016969827916693943042559057477018388994239169494291733407885856308695048796183711775379151873431872619952719836671980584723625119927353884018757183342465724416965812725676949714837821983811323299077567707746818532371566440384343221796215619238527982280417836124952516761939354332661077692625605989796792659219985292717654499271484691484854660974904273443694440), (⟨7, by decide⟩, 172721473929993093732862589316754073797781892143635484412334931105595149281792654705472547356397385900293463153914886685090715277468663278556546280282226059105749312505835899357532301207067138281943359802246625825193286411191445912662341399145316658597360302060254123927240431605296180934718143086482387712560943413018796799556177218109476539615426890295858657701696168809060959536921151714953812328237830296711325816480792131148404858174553308841220736474629457978512380378210577642836180235536427243919142852051417495969881865529798486932124652733940)]
  | 3 => [(⟨3, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800), (⟨4, by decide⟩, -415871461459957139733650469888135995021956506432752826765342336291796432413311231695177989510212201540223867056449612245831959099841325751817820466391895811353343261476662929158993689471179632967900176702326985794314512943919250556836799471036012182605795560941434046471182879409688289828551107832366108551038441470859604386599589561894524806485129502975425653970353026695630339630505407683004067119749588094135255298590897121846972660913527628098813871203788449822133631986627923631596845613162318116798986342228837436135849892336712601739530463011800), (⟨5, by decide⟩, -72050428830483693401867161571244543955866682977404140985434109662975376636076352579870959823654968248025570195592048720167252130501834610940080434278551488652424608394084967317716886106128722093481874838907185902536818922802256615628568337762686120460864724972080772921515196333092556830972819418546551773539949064754542130090453856734915135839424322482827240375951497272135461359135148675218046714685263164708089524713946998193790713203104031084854437459468461234840899341764979656809818468698706494548686649832476803153981706466426176162303382893900), (⟨6, by decide⟩, 254231086479652105392102225104598480010825079483224263560677443564258399427280175663936249709828108418373536463932252741265977805797267341176860385272451981076293347233753774440231811836812603276322514501685531580157929082225091702402416027176686377440261248595361052403949174869628782081459216372474772213546891150378879155158244037170371866982785616654299708673142053944417218485431520583650183917896599667029609157173573229142766253877694629477842804877082801545761258952832601989914773299777542677369796591829293493933029985881052365668247414139040), (⟨7, by decide⟩, 495408265130272579637517862489141313616562256602241949649753526357442516850395089955777718275850684124155326043080716926945935106639268480294989508879838011128820204110723537605192574251289120101814188582149084933696891168065157974659806310225859801430013886030894368021534292627615662999957077830338101511810060910318556538964564266542375998358642453621825279090723375152847798509766584301987759632203324185797533921847074887456619045701638228844788660244653295247779743412120499346565423578032573295276338335084682740261008843766545419738314666649780)]
  | 4 => [(⟨4, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800), (⟨5, by decide⟩, 429494519920949563854748890510917573425009310769216729510121290118123112865010029882439941741362775846034312389161579871658148749221900195756716143528426171460338584186694814950847295420982448502813283628371802953310302112682529535332690969977871623712585874013201517918437522418358587828856897345278767332838922907229043993516818664975902993542204811056148523040793471556433072996835949190450959240593887998489133385191592390754092585598511696461135078298377648016888179517521784596610979159501347912065297662094392630509080639332985982929244158682400), (⟨6, by decide⟩, -913033316339595109451849204882663754093928287838610900443118333722610536976071577155134401060657088639910601850720465267782829485623506001022832106369532838224764829114069590948319765053181322484810371377211135096805126764011337458466264848200474612795010150513425592233017848184912544547657299827936269168728919319017988022295337471804461775277838925915427493129099056618258307954868282395458073657112387807347052800091650936487684962033161418988240940051064880885751531252038711947863182119249732045425118321342966224817318370498830964200923915898112), (⟨7, by decide⟩, -1264915648206258544398687578566078061328319858796191826167783462813184586787525151021703618025637768427907703367328615225669261805055196759130938999536503335222749832920836610935889802321765713650417575184052553126166413129600828776153606854935086672012260906245524993455392729130151549784103512497240230079864553022013304596903247481808178343147229278167272990039683170710473162667154711872128463950326388661091380766166400362395275871019395500215949774804534210911603882924338109445606053218085650453774138787144353957867057100456465619268656554403552)]
  | 5 => [(⟨5, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800), (⟨6, by decide⟩, -498549473385591491622347652629403275714610944050654322761991886092617862587025748932495310849818154483979249527777394931548576366940033475901459046410515021435136434784225726645852036468331691494098606968767630594566672375203822317588458816101922308875323473448905781432663949583160441194527092845818068342506532481609650002529355285704910579233076318666267036719110674703313839483559516809606722338754020786147684179854947874556237580011886210643164202234750852340452578476619814619423721538474256280512040879220274116284748658821795726525564678886720), (⟨7, by decide⟩, -269957331953379051649964762133166456481087010018487711475465172407074893513103402008982867596143774998122616171487983226218080778578221897565657829179005196482315876914681760786572631022891493893862916724818443169061372012754193928005850095331421671333522618396398164442624926684565131969366961192141360350941912188859871388510104832333938692735058854084191557693463100818535827542164017188003860149665145666333506180908808551921220157382383298479017996585064882776958106208065139023532674565522983597166466230573515374526553491237760884716085003743640)]
  | 6 => [(⟨6, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800), (⟨7, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800)]
  | _ => []

def planar_4_14AT : SparseIntMatrix 8 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800)]
  | 1 => [(⟨0, by decide⟩, -306914916484836806203953558047637096917889448877084100644694531356895289359309080491393666704196199132748338440685505874961869844992373757099156334348579268746134931930409694381132131159111326013914926593744448025597806390248300064577106362297829701030930196857366801634620547304246299716888348604942360118468608418607296131360273527029658895568114078602397529469131168356064958957048080528261391209049568273049566176121227533285321023387778096784748870366845332108339579415207709410026564449793915502255563714836548241092109572676799809158587814357400), (⟨1, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800)]
  | 2 => [(⟨0, by decide⟩, 403368624269451427846064734913031755993254073490449606061949988701436336007610500829166731067566490142189300615123867230200858262100535763288897670599213460640722624964992607004560137312017530826648347398264531349068373414356486093351914670288564359179855483313671205532926685696609716891697356817568085155643725417833875378491941472050416176126118070456653636693177432808008879228084485923551439799733983269767401685966533476306223005251739458080271150001574099266096129242915246075593708186653380881864768090378437211436394366399694238231485285296000), (⟨1, by decide⟩, -535911984871829379644050410409734443771140229908154493035878688555996941562198702781462568172044680448904291602407993623148879326799260014397515847883935149772597004831482652801196452834201018146723433556625332922667865048416990784269118869447564978009764931927209286823940610851234080058251935069121185373624631366065930657482138490991779846212983573813951340908587184678673710499048068717067481163415271451918549706593882173152560527831085279363357232240003909756213091541399691215338607809143535578333383979475035398249965660280860964495451279228300), (⟨2, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800)]
  | 3 => [(⟨0, by decide⟩, 254781334230365212504137914573862507509901576223613422191035830338187927956727459967413038634246111051836445501599141106404542617816738240850449316049141246865421470813239536946345951961237875006050365052465031174209340028739314634779909095694984424557858956407309564360999072546114453897528201187538194140524034119711071934907552609533265690115040038598646235913601702302090328229991192547502844378780248905038791631139741224027653361733786390726321334354963107728137437980438412651647420730233019440562171450709506747376280408359154556474060891553000), (⟨1, by decide⟩, -366050922278508900288198073978866382337547447096300542461087735060018142511387564827566539643978710521022743241596677640103757590053662644884082077154529379887236049830647779882805149320519561173664546126716288457474285406633448164076299799459595307679299662171201734614105422305358458124802062407193734999495242584125300260278846972035289417820072023634108471480617294500045344169811913245870260547951108099796455445485764133384194783449280327260888901116134725096925703706748997212091832616387477626727280937923399413635924067075941183315746781847000), (⟨2, by decide⟩, 562441614788156107049963049471536555511256557878470508933566131082787297749614954295936967140288128884962509351859455330876146956417706849602537515552946182156609744836445592028129328676438500048778846951458709312203171993080740396817350036818501163917210809341878648389489919840534918485260923927709912588465948832595745246569123351756166877834917891080984998351407488342574732567342718103854733705767597758191662981621901739783779743367879019982128062073663778004023672403677378293925543619888372925230739576806286300012918443057497947531657000709400), (⟨3, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800)]
  | 4 => [(⟨0, by decide⟩, -251928721265678879109712044909599003549073585400491203029656913906428618659674612853614514478569106134427290156288690384437935562118244499960574687533189992110163966651515098711129411982508362443470090476886729682397816151431837441126576797548900671768391132712183772293442175904612025606454561729017330416457542417970962478879151537547471207961984543534325594901410049263577494604011575609107975553816014214723642434383758125459843839232334743735797831202267357203771809134176476947066201801905765233137281775433844491037876853493940009948226669375200), (⟨1, by decide⟩, 335415367806549331460622307211538543434764122755034794312303137269738791652325914998067338446359904706389039221279006992643468141886238948374413773470943615192367360474219194607570863718980906782631730725041961645376114364589097356063315531192565185358002025288351541638462175305285791252785413535801138200953810859843841767810452705269107290506718327966448280335078126107101512588865682768569601714809050706060026966868400979189954413687948299308584384649242670717339536787560783733407953688358038660340908205601537921867431521408546354774252685105550), (⟨2, by decide⟩, -268681701062205675771848083098760960900224093790219538650959541081488468702463266391140185724403310095654277733342927424877670574355602037743802220780883729194450142630618674572498351236559010140940498359007434287445250836817108346054095174097779885139659674328676631761150371710176330159037385620333513376939381636933659056488734332786676767541934637749705901420834574067583776882641969799527295240186401154991930296399912433162368956243402582916180013025025224373674254477663206255608023845748987243997593603757617581003069323277178846005526029387675), (⟨3, by decide⟩, -415871461459957139733650469888135995021956506432752826765342336291796432413311231695177989510212201540223867056449612245831959099841325751817820466391895811353343261476662929158993689471179632967900176702326985794314512943919250556836799471036012182605795560941434046471182879409688289828551107832366108551038441470859604386599589561894524806485129502975425653970353026695630339630505407683004067119749588094135255298590897121846972660913527628098813871203788449822133631986627923631596845613162318116798986342228837436135849892336712601739530463011800), (⟨4, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800)]
  | 5 => [(⟨0, by decide⟩, 216030791062955617296336343706213791340106702506626270232793977903343929114771565945392398453823962624403075307972777798318778433801204818074818896341437609810141575729503473345906922333269677476744844809106379214589784372476674661843835670063390630633093112725849950526203666624189682232104367887778736236775202220855336898041337146415465480401003538915902345004126528495169489670778490423068977425454417907572858360864869290793554493512802484777539737302243265304382233741534935449230157566129394033291989477840643844509574549806024438635546049886400), (⟨1, by decide⟩, -287441838914651559480651904016927682086185522423742956594249328988799299722958582253261416981243071176119327166168085786763233207718636044122983255417167619922279081958582809377225407674317556484126065528386772464522907864135967065393150402139519311393630947576179535378159956196623661841246921512673533630671102089187489309179794642283590631506460737641509972429155162600993051380473437578747764665518582026928018200147475907237482844984876484703888817197559207320682498422162361398280466931296768925243615883051295099687337956219165592594144131205000), (⟨2, by decide⟩, 197992739984390482237903331283758066474144176045991631008682585484734949274246561128714487802165582454387347379506398851943375012534686435109393610263051137464365068427116622018610809674984839091879589260120118240334912119389702167879934639580448363789950860139643771165338600985069993147986084252640003751050165325938071877330764834243095757253796672732779679578842383900044910557279196412990796246740433409097851183270817060604974120608553816058422044296599482752534651940744543155960773129056042210827334943481250613775981550375133087905689985909500), (⟨3, by decide⟩, -72050428830483693401867161571244543955866682977404140985434109662975376636076352579870959823654968248025570195592048720167252130501834610940080434278551488652424608394084967317716886106128722093481874838907185902536818922802256615628568337762686120460864724972080772921515196333092556830972819418546551773539949064754542130090453856734915135839424322482827240375951497272135461359135148675218046714685263164708089524713946998193790713203104031084854437459468461234840899341764979656809818468698706494548686649832476803153981706466426176162303382893900), (⟨4, by decide⟩, 429494519920949563854748890510917573425009310769216729510121290118123112865010029882439941741362775846034312389161579871658148749221900195756716143528426171460338584186694814950847295420982448502813283628371802953310302112682529535332690969977871623712585874013201517918437522418358587828856897345278767332838922907229043993516818664975902993542204811056148523040793471556433072996835949190450959240593887998489133385191592390754092585598511696461135078298377648016888179517521784596610979159501347912065297662094392630509080639332985982929244158682400), (⟨5, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800)]
  | 6 => [(⟨0, by decide⟩, -201647290145226131050511897273309178479415572770591672232882642492847284433315475751481374771668212916374734962035621750558188965643259344398393547649414997975488755065787425688601432746080879926361693786760002503761296492823850370083566049841919203526714601180294840836436527768830803632124749631310895257802796952700821110465781503418796439734944870895796764268672251595185473003869175442704246989778627833464795446039935043978641983165767358759671911603179604347037954829943853009920253359698837301507628235419805921570459097718093835962752485078080), (⟨1, by decide⟩, 268017299656962003275346037506992944212394544184255932595299590648353808231286877009124827945198425580316435169443846539872670695283142673427423414852879379031317549746342445483084880585009688911282461014385437091148643644706069591767698361805838645189101427243616711940050115349589508417394786475534446095885089507817307073932479418164604303567876004814764490801843457682793666989770703035217910826181251674366375684132380839663593175118006073287499544583739754641617688331542928265251670963341672680311665013802175935523857628399284992339951463779980), (⟨2, by decide⟩, -194510179359034903082178110433709780071679829056784599245054944308745020913618798774164214099783096650184335889093867350554261673206424290522971285624588782848747808372218304240301226975713344016969827916693943042559057477018388994239169494291733407885856308695048796183711775379151873431872619952719836671980584723625119927353884018757183342465724416965812725676949714837821983811323299077567707746818532371566440384343221796215619238527982280417836124952516761939354332661077692625605989796792659219985292717654499271484691484854660974904273443694440), (⟨3, by decide⟩, 254231086479652105392102225104598480010825079483224263560677443564258399427280175663936249709828108418373536463932252741265977805797267341176860385272451981076293347233753774440231811836812603276322514501685531580157929082225091702402416027176686377440261248595361052403949174869628782081459216372474772213546891150378879155158244037170371866982785616654299708673142053944417218485431520583650183917896599667029609157173573229142766253877694629477842804877082801545761258952832601989914773299777542677369796591829293493933029985881052365668247414139040), (⟨4, by decide⟩, -913033316339595109451849204882663754093928287838610900443118333722610536976071577155134401060657088639910601850720465267782829485623506001022832106369532838224764829114069590948319765053181322484810371377211135096805126764011337458466264848200474612795010150513425592233017848184912544547657299827936269168728919319017988022295337471804461775277838925915427493129099056618258307954868282395458073657112387807347052800091650936487684962033161418988240940051064880885751531252038711947863182119249732045425118321342966224817318370498830964200923915898112), (⟨5, by decide⟩, -498549473385591491622347652629403275714610944050654322761991886092617862587025748932495310849818154483979249527777394931548576366940033475901459046410515021435136434784225726645852036468331691494098606968767630594566672375203822317588458816101922308875323473448905781432663949583160441194527092845818068342506532481609650002529355285704910579233076318666267036719110674703313839483559516809606722338754020786147684179854947874556237580011886210643164202234750852340452578476619814619423721538474256280512040879220274116284748658821795726525564678886720), (⟨6, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800)]
  | 7 => [(⟨0, by decide⟩, 172729512071882855040802443097309653568629233763922097980464433505797981582600804751897313195460914430955291145649169792368220793318078511722709310410044500316024759235682191933831834017562636275920413613777644666090306968321965726820157440570106483273633408843704004686100219499311209954745976892871606047245475128081428306789778579993928371687796475364275465886504306473493804206061652633497104563503811746315791344198564250226489475843824692653329405981559785791245391876928595388843487069654469430534249216811113793763892983119564715734574395239680), (⟨1, by decide⟩, -229986552388607608818588315378765363912658925102955110691514790396581688840483629421115053529665268773698116651299045927909114012508599342732526984627820372193831034739152881334956040407898090137403351152707497109518296428152228388057967931423112512647344226431948333134822155905058727916659681328484432258898690748802999380576662458974325691042965538392842478910331908686496263740942108043601227683807083490584942645810098773426160300439603861590793416214643278285331670302244643890597698667979854010743436272131433214293485226817416909019244349921400), (⟨2, by decide⟩, 172721473929993093732862589316754073797781892143635484412334931105595149281792654705472547356397385900293463153914886685090715277468663278556546280282226059105749312505835899357532301207067138281943359802246625825193286411191445912662341399145316658597360302060254123927240431605296180934718143086482387712560943413018796799556177218109476539615426890295858657701696168809060959536921151714953812328237830296711325816480792131148404858174553308841220736474629457978512380378210577642836180235536427243919142852051417495969881865529798486932124652733940), (⟨3, by decide⟩, 495408265130272579637517862489141313616562256602241949649753526357442516850395089955777718275850684124155326043080716926945935106639268480294989508879838011128820204110723537605192574251289120101814188582149084933696891168065157974659806310225859801430013886030894368021534292627615662999957077830338101511810060910318556538964564266542375998358642453621825279090723375152847798509766584301987759632203324185797533921847074887456619045701638228844788660244653295247779743412120499346565423578032573295276338335084682740261008843766545419738314666649780), (⟨4, by decide⟩, -1264915648206258544398687578566078061328319858796191826167783462813184586787525151021703618025637768427907703367328615225669261805055196759130938999536503335222749832920836610935889802321765713650417575184052553126166413129600828776153606854935086672012260906245524993455392729130151549784103512497240230079864553022013304596903247481808178343147229278167272990039683170710473162667154711872128463950326388661091380766166400362395275871019395500215949774804534210911603882924338109445606053218085650453774138787144353957867057100456465619268656554403552), (⟨5, by decide⟩, -269957331953379051649964762133166456481087010018487711475465172407074893513103402008982867596143774998122616171487983226218080778578221897565657829179005196482315876914681760786572631022891493893862916724818443169061372012754193928005850095331421671333522618396398164442624926684565131969366961192141360350941912188859871388510104832333938692735058854084191557693463100818535827542164017188003860149665145666333506180908808551921220157382383298479017996585064882776958106208065139023532674565522983597166466230573515374526553491237760884716085003743640), (⟨6, by decide⟩, 380986902387020733287304817493728032055873223386944352144211189475904948456537244872520738756123965809761055593815686175550825980603019297226335362052516374921367596449239943098799009075733662667059483739915312375842167270749380649304347867950834395903001425087512694983398371497658848708600219422794513319274367154582964356698750755618286477496695774303459131709412623141296686568992499369338103648481458533023629998243565537725029037715838186940243676082809949272490787114257792659818411621585454472242624414411264569596991945973391403015799458571800)]
  | _ => []

def planar_4_14Aw : Fin 7 → ℤ := fun i =>
  match i.val with
  | 0 => 14712472415270987717301412573299829310604381422438237255154830136531320399512505345266672414458378801464226414886962406277887223178618513657457314930635451089109773762466506875458541065163595062442926152878694733167190114429384316024885749047968123063169873852865134053491212610276489542311383093869670231440103213840248884844840109725859965905695955905940933415211040374672334132332031432332092535606172376991739179165351901711928198250608296160473616630511778621711396427964047860712325950346590182945587429880929764400484624235682463163336531008933582496749057024385924273974242347975870038578125000000000000000000000
  | 1 => 1943161950344858963380797950012015262251855970627178767984978594206603531747661036992606542512492792871837066582850605596845813359650837813077443367052656796750365702772233722509267024046376698821230049478639602919007062561400340141905715434901016846405619809395187208509248130015474767137892424060197516936422806045949314377602561609944791153758398253769190343908212506820855813721262412857606518520814158159520347354607617607249399710816023150253198478438875326684386182887262183815885767926989297943971115244819916649120479519144775076489902961993150017761759707618086533131543292571664837000000000000000000000000000
  | 2 => 11281850383066288368533950087214224471143966862776524057796682138069977702877648078477503930549135993592315014845190782484702818810343442068685666550227338217983387193029712011349740844279313412574462030642078405152619116713948650999457188608836800755920013600986627705728286153604765002299580320181565149765863269170261697943303108657316779402637396827126531365705134101349922735519364531642499775993456792708314957841382008006164704813210165280795493719649634301349873371420868746976038782023349171402406462971867509659470490629595311011850660765891407916690023619764576430522096421434956000000000000000000000000000
  | 3 => 3773438571273090277986146590804779680802908180137457530322461309421364606630354098534913828862735531204377717627967077389685171929350866774883028247237443504786277758811719395742097234504179186601481409957988764767169277386016074521020808023435211326090247548576047770897675588128132463842046804401056026755489054786619353765743988036857250741887622352367245561646266801091948560755421543350043400425986896259312172570594397047829671735294071408499004244120296753981635028592797758051653876765321925049332761376176342023460848609423900185213694529251242334228127505635440829560908957838991000000000000000000000000000
  | 4 => 151080368727246563900703449772774724529153883829973833658653178630312549482783819414223238833044307850410523842081453776175049237530045491057822841236942729833410576129119679428051082493521163333902420264764455237076242879894634668263028953222934738930517865123950536479456604576128379016257758157499197906350722363346597017025942154876512470775829345869906611200366547862533368483514482546102535294365593641538308437981199555961832824270970363411291209640502800969690027837212262428782242226310938607010743721967359091690640393528050242098763524351376428968482171283788064060938541598579062500000000000000000000000
  | 5 => 307297675797891031643724609157477420306009440349774328179128647427699905429513031855307251975195893376994740000564628796468597679121355171891849747867639923574850783963450032725709915855422636869130778849051123763210729343386913077728560710662961437655108110924190262838523316489394683073377104502110861157945542745390997534092942770859375940836979168852177415073482437232620677609963047918077390174682969559804488334728797653098156915031764179014733536793074508034440263796249567040909829867641605515197815601637081078564383652552260313732046104142762791724026404027048146425555827158493750000000000000000000000000
  | 6 => 132854225541823659079247878082409457911863372236466840492160202441455726896472325315372010423238287647238561668892560601418795379800640381844135870321761660550448086577733741791337730887694392496526496591467341568092573138026150823081193518452846044880240605988739437257432490164285452261431769621170863594412957821805855812771193072010729898337479631764191581494254659148186364688089076333120304051436352268611453341350555923284437686662398441480257117469211070180565628337756449196277366580903758423969805440368038726073513235991953999239624155896712817613176144791482616698134627875849216000000000000000000000000
  | _ => 0

def planar_4_14A : Matrix (Fin 8) (Fin 8) ℚ := sparseRatScaledMatrix planar_4_14AD planar_4_14AM

theorem planar_4_14A_gram_check : SparseGramCheck planar_4_14AS planar_4_14AM planar_4_14AR planar_4_14AT planar_4_14Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_14A_posSemidef : (planar_4_14A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_14A_gram_check

/- N=4, d=14, H; dimension=8, rank=7. -/
def planar_4_14HD : ℤ := 32032
def planar_4_14HS : ℤ := 59926243905799752231826156873637349318498792845220986743910983567530856398368385473838041461766560104052601730258048330028971789935003856548562035175047491818928481624297145886588282069080661064135763771379910496213710221676194966245576783600000
def planar_4_14HM : SparseIntMatrix 8 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 17759720607300), (⟨1, by decide⟩, -2442789978300), (⟨2, by decide⟩, 2042649113400), (⟨3, by decide⟩, -1978724840400), (⟨4, by decide⟩, 1237415725350), (⟨5, by decide⟩, 1039763384100), (⟨6, by decide⟩, -1574986394520), (⟨7, by decide⟩, -1352409549120)]
  | 1 => [(⟨0, by decide⟩, -2442789978300), (⟨1, by decide⟩, 1645173015300), (⟨2, by decide⟩, -1683905070600), (⟨3, by decide⟩, 1405286031600), (⟨4, by decide⟩, -1284723142650), (⟨5, by decide⟩, -1217867967900), (⟨6, by decide⟩, 1999380822120), (⟨7, by decide⟩, 1880198982720)]
  | 2 => [(⟨0, by decide⟩, 2042649113400), (⟨1, by decide⟩, -1683905070600), (⟨2, by decide⟩, 2334457122000), (⟨3, by decide⟩, -1344208932000), (⟨4, by decide⟩, 1758582462900), (⟨5, by decide⟩, 1614425167800), (⟨6, by decide⟩, -2879416618320), (⟨7, by decide⟩, -2729732474880)]
  | 3 => [(⟨0, by decide⟩, -1978724840400), (⟨1, by decide⟩, 1405286031600), (⟨2, by decide⟩, -1344208932000), (⟨3, by decide⟩, 1541677190400), (⟨4, by decide⟩, -1320546547800), (⟨5, by decide⟩, -1252696726800), (⟨6, by decide⟩, 2039456106720), (⟨7, by decide⟩, 1920112456320)]
  | 4 => [(⟨0, by decide⟩, 1237415725350), (⟨1, by decide⟩, -1284723142650), (⟨2, by decide⟩, 1758582462900), (⟨3, by decide⟩, -1320546547800), (⟨4, by decide⟩, 1737922722825), (⟨5, by decide⟩, 1686912441750), (⟨6, by decide⟩, -3028646810340), (⟨7, by decide⟩, -3002769833760)]
  | 5 => [(⟨0, by decide⟩, 1039763384100), (⟨1, by decide⟩, -1217867967900), (⟨2, by decide⟩, 1614425167800), (⟨3, by decide⟩, -1252696726800), (⟨4, by decide⟩, 1686912441750), (⟨5, by decide⟩, 1748412495300), (⟨6, by decide⟩, -3093235352280), (⟨7, by decide⟩, -3093993835200)]
  | 6 => [(⟨0, by decide⟩, -1574986394520), (⟨1, by decide⟩, 1999380822120), (⟨2, by decide⟩, -2879416618320), (⟨3, by decide⟩, 2039456106720), (⟨4, by decide⟩, -3028646810340), (⟨5, by decide⟩, -3093235352280), (⟨6, by decide⟩, 5694620088720), (⟨7, by decide⟩, 5765021870976)]
  | 7 => [(⟨0, by decide⟩, -1352409549120), (⟨1, by decide⟩, 1880198982720), (⟨2, by decide⟩, -2729732474880), (⟨3, by decide⟩, 1920112456320), (⟨4, by decide⟩, -3002769833760), (⟨5, by decide⟩, -3093993835200), (⟨6, by decide⟩, 5765021870976), (⟨7, by decide⟩, 5943411355392)]
  | _ => []

def planar_4_14HR : SparseIntMatrix 7 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100), (⟨1, by decide⟩, -932057044168964690821099189429268607570937413157792390485936160747263266992619100), (⟨2, by decide⟩, 779381572637246956033831120659282824791187589830654628540549753867228395694151800), (⟨3, by decide⟩, -754990990772941967279649715499243782289154385028468170820405280405606637295230800), (⟨4, by decide⟩, 472141303027842224077839357071639197398035281059553995173628035399112220745056950), (⟨5, by decide⟩, 396726200380845036775938004871723717844046128701217491488545962303998060127405700), (⟨6, by decide⟩, -600942846713432534830663117389496398851658696231342339355517792604750887862254040), (⟨7, by decide⟩, -516017692088248838797261639051826884472682907004567827865176198335359838981138240)]
  | 1 => [(⟨1, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100), (⟨2, by decide⟩, -7261652333359509105560668134908147115117892295140552065991646388885321800045679420), (⟨3, by decide⟩, 5865029329010125610595791967569138828108269937816562281307053739381477550360058820), (⟨4, by decide⟩, -5768764406500415032845182768570463825784033192725302356421232222346110639982498030), (⟨5, by decide⟩, -5563438736962269734549945735473628060315736790961513249790248875316554149335632180), (⟨6, by decide⟩, 9227504973996808510729108712842248830403767470735040252248980000757111129601642720), (⟨7, by decide⟩, 8769081058499460893087861842719523820185607496103893521803383342084781007810274120)]
  | 2 => [(⟨2, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100), (⟨3, by decide⟩, 1110134724288940962247116643406259197366191908518029171103721647272953332062545900), (⟨4, by decide⟩, 4796265842846392516038263797612207938763940662495294992085023522285132285523076025), (⟨5, by decide⟩, 3899174660949717799326742038981319553783371214515730783033357002187539567510263900), (⟨6, by decide⟩, -8956028137747602085457509790595312684756768881836144548196000180921895636021302200), (⟨7, by decide⟩, -8624385475371955507076915042866317203932251897094815440362464023507912190170859300)]
  | 3 => [(⟨3, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100), (⟨4, by decide⟩, -5996900058932106647771192326523874684099978695779802764116512443639026356031573600), (⟨5, by decide⟩, -5486875215420320015189451713005059813066411752708719500417479415779926986912319500), (⟨6, by decide⟩, 9398484595504244268110156249652794278544027083477099499224511752440288036818841600), (⟨7, by decide⟩, 8925101621894438008737504700361962237321154720557160425107162773764149320078215560)]
  | 4 => [(⟨4, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100), (⟨5, by decide⟩, 10116187703714651075535577669994589236109703173936238854488095967600679959755471200), (⟨6, by decide⟩, -20099069337260828154265776757363068442585868470881599167082162990708061479551025760), (⟨7, by decide⟩, -24871433416870413327653051345647907937628832525787682728714555392596653014487746400)]
  | 5 => [(⟨5, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100), (⟨6, by decide⟩, -6154773489474502371311823591408225030811835727023347613614120839340132720507559616), (⟨7, by decide⟩, -2088994726285111439296090645052627642046040992297912535742152095921757903961308356)]
  | 6 => [(⟨6, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100), (⟨7, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100)]
  | _ => []

def planar_4_14HT : SparseIntMatrix 8 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100)]
  | 1 => [(⟨0, by decide⟩, -932057044168964690821099189429268607570937413157792390485936160747263266992619100), (⟨1, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100)]
  | 2 => [(⟨0, by decide⟩, 779381572637246956033831120659282824791187589830654628540549753867228395694151800), (⟨1, by decide⟩, -7261652333359509105560668134908147115117892295140552065991646388885321800045679420), (⟨2, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100)]
  | 3 => [(⟨0, by decide⟩, -754990990772941967279649715499243782289154385028468170820405280405606637295230800), (⟨1, by decide⟩, 5865029329010125610595791967569138828108269937816562281307053739381477550360058820), (⟨2, by decide⟩, 1110134724288940962247116643406259197366191908518029171103721647272953332062545900), (⟨3, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100)]
  | 4 => [(⟨0, by decide⟩, 472141303027842224077839357071639197398035281059553995173628035399112220745056950), (⟨1, by decide⟩, -5768764406500415032845182768570463825784033192725302356421232222346110639982498030), (⟨2, by decide⟩, 4796265842846392516038263797612207938763940662495294992085023522285132285523076025), (⟨3, by decide⟩, -5996900058932106647771192326523874684099978695779802764116512443639026356031573600), (⟨4, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100)]
  | 5 => [(⟨0, by decide⟩, 396726200380845036775938004871723717844046128701217491488545962303998060127405700), (⟨1, by decide⟩, -5563438736962269734549945735473628060315736790961513249790248875316554149335632180), (⟨2, by decide⟩, 3899174660949717799326742038981319553783371214515730783033357002187539567510263900), (⟨3, by decide⟩, -5486875215420320015189451713005059813066411752708719500417479415779926986912319500), (⟨4, by decide⟩, 10116187703714651075535577669994589236109703173936238854488095967600679959755471200), (⟨5, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100)]
  | 6 => [(⟨0, by decide⟩, -600942846713432534830663117389496398851658696231342339355517792604750887862254040), (⟨1, by decide⟩, 9227504973996808510729108712842248830403767470735040252248980000757111129601642720), (⟨2, by decide⟩, -8956028137747602085457509790595312684756768881836144548196000180921895636021302200), (⟨3, by decide⟩, 9398484595504244268110156249652794278544027083477099499224511752440288036818841600), (⟨4, by decide⟩, -20099069337260828154265776757363068442585868470881599167082162990708061479551025760), (⟨5, by decide⟩, -6154773489474502371311823591408225030811835727023347613614120839340132720507559616), (⟨6, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100)]
  | 7 => [(⟨0, by decide⟩, -516017692088248838797261639051826884472682907004567827865176198335359838981138240), (⟨1, by decide⟩, 8769081058499460893087861842719523820185607496103893521803383342084781007810274120), (⟨2, by decide⟩, -8624385475371955507076915042866317203932251897094815440362464023507912190170859300), (⟨3, by decide⟩, 8925101621894438008737504700361962237321154720557160425107162773764149320078215560), (⟨4, by decide⟩, -24871433416870413327653051345647907937628832525787682728714555392596653014487746400), (⟨5, by decide⟩, -2088994726285111439296090645052627642046040992297912535742152095921757903961308356), (⟨6, by decide⟩, 6776297938648984886692888243925995647942991224542391796453281239030624694243752100)]
  | _ => []

def planar_4_14Hw : Fin 7 → ℤ := fun i =>
  match i.val with
  | 0 => 23177586012577415469252403816238657504359442109324614848869977427299120177125767943338584508000
  | 1 => 1708558781818962180505248490215830514752645437783482006864915325531307026424214992798756160000
  | 2 => 777933704611709343360341469459181247764558285122762441679994238574504392121194034498722201600
  | 3 => 423464494446158361345873695189888391362144929202361651578583627091774058758953023827083264000
  | 4 => 195941567356527033459869779490094324407125498132866748215259563633261103241837544342552576000
  | 5 => 78760797749260764727884356360741164467569864293611521055536504007090675944467186612961280000
  | 6 => 119046000974205795145527228909925491507656044479882419658990841775056629562836662621634035712
  | _ => 0

def planar_4_14H : Matrix (Fin 8) (Fin 8) ℚ := sparseRatScaledMatrix planar_4_14HD planar_4_14HM

theorem planar_4_14H_gram_check : SparseGramCheck planar_4_14HS planar_4_14HM planar_4_14HR planar_4_14HT planar_4_14Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_14H_posSemidef : (planar_4_14H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_14H_gram_check

def planar_4_14KD : ℤ := 143329945047146887388180544825046161980713517030544444660737612514382198444881155850621151664539466258004349676621874928439005138580304769750925350670864264134301033495362599530259425323426775040000
def planar_4_14KU : SparseIntMatrix 8 1 := fun i =>
  match i.val with
  | 1 => [(⟨0, by decide⟩, -143329945047146887388180544825046161980713517030544444660737612514382198444881155850621151664539466258004349676621874928439005138580304769750925350670864264134301033495362599530259425323426775040000)]
  | 2 => [(⟨0, by decide⟩, -143329945047146887388180544825046161980713517030544444660737612514382198444881155850621151664539466258004349676621874928439005138580304769750925350670864264134301033495362599530259425323426775040000)]
  | 3 => [(⟨0, by decide⟩, 143329945047146887388180544825046161980713517030544444660737612514382198444881155850621151664539466258004349676621874928439005138580304769750925350670864264134301033495362599530259425323426775040000)]
  | 4 => [(⟨0, by decide⟩, 229327912075435019821088871720073859169141627248871111457180180023011517511809849360993842663263146012806959482594999885502408221728487631601480561073382822614881653592580159248415080517482840064000)]
  | 5 => [(⟨0, by decide⟩, -85997967028288132432908326895027697188428110218326666796442567508629319066928693510372690998723679754802609805973124957063403083148182861850555210402518558480580620097217559718155655194056065024000)]
  | 6 => [(⟨0, by decide⟩, -143329945047146887388180544825046161980713517030544444660737612514382198444881155850621151664539466258004349676621874928439005138580304769750925350670864264134301033495362599530259425323426775040000)]
  | 7 => [(⟨0, by decide⟩, 143329945047146887388180544825046161980713517030544444660737612514382198444881155850621151664539466258004349676621874928439005138580304769750925350670864264134301033495362599530259425323426775040000)]
  | _ => []

def planar_4_14KL : SparseIntMatrix 1 8 := fun i =>
  match i.val with
  | 0 => [(⟨7, by decide⟩, 1)]
  | _ => []

def planar_4_14KVA : SparseIntMatrix 8 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 119686798508911663224164507821276479667911787876775443060010495510321662127261770856770920669861144426446183019102093693344980133448647149191745228330604953600), (⟨1, by decide⟩, 318366604489621779196813409717189901517767159094502859326817078576184238380304944590332739672116329843078941959036292033126992411385537578977281369374824857600), (⟨2, by decide⟩, -110930467175735630474662518781331785637583646584832230788457105467857628568230673841417823600413215011840899535356652489524918496016306896746872522286552842240), (⟨3, by decide⟩, 1106882488170261833575482024476218065339081490917152031576312853276388921550503673542275194553057024479333610465163209884288303356813434176686561156708643635200), (⟨4, by decide⟩, 2548457517810757924649769219903261702599490324925647262254131849272028465104705888758344377632085916475789638015491120526750784952845115108956338422918215106560), (⟨5, by decide⟩, 5822315597516043934385012211745307448806786202765255269840899608380417631071585709875250196008548766002605097727031072374931703546680678139695016109243503738880), (⟨6, by decide⟩, 3957674187385930108682224712496850893360029031698507850189002109007477795120159275427248934090766435434700042118800005787992573363254650410065140169666723840000)]
  | 1 => [(⟨0, by decide⟩, 318366604489621779196813409717189901517767159094502859326817078576184238380304944590332739672116329843078941959036292033126992411385537578977281369374824857600), (⟨1, by decide⟩, 1572259875132359829306727604220425371593775702131985680117307094237119420758648946543062871083493116739842292796678558477973201869798482898807243402940559183052800), (⟨2, by decide⟩, 1045116076554189013965186463412810734780679996244308093471235955187120145220410019126208287580944157261576702129073105798096539373610572111992272093892513240186880), (⟨3, by decide⟩, -1563894342622768867069907549068867332147346674367219235066611046536874701572851884234007296202372300849541599139672562099619609826006603472188176411493758350131200), (⟨4, by decide⟩, -1631105069580064684260124765264972864151255814799927675393884377179385892379671560489821411782062737680209076968244832701667008347510495229917643677493557219819520), (⟨5, by decide⟩, -169654810306410675175844343061274613832313364755117579311374329260801357669767720285104882523996412526948434421397206640504206631559224193672297774821709247938560), (⟨6, by decide⟩, -421732503110011407480308161386149270170879809560252338598620001311827634652739702683018817443665505769022815114324180393437010712219163286963942376444734210048000)]
  | 2 => [(⟨0, by decide⟩, -110930467175735630474662518781331785637583646584832230788457105467857628568230673841417823600413215011840899535356652489524918496016306896746872522286552842240), (⟨1, by decide⟩, 1045116076554189013965186463412810734780679996244308093471235955187120145220410019126208287580944157261576702129073105798096539373610572111992272093892513240186880), (⟨2, by decide⟩, 817680911036293375846296097447210330095138674167408187319658046054127621562336596217415051319978518864409107840348219448857141343634128300657957410719137859108864), (⟨3, by decide⟩, -1040770602710155488231101433178110398231074329652036820574140047687134880529511760462672260692551677499620318582777510125462476100182352912264849183996150798090240), (⟨4, by decide⟩, -1051083825802923804784506261696837177830572091301898439231065921424316727881686004445525898749506666433356414157006705671342622424345487968170662509058357037367296), (⟨5, by decide⟩, -339592130679715268726584609057275952902858047004196238218873972188982419059233970677030071813345676518776047411873381273686400973883786284723793376104870448201728), (⟨6, by decide⟩, -320907994464559219144502884903254081672497798087603853517863437538349150090515200566903788127254226438431804109956767012383023518857417351794766409826106867712000)]
  | 3 => [(⟨0, by decide⟩, 1106882488170261833575482024476218065339081490917152031576312853276388921550503673542275194553057024479333610465163209884288303356813434176686561156708643635200), (⟨1, by decide⟩, -1563894342622768867069907549068867332147346674367219235066611046536874701572851884234007296202372300849541599139672562099619609826006603472188176411493758350131200), (⟨2, by decide⟩, -1040770602710155488231101433178110398231074329652036820574140047687134880529511760462672260692551677499620318582777510125462476100182352912264849183996150798090240), (⟨3, by decide⟩, 1581087112338617572201099340459085625708710277053022548161045885743669305245400603842616901213821434443957776797916249014738969916001277109289348246491339790745600), (⟨4, by decide⟩, 1674618740081338365384271280563160171754543949449885078386888422632559403820400641976420579381416189374133687256982011017602056759384683630275942319733105397596160), (⟨5, by decide⟩, 263960596015113520627054728446441678237621665716153346835144046121588901946301048845166456175263247207065198502843813744803575391568975711653192044946540021678080), (⟨6, by decide⟩, 488776941201702185677819145513504156265168970454853556562747591103758523027095610192189213701616223101132823467028974285217599987654980835414388273214270734336000)]
  | 4 => [(⟨0, by decide⟩, 2548457517810757924649769219903261702599490324925647262254131849272028465104705888758344377632085916475789638015491120526750784952845115108956338422918215106560), (⟨1, by decide⟩, -1631105069580064684260124765264972864151255814799927675393884377179385892379671560489821411782062737680209076968244832701667008347510495229917643677493557219819520), (⟨2, by decide⟩, -1051083825802923804784506261696837177830572091301898439231065921424316727881686004445525898749506666433356414157006705671342622424345487968170662509058357037367296), (⟨3, by decide⟩, 1674618740081338365384271280563160171754543949449885078386888422632559403820400641976420579381416189374133687256982011017602056759384683630275942319733105397596160), (⟨4, by decide⟩, 1900227592128208940993428070474691118247141334766890564857428412085784736725397799185404752791501875861645321482074686248570608037046185993278642490530945610809344), (⟨5, by decide⟩, 599225726970540895688745101915622168459120507913877547905584235538690575916060287985994061925751160613947689758894827100075745017849835651318969748215083451809792), (⟨6, by decide⟩, 768659303952490890471843566232534306626197265649591216493524158058156259493079371378999109488551079782604467093496422992754874809916471805464220921976403787776000)]
  | 5 => [(⟨0, by decide⟩, 5822315597516043934385012211745307448806786202765255269840899608380417631071585709875250196008548766002605097727031072374931703546680678139695016109243503738880), (⟨1, by decide⟩, -169654810306410675175844343061274613832313364755117579311374329260801357669767720285104882523996412526948434421397206640504206631559224193672297774821709247938560), (⟨2, by decide⟩, -339592130679715268726584609057275952902858047004196238218873972188982419059233970677030071813345676518776047411873381273686400973883786284723793376104870448201728), (⟨3, by decide⟩, 263960596015113520627054728446441678237621665716153346835144046121588901946301048845166456175263247207065198502843813744803575391568975711653192044946540021678080), (⟨4, by decide⟩, 599225726970540895688745101915622168459120507913877547905584235538690575916060287985994061925751160613947689758894827100075745017849835651318969748215083451809792), (⟨5, by decide⟩, 1789338963368720087868457252877539646666786682870813445324111365271761229428672541201422199555316387016022897459333250420427989727042303591313002005421389990854656), (⟨6, by decide⟩, 1091754719962771248356745579077267228905981524198259373535282743953613406266243437486915435268664338302484304492299213523581967602905575020892565294990869135360000)]
  | 6 => [(⟨0, by decide⟩, 3957674187385930108682224712496850893360029031698507850189002109007477795120159275427248934090766435434700042118800005787992573363254650410065140169666723840000), (⟨1, by decide⟩, -421732503110011407480308161386149270170879809560252338598620001311827634652739702683018817443665505769022815114324180393437010712219163286963942376444734210048000), (⟨2, by decide⟩, -320907994464559219144502884903254081672497798087603853517863437538349150090515200566903788127254226438431804109956767012383023518857417351794766409826106867712000), (⟨3, by decide⟩, 488776941201702185677819145513504156265168970454853556562747591103758523027095610192189213701616223101132823467028974285217599987654980835414388273214270734336000), (⟨4, by decide⟩, 768659303952490890471843566232534306626197265649591216493524158058156259493079371378999109488551079782604467093496422992754874809916471805464220921976403787776000), (⟨5, by decide⟩, 1091754719962771248356745579077267228905981524198259373535282743953613406266243437486915435268664338302484304492299213523581967602905575020892565294990869135360000), (⟨6, by decide⟩, 834308872297861365892740222320283303370151758993402824084238328239641143116446765347727148829353515930180212606280007748651276108154651481239394163934783078400000)]
  | _ => []

def planar_4_14KVH : SparseIntMatrix 8 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 10768370812775202086541255184469505275460704238963691143559536986874480612096106167106850708905894307464656902084885211478332899173788680002991791333731732728345621564744049816044205300), (⟨1, by decide⟩, 23282488036048285999634482333536708626085886876728197229329480713269639707986576791167648705022095353860064284991941733461249336775180912019348736940482460877424598541370922492091009400), (⟨2, by decide⟩, 1396887285199615309310116663143212655553560506104645424430842097174609087822972498278196937319341871195655630936302250219866431351553741646395266379242438506930234943513348702987143600), (⟨3, by decide⟩, 5678184624689050513059151515079503348174996924624572515989378645309967065414460926328873227292438296549007704298835704224365947571196336716065480334709319435626869424740452085696037600), (⟨4, by decide⟩, 7337191711813922576813828722893724420045325873544292435615945103830079507041874294721986352603826649430061090991064446740872356096110906110958880168292142891409503263161139969113907600), (⟨5, by decide⟩, 22444954080834268469331302637496312150669249195607341818106224986889845249516960329930992569603034800246813889869708252083559084074821506326648516161605197714171957492712591565659373600), (⟨6, by decide⟩, 9570537889209451936026980730627529808892075595648583303777777387247467351559542452730655108707325041968386180444433968016483143405178369556477387587124396515220473154693943901451793750)]
  | 1 => [(⟨0, by decide⟩, 23282488036048285999634482333536708626085886876728197229329480713269639707986576791167648705022095353860064284991941733461249336775180912019348736940482460877424598541370922492091009400), (⟨1, by decide⟩, 2641068921777174816935876304604300689743820290779226778326165236516594739698057230067937233814922716935251327143321770334660023253617944270023059762487531756489575186078821998955108094800), (⟨2, by decide⟩, 2115486639429878521254039590239106351304006602883996499051910189998349340306361685355776330407155882800760582455325846184886638736361658360173687006585010577109599506314522362261718324000), (⟨3, by decide⟩, -2391520468393491292550510834111252263946529322016331469077856319603819618375753362279946280585654433214449312883953818708332543384503307075501875696641895281834521575862899260209567044800), (⟨4, by decide⟩, -3963405605357773245535252532804963586832873790585837018440726503900463210297042849135279487982953869011417279180614483058440513697284422948805970417876129072301915145447761362554879824800), (⟨5, by decide⟩, 827921868397480992867371684039390494930736261381907987108001324544861944221228048677498520520381015186433014512579263781956967426722016611336163076796093115178118047400050705931353732800), (⟨6, by decide⟩, -652872893321519648956985510227150193679425256627566294757418256544016000324487106892650360018128853643652230130387703768639352925716775212585349771126048142364768184107394083377975457500)]
  | 2 => [(⟨0, by decide⟩, 1396887285199615309310116663143212655553560506104645424430842097174609087822972498278196937319341871195655630936302250219866431351553741646395266379242438506930234943513348702987143600), (⟨1, by decide⟩, 2115486639429878521254039590239106351304006602883996499051910189998349340306361685355776330407155882800760582455325846184886638736361658360173687006585010577109599506314522362261718324000), (⟨2, by decide⟩, 2047967938140587284572950117410978785029492863584095779640712048180089383949690575349417100113872347912898125317573113049171072254627180916786296611096894621236807487385557842920848110400), (⟨3, by decide⟩, -2047104098310165357552838690628380045116362354419190330895535031022066206244146869814523890737157132551949667505961104493265958402218344958420265200257226838561001193025120208474884425600), (⟨4, by decide⟩, -3999790069910662936903182853168223413760186693593987928133231988751083633269317647193977155523818288937949384662179291339285912853955191802787706247894222921289054561978114240560774875200), (⟨5, by decide⟩, 674993749762919855230167986772486149788621560113877291430041630723305826123989653500161356297401202826384534318507300781044667384837145127944394039313745442779594647111450216310507363200), (⟨6, by decide⟩, -734301553287516626940529230994682583581929688053376366191277593511237399907272726721755012445126082116056045296612358758803364752955438453829831269264634447998416864186839103583365951000)]
  | 3 => [(⟨0, by decide⟩, 5678184624689050513059151515079503348174996924624572515989378645309967065414460926328873227292438296549007704298835704224365947571196336716065480334709319435626869424740452085696037600), (⟨1, by decide⟩, -2391520468393491292550510834111252263946529322016331469077856319603819618375753362279946280585654433214449312883953818708332543384503307075501875696641895281834521575862899260209567044800), (⟨2, by decide⟩, -2047104098310165357552838690628380045116362354419190330895535031022066206244146869814523890737157132551949667505961104493265958402218344958420265200257226838561001193025120208474884425600), (⟨3, by decide⟩, 2750568501994565107762730871146320223030033850278983244591143449933915127943402517223118897652635632532038841542308457777958268514481057783535135207553738947155280705974623983221024236800), (⟨4, by decide⟩, 4614967711969137100591618912722044838930474601614766502644219169308311177453026820142471461246913318066504966311851694497533029882148531794206906473575312867777173335008701897675505571200), (⟨5, by decide⟩, -110890426645258397460037204751717272963883344368500972639782577457716185318959287710587107444454554324535622619294684688428668190150526727831824289787642218860820420551043743050659257600), (⟨6, by decide⟩, 1215264737633710163857379831550886557319161660696091797645904850821969825314456058966707798192561811564095071322853611048877227077391951352722055640034520474295756262906078975984729066000)]
  | 4 => [(⟨0, by decide⟩, 7337191711813922576813828722893724420045325873544292435615945103830079507041874294721986352603826649430061090991064446740872356096110906110958880168292142891409503263161139969113907600), (⟨1, by decide⟩, -3963405605357773245535252532804963586832873790585837018440726503900463210297042849135279487982953869011417279180614483058440513697284422948805970417876129072301915145447761362554879824800), (⟨2, by decide⟩, -3999790069910662936903182853168223413760186693593987928133231988751083633269317647193977155523818288937949384662179291339285912853955191802787706247894222921289054561978114240560774875200), (⟨3, by decide⟩, 4614967711969137100591618912722044838930474601614766502644219169308311177453026820142471461246913318066504966311851694497533029882148531794206906473575312867777173335008701897675505571200), (⟨4, by decide⟩, 10321310934848382911226816307215855045346088423645426084515225606427422181205447370584037559163880619965950382285590773567332037576480639236504371853169271462177260378253410598546892411200), (⟨5, by decide⟩, -1247623809870533219354862645823069692138237348586003197799824643390928769428536693164510834343089618176699597040078664214344086058883622567808262911041869616251160350213768863931640969600), (⟨6, by decide⟩, 2529973588585549122375708164018091516514877971988046962729084720610929932554351910827190269386987752476541534426018653268855285694885998367785102986647083551000192670640745736560845211000)]
  | 5 => [(⟨0, by decide⟩, 22444954080834268469331302637496312150669249195607341818106224986889845249516960329930992569603034800246813889869708252083559084074821506326648516161605197714171957492712591565659373600), (⟨1, by decide⟩, 827921868397480992867371684039390494930736261381907987108001324544861944221228048677498520520381015186433014512579263781956967426722016611336163076796093115178118047400050705931353732800), (⟨2, by decide⟩, 674993749762919855230167986772486149788621560113877291430041630723305826123989653500161356297401202826384534318507300781044667384837145127944394039313745442779594647111450216310507363200), (⟨3, by decide⟩, -110890426645258397460037204751717272963883344368500972639782577457716185318959287710587107444454554324535622619294684688428668190150526727831824289787642218860820420551043743050659257600), (⟨4, by decide⟩, -1247623809870533219354862645823069692138237348586003197799824643390928769428536693164510834343089618176699597040078664214344086058883622567808262911041869616251160350213768863931640969600), (⟨5, by decide⟩, 3671237921097745851761112421944545720726398339378286980580707770169771515081388609227544946903473195913027770886267547761349340872840251043065663453238278308113516848356643258182618502400), (⟨6, by decide⟩, 1427163655314505929317726792108008950480149938579043460994804631039073713405778347505868915537300162217428154021037130220234750545140737388558318469392835340823297951950458525047462822000)]
  | 6 => [(⟨0, by decide⟩, 9570537889209451936026980730627529808892075595648583303777777387247467351559542452730655108707325041968386180444433968016483143405178369556477387587124396515220473154693943901451793750), (⟨1, by decide⟩, -652872893321519648956985510227150193679425256627566294757418256544016000324487106892650360018128853643652230130387703768639352925716775212585349771126048142364768184107394083377975457500), (⟨2, by decide⟩, -734301553287516626940529230994682583581929688053376366191277593511237399907272726721755012445126082116056045296612358758803364752955438453829831269264634447998416864186839103583365951000), (⟨3, by decide⟩, 1215264737633710163857379831550886557319161660696091797645904850821969825314456058966707798192561811564095071322853611048877227077391951352722055640034520474295756262906078975984729066000), (⟨4, by decide⟩, 2529973588585549122375708164018091516514877971988046962729084720610929932554351910827190269386987752476541534426018653268855285694885998367785102986647083551000192670640745736560845211000), (⟨5, by decide⟩, 1427163655314505929317726792108008950480149938579043460994804631039073713405778347505868915537300162217428154021037130220234750545140737388558318469392835340823297951950458525047462822000), (⟨6, by decide⟩, 1571282217316520935469992459757953501685868780880033994875425251619451620276700959705212182545982639437516949095967222408585157288390501502023704392298169653278843228436042548340913278125)]
  | _ => []

def planar_4_14U : Matrix (Fin 8) (Fin 1) ℚ := sparseRatScaledMatrix planar_4_14KD planar_4_14KU
def planar_4_14L : Matrix (Fin 1) (Fin 8) ℚ := sparseRatMatrix planar_4_14KL

def planar_4_14AV : Matrix (Fin 8) (Fin 8) ℚ :=
  ((planar_4_14AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_14KD planar_4_14KVA

theorem planar_4_14A_kernel_check : SparseScaledFrameCheck planar_4_14KD planar_4_14AM planar_4_14KU planar_4_14KL planar_4_14KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_14A_kernel_frame : HasKernelFrame planar_4_14A planar_4_14U planar_4_14L planar_4_14AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_14KD≠0) planar_4_14A_kernel_check).scale_matrix
    (by norm_num [planar_4_14AD])

theorem planar_4_14A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_14A.map (Rat.castHom ℂ)).mulVecLin)=1 :=
  kernelFrame_finrank planar_4_14A_kernel_frame.ratCast

def planar_4_14HV : Matrix (Fin 8) (Fin 8) ℚ :=
  ((planar_4_14HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_14KD planar_4_14KVH

theorem planar_4_14H_kernel_check : SparseScaledFrameCheck planar_4_14KD planar_4_14HM planar_4_14KU planar_4_14KL planar_4_14KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_14H_kernel_frame : HasKernelFrame planar_4_14H planar_4_14U planar_4_14L planar_4_14HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_14KD≠0) planar_4_14H_kernel_check).scale_matrix
    (by norm_num [planar_4_14HD])

theorem planar_4_14H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_14H.map (Rat.castHom ℂ)).mulVecLin)=1 :=
  kernelFrame_finrank planar_4_14H_kernel_frame.ratCast

theorem planar_4_14_same_kernel (v : Fin 8 → ℂ) :
    (planar_4_14A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_14H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_14A_kernel_frame.ratCast planar_4_14H_kernel_frame.ratCast v

def planar_4_14WS : SparseIntMatrix 8 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 1)]
  | 5 => [(⟨5, by decide⟩, 1)]
  | 6 => [(⟨6, by decide⟩, 1)]
  | _ => []

def planar_4_14RS : SparseIntMatrix 7 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 5)]
  | 1 => [(⟨1, by decide⟩, 5), (⟨7, by decide⟩, 5)]
  | 2 => [(⟨2, by decide⟩, 5), (⟨7, by decide⟩, 5)]
  | 3 => [(⟨3, by decide⟩, 5), (⟨7, by decide⟩, -5)]
  | 4 => [(⟨4, by decide⟩, 5), (⟨7, by decide⟩, -8)]
  | 5 => [(⟨5, by decide⟩, 5), (⟨7, by decide⟩, 3)]
  | 6 => [(⟨6, by decide⟩, 5), (⟨7, by decide⟩, 5)]
  | _ => []

def planar_4_14W : Matrix (Fin 8) (Fin 7) ℚ := sparseRatMatrix planar_4_14WS
def planar_4_14R : Matrix (Fin 7) (Fin 8) ℚ := sparseRatScaledMatrix 5 planar_4_14RS

theorem planar_4_14_complement : HasComplement planar_4_14U planar_4_14L planar_4_14W planar_4_14R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_14A_active_posDef :
    ((planar_4_14W.map (Rat.castHom ℂ))ᴴ * (planar_4_14A.map (Rat.castHom ℂ)) * (planar_4_14W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_14A_kernel_frame.ratCast planar_4_14A_posSemidef _ _
    ((planar_4_14_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_14_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_14H_active_posDef :
    ((planar_4_14W.map (Rat.castHom ℂ))ᴴ * (planar_4_14H.map (Rat.castHom ℂ)) * (planar_4_14W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_14H_kernel_frame.ratCast planar_4_14H_posSemidef _ _
    ((planar_4_14_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_14_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=15, A; dimension=7, rank=6. -/
def planar_4_15AD : ℤ := 25025000000000000000000000
def planar_4_15AS : ℤ := 136941488659994787870142696935506472770799401268130013001194814918395271761631189791513509873376360745487041093511678330066088592257264111478590721127290089851479816836338649978241822418291796874680339870554746684588060614688981664001878298016680396425900192668584785610006064793990664011498367849859059214750470257814161820795053949323031511511575680747317884990147660120286664143772768873887420028198679507625162187883930403736252396779233056277240689393711978304974799152882451928465113502922804034127486057769669641097196112029189546073617528011310256491154453762230344743178339062231865002435063086452602970639701131947281182993946249613465739852878694094434827268043013229714968942146651894291538231962318397243268558293271451822581113195556615883198174908703988958788381544189192791236171206124305741311507721584019529417120444646493543841294729923696713155150507806813324417911989802222433472898074756504695041304369873331244034066486859721359312958793958358644261853603857197789450000000000000000000000000
def planar_4_15AM : SparseIntMatrix 7 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 252555329330990005033862428455), (⟨1, by decide⟩, -4527280830296362179131322120), (⟨2, by decide⟩, 6602727844359448254687565800), (⟨3, by decide⟩, -4544194264174088777880222120), (⟨4, by decide⟩, 5314229752308393577440172680), (⟨5, by decide⟩, 5241874070998453772876116320), (⟨6, by decide⟩, -9142628969993059708430756976)]
  | 1 => [(⟨0, by decide⟩, -4527280830296362179131322120), (⟨1, by decide⟩, 6805976385568510702405463040), (⟨2, by decide⟩, -9677338139174777025380748000), (⟨3, by decide⟩, 5445880727510665232285051520), (⟨4, by decide⟩, -7392641721970898824724740320), (⟨5, by decide⟩, -6504908973095949304676597280), (⟨6, by decide⟩, 12274162350719024258846505792)]
  | 2 => [(⟨0, by decide⟩, 6602727844359448254687565800), (⟨1, by decide⟩, -9677338139174777025380748000), (⟨2, by decide⟩, 14652579758895273409681950000), (⟨3, by decide⟩, -7563361160720224628137548000), (⟨4, by decide⟩, 11323841520306695980559785200), (⟨5, by decide⟩, 9953294905264567785616684800), (⟨6, by decide⟩, -18989200695760080220274444640)]
  | 3 => [(⟨0, by decide⟩, -4544194264174088777880222120), (⟨1, by decide⟩, 5445880727510665232285051520), (⟨2, by decide⟩, -7563361160720224628137548000), (⟨3, by decide⟩, 5454929805820259372022366720), (⟨4, by decide⟩, -7059432695671386220561187040), (⟨5, by decide⟩, -6758968787607690726253644960), (⟨6, by decide⟩, 12881154837307633051575670848)]
  | 4 => [(⟨0, by decide⟩, 5314229752308393577440172680), (⟨1, by decide⟩, -7392641721970898824724740320), (⟨2, by decide⟩, 11323841520306695980559785200), (⟨3, by decide⟩, -7059432695671386220561187040), (⟨4, by decide⟩, 10897066091636090201305134000), (⟨5, by decide⟩, 10461370673828646741577363200), (⟨6, by decide⟩, -20788180388683027965837941472)]
  | 5 => [(⟨0, by decide⟩, 5241874070998453772876116320), (⟨1, by decide⟩, -6504908973095949304676597280), (⟨2, by decide⟩, 9953294905264567785616684800), (⟨3, by decide⟩, -6758968787607690726253644960), (⟨4, by decide⟩, 10461370673828646741577363200), (⟨5, by decide⟩, 10754578110495612183563049600), (⟨6, by decide⟩, -21778831223905651509673185408)]
  | 6 => [(⟨0, by decide⟩, -9142628969993059708430756976), (⟨1, by decide⟩, 12274162350719024258846505792), (⟨2, by decide⟩, -18989200695760080220274444640), (⟨3, by decide⟩, 12881154837307633051575670848), (⟨4, by decide⟩, -20788180388683027965837941472), (⟨5, by decide⟩, -21778831223905651509673185408), (⟨6, by decide⟩, 44903112993599247872623134144)]
  | _ => []

def planar_4_15AR : SparseIntMatrix 6 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300), (⟨1, by decide⟩, -255074675205064305429102628254703359381433534217455557522460119098423938472219050290571268431579699106712802501445538420064361414646824718722249204563741035061024226421497273420490008097741572658458631795996451481152029672354185112565956094457423719923327738477763166696072166688381556373620872382104739678078108235080735101087200), (⟨2, by decide⟩, 372008877624048624449005957414875929047617344988295454553226584847397889074445554896980790724210765743858232602991926531045361000252273412873178641219410105725202823681882557418123814703131326556636192788554958849627756216733292178571379636249874217942438316873153208563000796762649170830784503725056044295061770381139672812348000), (⟨3, by decide⟩, -256027606736082457581195355036241623534656716685697832269058742563247272738997788185294441584014635283644489346666688982632587299637488369842338691185711914544676015088785162487592809087008976320913164271355249092045010144313453035896555402193764711628331894308443635659567672900890403940738524153457086585587557475578807235087200), (⟨4, by decide⟩, 299412711260153530395585325031355516471473192483008127700248548753615787864701919498608412065228574611438661486781054666418320328222103329787777706558384700810696099623278981396749997957738111525897842537389858570356731516149143984939460304313056803489320577770687388482679984409941628202817469696356459697345240293144221339000800), (⟨5, by decide⟩, 295336069540499953034704377251100225191897260468395780544668364578008538105075209665176838064242597916984291960588924032063128733878866089602984137375105259996934476843643968381699068928597577585890853634392110119569260037570291011913148810359222175818903521240804988440548786795460390839851141338974550649294897305576001510339200), (⟨6, by decide⟩, -515111211885817968058705925512424351481307540170120110728888546541239407123065866945996225455699703376062903411180513158161623919003338088478524631145114107476745076382627310842060028115171361437604215990917703924302334122381917548321014660369215697729516662604238540235030573494908357512584004826403467411139898391431962628266560)]
  | 1 => [(⟨1, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300), (⟨2, by decide⟩, -20226335388429603227110412632819633530027490063834981084123197027769031611244858912703970231082311427538911907830001213720417208981252931758980031175475446625606022142257775306892117492012620058761100462160062634647792328319980997759829749524050086101897545506085780716781245077805897504999254191759103480767981008009568856300505250), (⟨3, by decide⟩, 11350857202699993904756145580085903264932704102793856946242840529017177281263988208188173900283564834801607625178294563529179115087459556874295351986545401824132962011989000256696515760539763166828022448673151052894294700250981359108953481301369799045457379276760304190575320051117549439563615662384989295824935176492778638793988700), (⟨4, by decide⟩, -15440901526703662476172058383203955081458984525484558998111302116991366681980915268614052296043918177168173145434472041526494092108387053462855248061508707015460484266105393969491241392221760245049735975017087819939901507958064061704630102078980450121455830282810143449927210150332065309873132332438656271068517757935904267136135250), (⟨5, by decide⟩, -13565246478806638940307827748795628423031799522891301211505387044471036183697099361383821573100144918518154401079188183102089990025952357617530687873696418586978092280167449963646520368070273059862309867795961890885932462925538420222039853901262789226314577051299598291894407973911108140317986590721124499507681656833177871386715250), (⟨6, by decide⟩, 25624750422847555827323640187716613501052475705943625964300913580544029060242868575214159813936044518559947249500843474167574463485979191140780855367821370598606291067828961799330114840709474765107867702827916844028138236594215926538616230624741982858654070702901160243576713851654620384954148487304862771187289825852163708759874540)]
  | 2 => [(⟨2, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300), (⟨3, by decide⟩, 2881097106803500974545544942805855447393021454030646336916487333401425378226490393924448869222746266429699525549338923636870883773934739132579226552856585724521693064878302724631954220349661584290346072458262047601676721607658587856970090248237006651037456867154395013254193463724824594296943964313947281274254879804996999223534440), (⟨4, by decide⟩, 12948835709428856524923137506874187438628755954132573216696378432601177365829910297723283639670403141793268250987469658385580055133806283676160883630108797468586645614475579105651369777255840608719137644098069440002461934268515138176644585103355723746848364218638949888941576831063920410593320494689882480350087091611745363838830140), (⟨5, by decide⟩, 11216621713019634706891636859703286713918885912873365026873915368713285024871796056590487198440695238409686787050197749428299823151946357919482220882343296626564776312256838887604353379905384108113742908975969626390260127332553945480006311431087253961374718796333044583050742794950383866162651812727322522551015533967331541164531810), (⟨6, by decide⟩, -24493334179358610305392834597608719390194208410832704532852322516940441712138969443879674768151292370206049016189372163559508272883922512452359363476342873999255857955498369485875319687490201180761796979864285832096331498217503302561112065301089779203886880325222940767913669817563179112408208633678273518508851046936743567609575344)]
  | 3 => [(⟨3, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300), (⟨4, by decide⟩, -17590080807201325216567329661138419564127536069682975052923999445360831637403407290407806494267146525667237464822456644170729806548529183380753901564204453488650517683306691591508310185833253523756120363710479006770513514672141789884639274022195429464774680299955212888361156910662132247683038235417544403556262018378906422674217700), (⟨5, by decide⟩, -22784092587390122931287880149977710412351156020873673032539908540325672481313398701371588148129302428454966921111207698917310868239886454027320827562627442487199218769437237628917465089034440205443784620839388759866371991872387140638131598652613213006216731928888236217100716472413345181525420726671573443621940937125235736225581425), (⟨6, by decide⟩, 45314717264158070586380675151004926390285254148446451843165802991986310922398477906644525099721965739615627706830650251436053965442487387530034747498144783102493687661827164093155941646406556840589940982830990705103836559827574029966992257819298145485621500705658649797397911906750119401615415296053244202175782010337456412783759820)]
  | 4 => [(⟨4, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300), (⟨5, by decide⟩, 18385487548887693977464033218138528518303373484875795716401500869478028481800445084858617944021981844909876348144158821502945106517906796877922881720169484428041603406943465422551342589913770758957195330943405275355824352074325682063051133605461613193854866937308461169412462873355275446502833395246515793126894174688801000617919325), (⟨6, by decide⟩, -52662807301572902508192523297371595731571257196613401919371192303323754934262092496900098930945034143816546971001576405521895399469701003434438164524414084467289025888724126087473633935268500578666760648011242541984448871893856000449311496378946795983036022408245840316587268798955170378459121886824091634069103212020459490523934760)]
  | 5 => [(⟨5, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300), (⟨6, by decide⟩, -34150548736969747849115374295356509150572643331645968800030360866305946311764097172957663461169110864131374941822380935659308575306898763709692993584029287359956710848239236293401646877901803028677967414988279524521881707661897453991955102903355697271137367034822134039989431611610037227409286952929814922258228771069348356163713520)]
  | _ => []

def planar_4_15AT : SparseIntMatrix 7 6 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300)]
  | 1 => [(⟨0, by decide⟩, -255074675205064305429102628254703359381433534217455557522460119098423938472219050290571268431579699106712802501445538420064361414646824718722249204563741035061024226421497273420490008097741572658458631795996451481152029672354185112565956094457423719923327738477763166696072166688381556373620872382104739678078108235080735101087200), (⟨1, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300)]
  | 2 => [(⟨0, by decide⟩, 372008877624048624449005957414875929047617344988295454553226584847397889074445554896980790724210765743858232602991926531045361000252273412873178641219410105725202823681882557418123814703131326556636192788554958849627756216733292178571379636249874217942438316873153208563000796762649170830784503725056044295061770381139672812348000), (⟨1, by decide⟩, -20226335388429603227110412632819633530027490063834981084123197027769031611244858912703970231082311427538911907830001213720417208981252931758980031175475446625606022142257775306892117492012620058761100462160062634647792328319980997759829749524050086101897545506085780716781245077805897504999254191759103480767981008009568856300505250), (⟨2, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300)]
  | 3 => [(⟨0, by decide⟩, -256027606736082457581195355036241623534656716685697832269058742563247272738997788185294441584014635283644489346666688982632587299637488369842338691185711914544676015088785162487592809087008976320913164271355249092045010144313453035896555402193764711628331894308443635659567672900890403940738524153457086585587557475578807235087200), (⟨1, by decide⟩, 11350857202699993904756145580085903264932704102793856946242840529017177281263988208188173900283564834801607625178294563529179115087459556874295351986545401824132962011989000256696515760539763166828022448673151052894294700250981359108953481301369799045457379276760304190575320051117549439563615662384989295824935176492778638793988700), (⟨2, by decide⟩, 2881097106803500974545544942805855447393021454030646336916487333401425378226490393924448869222746266429699525549338923636870883773934739132579226552856585724521693064878302724631954220349661584290346072458262047601676721607658587856970090248237006651037456867154395013254193463724824594296943964313947281274254879804996999223534440), (⟨3, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300)]
  | 4 => [(⟨0, by decide⟩, 299412711260153530395585325031355516471473192483008127700248548753615787864701919498608412065228574611438661486781054666418320328222103329787777706558384700810696099623278981396749997957738111525897842537389858570356731516149143984939460304313056803489320577770687388482679984409941628202817469696356459697345240293144221339000800), (⟨1, by decide⟩, -15440901526703662476172058383203955081458984525484558998111302116991366681980915268614052296043918177168173145434472041526494092108387053462855248061508707015460484266105393969491241392221760245049735975017087819939901507958064061704630102078980450121455830282810143449927210150332065309873132332438656271068517757935904267136135250), (⟨2, by decide⟩, 12948835709428856524923137506874187438628755954132573216696378432601177365829910297723283639670403141793268250987469658385580055133806283676160883630108797468586645614475579105651369777255840608719137644098069440002461934268515138176644585103355723746848364218638949888941576831063920410593320494689882480350087091611745363838830140), (⟨3, by decide⟩, -17590080807201325216567329661138419564127536069682975052923999445360831637403407290407806494267146525667237464822456644170729806548529183380753901564204453488650517683306691591508310185833253523756120363710479006770513514672141789884639274022195429464774680299955212888361156910662132247683038235417544403556262018378906422674217700), (⟨4, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300)]
  | 5 => [(⟨0, by decide⟩, 295336069540499953034704377251100225191897260468395780544668364578008538105075209665176838064242597916984291960588924032063128733878866089602984137375105259996934476843643968381699068928597577585890853634392110119569260037570291011913148810359222175818903521240804988440548786795460390839851141338974550649294897305576001510339200), (⟨1, by decide⟩, -13565246478806638940307827748795628423031799522891301211505387044471036183697099361383821573100144918518154401079188183102089990025952357617530687873696418586978092280167449963646520368070273059862309867795961890885932462925538420222039853901262789226314577051299598291894407973911108140317986590721124499507681656833177871386715250), (⟨2, by decide⟩, 11216621713019634706891636859703286713918885912873365026873915368713285024871796056590487198440695238409686787050197749428299823151946357919482220882343296626564776312256838887604353379905384108113742908975969626390260127332553945480006311431087253961374718796333044583050742794950383866162651812727322522551015533967331541164531810), (⟨3, by decide⟩, -22784092587390122931287880149977710412351156020873673032539908540325672481313398701371588148129302428454966921111207698917310868239886454027320827562627442487199218769437237628917465089034440205443784620839388759866371991872387140638131598652613213006216731928888236217100716472413345181525420726671573443621940937125235736225581425), (⟨4, by decide⟩, 18385487548887693977464033218138528518303373484875795716401500869478028481800445084858617944021981844909876348144158821502945106517906796877922881720169484428041603406943465422551342589913770758957195330943405275355824352074325682063051133605461613193854866937308461169412462873355275446502833395246515793126894174688801000617919325), (⟨5, by decide⟩, 14229395307070728270464739289731878812738601388185820333345983694294144296568373822065693108820462860054739559092658723191378573044541151545705413993345536399981962853433015122250686199125751261949153089578449801884117378192457272496647959543064873862973902931175889183328929838170848844753869563720756217607595321278895148401547300)]
  | 6 => [(⟨0, by decide⟩, -515111211885817968058705925512424351481307540170120110728888546541239407123065866945996225455699703376062903411180513158161623919003338088478524631145114107476745076382627310842060028115171361437604215990917703924302334122381917548321014660369215697729516662604238540235030573494908357512584004826403467411139898391431962628266560), (⟨1, by decide⟩, 25624750422847555827323640187716613501052475705943625964300913580544029060242868575214159813936044518559947249500843474167574463485979191140780855367821370598606291067828961799330114840709474765107867702827916844028138236594215926538616230624741982858654070702901160243576713851654620384954148487304862771187289825852163708759874540), (⟨2, by decide⟩, -24493334179358610305392834597608719390194208410832704532852322516940441712138969443879674768151292370206049016189372163559508272883922512452359363476342873999255857955498369485875319687490201180761796979864285832096331498217503302561112065301089779203886880325222940767913669817563179112408208633678273518508851046936743567609575344), (⟨3, by decide⟩, 45314717264158070586380675151004926390285254148446451843165802991986310922398477906644525099721965739615627706830650251436053965442487387530034747498144783102493687661827164093155941646406556840589940982830990705103836559827574029966992257819298145485621500705658649797397911906750119401615415296053244202175782010337456412783759820), (⟨4, by decide⟩, -52662807301572902508192523297371595731571257196613401919371192303323754934262092496900098930945034143816546971001576405521895399469701003434438164524414084467289025888724126087473633935268500578666760648011242541984448871893856000449311496378946795983036022408245840316587268798955170378459121886824091634069103212020459490523934760), (⟨5, by decide⟩, -34150548736969747849115374295356509150572643331645968800030360866305946311764097172957663461169110864131374941822380935659308575306898763709692993584029287359956710848239236293401646877901803028677967414988279524521881707661897453991955102903355697271137367034822134039989431611610037227409286952929814922258228771069348356163713520)]
  | _ => []

def planar_4_15Aw : Fin 6 → ℤ := fun i =>
  match i.val with
  | 0 => 170812123816526567918419513881110042665317699016378120160865538241050164123914063939493659926707364818057285726587301930768301575597848470756462786328284657151855399698680577195558418285186449256044246415447943852497143223079987354377027591392163565093906170077010320014690684870579673822262799297802912775995447225953816082895284433889875299517067120636560775000000000000000000000
  | 1 => 4548234752480830865342362330592640948732014661945546854781492708161232711595610331766145961479412045943242751673182292490012404932791445099100568416594262645378286656021682010732748128503362260200359929394366908104071746061709489545906970737459261045553008785202773126266185711847223188287658384786842297289237076455550112442992514077536320482215613897268800000000000000000000000
  | 2 => 603545716701851965590129945868320780839453815372173240861407748105878493050219691677954146963140530531015220950215641022395442380294413941311572055935664732673906131459538919136293163037649395760053228048243645275859365647468887763455165998068133982947973895298195974654870619807873650438226560096196954755392425428341397471429574912226280398379852416140000000000000000000000000
  | 3 => 715128363415644455849871972286809509009408077519454248501416101060535490320938865704204390854629400407222529290307863070605063903191462711443613208725364954599310029221077266023004249279260257430490267577491772473657041259847075950777609349542126944542584186169118175685754018891697966955215485895437396336040168756088565656112685755656644396302068862108800000000000000000000000
  | 4 => 346137086498904318419578082918532252615323101484886638892448362516380238141472996044439339666547584815563662571402915111222717092962759055927616886210051994827252315503880459297101390423833991848843634125761919059038347001129422277713322495508856056019540564623407732172804296006297887683809999190248827157965913854156375053347336423091417035236404650515200000000000000000000000
  | 5 => 280185442794685300120903853372464764909238661261865222438079832013923790303058436347909733084678693080768066808506199481400239193883425288358868857820445508078208854752217599962900850558506205694096030273808713015178546676827220504159473730421988799879170000413244046836220597773385921517630247725476934942998805524526927819942768584353256261709701265880000000000000000000000000
  | _ => 0

def planar_4_15A : Matrix (Fin 7) (Fin 7) ℚ := sparseRatScaledMatrix planar_4_15AD planar_4_15AM

theorem planar_4_15A_gram_check : SparseGramCheck planar_4_15AS planar_4_15AM planar_4_15AR planar_4_15AT planar_4_15Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_15A_posSemidef : (planar_4_15A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_15A_gram_check

/- N=4, d=15, H; dimension=7, rank=6. -/
def planar_4_15HD : ℤ := 2002
def planar_4_15HS : ℤ := 2128979162262433703006456972386742662310348416091776778710337640810277227808133802017981735181560693807917551693106008513094267151476057315633375001580583777759680000
def planar_4_15HM : SparseIntMatrix 7 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1369920691125), (⟨1, by decide⟩, -585507673800), (⟨2, by decide⟩, 725135803875), (⟨3, by decide⟩, -491006908350), (⟨4, by decide⟩, 513661486275), (⟨5, by decide⟩, 419611477950), (⟨6, by decide⟩, -722429706600)]
  | 1 => [(⟨0, by decide⟩, -585507673800), (⟨1, by decide⟩, 583838409600), (⟨2, by decide⟩, -831483387000), (⟨3, by decide⟩, 450683190000), (⟨4, by decide⟩, -615146081400), (⟨5, by decide⟩, -537101722800), (⟨6, by decide⟩, 1013065704000)]
  | 2 => [(⟨0, by decide⟩, 725135803875), (⟨1, by decide⟩, -831483387000), (⟨2, by decide⟩, 1271789245125), (⟨3, by decide⟩, -621488423250), (⟨4, by decide⟩, 948922129125), (⟨5, by decide⟩, 822570743250), (⟨6, by decide⟩, -1565726765400)]
  | 3 => [(⟨0, by decide⟩, -491006908350), (⟨1, by decide⟩, 450683190000), (⟨2, by decide⟩, -621488423250), (⟨3, by decide⟩, 463872050100), (⟨4, by decide⟩, -588756316050), (⟨5, by decide⟩, -562883901300), (⟨6, by decide⟩, 1064222325360)]
  | 4 => [(⟨0, by decide⟩, 513661486275), (⟨1, by decide⟩, -615146081400), (⟨2, by decide⟩, 948922129125), (⟨3, by decide⟩, -588756316050), (⟨4, by decide⟩, 913540299525), (⟨5, by decide⟩, 868701503250), (⟨6, by decide⟩, -1721031329880)]
  | 5 => [(⟨0, by decide⟩, 419611477950), (⟨1, by decide⟩, -537101722800), (⟨2, by decide⟩, 822570743250), (⟨3, by decide⟩, -562883901300), (⟨4, by decide⟩, 868701503250), (⟨5, by decide⟩, 895985776500), (⟨6, by decide⟩, -1812920972400)]
  | 6 => [(⟨0, by decide⟩, -722429706600), (⟨1, by decide⟩, 1013065704000), (⟨2, by decide⟩, -1565726765400), (⟨3, by decide⟩, 1064222325360), (⟨4, by decide⟩, -1721031329880), (⟨5, by decide⟩, -1812920972400), (⟨6, by decide⟩, 3746283096384)]
  | _ => []

def planar_4_15HR : SparseIntMatrix 6 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 15643596761095263028631437247243073685403873708355572400), (⟨1, by decide⟩, -6686114027471344720830424722798908689782649265982522240), (⟨2, by decide⟩, 8280575792703380598573134343989977425191287688491803600), (⟨3, by decide⟩, -5606977200141133213602025872814270046761132389384706080), (⟨4, by decide⟩, 5865677637434676281905685444070762775956239787666503120), (⟨5, by decide⟩, 4791688161149217476885585900342932680392814217570736160), (⟨6, by decide⟩, -8249673934777843225215441473254012773555333933514807680)]
  | 1 => [(⟨1, by decide⟩, 15643596761095263028631437247243073685403873708355572400), (⟨2, by decide⟩, -24458251278389205936998697011593788445278719315986596000), (⟨3, by decide⟩, 11293407196619994046179073965975101899414533953751466800), (⟨4, by decide⟩, -18551758777227810083887528668591480107539286150109103200), (⟨5, by decide⟩, -16776934018213143614523826135683665241898684715665049600), (⟨6, by decide⟩, 33027711021924401363624311508977056700186771348120732800)]
  | 2 => [(⟨2, by decide⟩, 15643596761095263028631437247243073685403873708355572400), (⟨3, by decide⟩, 3222436254441180726872292834209594346697236708634264800), (⟨4, by decide⟩, 12622287398176093794740862742430748223151661055026673200), (⟨5, by decide⟩, 8869630189013968373498999249991061168457347203297285600), (⟨6, by decide⟩, -17728298887661570362231888566087354138160887604661887680)]
  | 3 => [(⟨3, by decide⟩, 15643596761095263028631437247243073685403873708355572400), (⟨4, by decide⟩, -18485376998146598693865762374897326619607621943000625520), (⟨5, by decide⟩, -22937452984344054162609983718839936522876353562912418000), (⟨6, by decide⟩, 44240077895780320966499406204013940467102398525092377152)]
  | 4 => [(⟨4, by decide⟩, 15643596761095263028631437247243073685403873708355572400), (⟨5, by decide⟩, 19434263477595292130455121679401034652116157412967412125), (⟨6, by decide⟩, -56028390402885858930271154378908327376321102016135132540)]
  | 5 => [(⟨5, by decide⟩, 15643596761095263028631437247243073685403873708355572400), (⟨6, by decide⟩, -37544632226628631268715449393383376844969296900053373760)]
  | _ => []

def planar_4_15HT : SparseIntMatrix 7 6 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 15643596761095263028631437247243073685403873708355572400)]
  | 1 => [(⟨0, by decide⟩, -6686114027471344720830424722798908689782649265982522240), (⟨1, by decide⟩, 15643596761095263028631437247243073685403873708355572400)]
  | 2 => [(⟨0, by decide⟩, 8280575792703380598573134343989977425191287688491803600), (⟨1, by decide⟩, -24458251278389205936998697011593788445278719315986596000), (⟨2, by decide⟩, 15643596761095263028631437247243073685403873708355572400)]
  | 3 => [(⟨0, by decide⟩, -5606977200141133213602025872814270046761132389384706080), (⟨1, by decide⟩, 11293407196619994046179073965975101899414533953751466800), (⟨2, by decide⟩, 3222436254441180726872292834209594346697236708634264800), (⟨3, by decide⟩, 15643596761095263028631437247243073685403873708355572400)]
  | 4 => [(⟨0, by decide⟩, 5865677637434676281905685444070762775956239787666503120), (⟨1, by decide⟩, -18551758777227810083887528668591480107539286150109103200), (⟨2, by decide⟩, 12622287398176093794740862742430748223151661055026673200), (⟨3, by decide⟩, -18485376998146598693865762374897326619607621943000625520), (⟨4, by decide⟩, 15643596761095263028631437247243073685403873708355572400)]
  | 5 => [(⟨0, by decide⟩, 4791688161149217476885585900342932680392814217570736160), (⟨1, by decide⟩, -16776934018213143614523826135683665241898684715665049600), (⟨2, by decide⟩, 8869630189013968373498999249991061168457347203297285600), (⟨3, by decide⟩, -22937452984344054162609983718839936522876353562912418000), (⟨4, by decide⟩, 19434263477595292130455121679401034652116157412967412125), (⟨5, by decide⟩, 15643596761095263028631437247243073685403873708355572400)]
  | 6 => [(⟨0, by decide⟩, -8249673934777843225215441473254012773555333933514807680), (⟨1, by decide⟩, 33027711021924401363624311508977056700186771348120732800), (⟨2, by decide⟩, -17728298887661570362231888566087354138160887604661887680), (⟨3, by decide⟩, 44240077895780320966499406204013940467102398525092377152), (⟨4, by decide⟩, -56028390402885858930271154378908327376321102016135132540), (⟨5, by decide⟩, -37544632226628631268715449393383376844969296900053373760)]
  | _ => []

def planar_4_15Hw : Fin 6 → ℤ := fun i =>
  match i.val with
  | 0 => 11917731874181708152436992008789969057212085150443325062156904402750
  | 1 => 2902100080009838027919779849157711040134184513221725789259780120960
  | 2 => 630857113059448949736557285181490655966301489077491196151622656000
  | 3 => 965234404556108359417680660280896344671235572771833532555984896000
  | 4 => 431985849110381940836106492179212015335451549372310176165905039360
  | 5 => 394068062160515617059523983785411793227676909704424407732689305600
  | _ => 0

def planar_4_15H : Matrix (Fin 7) (Fin 7) ℚ := sparseRatScaledMatrix planar_4_15HD planar_4_15HM

theorem planar_4_15H_gram_check : SparseGramCheck planar_4_15HS planar_4_15HM planar_4_15HR planar_4_15HT planar_4_15Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_15H_posSemidef : (planar_4_15H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_15H_gram_check

def planar_4_15KD : ℤ := 12711222759954090024244085064246925436126775500562834368398673333612624988213118371737106566418455111097933321078271165529802238696099399101994500096000
def planar_4_15KU : SparseIntMatrix 7 1 := fun i =>
  match i.val with
  | 1 => [(⟨0, by decide⟩, -17795711863935726033941719089945695610577485700787968115758142667057674983498365720431949192985837155537106649509579631741723134174539158742792300134400)]
  | 2 => [(⟨0, by decide⟩, -12711222759954090024244085064246925436126775500562834368398673333612624988213118371737106566418455111097933321078271165529802238696099399101994500096000)]
  | 3 => [(⟨0, by decide⟩, 17795711863935726033941719089945695610577485700787968115758142667057674983498365720431949192985837155537106649509579631741723134174539158742792300134400)]
  | 4 => [(⟨0, by decide⟩, 7626733655972454014546451038548155261676065300337700621039204000167574992927871023042263939851073066658759992646962699317881343217659639461196700057600)]
  | 5 => [(⟨0, by decide⟩, 30506934623889816058185804154192621046704261201350802484156816000670299971711484092169055759404292266635039970587850797271525372870638557844786800230400)]
  | 6 => [(⟨0, by decide⟩, 12711222759954090024244085064246925436126775500562834368398673333612624988213118371737106566418455111097933321078271165529802238696099399101994500096000)]
  | _ => []

def planar_4_15KL : SparseIntMatrix 1 7 := fun i =>
  match i.val with
  | 0 => [(⟨6, by decide⟩, 1)]
  | _ => []

def planar_4_15KVA : SparseIntMatrix 7 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 51574029430521445670257480963257548266670333691847216844166857953032858822480730130845068687630926418595699089367420108800), (⟨1, by decide⟩, -179253160848370235195441718688589764395914942484241508192958861113342644544763650774942778432070620147057717025031218790400), (⟨2, by decide⟩, -148686484686539958748463155920723382460061601545799532677766874128105588710480041464981828143872149477032942326186592174080), (⟨3, by decide⟩, 160774430855733419865625947418482487541194850252031537232076545636615506237951687754821036603880382858071140887708880076800), (⟨4, by decide⟩, 166514557432556087399324105612964588667810921447179886472903629921005514667260626476323200041031298449458808966098064506880), (⟨5, by decide⟩, -56882824520013975528296519996828301072556237307838073726515560177176001122963246596623793394260573580144970574407317585920)]
  | 1 => [(⟨0, by decide⟩, -179253160848370235195441718688589764395914942484241508192958861113342644544763650774942778432070620147057717025031218790400), (⟨1, by decide⟩, 104822050305184835893554038971931175545093837248571051043216234932891486558457727264340996293701013050783540488575302972211200), (⟨2, by decide⟩, 68726672895012340719770847876410063357384666558970394816908971617640303970732548639734898310695739179043870326270672555212800), (⟨3, by decide⟩, -60636032076329927953253943734219559212407691969968008030967104277018122429908925661688473004617858088217842414594212390502400), (⟨4, by decide⟩, -42381267712844769941046645001914431440608830615959272939780157518991020711396501740373497428979344726245189801081250932326400), (⟨5, by decide⟩, 3000561951737215102995405580574251208178575201316365341941663107553862216458444555498419511987809337200163566106181632000000)]
  | 2 => [(⟨0, by decide⟩, -148686484686539958748463155920723382460061601545799532677766874128105588710480041464981828143872149477032942326186592174080), (⟨1, by decide⟩, 68726672895012340719770847876410063357384666558970394816908971617640303970732548639734898310695739179043870326270672555212800), (⟨2, by decide⟩, 52764212590924494809991624398750779193928484913436932021512683478743719170328280160460228476787917570809648853838494785601536), (⟨3, by decide⟩, -38012004021268932123257765420536900687117714514913161530252202427432666064277602041768453212470739984427675512620226319482880), (⟨4, by decide⟩, -44150451219017746315001836405563053814588671740094700106753861906079395741649273419316080008054519691835368119547890877071360), (⟨5, by decide⟩, 11866078264218925626316413442743528010153128727321466933136908774400933637912183651673897072227040558478215180789488853975040)]
  | 3 => [(⟨0, by decide⟩, 160774430855733419865625947418482487541194850252031537232076545636615506237951687754821036603880382858071140887708880076800), (⟨1, by decide⟩, -60636032076329927953253943734219559212407691969968008030967104277018122429908925661688473004617858088217842414594212390502400), (⟨2, by decide⟩, -38012004021268932123257765420536900687117714514913161530252202427432666064277602041768453212470739984427675512620226319482880), (⟨3, by decide⟩, 49976744626432466767139651594869737269720361741238892919108329743482194146696960326025092652658715913376740028866832734617600), (⟨4, by decide⟩, 30546171015048570186212237722476354084128878147757101036099050198678979990384355579550299824531681407576741667604436709539840), (⟨5, by decide⟩, 121482857388558530731340887002471234020070508856750649355817683028681049516564091441631006694718672765855060558814946263040)]
  | 4 => [(⟨0, by decide⟩, 166514557432556087399324105612964588667810921447179886472903629921005514667260626476323200041031298449458808966098064506880), (⟨1, by decide⟩, -42381267712844769941046645001914431440608830615959272939780157518991020711396501740373497428979344726245189801081250932326400), (⟨2, by decide⟩, -44150451219017746315001836405563053814588671740094700106753861906079395741649273419316080008054519691835368119547890877071360), (⟨3, by decide⟩, 30546171015048570186212237722476354084128878147757101036099050198678979990384355579550299824531681407576741667604436709539840), (⟨4, by decide⟩, 76062051486183268099042071326174477842697861397453973347904067459742571414505710621568035574927726041680767189912815084240896), (⟨5, by decide⟩, -39645383552070128215906620344258022965735607937437159865467964898680544007588991270899537915666199797719089118141488073539584)]
  | 5 => [(⟨0, by decide⟩, -56882824520013975528296519996828301072556237307838073726515560177176001122963246596623793394260573580144970574407317585920), (⟨1, by decide⟩, 3000561951737215102995405580574251208178575201316365341941663107553862216458444555498419511987809337200163566106181632000000), (⟨2, by decide⟩, 11866078264218925626316413442743528010153128727321466933136908774400933637912183651673897072227040558478215180789488853975040), (⟨3, by decide⟩, 121482857388558530731340887002471234020070508856750649355817683028681049516564091441631006694718672765855060558814946263040), (⟨4, by decide⟩, -39645383552070128215906620344258022965735607937437159865467964898680544007588991270899537915666199797719089118141488073539584), (⟨5, by decide⟩, 30683430785438979932602785706624040287591375729791207697543837616955863502549218987911180387718097747783914793230239568756736)]
  | _ => []

def planar_4_15KVH : SparseIntMatrix 7 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 20854261381752853162049075681512746682008105998596357162507179128176989650863946714302954301709534431904360726335318316894849467105764461840), (⟨1, by decide⟩, 40594391336300584519378410589063190332370499627591107829385488586059556071871046053440955374648835009956031773803826824822652887412165095940), (⟨2, by decide⟩, 17711590070294039720355675611539072539533688182424816598170452573372215283090102012401375677336579450912612559004749672384755356763845161980), (⟨3, by decide⟩, 16006200863049592169829955659411033210376351712585652917530202403476644613816010201009894574150964713111304642042527097835859079320213013820), (⟨4, by decide⟩, -5453102143743235851124866903699185301986391145200797873307530769033044285845344928939749875017177625217396347658676368458906829250449694260), (⟨5, by decide⟩, 13650155406189926576417815774440470433824589537346648000661186141069428854275893128146125694537917042934237372218045366305815024178721341120)]
  | 1 => [(⟨0, by decide⟩, 40594391336300584519378410589063190332370499627591107829385488586059556071871046053440955374648835009956031773803826824822652887412165095940), (⟨1, by decide⟩, 1052506088687360019925362177476026922566425568459395540658235924166255213900584842671679178287374256358583215691357889670858849773374347156785), (⟨2, by decide⟩, 685141562492837545653623117020389420346721394493451234846150591792729872535681222895120649332462066060393287170265283688130922004145919661135), (⟨3, by decide⟩, -515767907631022480776134798065222698074510153815293967277227132351668062773246991439423098403153759022839534761743718449136890675176366563425), (⟨4, by decide⟩, -433361603839838563229266439442122572909408995975615179664749685386960973566610210321246007812554426190308920549743419065217549466914964398205), (⟨5, by decide⟩, 79059269920202743338561732736834306008574222516931859894885333268002558154754474622260428582507772741958005151204743879740826105754827905200)]
  | 2 => [(⟨0, by decide⟩, 17711590070294039720355675611539072539533688182424816598170452573372215283090102012401375677336579450912612559004749672384755356763845161980), (⟨1, by decide⟩, 685141562492837545653623117020389420346721394493451234846150591792729872535681222895120649332462066060393287170265283688130922004145919661135), (⟨2, by decide⟩, 515808298785620879333192661196565626322003024523165157235190597648392105352468030407771995537568643197697548518796609486442819233758691080753), (⟨3, by decide⟩, -341507687200681226394843722460187795190237280269263822918403411191732317973104130316746048144065612256850359655069785409099404724429264427295), (⟨4, by decide⟩, -420767573109117229204206088327557284111579701236185388763833557478976325069054449132160648306389085283982385964220808523434285343448731869955), (⟨5, by decide⟩, 122281132402803195019801509321582862786025647480394818754413165533865712129392426375342662430569987721166014647557250027834037930164646670160)]
  | 3 => [(⟨0, by decide⟩, 16006200863049592169829955659411033210376351712585652917530202403476644613816010201009894574150964713111304642042527097835859079320213013820), (⟨1, by decide⟩, -515767907631022480776134798065222698074510153815293967277227132351668062773246991439423098403153759022839534761743718449136890675176366563425), (⟨2, by decide⟩, -341507687200681226394843722460187795190237280269263822918403411191732317973104130316746048144065612256850359655069785409099404724429264427295), (⟨3, by decide⟩, 472002955766572859076149656981646079929171670489065721806733146685227832783520417002669620703660378891246880479113359355857524166976631413905), (⟨4, by decide⟩, 303093709341587781714788498058842256797262922429836374793350754456550003411221115506624227387024867862070590416017799039980152274561328003565), (⟨5, by decide⟩, -487821395081474748145464364585817303133270733512774968976740142115199257704455518931114124920897491098179004579540024001398300273257208240)]
  | 4 => [(⟨0, by decide⟩, -5453102143743235851124866903699185301986391145200797873307530769033044285845344928939749875017177625217396347658676368458906829250449694260), (⟨1, by decide⟩, -433361603839838563229266439442122572909408995975615179664749685386960973566610210321246007812554426190308920549743419065217549466914964398205), (⟨2, by decide⟩, -420767573109117229204206088327557284111579701236185388763833557478976325069054449132160648306389085283982385964220808523434285343448731869955), (⟨3, by decide⟩, 303093709341587781714788498058842256797262922429836374793350754456550003411221115506624227387024867862070590416017799039980152274561328003565), (⟨4, by decide⟩, 689074940593659664786534613981203778451063089254701136827941799055491399799179934262743045914877687490616844187679886297319653447040507758425), (⟨5, by decide⟩, -348614743430438949358194585316896811029566480945846740726648965941119599577675236220075662620107216094356693243480410889034790596207526850800)]
  | 5 => [(⟨0, by decide⟩, 13650155406189926576417815774440470433824589537346648000661186141069428854275893128146125694537917042934237372218045366305815024178721341120), (⟨1, by decide⟩, 79059269920202743338561732736834306008574222516931859894885333268002558154754474622260428582507772741958005151204743879740826105754827905200), (⟨2, by decide⟩, 122281132402803195019801509321582862786025647480394818754413165533865712129392426375342662430569987721166014647557250027834037930164646670160), (⟨3, by decide⟩, -487821395081474748145464364585817303133270733512774968976740142115199257704455518931114124920897491098179004579540024001398300273257208240), (⟨4, by decide⟩, -348614743430438949358194585316896811029566480945846740726648965941119599577675236220075662620107216094356693243480410889034790596207526850800), (⟨5, by decide⟩, 280617193313531902695161847981371642716427617070447167995053125872513310293413993179732373302229950996554636269088798986193376068972119066880)]
  | _ => []

def planar_4_15U : Matrix (Fin 7) (Fin 1) ℚ := sparseRatScaledMatrix planar_4_15KD planar_4_15KU
def planar_4_15L : Matrix (Fin 1) (Fin 7) ℚ := sparseRatMatrix planar_4_15KL

def planar_4_15AV : Matrix (Fin 7) (Fin 7) ℚ :=
  ((planar_4_15AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_15KD planar_4_15KVA

theorem planar_4_15A_kernel_check : SparseScaledFrameCheck planar_4_15KD planar_4_15AM planar_4_15KU planar_4_15KL planar_4_15KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_15A_kernel_frame : HasKernelFrame planar_4_15A planar_4_15U planar_4_15L planar_4_15AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_15KD≠0) planar_4_15A_kernel_check).scale_matrix
    (by norm_num [planar_4_15AD])

theorem planar_4_15A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_15A.map (Rat.castHom ℂ)).mulVecLin)=1 :=
  kernelFrame_finrank planar_4_15A_kernel_frame.ratCast

def planar_4_15HV : Matrix (Fin 7) (Fin 7) ℚ :=
  ((planar_4_15HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_15KD planar_4_15KVH

theorem planar_4_15H_kernel_check : SparseScaledFrameCheck planar_4_15KD planar_4_15HM planar_4_15KU planar_4_15KL planar_4_15KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_15H_kernel_frame : HasKernelFrame planar_4_15H planar_4_15U planar_4_15L planar_4_15HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_15KD≠0) planar_4_15H_kernel_check).scale_matrix
    (by norm_num [planar_4_15HD])

theorem planar_4_15H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_15H.map (Rat.castHom ℂ)).mulVecLin)=1 :=
  kernelFrame_finrank planar_4_15H_kernel_frame.ratCast

theorem planar_4_15_same_kernel (v : Fin 7 → ℂ) :
    (planar_4_15A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_15H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_15A_kernel_frame.ratCast planar_4_15H_kernel_frame.ratCast v

def planar_4_15WS : SparseIntMatrix 7 6 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 1)]
  | 5 => [(⟨5, by decide⟩, 1)]
  | _ => []

def planar_4_15RS : SparseIntMatrix 6 7 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 5)]
  | 1 => [(⟨1, by decide⟩, 5), (⟨6, by decide⟩, 7)]
  | 2 => [(⟨2, by decide⟩, 5), (⟨6, by decide⟩, 5)]
  | 3 => [(⟨3, by decide⟩, 5), (⟨6, by decide⟩, -7)]
  | 4 => [(⟨4, by decide⟩, 5), (⟨6, by decide⟩, -3)]
  | 5 => [(⟨5, by decide⟩, 5), (⟨6, by decide⟩, -12)]
  | _ => []

def planar_4_15W : Matrix (Fin 7) (Fin 6) ℚ := sparseRatMatrix planar_4_15WS
def planar_4_15R : Matrix (Fin 6) (Fin 7) ℚ := sparseRatScaledMatrix 5 planar_4_15RS

theorem planar_4_15_complement : HasComplement planar_4_15U planar_4_15L planar_4_15W planar_4_15R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_15A_active_posDef :
    ((planar_4_15W.map (Rat.castHom ℂ))ᴴ * (planar_4_15A.map (Rat.castHom ℂ)) * (planar_4_15W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_15A_kernel_frame.ratCast planar_4_15A_posSemidef _ _
    ((planar_4_15_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_15_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_15H_active_posDef :
    ((planar_4_15W.map (Rat.castHom ℂ))ᴴ * (planar_4_15H.map (Rat.castHom ℂ)) * (planar_4_15W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_15H_kernel_frame.ratCast planar_4_15H_posSemidef _ _
    ((planar_4_15_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_15_complement.map (Rat.castHom ℂ)).2.2)

/- N=4, d=16, A; dimension=10, rank=8. -/
def planar_4_16AD : ℤ := 7013308548339843750000000000000
def planar_4_16AS : ℤ := 1140585880864924357364286785200329566974648745332692429847922589205531127312789172022801618031800641975543129757307974798190113275855327755188890609036122014547381671766297691912771329122205610551418859296464564853316045150269256371231236312528082399377182518933860175569008370875816073101145508426611409168120804078118364649164140976524312213033414015348958877499916364863481581447127044231112570220569396895392476638695089874312045269966576754994209333674119526794402249876705703093004940678413228967706721334376961500376614363513642171105891385276456664845241990640723774122940874170919487139543486555386905785676827871472110250465726357512547567259537140681806457993893150603026122107388402668705832110835326828581119595890961308699174506476320053137051711749625030009627396773879407803644820387753113175150109610226470614902098197428848055654177940635318387739448836011967943986918821668846026640598300990018068426130924758158667644684164285909851678807192368380053171741281854359142319972743206357584233457472896752769427182815449019064355594222068083577906024120697738196045966735534463396773994166213764785689407686831828382602315527948114968953379590444519413419641638188397029975684648369757735106101565421674738450990586446020448258949370917110992409155523463153903403329111708802358445314631139398383980911833114522494718257605307770534116399853551589105014540832441111031282744121914533866819419614036573321616521424231498372468927122725823212135149114980844162448988184479621918085234157038015413937157375235087781882050951620568491585995376620373577692002146460178262380645305669788087251371789490239049179356770099198101140243304486471406861832175017554106172578228074283380109538489938538711228303198233250557393072187888293251454040343236949895281239162468737703962322414995690063243206920788787725951093957655459423863471302933654072393879924109241086680700171421602181779464813141471547427340319415852494492266315675433977473556251051790411007809791130518921002905924634750000000000000000000000
def planar_4_16AM : SparseIntMatrix 10 10 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 47239620006716325982834458841892201600), (⟨1, by decide⟩, -47014235256888698555631217386082554200), (⟨2, by decide⟩, 60430566900169853599719893642020447200), (⟨3, by decide⟩, 41093552901949051778555723654792830600), (⟨4, by decide⟩, -40265945402798306390441055463270160400), (⟨5, by decide⟩, 50330240629986716313975852068446071000), (⟨6, by decide⟩, 35250114235044642721341364250136992400), (⟨7, by decide⟩, -33573059190843497456334939281249032000), (⟨8, by decide⟩, 29359704711848878274160681925437626000), (⟨9, by decide⟩, 23511000240946996508156195441100399040)]
  | 1 => [(⟨0, by decide⟩, -47014235256888698555631217386082554200), (⟨1, by decide⟩, 47003990003326057967597560804914373175), (⟨2, by decide⟩, -60426725855026447218191482526277276450), (⟨3, by decide⟩, -41101832920145577555058479995365683175), (⟨4, by decide⟩, 40266513224187551502011779945308305925), (⟨5, by decide⟩, -50330655533853931332664520816224672500), (⟨6, by decide⟩, -35250542835903362297865180587222535450), (⟨7, by decide⟩, 33575148437456766840183893110171121050), (⟨8, by decide⟩, -29356971758346205557281302249488299225), (⟨9, by decide⟩, -23517457232741800243060929608904831640)]
  | 2 => [(⟨0, by decide⟩, 60430566900169853599719893642020447200), (⟨1, by decide⟩, -60426725855026447218191482526277276450), (⟨2, by decide⟩, 77691295226478633052120531593369603300), (⟨3, by decide⟩, 52852358125372080728035952126811109350), (⟨4, by decide⟩, -51771895082902314842078443453837286850), (⟨5, by decide⟩, 64709682605100594141466174030973592000), (⟨6, by decide⟩, 45321072566556629820303988580222184600), (⟨7, by decide⟩, -43169437588633555409498261411267662800), (⟨8, by decide⟩, 37743313839988160980061567005557155850), (⟨9, by decide⟩, 30240617585690268034403751301587962400)]
  | 3 => [(⟨0, by decide⟩, 41093552901949051778555723654792830600), (⟨1, by decide⟩, -41101832920145577555058479995365683175), (⟨2, by decide⟩, 52852358125372080728035952126811109350), (⟨3, by decide⟩, 35989979103688885552417690883574881675), (⟨4, by decide⟩, -35251334202264048095407213128069066225), (⟨5, by decide⟩, 44066130599777885118799828142611969875), (⟨6, by decide⟩, 30827081302974340665586521261374232750), (⟨7, by decide⟩, -29355990937882780690258276252587515000), (⟨8, by decide⟩, 25708166369411144199704541049647628375), (⟨9, by decide⟩, 20534149298674139955579121758264265880)]
  | 4 => [(⟨0, by decide⟩, -40265945402798306390441055463270160400), (⟨1, by decide⟩, 40266513224187551502011779945308305925), (⟨2, by decide⟩, -51771895082902314842078443453837286850), (⟨3, by decide⟩, -35251334202264048095407213128069066225), (⟨4, by decide⟩, 34533582222526771545866307227498222625), (⟨5, by decide⟩, -43171119934064405842581956765205435375), (⟨6, by decide⟩, -30196182748000244117588136798194438550), (⟨7, by decide⟩, 28751601250902443602127048920235667300), (⟨8, by decide⟩, -25189205275093053630701671371517577475), (⟨9, by decide⟩, -20101880174502596016149171134000295280)]
  | 5 => [(⟨0, by decide⟩, 50330240629986716313975852068446071000), (⟨1, by decide⟩, -50330655533853931332664520816224672500), (⟨2, by decide⟩, 64709682605100594141466174030973592000), (⟨3, by decide⟩, 44066130599777885118799828142611969875), (⟨4, by decide⟩, -43171119934064405842581956765205435375), (⟨5, by decide⟩, 53972122692380728663419597114498956250), (⟨6, by decide⟩, 37741464476110671727175162392580444250), (⟨7, by decide⟩, -35931822828988064676136658353269698250), (⟨8, by decide⟩, 31493916516661837236285202922596606500), (⟨9, by decide⟩, 25110744556247647075179196633516513800)]
  | 6 => [(⟨0, by decide⟩, 35250114235044642721341364250136992400), (⟨1, by decide⟩, -35250542835903362297865180587222535450), (⟨2, by decide⟩, 45321072566556629820303988580222184600), (⟨3, by decide⟩, 30827081302974340665586521261374232750), (⟨4, by decide⟩, -30196182748000244117588136798194438550), (⟨5, by decide⟩, 37741464476110671727175162392580444250), (⟨6, by decide⟩, 26442371867453666231973002712736821900), (⟨7, by decide⟩, -25189767716678238488293984671379312500), (⟨8, by decide⟩, 22008899869303539385853865199061382750), (⟨9, by decide⟩, 17657848388197105161966637937761089360)]
  | 7 => [(⟨0, by decide⟩, -33573059190843497456334939281249032000), (⟨1, by decide⟩, 33575148437456766840183893110171121050), (⟨2, by decide⟩, -43169437588633555409498261411267662800), (⟨3, by decide⟩, -29355990937882780690258276252587515000), (⟨4, by decide⟩, 28751601250902443602127048920235667300), (⟨5, by decide⟩, -35931822828988064676136658353269698250), (⟨6, by decide⟩, -25189767716678238488293984671379312500), (⟨7, by decide⟩, 24003612047605210412517744261088836500), (⟨8, by decide⟩, -20947200061645029128946085768732510750), (⟨9, by decide⟩, -16847967567848108051959477326095090240)]
  | 8 => [(⟨0, by decide⟩, 29359704711848878274160681925437626000), (⟨1, by decide⟩, -29356971758346205557281302249488299225), (⟨2, by decide⟩, 37743313839988160980061567005557155850), (⟨3, by decide⟩, 25708166369411144199704541049647628375), (⟨4, by decide⟩, -25189205275093053630701671371517577475), (⟨5, by decide⟩, 31493916516661837236285202922596606500), (⟨6, by decide⟩, 22008899869303539385853865199061382750), (⟨7, by decide⟩, -20947200061645029128946085768732510750), (⟨8, by decide⟩, 18385584355276564402535000356258935125), (⟨9, by decide⟩, 14616076036061949918697266456831659680)]
  | 9 => [(⟨0, by decide⟩, 23511000240946996508156195441100399040), (⟨1, by decide⟩, -23517457232741800243060929608904831640), (⟨2, by decide⟩, 30240617585690268034403751301587962400), (⟨3, by decide⟩, 20534149298674139955579121758264265880), (⟨4, by decide⟩, -20101880174502596016149171134000295280), (⟨5, by decide⟩, 25110744556247647075179196633516513800), (⟨6, by decide⟩, 17657848388197105161966637937761089360), (⟨7, by decide⟩, -16847967567848108051959477326095090240), (⟨8, by decide⟩, 14616076036061949918697266456831659680), (⟨9, by decide⟩, 11898640912774292286586392658984254464)]
  | _ => []

def planar_4_16AR : SparseIntMatrix 8 10 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360), (⟨1, by decide⟩, -508260036139085628979741416161791495822345783010538321849456991676066601854628250254383779245781663134902700118761496440111944947174826051953067219617081699348422163026318220615628451079994211505006964348102983946122064092168936207486711612967820426515991040960487302053470879019157430319008540412967568032752529787489816093821443099581037797775058979299336976203877164417020037116222367128411386373421054174694615539686288590408596687848945940281178031671663606800960926722807237298754003039658959147169983137359380225381185651742371788099142723411747347191536747636319910917342331879454844272285939468222545360494090991370444903950948949570817646495638115064445), (⟨2, by decide⟩, 653300898095228905175473397167069932128078829928121466249893769517283249224376289204270707593856022259909764183111221248283325020057652684202489936663255485762240752127648377935178390956124302223489283263041731681664858321482201516621279117358507302461928976393853530798670271071094820078377349232953553489733237384883586581952942450945117412164352183238126623801505045542468653801970094459923763929241806100695308885202094866059695793367325895467651422637789790494256888908427464277992117607883508985630189990518068158527018276850475764704546179008594909766221982500777578947388806601024778108028603448422966411374721143133210935597965026831190814726006868211620), (⟨3, by decide⟩, 444252906995179248837442214835250547529450475766814351218290293225080564278116455609597727124849436144759461854120566751387569255252183359772517463072662093025210916414387203155587996341902067647755815313524935132211003088895451079276580310880134747180838588074579255575638183046756751898966852952897619019950810460040861026401918938284309244642488724348802493052516521608320299267725688210027033982447703202223885216126638411935367263985146444731629039633126441397112115378387423038518746100227289754323360576375286014236215810242690810194838687782493221800051986572153784283484706671927776061750193954134745874540015998510643841054293340974012674011474486196135), (⟨4, by decide⟩, -435305833515648335106325925252782840317360728144646767402198023803102221473349589964856663298482430867136099474587480430510047226972044857269832893460576892891463120527945502063417651363120634795317463702070570332763160794691606915894743785618542778367872340932908698090893599695656398620823816771467615618407567056248759640446160934628123642501263928175435367488513870914566396150635524958203822406576978838227343723686088303795052414658614749977616352686037021515623469219517533066985150091084652289304770017241807125667281469792061060820002318374685793298328674783867939915545533075695880255954029839519639968761487593916649944272528510140625914530052620900590), (⟨5, by decide⟩, 544108604164474293610300963400644082233852823782633068506482746190625368432321011328243249116022701224509582722765108427426275123343909748213872617598184703726138496401141688441461700853763180539800907947088260314055172656366564077110864722044529044635151077529749880339190094050865264398231924817481734007435183621136459458984808494148486253996182315512570731147824097990694972752442880834089414107581556217395124944712044088336183425985120520909364351896973830315810602489215025984751928385279900209338843949829481822111722375465177179653244156540495418280550307281004360115788967497800527419121807493036113038041962173928136658188068589480981504287240189939725), (⟨6, by decide⟩, 381080841517794035341724796274114373082299858371022064032115088372402853768942585129766591291590045768621870940458863979572218020882119659986303334423852102942239143992478549674049744358610924301929106850569442049692953489416860568433026707870169933606150612308953490130289097093051834510399868368961581865224524641954422458863629517382023248127498113711801600766905820508190829499315044167046715409348253721169104661705179839790695987173341706042411159563368368326338417118334330834837552085360026768680934937203243318845309600356811273860770600891776481834882929016358966460146041030623428624656703436675783881327129482522020369371676387260882596105283932597790), (⟨7, by decide⟩, -362950586867995896164921557257909072773761264693185752304628240535769700278487528973255967739430253688263426000625258513735990940391436116628438751154818811799321394135299347836691395352325106744896808878680000998317455989721659811430518466544397407602702533910762434321202092510004087636460397296434387226833700520576161152913910874769599710453711377339984062300086920966813554021344705788660853902935452273073055203480676373721292784913598850165965207900083178802519622169902843949446028581099871739383197251353435580081258594962639106526746969894669024475592062323256751566993864082277798648936941867246433854546587296247459629374481148428910612224893802442200), (⟨8, by decide⟩, 317400984964244713265061281849499798586322425612675695902591676000471987781355094394972066508992084582958922627555609580279377269447361691289056881535555771703217575426538476215666463359511257185978205459897723526081572134793406323874059508243839307512951123208841362420041180716638437598914498769074393151025158138494296015468357440945058895546865058350263105237151437080052643313946571041195337287631396995195395573188758556179990405832887047613180504285223844903928951415415402326140291428945160006048889012301807094170700403127416677157668729138679293019510929953066343012241153113939778634750046849135830523947925835213759381253573362932414803614277454408350), (⟨9, by decide⟩, 254171992096348246799277327712007184662162428823663962441806496648648062893140084775057899852892518304156072854774671429783262628994348244662369479853579185394063411739097397043935861984539888743942582544069757726974582866639477095386002171801542562271450042481094584374037991077401000066350683999918377935753683128273922587317764626239027675940703707968279659954137260042341805007070994144834940137389981813282759260434127646203277416943974256450896114063134844461958832326655776939135258008985111518796078937265679110164239869529721045196131181722921796270391889881332163001688085642317062659596982721696811229496995775455987028970025302421002620082107244734984)]
  | 1 => [(⟨1, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360), (⟨2, by decide⟩, -678686464691069104435561065710387886597307027288239438474737838557477139355745937773873046437790184038211125686868917182921918953159272870628208007286990644702023621383419870327880632382176350996284945108454992006241631735874673983233311506587764995903853955893572590810418959102607397593844141402781910446944199123679598566500968896808608980199213802039677577564213869493539084455558146211965130334277833695330247478272760616105746217986397746909852520387407084235451323066550154248756397426666856534821044201797982410176176660646477134331708035383765462101728528150041979115870735143657486443645861315643494241301678959009174803629569004084169852198767952075520), (⟨3, by decide⟩, -487500596205846882126507748841004443870613560476872985463206236015314556777631435694317405093284066343147580588917070776983413499552187116202487927797532321861449907982779084071190119635671248826256546313985301498953774848019872994973457002195232923693338064581029583814291919030438053649157167218297132302033051444053793342942420399298580761759936820261474388091431308274678536079672671158667324811247552589844263431893543577357283342094855030611216494211015976764934018583141295885360113295170639684723920220667612407377627795851710005509032276472121509538187097976040211039590864924198541443951114382206870916020721667549313114741280055345725054956693236522640), (⟨4, by decide⟩, 459681242247623648183711376991066417016670087067247094035369644565913232804295249976208893271506876457297651719772396744883782488342818818957390329585013552726466144226391094488954281063664611374166445034216757585625178936963272475091646861491235315286931906329386521095168080448035089699760595776668772501154283512021276351768337096590947379863037857660640315623305720801238984135477955652836703054598644033960488067084724178478042818113762103522384084499809031976466360651560735216930028016138588231003171914601379009407732494017462446657606297375345159910760488052776786290045795541049923699458232988018448753364548093233126563665222989563402494806396163115200), (⟨5, by decide⟩, -573873129016107794667814306290619863522265559479912530642183944010767663138055817813607492681034896928854252765849076219352639173592516812279384351559835202789014085400312504909060491056299321233947984863502825997558007938710359635645655566393362992471493049427393725066587067428550475499931922251138200839384196199312431332426413679315849662140757302055704383836472798801546181452025250362042924007366192323414365893305590530703050114394332943648874470506728678902045821597262409558829911852060030344311165700690045413192583001808721330272957689961008674820439322916731812752057952497885124335922349867965448450033294698446552409743693379036305218689974233333200), (⟨6, by decide⟩, -402256470731739781996608285814872726262065584071235276741902573757585999484319067962358135188403900673785024995066525557971933906901072811949944706707624468904456647774365894940702859350287676441436474116773183987520989339615134771852824972806803491083272253290527063780315731250197538047139720560145199951492240299271163082083120469454009715521664759561030138544248514960535260115104734151167165346235376362158515681831379891049860042561213229007567833801411914335199497176775751782419767009909265520818468573061611701889144695250215447713754879347480588638796901046617563749855428574467494518606090215268978201319016227369374780105445598221050081954835944768160), (⟨7, by decide⟩, 387129245904267622263747010814693262315434663631262152635143819535167638128620698659215327241937648888196376054999009704393382920811692417831757210831095285353092856385495709092131066534831082808994529834697817980777017288788738691932903154679473261563040167552661636475018004540693522024891890891609403046744104573034128250536883210891143438736274534064721369229127556974779478488764245879433432179344146654298241903120808151921860737827570293677802011615239787447964862849437906867743642644150447313786034291660993813473986988169400347833204266633268917457121716192917614854301645109755723272020564406851050551026773650511267785612045924595784400547184621824320), (⟨8, by decide⟩, -327666388213707007633825310380871966183937499540990734543774940138063539713314525649807837123255579473920526744420781675367551276472169441176257362380076108405176877682712946973278858390717614217051929814273063110650601261129994432399216762554749337817680778349497752793811788557277047455606564779656921552341185439814120284630483734570812403140070428286161227374037064572125398659705069192030078699347443561656252566755613725931770670970338294038800466037879113695933006740859634182271126185400633315232710706611103024002721091768653389071657968948282618622416830135805357328585796319860115447173984095747822519521020429737976029146368424548224636773876923512640), (⟨9, by decide⟩, -283018201566147919049813134536790599803013504677835861299550561039526132192418522474664791827570436233016196855910736004391447423321629103321446872247846553123938016563546702544760910406821725174389812132691338947719875032666603478350107521739461801859161664168698715177874524394087697753933135669910659996889409338242807109311607279344192560545788573591786470084272059180528029693534704959991098534231824197673277205836848570801709805694511441171761455378710368547131526257509353254867434672689401392747520040122334639611343057214491544668747761178039062083019877342861408884938628912378687484015956758301776785207695091260372689746069167032296918339928426184064)]
  | 2 => [(⟨2, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360), (⟨3, by decide⟩, 763977528498924844758104533941668749041347804237291403928915839457656764312259061312816296560812555347987803220655464072971271526768494852066528757644366566678803284381629531790690963326983265038675649379969557744750695496417229547029480600630614470964707013602072731231587162939192904112992961814210465180740052064192930606193792946063108412980815705779977082684508226884727303128189690009429232931281673420549279726680214639857819022374060042654304549488245577123246001959007894562132790221738483908292173936201562743176532552648686286069611532580690121956095814888292317402116931164602686001753586055147553568778750072454108876090806541623756855973752172067840), (⟨4, by decide⟩, -381134981682744714789631681545328693368949158002076527824392657137230171827959001169731604186127647943594319870754153449816420737270729652123631016677674442991219366197128618919811655956056662754474256031216917096907312651290132126770042437076572183038294445954308119101917751851010593981848580393406879151804879269662064737431122295332253542696243090421065695780470890086730815840537451311387113415443159385953577389587563737494376277971941674983682808833145979758731543984278593063354710770754775195239247653807370252265394021427171602850960225516537925112026349529979624589640524102734063922081515014267139760486470955183894831804362274077014832680711871369560), (⟨5, by decide⟩, 355521579372530370203327184046199850446883006150277198127927785136837885999779964253031994873451962645975206503715217925580040629684290150512869680231112206804104245495079010152299226487150863877051598340547645849696937533345120275001685772647554961811506507190838931079808846281263847229989023156085354104250273080354763402004114141434539100492020631674268697605011453802843497313840744972295203285401954782754082142170547405030314587037237353727050953745388263797452139893046223059566425526476188516573300566795329253610405765335914632669881377173665338008937715375361713178384734327889520368988388624312799152803628884180978653288369915451673259970979306935800), (⟨6, by decide⟩, 233879547084862303054864932459160887707816957624988974597862228312127997886157898137351245933485318899596789191242840238938519476582878191938574268413400037189740239711379540612053061525552897099378520540211196293836077098212578007559066841920891194804740474718027778703911500214185042145903567301404153483064424558784216291705462341630474167365911632651038187594626818234309439078230439450769831760076907871602353438356024474838253858476561570068557581667335101901013208338356481887057322133842991361452638290948079572541716627358313498133122486514296449951806798122597013162272097541919572421639581542774645747146077122878846680636337104653212110364571977073200), (⟨7, by decide⟩, -364631342537673794090440713876051313484208858467457180840796796124802187434570895284190575246241435887854175411667207575844529839797521243467958776194308885756281413501375097129703184032100168791137170412072100356876022981803920592776457889845841508024075877075782051501420136166926524333952370678288709455700377123343783377410834987184111530535177069592562921452423514282372074069801378357648777603524482166476575132382419759111926456570728899099967096314128760117557293558556839177894090321178777244423287245111203392564507253938387433798991408735232694811796128306185746962063148688232791400459058606014287239057657777559122363348374038330961055208353049040640), (⟨8, by decide⟩, 173232415092330948552822990932779078324385077180720518389013911504854125623424383816566021682909251814179159107959877566469077521435755920943932866291441140239493057145790647320666949411968810555780284233836195972692383465355733913499206137446662448308397793877723130312251156009410538948620671545211600620688476354083330769311374479395843225904125085665669491831564105448035760118340885623087309630477063824869656558685576865804527082316868017055290335254987566135287784112033619820147258833018318700281021658233216648656586052416382385128073030741826100481158136068204467603441232420905652874350914945514306268958516008724569934301191260956588189430359954476280), (⟨9, by decide⟩, 420283867670257745477552990407232230874772789491075930777038069621306502681969875201777021900916906980971117641834983776591180855658091232720830165253603874822924638456018880986907352240795900407752085439788572705355790180967471560511458854890097290335884633512304799905084266025294426372597431460090374345423741491381258099327106557032274256479871168220653936592030927120558518165154207336890123900992279637510575115851906872806355531344473630714816203590362975804798835440270735860127980547492996508512622874770749391736069877668903131029570512504100671979730586581126551547317721554725917248678074089266353091214400023637481779482132507682159905966215578137920)]
  | 3 => [(⟨3, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360), (⟨4, by decide⟩, -542038863521049568567030728292130095297630129308597991756205634473598003818484836599808884585034355535085155795654585652405842199328561018409684355802528066522203073983188841728249910419959716602722082699507815865836803579520660671462596401205089753218543819246284327553206812530387840679851696924061303087492230150786307698461866911710095086177516760618895770108591035782571189871809440380216070935361006403793719424592483158897777618630785368178156326643644230888780998689222427593974262275781036054681712776991864613638938649875553346923295447043257453941301439262678421281561957721983918508034052382714326043903294173310916103738359002483768431785535108924220), (⟨5, by decide⟩, 802432246070274816037163345593772641315339491269715031505764470821408621127241389685710369322985621804915617584837879522942550058828833654877041847517521782887887588394492948835712203508349205586432509937645416143498355165371311464522736434595947048056083947771708993157590295960610218435886008973220443402463599259491133138736644151413251703546422877021716870679705560427296108386051035634606437775025632610611139015528948730588039689344839056447026531080009642671026067835598227503354659063372021303317649869932772868972272922375815730017338038851943815672962666828031417501013578113321143749930041046238473686164134710351666004966588489056359822551491933243270), (⟨6, by decide⟩, -61826143378605374624206605003527661849907861092575372391847319275748024108653185695654895087411269797191416594977628527046934615333694081636063409235670362852754135307852280134784790814883260100164332857862311901247953675611936731432951764816562530793986609759954457721601873064371396323619884382307002176572669635711053283193158955295249653420912827411536220610878895433670193011779538498982393258118289977968407185099205877785729591872524225017403279717925827554499059768514326827086429914006124300679720635462784799348118445089239490620178464028166086498983947930542755711571075849535164103045999477169522773096850809882970427046734948113080892583361068064840), (⟨7, by decide⟩, 226270673114512483669439351676116283801292966581332523208000197223576819992236129030961465303813293908209317913632647811574996701967240199165589462801472944095700253249015608351495289865758017243543166339410691532735754157274174873570873763189496703649330499614929967624766499138088829486480851454652213949044939915308373349006828871596345928227552034528852681016425625592125825917149805082583452575435383405212779009474422000902895995684866655661963227908080824823062934200720924632397939974486376542122495428082625705631327597243774015365724236518316789958156205923776085386829720341322486179371341288791716067660370246452702594304836995052710340157439098274260), (⟨8, by decide⟩, 577754731462744654149614014291803941300922769901930020820947408845230684551057993194420286996502756057590888014874804907921612615797075373777701922923513650168150634789767606842048984195179496452753418652973315324715594880115706334737537250472033946120716167032388346326255402758098683741937764892119843295072386689817724661587344061580680149560366462050246939518864937292920195499029937879615065329464852238652059784197501294817229439830446332156236007278308788757168858073519042207752683822668393479509558410192230879869988311924242165001437067050980413433201008110226468171679892237034265498729448720821427314214539143870170482195402052769463825509526162518040), (⟨9, by decide⟩, -728044136132444001755211786632230447653133308049498591079432698543012520293589198570533734656592178528919195754429364209079982312550937750409738569807944862423717587014285804320299610611302221891408789664613075571457862632743376755858713850585980223466816130432422122186275987078324844619443270137657337762029076685675058581550520105496327041573541741269921589518511465826852746268313574849213392935386813237070537028352312736690437534590409081008693066946251254626444059755476787289149499524784356014899294347298254340840097044148634771051467909922938429858904863739110940788167687193403520904554296581988538636754135954764699049873603000611138081861653854636800)]
  | 4 => [(⟨4, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360), (⟨5, by decide⟩, -748034016253278114168164023508477261272777261937395070831217422568165864618242576857433318034616770591718530476588337228698864150053054156887667192799809839472455767948282341860760926291275597115456648583727311004630089999485357169677692191125822837969954272777367425635246536936429992418076217981125235069604713196155687542945995514943272179356038516112311192202380203444912461657200567535401457489115627941691465091045807201708885737910735603038396414939089881049688497656532714928472887712701730902412316411572969367102013805951189428134538176549074810229402364640883928247090117253857679330533012133186757946592369738699836467235569390879631139014789102587000), (⟨6, by decide⟩, 572778428335659974934831695076965464051397520673595639279334535590810761446880963369526830606946621897792345572543746134967420656937769338650554084150401627816049852278132479411865603661334422738281828993038024055314402223818831797694089585975256597347030698890145387277738500846125040894600070798482980243050688200620489636902863607457515671936454713865372268700658466904620972799856899297066151147157418771952419171568475379130085430937628069457040468295710235997705413218268762078362655724404580074912895394322279958298843564092713076185341443288875569740360497281976800159010861019802604862517610403345288954696447857882924095701127198530900769156174006547680), (⟨7, by decide⟩, -1128629694665823501071160286561895048192230915259084990367471522814466897951707097354905905656079654692247430096675956618515402157096729587704200837790737241114391057544023988416298308729088156165478588387530801720105497623534929474858086900811016168667452549940339456963507726869866952489351346556858685554228238904590614694774990313787251171084330038040887517860800596565461605322793000714926466612206041074436975227243635541671019660336858905138102613360939625997125930146785941563735219767997166170433311671324985628094677931281462708855924530290697618310532302769759344377145442027435730400784817595064264420323149188983574396298928909903284380446392347954640), (⟨8, by decide⟩, -1597938440110572730084726069625324838985435631696713853713743998504777710986371021284864778402715713223107108317530792483479062843852611920237141215121123649619333353068593253752842843778069443887541252859464665766978445239797283560254853851574573979930870347601985635566328507229765174107200174659697600417879708525833276041385009618819448200930757376412430246401405759153010098228359360356893882457701120539087551573195077598458978582474073170707384932092513695072316267051656284394623571510809046598206900112723986737441267896974033604992909021188094030863294690077861170176758824249630619590219711027913766747003440925137311666346305190350694933067105352345120), (⟨9, by decide⟩, 3322094354176250369079850563072330275582575158435431653814442615861279271862314649578481885733105886546215263402228399066674232665868312857323227080730308436705594621963318915895775975543973668732517788491338322282584709666551244417971280770592198398858576503094020086229520322185299340987480900954467148745806482454786550493463802539939656736950280252960970044890026171149882113903217827719952715686660500569572986035806526265651376614397304224127038660597986559990879638112848614065542218354222300620755050589560834771226185342251997361245062242018036050495706966778167904323505862220856676190074176441027431052334584150005569523231900533872888297430912822519808)]
  | 5 => [(⟨5, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360), (⟨6, by decide⟩, 70224175090294218075581995336465166670152134278555432066224598195362681321845797810542299977577689097009457536053041891038915786804402494898742978598191944953483652960727273803950203485642569727165419415305000040389895266063510353541097820042808402630916153256945170311690635096344782776572620537484080198619697849298787666276227280946052405090320712144540438048091941754724473350488025385381582335668581370006589021202222671288745974786835975563228544067740567678460767764209763025678319022673348537719723647577097553804504918671762790464999833663941287966968504540456783489721370656666870585912446115328881875810066967816692389085940724929459264004346180194160), (⟨7, by decide⟩, 562008037552722091312870350153315420992493521810055638455869809504793146545620886883866031155621245986707312148344511132604300688005552458381612782682537624145680878866369384111696883450756374484811147555581753742429572529756751103889582903892057170987118330308811057876795824634262261934339786632387243570499268822100196906860157458720313155265973444591160452182527388211664783913095849629979340900268710689769767301772115639963055147922205397746087341131250015983624842117202479251077268544468663186045464559651799303774043018511900903521321245863111013223657543055838990464776657941488823344203778098653110502175525995330093784460272997608101684635893777306480), (⟨8, by decide⟩, 608824154279584903363258347044292198772594944662425926500019541635034934093518085424227564474006372051380283839046539059963577879208487454980774768414665587448003314173520899980997019107851420969588093832451753769356169373799091339583648117253929439407729099146774504751256248031825450452054866990709963702912400721632722017710975646017681425326187252687520744214588682714814432813421199886900395790714431603107493315906930754155552464446762714788239703843077061102598687293342321268196147892917562211191946991369864339643712964293076097164654468305738538534969879416143512791257571712600070401478742175539031752715570640541222043850900147561074527305457897435920), (⟨9, by decide⟩, -1443121347211193594961475403440687570377014179238118375223424762339433288774131443233321992147193786502131779351711144458110184022153612285978902584820153612857252155726632144014592269276859267276906038810824329147433561466562274279497348828836913622623860156663989247604587674023670835787412833443601211331684834420098946131689483309068116981072046570425772989194431351702171195059595383933576737261903332951478583298405213567001357753372770290618106589984239651200107742328246287070877551028846289466553501574060144065314733408798952850479232499281937082912141931549614408140284621202021294697443657908509551210606821762462322070905220379504793572955810728939264)]
  | 6 => [(⟨6, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360), (⟨7, by decide⟩, -640408491844171058746900909829744980162412933684939505034740389264287812942240269550251731429476555665953342639242614536788835208039633768417050960833956814639499478127025138890443709014643339527025249668428708729838844506868313285117633634822753154043623968818777370647603685616071326346112080247437381847622333521639339637317579431039972985518241965432455229108200653128729229585709851840504379309652172392061830888141787181023267951457419938618656598535291710891484601405943511130482847758884317092398101973376822518531094964366601882834601558455443492839764974966891147678767070813153488948651304712338229167939679150286836305012464886877205486005961793967280), (⟨8, by decide⟩, -299944079443428707158852811250515606764758374930262455888408856163947284675873109746394360835636366414198179198222347888145392091487209011763727054128361817153242599309695438245995067352028311707991696148178356696339158200678349838240502964923928270245715330050080129265745106579812026793745863460039687837348228819643477862166141413705089994396616439719738866038449663585810906343521468171166439332212162267014288570676283590540061601019166747202399546163806020328687023119123704110564132201918343567978561158331280752579434027664850037397050043886118109221230554101789937316518821652328171976205984564973017849348509693723228304806547121756667726516030190465040), (⟨9, by decide⟩, 1121949193827880309816513987825521875019474842389295464764489570887522926377878721078898038019315702583800358306262062814287366046022238066992669156048108677566901901298163400229717821495680768152881832959881518377603043774163378484080849281711003583974804713800881611918090936082238680964445800800354246850066209397386583263910312211797770878284983552760927053451654153054632578540629506882767275722753354745362843835539015284981171348596642897913035572668386176286375152091066536081893664153612160188452970182840017088555573975071015680781235603583599186437744210205616149984838468366163379810833943565117824083362283795628058636404035543508831598001482128631808)]
  | 7 => [(⟨7, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360), (⟨8, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360), (⟨9, by decide⟩, -1736368503243785993099045302754069804328038249648852950646290818811736694158472514999672590028584965183951333549203359908081559894417366258931951924198534487179910081968381473286688072479336641877071122953276795370848400161568813579073366416484006907369334057720355931047478753084922427717067705615728239452397933980178895053272333888407903254720290181134853451655730046668883448535160756713623493884944051637742465819074068311464352387235091276222910967094577021870267649262781015801585449340526464974539658156732263006353470777178934411731512724303559456454525546412016172847466070720209116559471132751562577724814964228474400801050180602114742573398651177861424)]
  | _ => []

def planar_4_16AT : SparseIntMatrix 10 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360)]
  | 1 => [(⟨0, by decide⟩, -508260036139085628979741416161791495822345783010538321849456991676066601854628250254383779245781663134902700118761496440111944947174826051953067219617081699348422163026318220615628451079994211505006964348102983946122064092168936207486711612967820426515991040960487302053470879019157430319008540412967568032752529787489816093821443099581037797775058979299336976203877164417020037116222367128411386373421054174694615539686288590408596687848945940281178031671663606800960926722807237298754003039658959147169983137359380225381185651742371788099142723411747347191536747636319910917342331879454844272285939468222545360494090991370444903950948949570817646495638115064445), (⟨1, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360)]
  | 2 => [(⟨0, by decide⟩, 653300898095228905175473397167069932128078829928121466249893769517283249224376289204270707593856022259909764183111221248283325020057652684202489936663255485762240752127648377935178390956124302223489283263041731681664858321482201516621279117358507302461928976393853530798670271071094820078377349232953553489733237384883586581952942450945117412164352183238126623801505045542468653801970094459923763929241806100695308885202094866059695793367325895467651422637789790494256888908427464277992117607883508985630189990518068158527018276850475764704546179008594909766221982500777578947388806601024778108028603448422966411374721143133210935597965026831190814726006868211620), (⟨1, by decide⟩, -678686464691069104435561065710387886597307027288239438474737838557477139355745937773873046437790184038211125686868917182921918953159272870628208007286990644702023621383419870327880632382176350996284945108454992006241631735874673983233311506587764995903853955893572590810418959102607397593844141402781910446944199123679598566500968896808608980199213802039677577564213869493539084455558146211965130334277833695330247478272760616105746217986397746909852520387407084235451323066550154248756397426666856534821044201797982410176176660646477134331708035383765462101728528150041979115870735143657486443645861315643494241301678959009174803629569004084169852198767952075520), (⟨2, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360)]
  | 3 => [(⟨0, by decide⟩, 444252906995179248837442214835250547529450475766814351218290293225080564278116455609597727124849436144759461854120566751387569255252183359772517463072662093025210916414387203155587996341902067647755815313524935132211003088895451079276580310880134747180838588074579255575638183046756751898966852952897619019950810460040861026401918938284309244642488724348802493052516521608320299267725688210027033982447703202223885216126638411935367263985146444731629039633126441397112115378387423038518746100227289754323360576375286014236215810242690810194838687782493221800051986572153784283484706671927776061750193954134745874540015998510643841054293340974012674011474486196135), (⟨1, by decide⟩, -487500596205846882126507748841004443870613560476872985463206236015314556777631435694317405093284066343147580588917070776983413499552187116202487927797532321861449907982779084071190119635671248826256546313985301498953774848019872994973457002195232923693338064581029583814291919030438053649157167218297132302033051444053793342942420399298580761759936820261474388091431308274678536079672671158667324811247552589844263431893543577357283342094855030611216494211015976764934018583141295885360113295170639684723920220667612407377627795851710005509032276472121509538187097976040211039590864924198541443951114382206870916020721667549313114741280055345725054956693236522640), (⟨2, by decide⟩, 763977528498924844758104533941668749041347804237291403928915839457656764312259061312816296560812555347987803220655464072971271526768494852066528757644366566678803284381629531790690963326983265038675649379969557744750695496417229547029480600630614470964707013602072731231587162939192904112992961814210465180740052064192930606193792946063108412980815705779977082684508226884727303128189690009429232931281673420549279726680214639857819022374060042654304549488245577123246001959007894562132790221738483908292173936201562743176532552648686286069611532580690121956095814888292317402116931164602686001753586055147553568778750072454108876090806541623756855973752172067840), (⟨3, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360)]
  | 4 => [(⟨0, by decide⟩, -435305833515648335106325925252782840317360728144646767402198023803102221473349589964856663298482430867136099474587480430510047226972044857269832893460576892891463120527945502063417651363120634795317463702070570332763160794691606915894743785618542778367872340932908698090893599695656398620823816771467615618407567056248759640446160934628123642501263928175435367488513870914566396150635524958203822406576978838227343723686088303795052414658614749977616352686037021515623469219517533066985150091084652289304770017241807125667281469792061060820002318374685793298328674783867939915545533075695880255954029839519639968761487593916649944272528510140625914530052620900590), (⟨1, by decide⟩, 459681242247623648183711376991066417016670087067247094035369644565913232804295249976208893271506876457297651719772396744883782488342818818957390329585013552726466144226391094488954281063664611374166445034216757585625178936963272475091646861491235315286931906329386521095168080448035089699760595776668772501154283512021276351768337096590947379863037857660640315623305720801238984135477955652836703054598644033960488067084724178478042818113762103522384084499809031976466360651560735216930028016138588231003171914601379009407732494017462446657606297375345159910760488052776786290045795541049923699458232988018448753364548093233126563665222989563402494806396163115200), (⟨2, by decide⟩, -381134981682744714789631681545328693368949158002076527824392657137230171827959001169731604186127647943594319870754153449816420737270729652123631016677674442991219366197128618919811655956056662754474256031216917096907312651290132126770042437076572183038294445954308119101917751851010593981848580393406879151804879269662064737431122295332253542696243090421065695780470890086730815840537451311387113415443159385953577389587563737494376277971941674983682808833145979758731543984278593063354710770754775195239247653807370252265394021427171602850960225516537925112026349529979624589640524102734063922081515014267139760486470955183894831804362274077014832680711871369560), (⟨3, by decide⟩, -542038863521049568567030728292130095297630129308597991756205634473598003818484836599808884585034355535085155795654585652405842199328561018409684355802528066522203073983188841728249910419959716602722082699507815865836803579520660671462596401205089753218543819246284327553206812530387840679851696924061303087492230150786307698461866911710095086177516760618895770108591035782571189871809440380216070935361006403793719424592483158897777618630785368178156326643644230888780998689222427593974262275781036054681712776991864613638938649875553346923295447043257453941301439262678421281561957721983918508034052382714326043903294173310916103738359002483768431785535108924220), (⟨4, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360)]
  | 5 => [(⟨0, by decide⟩, 544108604164474293610300963400644082233852823782633068506482746190625368432321011328243249116022701224509582722765108427426275123343909748213872617598184703726138496401141688441461700853763180539800907947088260314055172656366564077110864722044529044635151077529749880339190094050865264398231924817481734007435183621136459458984808494148486253996182315512570731147824097990694972752442880834089414107581556217395124944712044088336183425985120520909364351896973830315810602489215025984751928385279900209338843949829481822111722375465177179653244156540495418280550307281004360115788967497800527419121807493036113038041962173928136658188068589480981504287240189939725), (⟨1, by decide⟩, -573873129016107794667814306290619863522265559479912530642183944010767663138055817813607492681034896928854252765849076219352639173592516812279384351559835202789014085400312504909060491056299321233947984863502825997558007938710359635645655566393362992471493049427393725066587067428550475499931922251138200839384196199312431332426413679315849662140757302055704383836472798801546181452025250362042924007366192323414365893305590530703050114394332943648874470506728678902045821597262409558829911852060030344311165700690045413192583001808721330272957689961008674820439322916731812752057952497885124335922349867965448450033294698446552409743693379036305218689974233333200), (⟨2, by decide⟩, 355521579372530370203327184046199850446883006150277198127927785136837885999779964253031994873451962645975206503715217925580040629684290150512869680231112206804104245495079010152299226487150863877051598340547645849696937533345120275001685772647554961811506507190838931079808846281263847229989023156085354104250273080354763402004114141434539100492020631674268697605011453802843497313840744972295203285401954782754082142170547405030314587037237353727050953745388263797452139893046223059566425526476188516573300566795329253610405765335914632669881377173665338008937715375361713178384734327889520368988388624312799152803628884180978653288369915451673259970979306935800), (⟨3, by decide⟩, 802432246070274816037163345593772641315339491269715031505764470821408621127241389685710369322985621804915617584837879522942550058828833654877041847517521782887887588394492948835712203508349205586432509937645416143498355165371311464522736434595947048056083947771708993157590295960610218435886008973220443402463599259491133138736644151413251703546422877021716870679705560427296108386051035634606437775025632610611139015528948730588039689344839056447026531080009642671026067835598227503354659063372021303317649869932772868972272922375815730017338038851943815672962666828031417501013578113321143749930041046238473686164134710351666004966588489056359822551491933243270), (⟨4, by decide⟩, -748034016253278114168164023508477261272777261937395070831217422568165864618242576857433318034616770591718530476588337228698864150053054156887667192799809839472455767948282341860760926291275597115456648583727311004630089999485357169677692191125822837969954272777367425635246536936429992418076217981125235069604713196155687542945995514943272179356038516112311192202380203444912461657200567535401457489115627941691465091045807201708885737910735603038396414939089881049688497656532714928472887712701730902412316411572969367102013805951189428134538176549074810229402364640883928247090117253857679330533012133186757946592369738699836467235569390879631139014789102587000), (⟨5, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360)]
  | 6 => [(⟨0, by decide⟩, 381080841517794035341724796274114373082299858371022064032115088372402853768942585129766591291590045768621870940458863979572218020882119659986303334423852102942239143992478549674049744358610924301929106850569442049692953489416860568433026707870169933606150612308953490130289097093051834510399868368961581865224524641954422458863629517382023248127498113711801600766905820508190829499315044167046715409348253721169104661705179839790695987173341706042411159563368368326338417118334330834837552085360026768680934937203243318845309600356811273860770600891776481834882929016358966460146041030623428624656703436675783881327129482522020369371676387260882596105283932597790), (⟨1, by decide⟩, -402256470731739781996608285814872726262065584071235276741902573757585999484319067962358135188403900673785024995066525557971933906901072811949944706707624468904456647774365894940702859350287676441436474116773183987520989339615134771852824972806803491083272253290527063780315731250197538047139720560145199951492240299271163082083120469454009715521664759561030138544248514960535260115104734151167165346235376362158515681831379891049860042561213229007567833801411914335199497176775751782419767009909265520818468573061611701889144695250215447713754879347480588638796901046617563749855428574467494518606090215268978201319016227369374780105445598221050081954835944768160), (⟨2, by decide⟩, 233879547084862303054864932459160887707816957624988974597862228312127997886157898137351245933485318899596789191242840238938519476582878191938574268413400037189740239711379540612053061525552897099378520540211196293836077098212578007559066841920891194804740474718027778703911500214185042145903567301404153483064424558784216291705462341630474167365911632651038187594626818234309439078230439450769831760076907871602353438356024474838253858476561570068557581667335101901013208338356481887057322133842991361452638290948079572541716627358313498133122486514296449951806798122597013162272097541919572421639581542774645747146077122878846680636337104653212110364571977073200), (⟨3, by decide⟩, -61826143378605374624206605003527661849907861092575372391847319275748024108653185695654895087411269797191416594977628527046934615333694081636063409235670362852754135307852280134784790814883260100164332857862311901247953675611936731432951764816562530793986609759954457721601873064371396323619884382307002176572669635711053283193158955295249653420912827411536220610878895433670193011779538498982393258118289977968407185099205877785729591872524225017403279717925827554499059768514326827086429914006124300679720635462784799348118445089239490620178464028166086498983947930542755711571075849535164103045999477169522773096850809882970427046734948113080892583361068064840), (⟨4, by decide⟩, 572778428335659974934831695076965464051397520673595639279334535590810761446880963369526830606946621897792345572543746134967420656937769338650554084150401627816049852278132479411865603661334422738281828993038024055314402223818831797694089585975256597347030698890145387277738500846125040894600070798482980243050688200620489636902863607457515671936454713865372268700658466904620972799856899297066151147157418771952419171568475379130085430937628069457040468295710235997705413218268762078362655724404580074912895394322279958298843564092713076185341443288875569740360497281976800159010861019802604862517610403345288954696447857882924095701127198530900769156174006547680), (⟨5, by decide⟩, 70224175090294218075581995336465166670152134278555432066224598195362681321845797810542299977577689097009457536053041891038915786804402494898742978598191944953483652960727273803950203485642569727165419415305000040389895266063510353541097820042808402630916153256945170311690635096344782776572620537484080198619697849298787666276227280946052405090320712144540438048091941754724473350488025385381582335668581370006589021202222671288745974786835975563228544067740567678460767764209763025678319022673348537719723647577097553804504918671762790464999833663941287966968504540456783489721370656666870585912446115328881875810066967816692389085940724929459264004346180194160), (⟨6, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360)]
  | 7 => [(⟨0, by decide⟩, -362950586867995896164921557257909072773761264693185752304628240535769700278487528973255967739430253688263426000625258513735990940391436116628438751154818811799321394135299347836691395352325106744896808878680000998317455989721659811430518466544397407602702533910762434321202092510004087636460397296434387226833700520576161152913910874769599710453711377339984062300086920966813554021344705788660853902935452273073055203480676373721292784913598850165965207900083178802519622169902843949446028581099871739383197251353435580081258594962639106526746969894669024475592062323256751566993864082277798648936941867246433854546587296247459629374481148428910612224893802442200), (⟨1, by decide⟩, 387129245904267622263747010814693262315434663631262152635143819535167638128620698659215327241937648888196376054999009704393382920811692417831757210831095285353092856385495709092131066534831082808994529834697817980777017288788738691932903154679473261563040167552661636475018004540693522024891890891609403046744104573034128250536883210891143438736274534064721369229127556974779478488764245879433432179344146654298241903120808151921860737827570293677802011615239787447964862849437906867743642644150447313786034291660993813473986988169400347833204266633268917457121716192917614854301645109755723272020564406851050551026773650511267785612045924595784400547184621824320), (⟨2, by decide⟩, -364631342537673794090440713876051313484208858467457180840796796124802187434570895284190575246241435887854175411667207575844529839797521243467958776194308885756281413501375097129703184032100168791137170412072100356876022981803920592776457889845841508024075877075782051501420136166926524333952370678288709455700377123343783377410834987184111530535177069592562921452423514282372074069801378357648777603524482166476575132382419759111926456570728899099967096314128760117557293558556839177894090321178777244423287245111203392564507253938387433798991408735232694811796128306185746962063148688232791400459058606014287239057657777559122363348374038330961055208353049040640), (⟨3, by decide⟩, 226270673114512483669439351676116283801292966581332523208000197223576819992236129030961465303813293908209317913632647811574996701967240199165589462801472944095700253249015608351495289865758017243543166339410691532735754157274174873570873763189496703649330499614929967624766499138088829486480851454652213949044939915308373349006828871596345928227552034528852681016425625592125825917149805082583452575435383405212779009474422000902895995684866655661963227908080824823062934200720924632397939974486376542122495428082625705631327597243774015365724236518316789958156205923776085386829720341322486179371341288791716067660370246452702594304836995052710340157439098274260), (⟨4, by decide⟩, -1128629694665823501071160286561895048192230915259084990367471522814466897951707097354905905656079654692247430096675956618515402157096729587704200837790737241114391057544023988416298308729088156165478588387530801720105497623534929474858086900811016168667452549940339456963507726869866952489351346556858685554228238904590614694774990313787251171084330038040887517860800596565461605322793000714926466612206041074436975227243635541671019660336858905138102613360939625997125930146785941563735219767997166170433311671324985628094677931281462708855924530290697618310532302769759344377145442027435730400784817595064264420323149188983574396298928909903284380446392347954640), (⟨5, by decide⟩, 562008037552722091312870350153315420992493521810055638455869809504793146545620886883866031155621245986707312148344511132604300688005552458381612782682537624145680878866369384111696883450756374484811147555581753742429572529756751103889582903892057170987118330308811057876795824634262261934339786632387243570499268822100196906860157458720313155265973444591160452182527388211664783913095849629979340900268710689769767301772115639963055147922205397746087341131250015983624842117202479251077268544468663186045464559651799303774043018511900903521321245863111013223657543055838990464776657941488823344203778098653110502175525995330093784460272997608101684635893777306480), (⟨6, by decide⟩, -640408491844171058746900909829744980162412933684939505034740389264287812942240269550251731429476555665953342639242614536788835208039633768417050960833956814639499478127025138890443709014643339527025249668428708729838844506868313285117633634822753154043623968818777370647603685616071326346112080247437381847622333521639339637317579431039972985518241965432455229108200653128729229585709851840504379309652172392061830888141787181023267951457419938618656598535291710891484601405943511130482847758884317092398101973376822518531094964366601882834601558455443492839764974966891147678767070813153488948651304712338229167939679150286836305012464886877205486005961793967280), (⟨7, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360)]
  | 8 => [(⟨0, by decide⟩, 317400984964244713265061281849499798586322425612675695902591676000471987781355094394972066508992084582958922627555609580279377269447361691289056881535555771703217575426538476215666463359511257185978205459897723526081572134793406323874059508243839307512951123208841362420041180716638437598914498769074393151025158138494296015468357440945058895546865058350263105237151437080052643313946571041195337287631396995195395573188758556179990405832887047613180504285223844903928951415415402326140291428945160006048889012301807094170700403127416677157668729138679293019510929953066343012241153113939778634750046849135830523947925835213759381253573362932414803614277454408350), (⟨1, by decide⟩, -327666388213707007633825310380871966183937499540990734543774940138063539713314525649807837123255579473920526744420781675367551276472169441176257362380076108405176877682712946973278858390717614217051929814273063110650601261129994432399216762554749337817680778349497752793811788557277047455606564779656921552341185439814120284630483734570812403140070428286161227374037064572125398659705069192030078699347443561656252566755613725931770670970338294038800466037879113695933006740859634182271126185400633315232710706611103024002721091768653389071657968948282618622416830135805357328585796319860115447173984095747822519521020429737976029146368424548224636773876923512640), (⟨2, by decide⟩, 173232415092330948552822990932779078324385077180720518389013911504854125623424383816566021682909251814179159107959877566469077521435755920943932866291441140239493057145790647320666949411968810555780284233836195972692383465355733913499206137446662448308397793877723130312251156009410538948620671545211600620688476354083330769311374479395843225904125085665669491831564105448035760118340885623087309630477063824869656558685576865804527082316868017055290335254987566135287784112033619820147258833018318700281021658233216648656586052416382385128073030741826100481158136068204467603441232420905652874350914945514306268958516008724569934301191260956588189430359954476280), (⟨3, by decide⟩, 577754731462744654149614014291803941300922769901930020820947408845230684551057993194420286996502756057590888014874804907921612615797075373777701922923513650168150634789767606842048984195179496452753418652973315324715594880115706334737537250472033946120716167032388346326255402758098683741937764892119843295072386689817724661587344061580680149560366462050246939518864937292920195499029937879615065329464852238652059784197501294817229439830446332156236007278308788757168858073519042207752683822668393479509558410192230879869988311924242165001437067050980413433201008110226468171679892237034265498729448720821427314214539143870170482195402052769463825509526162518040), (⟨4, by decide⟩, -1597938440110572730084726069625324838985435631696713853713743998504777710986371021284864778402715713223107108317530792483479062843852611920237141215121123649619333353068593253752842843778069443887541252859464665766978445239797283560254853851574573979930870347601985635566328507229765174107200174659697600417879708525833276041385009618819448200930757376412430246401405759153010098228359360356893882457701120539087551573195077598458978582474073170707384932092513695072316267051656284394623571510809046598206900112723986737441267896974033604992909021188094030863294690077861170176758824249630619590219711027913766747003440925137311666346305190350694933067105352345120), (⟨5, by decide⟩, 608824154279584903363258347044292198772594944662425926500019541635034934093518085424227564474006372051380283839046539059963577879208487454980774768414665587448003314173520899980997019107851420969588093832451753769356169373799091339583648117253929439407729099146774504751256248031825450452054866990709963702912400721632722017710975646017681425326187252687520744214588682714814432813421199886900395790714431603107493315906930754155552464446762714788239703843077061102598687293342321268196147892917562211191946991369864339643712964293076097164654468305738538534969879416143512791257571712600070401478742175539031752715570640541222043850900147561074527305457897435920), (⟨6, by decide⟩, -299944079443428707158852811250515606764758374930262455888408856163947284675873109746394360835636366414198179198222347888145392091487209011763727054128361817153242599309695438245995067352028311707991696148178356696339158200678349838240502964923928270245715330050080129265745106579812026793745863460039687837348228819643477862166141413705089994396616439719738866038449663585810906343521468171166439332212162267014288570676283590540061601019166747202399546163806020328687023119123704110564132201918343567978561158331280752579434027664850037397050043886118109221230554101789937316518821652328171976205984564973017849348509693723228304806547121756667726516030190465040), (⟨7, by decide⟩, 510696618601113527382072147868844060096481838132015573719497299650510792399550739705786055890760283877632745161530399972965164674828637134979985860058392496229385318225994550966672962493922541728550330280375528050249529459284945170315696004848237325696862958153045862072787868554388949328549325181096541015411157052993792662727157026002324486682438288569074544604626484314377484863282575504006909966160015187571313476198255385724809525657379787124385578557228535844196367430229710529878073335448960286629311222568312648927491405052627768156327271853988075427801631297651815543372373741237975458667980221047816977886754184845412000308876647680806639234897405253360)]
  | 9 => [(⟨0, by decide⟩, 254171992096348246799277327712007184662162428823663962441806496648648062893140084775057899852892518304156072854774671429783262628994348244662369479853579185394063411739097397043935861984539888743942582544069757726974582866639477095386002171801542562271450042481094584374037991077401000066350683999918377935753683128273922587317764626239027675940703707968279659954137260042341805007070994144834940137389981813282759260434127646203277416943974256450896114063134844461958832326655776939135258008985111518796078937265679110164239869529721045196131181722921796270391889881332163001688085642317062659596982721696811229496995775455987028970025302421002620082107244734984), (⟨1, by decide⟩, -283018201566147919049813134536790599803013504677835861299550561039526132192418522474664791827570436233016196855910736004391447423321629103321446872247846553123938016563546702544760910406821725174389812132691338947719875032666603478350107521739461801859161664168698715177874524394087697753933135669910659996889409338242807109311607279344192560545788573591786470084272059180528029693534704959991098534231824197673277205836848570801709805694511441171761455378710368547131526257509353254867434672689401392747520040122334639611343057214491544668747761178039062083019877342861408884938628912378687484015956758301776785207695091260372689746069167032296918339928426184064), (⟨2, by decide⟩, 420283867670257745477552990407232230874772789491075930777038069621306502681969875201777021900916906980971117641834983776591180855658091232720830165253603874822924638456018880986907352240795900407752085439788572705355790180967471560511458854890097290335884633512304799905084266025294426372597431460090374345423741491381258099327106557032274256479871168220653936592030927120558518165154207336890123900992279637510575115851906872806355531344473630714816203590362975804798835440270735860127980547492996508512622874770749391736069877668903131029570512504100671979730586581126551547317721554725917248678074089266353091214400023637481779482132507682159905966215578137920), (⟨3, by decide⟩, -728044136132444001755211786632230447653133308049498591079432698543012520293589198570533734656592178528919195754429364209079982312550937750409738569807944862423717587014285804320299610611302221891408789664613075571457862632743376755858713850585980223466816130432422122186275987078324844619443270137657337762029076685675058581550520105496327041573541741269921589518511465826852746268313574849213392935386813237070537028352312736690437534590409081008693066946251254626444059755476787289149499524784356014899294347298254340840097044148634771051467909922938429858904863739110940788167687193403520904554296581988538636754135954764699049873603000611138081861653854636800), (⟨4, by decide⟩, 3322094354176250369079850563072330275582575158435431653814442615861279271862314649578481885733105886546215263402228399066674232665868312857323227080730308436705594621963318915895775975543973668732517788491338322282584709666551244417971280770592198398858576503094020086229520322185299340987480900954467148745806482454786550493463802539939656736950280252960970044890026171149882113903217827719952715686660500569572986035806526265651376614397304224127038660597986559990879638112848614065542218354222300620755050589560834771226185342251997361245062242018036050495706966778167904323505862220856676190074176441027431052334584150005569523231900533872888297430912822519808), (⟨5, by decide⟩, -1443121347211193594961475403440687570377014179238118375223424762339433288774131443233321992147193786502131779351711144458110184022153612285978902584820153612857252155726632144014592269276859267276906038810824329147433561466562274279497348828836913622623860156663989247604587674023670835787412833443601211331684834420098946131689483309068116981072046570425772989194431351702171195059595383933576737261903332951478583298405213567001357753372770290618106589984239651200107742328246287070877551028846289466553501574060144065314733408798952850479232499281937082912141931549614408140284621202021294697443657908509551210606821762462322070905220379504793572955810728939264), (⟨6, by decide⟩, 1121949193827880309816513987825521875019474842389295464764489570887522926377878721078898038019315702583800358306262062814287366046022238066992669156048108677566901901298163400229717821495680768152881832959881518377603043774163378484080849281711003583974804713800881611918090936082238680964445800800354246850066209397386583263910312211797770878284983552760927053451654153054632578540629506882767275722753354745362843835539015284981171348596642897913035572668386176286375152091066536081893664153612160188452970182840017088555573975071015680781235603583599186437744210205616149984838468366163379810833943565117824083362283795628058636404035543508831598001482128631808), (⟨7, by decide⟩, -1736368503243785993099045302754069804328038249648852950646290818811736694158472514999672590028584965183951333549203359908081559894417366258931951924198534487179910081968381473286688072479336641877071122953276795370848400161568813579073366416484006907369334057720355931047478753084922427717067705615728239452397933980178895053272333888407903254720290181134853451655730046668883448535160756713623493884944051637742465819074068311464352387235091276222910967094577021870267649262781015801585449340526464974539658156732263006353470777178934411731512724303559456454525546412016172847466070720209116559471132751562577724814964228474400801050180602114742573398651177861424)]
  | _ => []

def planar_4_16Aw : Fin 8 → ℤ := fun i =>
  match i.val with
  | 0 => 206589584442704248653617001067188960641111673454483218344271812869657380011576156160572553304691014107099945157861374205063120445561491720955396764591238813314308091967652247978411648981469826134174349170063958980977683088600870779936340516443238150983790732360012790927011868398963904046417894024550804497240812718787231853456811203733254244391843189786132998183348847427511408375657123486947984384484479250829129420225976513975979816766209444316983969886595915590006771604699121530482249619656208260387844751766932294590755368700878402866128403466808206410322272247782276157270461842450747248502865119350884005906652412465462453542624967242782601670872092748316773486057810076870031324263835092900420375000000000000000000000
  | 1 => 936151194438830545786260040020693232947700539797609876770386879096668729343506612391145579366645296194867709423142663603911446769390247624822152946238223963173241963382418941011094262770250250788533566599360036814779085475802959320821808071702114389956880775088964749425101043718466928069763155404360501040932970945561850819223452795930355621223240343798329034153233833676326406291623688361691120994749563781376723568063355748687132324274782978753593438000042561828552625387743151571488304838539258259630201681535933545506993232467844457821842460892055030725344511674372896495378641941071204277140318913244954014270704906639360214229425551520847195586427129600489266639743484562331553559687478598678733886718750000000000000
  | 2 => 36531790235195070624933042697683432809881268744304032690438386519373917027782364206709297098887765464811177775580145798440170018807561340981633954189093665848922133475326140467441995856134595022513421124730093801711423909519070870600773565532028816912792389848847043560800477500283879590922637015623118816127214992796536841741457478762182699232490354796614999522516327933064527146356077456515079461086106830932279411173918866504948119758221209222437067266255152713004103937088856192365676376680312350449951064782463066089476470632892671344353233525589085239465039922815619138511098022953431110621707888376520394541091528215077991191356806620504558344903732068067479381726888877831191823443046691295675781250000000000000000
  | 3 => 127308160383821393476655275942312141699229158098843955814279633063920927525869095290021872698211278860974753941806242328113499791216237840042691870206625771176854504867661037654550655356528325076115119673740856291276645262308640805705586423907680888999712788460815886685777714900440397371608198175105766670466373535888621284507315786892148884728322987086460971028755133888946148967596322539215209859700469498415856892356901892570715535906839014297615472519265583669842876476057697400452053309105040043596472940491355458937842820471715391199158890680301461110947494349162837649666160869234055372938600944402760775238147998494515581059312027454992500396705621804101485111756923094457673068133585639729179687500000000000000000
  | 4 => 4174212961354342260517780074964096371808223092548097608053775448424660974336674463067979548634183430391684490495344320721755130102053151044488348271987280256725365803800642291720866553006071936312812505044152685603029031416684942312039998791104375297194994216213996896390373243463937407788811025517683849096172862002832644089792587068559393256586057869582191066580165516612928502421119642551419477127991778148010152542192045081207453484682325810412002732577807144650180082860375864922139702550729465466338913475778763157878987250227441787718737445161209974075193404123553862919036763571098358587291845755150315176653148035806637391920572797255525756607375010759703555986300641650973574890643252922184082031250000000000000
  | 5 => 3461974265742746470222124112867123948049466040185132641085639769125426445734165039430245025352998272701415207181835998774255097469338106785071044823530297180362457493619954466103431808072635902101422274170886557045808527527412402549859220380890936879368094143781194462048321625788104488630274450428471498380184024222178585109803407786646411427082368379087204632307794216503316791526901633040227274027556336827780536057967002924598419481815519407161342091324582684927076781828372166263552338671394678195807127678259436026951503490065911771769852162226587255879940505879607554607976807489356925851771438047966852789359406430693850053145679821480234726315080051804425701896267853298204028783120686554643554687500000000000000
  | 6 => 11377991386955687858057191719609959449411145683554557978902702584927363724007568543130521810486277236289754468281237923225262753607573087069355374706470637071446131391788043339308843063729514445869600696215448227025669321638093945108520882002651580562733791434578863059699385341808264273603122503081500715309626805790402962967114318826035604304561617296423681741664802028695635824212209440571940953866090767463513809123034793066664404904294006118775395178919817509596099384132562418339709904837570852455684408088257719962023508530826449688226731198248316512169577883346606613326528262755082300518261934481554769342450609881007952680568204191931158852674076509660319735857776424220733436862380934314086914062500000000000000
  | 7 => 2824037343023565716176368362473930484222102066325509561796097455213638974983687354476306434526635363257374323884699429005067595647506355372673133123829469880866602919620224482383304878134600444359411577989825211244741850558581147966044178092173822678380855478483708667308403697509718243033484340274948419458901214014135765662378316219320058289416306933052890137275419059891123606673923359700668626535533079558498126590091670659814246273179976999093575945175919202052197850313331109368957656669064863798193211708553327286310638665400192937503192656095005818956117577751448406017285687857196743139762567495735688436301414715991090450431596399962217072937121620583461340558836725125866168456095211165625000000000000000000000
  | _ => 0

def planar_4_16A : Matrix (Fin 10) (Fin 10) ℚ := sparseRatScaledMatrix planar_4_16AD planar_4_16AM

theorem planar_4_16A_gram_check : SparseGramCheck planar_4_16AS planar_4_16AM planar_4_16AR planar_4_16AT planar_4_16Aw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_16A_posSemidef : (planar_4_16A.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_16A_gram_check

/- N=4, d=16, H; dimension=10, rank=8. -/
def planar_4_16HD : ℤ := 8008
def planar_4_16HS : ℤ := 250869060484654785356006758896734064918573881999606066822595224864691908193747377471799639305731058167280679842804953593688659722030990155100041534065912176382818114780811343169969801036100442291976511508241699415236333283862191038760204603946244681589732754277023395181152157562122801570258300270053790773733327100011013678272326075885142675200
def planar_4_16HM : SparseIntMatrix 10 10 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 286465287326400), (⟨1, by decide⟩, -29114414456400), (⟨2, by decide⟩, 18813009196800), (⟨3, by decide⟩, -24654552085800), (⟨4, by decide⟩, 11549671988400), (⟨5, by decide⟩, -16938978638400), (⟨6, by decide⟩, 9775574499600), (⟨7, by decide⟩, -11047734079200), (⟨8, by decide⟩, -9426990900600), (⟨9, by decide⟩, 18990487283040)]
  | 1 => [(⟨0, by decide⟩, -29114414456400), (⟨1, by decide⟩, 17416085491350), (⟨2, by decide⟩, -14427191961000), (⟨3, by decide⟩, 15200186110200), (⟨4, by decide⟩, -10901316985650), (⟨5, by decide⟩, 16465229316900), (⟨6, by decide⟩, -10264963445100), (⟨7, by decide⟩, 13433296722300), (⟨8, by decide⟩, 12547556821800), (⟨9, by decide⟩, -26363268608040)]
  | 2 => [(⟨0, by decide⟩, 18813009196800), (⟨1, by decide⟩, -14427191961000), (⟨2, by decide⟩, 18310097239200), (⟨3, by decide⟩, -11385445617000), (⟨4, by decide⟩, 13258038900600), (⟨5, by decide⟩, -22494358270800), (⟨6, by decide⟩, 11994394464000), (⟨7, by decide⟩, -18858064539600), (⟨8, by decide⟩, -17690182169400), (⟨9, by decide⟩, 38333758619520)]
  | 3 => [(⟨0, by decide⟩, -24654552085800), (⟨1, by decide⟩, 15200186110200), (⟨2, by decide⟩, -11385445617000), (⟨3, by decide⟩, 16245006805125), (⟨4, by decide⟩, -11168568608400), (⟨5, by decide⟩, 16201946583900), (⟨6, by decide⟩, -10593308429550), (⟨7, by decide⟩, 13667486200200), (⟨8, by decide⟩, 12789295282575), (⟨9, by decide⟩, -26745326373780)]
  | 4 => [(⟨0, by decide⟩, 11549671988400), (⟨1, by decide⟩, -10901316985650), (⟨2, by decide⟩, 13258038900600), (⟨3, by decide⟩, -11168568608400), (⟨4, by decide⟩, 12839505027750), (⟨5, by decide⟩, -20779015560300), (⟨6, by decide⟩, 12403233450900), (⟨7, by decide⟩, -19426357502100), (⟨8, by decide⟩, -19031419724400), (⟨9, by decide⟩, 41277188940120)]
  | 5 => [(⟨0, by decide⟩, -16938978638400), (⟨1, by decide⟩, 16465229316900), (⟨2, by decide⟩, -22494358270800), (⟨3, by decide⟩, 16201946583900), (⟨4, by decide⟩, -20779015560300), (⟨5, by decide⟩, 35362773249000), (⟨6, by decide⟩, -19801839718800), (⟨7, by decide⟩, 33050749773000), (⟨8, by decide⟩, 32250140356500), (⟨9, by decide⟩, -70557314637600)]
  | 6 => [(⟨0, by decide⟩, 9775574499600), (⟨1, by decide⟩, -10264963445100), (⟨2, by decide⟩, 11994394464000), (⟨3, by decide⟩, -10593308429550), (⟨4, by decide⟩, 12403233450900), (⟨5, by decide⟩, -19801839718800), (⟨6, by decide⟩, 12796693375500), (⟨7, by decide⟩, -19673631909000), (⟨8, by decide⟩, -19491819295050), (⟨9, by decide⟩, 42329815322760)]
  | 7 => [(⟨0, by decide⟩, -11047734079200), (⟨1, by decide⟩, 13433296722300), (⟨2, by decide⟩, -18858064539600), (⟨3, by decide⟩, 13667486200200), (⟨4, by decide⟩, -19426357502100), (⟨5, by decide⟩, 33050749773000), (⟨6, by decide⟩, -19673631909000), (⟨7, by decide⟩, 33988294579800), (⟨8, by decide⟩, 34157548459800), (⟨9, by decide⟩, -75675533658480)]
  | 8 => [(⟨0, by decide⟩, -9426990900600), (⟨1, by decide⟩, 12547556821800), (⟨2, by decide⟩, -17690182169400), (⟨3, by decide⟩, 12789295282575), (⟨4, by decide⟩, -19031419724400), (⟨5, by decide⟩, 32250140356500), (⟨6, by decide⟩, -19491819295050), (⟨7, by decide⟩, 34157548459800), (⟨8, by decide⟩, 34950114506925), (⟨9, by decide⟩, -77535155291580)]
  | 9 => [(⟨0, by decide⟩, 18990487283040), (⟨1, by decide⟩, -26363268608040), (⟨2, by decide⟩, 38333758619520), (⟨3, by decide⟩, -26745326373780), (⟨4, by decide⟩, 41277188940120), (⟨5, by decide⟩, -70557314637600), (⟨6, by decide⟩, 42329815322760), (⟨7, by decide⟩, -75675533658480), (⟨8, by decide⟩, -77535155291580), (⟨9, by decide⟩, 172937570017968)]
  | _ => []

def planar_4_16HR : SparseIntMatrix 8 10 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320), (⟨1, by decide⟩, -2872538958868782124515262325145443559660580385607497660181719263505507032235904855362130696102292938360755007390570), (⟨2, by decide⟩, 1856163102036395280478949940546048040681619163407120529955483761132270696711697722367989206015472244692510280047840), (⟨3, by decide⟩, -2432511960217424746836424790009665973073831703262896184988164537554884095601209581516107920426265059330316252354165), (⟨4, by decide⟩, 1139534604019537517747039081922155309312882145625118025027585250689652367538529389055151213901864271985192152199670), (⟨5, by decide⟩, -1671264113352414900115991929889856853325392681736346049356438633469558137227101280624262232469194788712267930750920), (⟨6, by decide⟩, 964495392393249017845279614836513134407047529979620963648455137213326801780431999868542997854497354490320797329730), (⟨7, by decide⟩, -1090011499192224275119392140454778688216130986152936034200236170416795155783748556461762101044022297268213662338460), (⟨8, by decide⟩, -930102807577582890000825128357091660038032394479199712051979128242350140417340423119352361971353481921248526106655), (⟨9, by decide⟩, 1873673765623098645546406710527786849951793741535247115874312681136169129014090821508922783115492509209147446643052)]
  | 1 => [(⟨1, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320), (⟨2, by decide⟩, -24467268058046436467424361729909864415152931500205447889712368047209330055912946547842642857141233857307155605505120), (⟨3, by decide⟩, 24817799031679402151719553184593832360508459122195303479442430919775045821973777877056141307386336527496781809006840), (⟨4, by decide⟩, -19017330139996419835477600430282970479197537247792171851545925097822276705682990483825002518216352572308131121294600), (⟨5, by decide⟩, 28824009990682466185791508800906487856847215207218806393606593056923098557592361076930372906407638511344175401559600), (⟨6, by decide⟩, -18125755436121708548676342047775781675276028807343059124178620275776253004056776399809774323687117067251014530676800), (⟨7, by decide⟩, 24067107553415118235579499073816811708700979682624516281195487419365769549778314834434902661379445606431579025946160), (⟨8, by decide⟩, 22657509462421993094727895786982491937907344132308033231564170997212945627043218635416385028842572979817960802489320), (⟨9, by decide⟩, -47767151525451996698669508556789341928572632886932539353144373882088216851625850758496150849478709593056835583155200)]
  | 2 => [(⟨2, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320), (⟨3, by decide⟩, 5539007876876539594422100142671540915574344547965030164385733490108148471114177183030939659980001302130748197459900), (⟨4, by decide⟩, 18472674003570102188702958765750756844118711278090498344855184899962455816494565982327797087473158706170564766122040), (⟨5, by decide⟩, -39034686976531306909198916029377994224030943724994145151561481450736830751767165554340422715412439928520966623868200), (⟨6, by decide⟩, 15065240726984082021142564443048270871603991540020173126781101834297576892669916100747719906222109363093547058147640), (⟨7, by decide⟩, -33857738826421581894477289977830782040117222400053415122468535721793548132406533281045503063640833582902658576224680), (⟨8, by decide⟩, -31877287168439084337695406159006456458430879187496472460692821923328812254180548014745846047839838304077873002440900), (⟨9, by decide⟩, 72172444142609048746871174950864528830510557020523155910924392904701591057412974494864842127830380329553068067394432)]
  | 3 => [(⟨3, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320), (⟨4, by decide⟩, -25120709652403712150832615402321126842866941534356308069561174078649252646110685636590748587257764622112707371649020), (⟨5, by decide⟩, 36013057048606913962935803307857624264855348523356337097459494442950064399779157756573525536414370545273340298191920), (⟨6, by decide⟩, -23369449560496825032031752281109575793174441259134528294801145343588481073798400946010166229735189533345065130227920), (⟨7, by decide⟩, 34826276545786258824459210408101552093887537857954746739599815399229032741101458139238966706260958672308277562820520), (⟨8, by decide⟩, 32850737203308076269545195615515432313493600711799553342601654402273540320369171883504991647778918504421969419401620), (⟨9, by decide⟩, -70017145438972478768722770540083190225955597955375295088740654078172503264171315006060740689488608818073037615127040)]
  | 4 => [(⟨4, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320), (⟨5, by decide⟩, -40755191395893164251312816095840131122327423433362689288270399926700953225991055328603212553009111418725987891533440), (⟨6, by decide⟩, 44767753841335237305009729736608997005458021368421902825031832056346082214485159386405937093483407442574049432122880), (⟨7, by decide⟩, -79471177219864755235057448081203786665776425352958238596136445120597033487590338440547227571851872444613808642456080), (⟨8, by decide⟩, -96732267530340962784407415382989367533897542547331450017891925247997299980796612770796233760787692231526848481066360), (⟨9, by decide⟩, 215451265817022993252215711017618628629605055768195094723942778005074551273949895186613902909801278765373555694570240)]
  | 5 => [(⟨5, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320), (⟨6, by decide⟩, -158949735737867600300050335768433481460465017697328673888711836618725980651131849740900050634495533494769371528320), (⟨7, by decide⟩, 36625457186832293137408640009826883674531639793418693243753392579821386107481924353789119780901613694289134877702800), (⟨8, by decide⟩, 36519490696340381403875273119314594686891329781620474127827584688742235453714503120628519747145283338625955296683920), (⟨9, by decide⟩, -90281551447321086951299291941965371844055559624257852189712305230273034400698142956831012889515036639014269471812608)]
  | 6 => [(⟨6, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320), (⟨7, by decide⟩, -12818483014373387040543009095898119138940981210701244290623095071040121069230664554529190369753117491900622619502200), (⟨8, by decide⟩, 6024020800839825927199572421245179076429604698627214364754252194945607451914554347278661997416785740884339831174680), (⟨9, by decide⟩, -14828919578291444262155771777090619395249480202533991243551253283019346780165919110205095081066100549171266690790848)]
  | 7 => [(⟨7, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320), (⟨8, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320), (⟨9, by decide⟩, -96096769457587386135487165737430820898389988137575139142424471056527215457840616399220047072566506487203308498452088)]
  | _ => []

def planar_4_16HT : SparseIntMatrix 10 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320)]
  | 1 => [(⟨0, by decide⟩, -2872538958868782124515262325145443559660580385607497660181719263505507032235904855362130696102292938360755007390570), (⟨1, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320)]
  | 2 => [(⟨0, by decide⟩, 1856163102036395280478949940546048040681619163407120529955483761132270696711697722367989206015472244692510280047840), (⟨1, by decide⟩, -24467268058046436467424361729909864415152931500205447889712368047209330055912946547842642857141233857307155605505120), (⟨2, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320)]
  | 3 => [(⟨0, by decide⟩, -2432511960217424746836424790009665973073831703262896184988164537554884095601209581516107920426265059330316252354165), (⟨1, by decide⟩, 24817799031679402151719553184593832360508459122195303479442430919775045821973777877056141307386336527496781809006840), (⟨2, by decide⟩, 5539007876876539594422100142671540915574344547965030164385733490108148471114177183030939659980001302130748197459900), (⟨3, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320)]
  | 4 => [(⟨0, by decide⟩, 1139534604019537517747039081922155309312882145625118025027585250689652367538529389055151213901864271985192152199670), (⟨1, by decide⟩, -19017330139996419835477600430282970479197537247792171851545925097822276705682990483825002518216352572308131121294600), (⟨2, by decide⟩, 18472674003570102188702958765750756844118711278090498344855184899962455816494565982327797087473158706170564766122040), (⟨3, by decide⟩, -25120709652403712150832615402321126842866941534356308069561174078649252646110685636590748587257764622112707371649020), (⟨4, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320)]
  | 5 => [(⟨0, by decide⟩, -1671264113352414900115991929889856853325392681736346049356438633469558137227101280624262232469194788712267930750920), (⟨1, by decide⟩, 28824009990682466185791508800906487856847215207218806393606593056923098557592361076930372906407638511344175401559600), (⟨2, by decide⟩, -39034686976531306909198916029377994224030943724994145151561481450736830751767165554340422715412439928520966623868200), (⟨3, by decide⟩, 36013057048606913962935803307857624264855348523356337097459494442950064399779157756573525536414370545273340298191920), (⟨4, by decide⟩, -40755191395893164251312816095840131122327423433362689288270399926700953225991055328603212553009111418725987891533440), (⟨5, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320)]
  | 6 => [(⟨0, by decide⟩, 964495392393249017845279614836513134407047529979620963648455137213326801780431999868542997854497354490320797329730), (⟨1, by decide⟩, -18125755436121708548676342047775781675276028807343059124178620275776253004056776399809774323687117067251014530676800), (⟨2, by decide⟩, 15065240726984082021142564443048270871603991540020173126781101834297576892669916100747719906222109363093547058147640), (⟨3, by decide⟩, -23369449560496825032031752281109575793174441259134528294801145343588481073798400946010166229735189533345065130227920), (⟨4, by decide⟩, 44767753841335237305009729736608997005458021368421902825031832056346082214485159386405937093483407442574049432122880), (⟨5, by decide⟩, -158949735737867600300050335768433481460465017697328673888711836618725980651131849740900050634495533494769371528320), (⟨6, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320)]
  | 7 => [(⟨0, by decide⟩, -1090011499192224275119392140454778688216130986152936034200236170416795155783748556461762101044022297268213662338460), (⟨1, by decide⟩, 24067107553415118235579499073816811708700979682624516281195487419365769549778314834434902661379445606431579025946160), (⟨2, by decide⟩, -33857738826421581894477289977830782040117222400053415122468535721793548132406533281045503063640833582902658576224680), (⟨3, by decide⟩, 34826276545786258824459210408101552093887537857954746739599815399229032741101458139238966706260958672308277562820520), (⟨4, by decide⟩, -79471177219864755235057448081203786665776425352958238596136445120597033487590338440547227571851872444613808642456080), (⟨5, by decide⟩, 36625457186832293137408640009826883674531639793418693243753392579821386107481924353789119780901613694289134877702800), (⟨6, by decide⟩, -12818483014373387040543009095898119138940981210701244290623095071040121069230664554529190369753117491900622619502200), (⟨7, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320)]
  | 8 => [(⟨0, by decide⟩, -930102807577582890000825128357091660038032394479199712051979128242350140417340423119352361971353481921248526106655), (⟨1, by decide⟩, 22657509462421993094727895786982491937907344132308033231564170997212945627043218635416385028842572979817960802489320), (⟨2, by decide⟩, -31877287168439084337695406159006456458430879187496472460692821923328812254180548014745846047839838304077873002440900), (⟨3, by decide⟩, 32850737203308076269545195615515432313493600711799553342601654402273540320369171883504991647778918504421969419401620), (⟨4, by decide⟩, -96732267530340962784407415382989367533897542547331450017891925247997299980796612770796233760787692231526848481066360), (⟨5, by decide⟩, 36519490696340381403875273119314594686891329781620474127827584688742235453714503120628519747145283338625955296683920), (⟨6, by decide⟩, 6024020800839825927199572421245179076429604698627214364754252194945607451914554347278661997416785740884339831174680), (⟨7, by decide⟩, 28263755722819819451613872275714947323055878863992687983066020898978592781717828352711778550754854849177443676015320)]
  | 9 => [(⟨0, by decide⟩, 1873673765623098645546406710527786849951793741535247115874312681136169129014090821508922783115492509209147446643052), (⟨1, by decide⟩, -47767151525451996698669508556789341928572632886932539353144373882088216851625850758496150849478709593056835583155200), (⟨2, by decide⟩, 72172444142609048746871174950864528830510557020523155910924392904701591057412974494864842127830380329553068067394432), (⟨3, by decide⟩, -70017145438972478768722770540083190225955597955375295088740654078172503264171315006060740689488608818073037615127040), (⟨4, by decide⟩, 215451265817022993252215711017618628629605055768195094723942778005074551273949895186613902909801278765373555694570240), (⟨5, by decide⟩, -90281551447321086951299291941965371844055559624257852189712305230273034400698142956831012889515036639014269471812608), (⟨6, by decide⟩, -14828919578291444262155771777090619395249480202533991243551253283019346780165919110205095081066100549171266690790848), (⟨7, by decide⟩, -96096769457587386135487165737430820898389988137575139142424471056527215457840616399220047072566506487203308498452088)]
  | _ => []

def planar_4_16Hw : Fin 8 → ℤ := fun i =>
  match i.val with
  | 0 => 89962054489564021071368217818342149176471587356181535446418579716073886772194874844766844946083978666437141548306458622758227200
  | 1 => 4540129957606681270942553511131314686838119286361788408228219989905176209995275764080034531670544049683738550910461384258792600
  | 2 => 1959780432679088784290594428562036271257401907018837488830418757401134675362946028542210078910869054017200273950959374467379200
  | 3 => 859440595065694098742766830817969916145911936987649836510789697232633486714971065232927596414396980935402024779210355182796800
  | 4 => 314371215764515478170472947091378640646530486478017549822948393432846237824072780947655528639142849870353749619556982141747200
  | 5 => 281863381343866396938926287127725236480507575936534885506173847329778326349196093938285042753377720301263942875589479969587200
  | 6 => 113617811651764028594597877101709163930127286557970795781262438644520598886447595428746133467097854190910792007512039935180800
  | 7 => 148662250179739871289911622406731136905448317498397530201984261118481730216644674298534105764344765235599392418436302766080000
  | _ => 0

def planar_4_16H : Matrix (Fin 10) (Fin 10) ℚ := sparseRatScaledMatrix planar_4_16HD planar_4_16HM

theorem planar_4_16H_gram_check : SparseGramCheck planar_4_16HS planar_4_16HM planar_4_16HR planar_4_16HT planar_4_16Hw := by
  unfold SparseGramCheck
  decide +kernel

theorem planar_4_16H_posSemidef : (planar_4_16H.map (Rat.castHom ℂ)).PosSemidef :=
  sparseGramCheck_scaled_posSemidef (by decide) (by decide)
    (by decide +kernel) planar_4_16H_gram_check

def planar_4_16KD : ℤ := 5497108810350300355932523111827820926285450707226394298992645219873161484332245798749713615117505332963282541014877998624176837626065909732150209921463216589204061908641929115157939426166196827852650001203200000
def planar_4_16KU : SparseIntMatrix 10 2 := fun i =>
  match i.val with
  | 1 => [(⟨0, by decide⟩, -5497108810350300355932523111827820926285450707226394298992645219873161484332245798749713615117505332963282541014877998624176837626065909732150209921463216589204061908641929115157939426166196827852650001203200000), (⟨1, by decide⟩, 6596530572420360427119027734193385111542540848671673158791174263847793781198694958499656338141006399555939049217853598349012205151279091678580251905755859907044874290370314938189527311399436193423180001443840000)]
  | 2 => [(⟨0, by decide⟩, -5497108810350300355932523111827820926285450707226394298992645219873161484332245798749713615117505332963282541014877998624176837626065909732150209921463216589204061908641929115157939426166196827852650001203200000), (⟨1, by decide⟩, 5497108810350300355932523111827820926285450707226394298992645219873161484332245798749713615117505332963282541014877998624176837626065909732150209921463216589204061908641929115157939426166196827852650001203200000)]
  | 3 => [(⟨0, by decide⟩, 5497108810350300355932523111827820926285450707226394298992645219873161484332245798749713615117505332963282541014877998624176837626065909732150209921463216589204061908641929115157939426166196827852650001203200000), (⟨1, by decide⟩, -6596530572420360427119027734193385111542540848671673158791174263847793781198694958499656338141006399555939049217853598349012205151279091678580251905755859907044874290370314938189527311399436193423180001443840000)]
  | 4 => [(⟨0, by decide⟩, 9161848017250500593220871853046368210475751178710657164987742033121935807220409664582856025195842221605470901691463331040294729376776516220250349869105360982006769847736548525263232376943661379754416668672000000), (⟨1, by decide⟩, -16857800351740921091526404209605317507275382168827609183577445340944361885285553782832455086360349687754066459112292529114142302053268789845260643759153864206892456519835249286484347573576336938748126670356480000)]
  | 5 => [(⟨1, by decide⟩, -6596530572420360427119027734193385111542540848671673158791174263847793781198694958499656338141006399555939049217853598349012205151279091678580251905755859907044874290370314938189527311399436193423180001443840000)]
  | 6 => [(⟨0, by decide⟩, -3664739206900200237288348741218547284190300471484262865995096813248774322888163865833142410078336888642188360676585332416117891750710606488100139947642144392802707939094619410105292950777464551901766667468800000), (⟨1, by decide⟩, 11360691541390620735593881097777496580989931461601214884584800121071200400953307984082741471242844354790783918097414530489965464427202880113110433837690647617688394611193320171326408147410140110895476669153280000)]
  | 7 => [(⟨0, by decide⟩, -5497108810350300355932523111827820926285450707226394298992645219873161484332245798749713615117505332963282541014877998624176837626065909732150209921463216589204061908641929115157939426166196827852650001203200000), (⟨1, by decide⟩, 18690169955191021210170578580214591149370532404569740616574993747568749046729635715749026291399518132075160639450585195322201247928624093089310713732974936403293810489382558991536994048965069214699010004090880000)]
  | 8 => [(⟨0, by decide⟩, 5497108810350300355932523111827820926285450707226394298992645219873161484332245798749713615117505332963282541014877998624176837626065909732150209921463216589204061908641929115157939426166196827852650001203200000)]
  | 9 => [(⟨1, by decide⟩, 5497108810350300355932523111827820926285450707226394298992645219873161484332245798749713615117505332963282541014877998624176837626065909732150209921463216589204061908641929115157939426166196827852650001203200000)]
  | _ => []

def planar_4_16KL : SparseIntMatrix 2 10 := fun i =>
  match i.val with
  | 0 => [(⟨8, by decide⟩, 1)]
  | 1 => [(⟨9, by decide⟩, 1)]
  | _ => []

def planar_4_16KVA : SparseIntMatrix 10 10 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 27633176842459671816447793227059445366177246908330795439750065429428134463166343115102764457940408637810597829292019560922105452455474194692795652859176276590908099821935001600), (⟨1, by decide⟩, 71418381962012088834103946476572886204858227412835284562705124997935159765598639514921237641171450133340314237751083628538515735391940507260892498725691036604745392049461657600), (⟨2, by decide⟩, 17448799773912310048729674719303595425697669803637697269920351077411818865484354554231360488556350232095085236190716112485222790575887483031867115325347548093641785173879029760), (⟨3, by decide⟩, 10466043029728808258702797434178860551925127171788794508975347772462129569602031633473579454144002290884117420853968239024376356839394263875030501304284984974090221715351142400), (⟨4, by decide⟩, 44729496113127783553072254840592457338695219282337370445037497226558802142915263068144212488207893224695665424617175002983429577221393008499691706441052234222712729775961538560), (⟨5, by decide⟩, 25443868926500041277324347444481450462711922528125848169838343617193885490364615258514865963803753026581938548856162590381461772765157645709223188670051495887592541806888222720), (⟨6, by decide⟩, 41683197358098063140395876913561420667871663229124819414465535898778565534891823005359079203312251436011163174887137172833861941392453159941689198830973459399624213827923476480), (⟨7, by decide⟩, 11187210323055327569064312094830581968366653216621189203932084467028573662733985948703171081868602049647270706693914597444566953962641198569995267975076830903854484923036467200)]
  | 1 => [(⟨0, by decide⟩, 71418381962012088834103946476572886204858227412835284562705124997935159765598639514921237641171450133340314237751083628538515735391940507260892498725691036604745392049461657600), (⟨1, by decide⟩, 13227116254342040069059561456663216118275648541961596154903347101483292111345958432379913302808702968669168562883344855745095196107403928672830980257845285059574758010652427550720), (⟨2, by decide⟩, 10568755554022208840911211131653625292241128167921090453868767843547388329188519320517994159829081667740926045406627147534861587624548172129926891610068081754479440850664753725440), (⟨3, by decide⟩, -11598575733709264042478646722566889325566957207684576424870489652563446368255136730443852817920533525015191040926971342525625996962091548261234345838432856121798402744188529541120), (⟨4, by decide⟩, -546945731313385525358842773121963187492634786706163780405170410122801453441808764782858811528765668486347560606540770961843024250364801341690623883775467285912243048020422164480), (⟨5, by decide⟩, 7919845400480501898624145135444875892920334484250608196980830526488793036718839723732505811177393043468151598277639530064097573894971702556117032059823203475835008553202671943680), (⟨6, by decide⟩, -3337612355086074649348519272501038412769782371018881362896548156454974905904928828178708237512089738321134076393267448932517419693474362348361164076699630632161057405413789532160), (⟨7, by decide⟩, -4570926297509855668382347435769905815357961573524781902758927572638315040467869734224026948610867900706148806480483541745491778285856767104289188349492530254428294409128184381440)]
  | 2 => [(⟨0, by decide⟩, 17448799773912310048729674719303595425697669803637697269920351077411818865484354554231360488556350232095085236190716112485222790575887483031867115325347548093641785173879029760), (⟨1, by decide⟩, 10568755554022208840911211131653625292241128167921090453868767843547388329188519320517994159829081667740926045406627147534861587624548172129926891610068081754479440850664753725440), (⟨2, by decide⟩, 9984869018097046201339146986536823776034620265798738908026538209378140336824350545255817318013181805727654431218338445261199967806531548369188455795347736241296192317536375668736), (⟨3, by decide⟩, -9194610530613451239416900165404726846129790379923761237625233043357090126786731666265614605063910117998585911645937953577519130393192635979783518000647702713182915905229516963840), (⟨4, by decide⟩, 4514605030889004727221170020487874084926606008418620330212894117148219000608780890628429163747824408503259203210627653111372105134422047443635824269286265222843163632913755406336), (⟨5, by decide⟩, 9768039050570885949303777265261921659574254692254442006463768023330215069947835693003869132583162114530418659873563184776514217265812365873374668578776992262262248825344934019072), (⟨6, by decide⟩, -6286448167647682749748522492666730442161966120936985832117613605023873231426185549269850053257741598521407391511609041411186712820789188049302587934469540069661947171008877166592), (⟨7, by decide⟩, -5428778568564381191323933829674425563780472221796109412369971322092138746741727025523043326208296624552371061500719655188270654414483057174274088028538878954014227309325126205440)]
  | 3 => [(⟨0, by decide⟩, 10466043029728808258702797434178860551925127171788794508975347772462129569602031633473579454144002290884117420853968239024376356839394263875030501304284984974090221715351142400), (⟨1, by decide⟩, -11598575733709264042478646722566889325566957207684576424870489652563446368255136730443852817920533525015191040926971342525625996962091548261234345838432856121798402744188529541120), (⟨2, by decide⟩, -9194610530613451239416900165404726846129790379923761237625233043357090126786731666265614605063910117998585911645937953577519130393192635979783518000647702713182915905229516963840), (⟨3, by decide⟩, 11975371298273725186635421133722163822946317340784658915534684934655400320594667649389461634280837492757281677964589551073729546847746963069404299602505935345762905538266943979520), (⟨4, by decide⟩, 3663037493617656426255068381087191387796894855219840633485901785815494407222204807588070361293246378210679560914233554754157383544279938137610583129087299518164201671160737300480), (⟨5, by decide⟩, -6120303124169410060451039256088875037473838172968749404655903833929520997982970429858618947739244470404157662624778806474719855162612025190217955790470054430183205510293886074880), (⟨6, by decide⟩, 3966512515133736479811302165278127128903051601419424042636534367881686097139805580250954450293426415497279094751272569008790510579683938029708794962438881208744359684441961922560), (⟨7, by decide⟩, 4960990563657169961062820966415091403333587717819482850345414193130875623007175077150811264274526332144263032687439622406139958163794382615688694851637318079832667748831581962240)]
  | 4 => [(⟨0, by decide⟩, 44729496113127783553072254840592457338695219282337370445037497226558802142915263068144212488207893224695665424617175002983429577221393008499691706441052234222712729775961538560), (⟨1, by decide⟩, -546945731313385525358842773121963187492634786706163780405170410122801453441808764782858811528765668486347560606540770961843024250364801341690623883775467285912243048020422164480), (⟨2, by decide⟩, 4514605030889004727221170020487874084926606008418620330212894117148219000608780890628429163747824408503259203210627653111372105134422047443635824269286265222843163632913755406336), (⟨3, by decide⟩, 3663037493617656426255068381087191387796894855219840633485901785815494407222204807588070361293246378210679560914233554754157383544279938137610583129087299518164201671160737300480), (⟨4, by decide⟩, 33936634279849948765305176602187846185464929548343125004389873267575041454661174470169097060963779379543545203942120265313006969726858352959517378032461128401435061755644955590656), (⟨5, by decide⟩, 22051417454474035205736359571699513030707509432101366386280007519483805376873287864775992296214106092316320298542946299906204689291861234942035440632727961964238123793128695529472), (⟨6, by decide⟩, -14120311554407848088729796430802510421282919576290871207002471398800332734798702348292298259974780113011220623020975115158634326008883029055417969020898760733154064967445210202112), (⟨7, by decide⟩, -9031214698010596633990335479434658883554919720898571593941707094156406691356256669891929972053682887423079878474954266314330259023255896842044464474488293447460246953616474112000)]
  | 5 => [(⟨0, by decide⟩, 25443868926500041277324347444481450462711922528125848169838343617193885490364615258514865963803753026581938548856162590381461772765157645709223188670051495887592541806888222720), (⟨1, by decide⟩, 7919845400480501898624145135444875892920334484250608196980830526488793036718839723732505811177393043468151598277639530064097573894971702556117032059823203475835008553202671943680), (⟨2, by decide⟩, 9768039050570885949303777265261921659574254692254442006463768023330215069947835693003869132583162114530418659873563184776514217265812365873374668578776992262262248825344934019072), (⟨3, by decide⟩, -6120303124169410060451039256088875037473838172968749404655903833929520997982970429858618947739244470404157662624778806474719855162612025190217955790470054430183205510293886074880), (⟨4, by decide⟩, 22051417454474035205736359571699513030707509432101366386280007519483805376873287864775992296214106092316320298542946299906204689291861234942035440632727961964238123793128695529472), (⟨5, by decide⟩, 20776976350164015488948330286773288651586602493442811626926345768746682904044165636255732079660377549134312340762001003262772999487073107754701013738911461562029499147476736671744), (⟨6, by decide⟩, -13878550979211564076717375351804912461885957030059778911389879595063109443270880532019486687078658835249629288573965049442154273973477195346788212280616586215277781784855559798784), (⟨7, by decide⟩, -10835826321689429767338224985243812113824474596813817992099996793926281409565915133706005827542994570885750279897043228261206043335952324471588013806910643022125292308063458426880)]
  | 6 => [(⟨0, by decide⟩, 41683197358098063140395876913561420667871663229124819414465535898778565534891823005359079203312251436011163174887137172833861941392453159941689198830973459399624213827923476480), (⟨1, by decide⟩, -3337612355086074649348519272501038412769782371018881362896548156454974905904928828178708237512089738321134076393267448932517419693474362348361164076699630632161057405413789532160), (⟨2, by decide⟩, -6286448167647682749748522492666730442161966120936985832117613605023873231426185549269850053257741598521407391511609041411186712820789188049302587934469540069661947171008877166592), (⟨3, by decide⟩, 3966512515133736479811302165278127128903051601419424042636534367881686097139805580250954450293426415497279094751272569008790510579683938029708794962438881208744359684441961922560), (⟨4, by decide⟩, -14120311554407848088729796430802510421282919576290871207002471398800332734798702348292298259974780113011220623020975115158634326008883029055417969020898760733154064967445210202112), (⟨5, by decide⟩, -13878550979211564076717375351804912461885957030059778911389879595063109443270880532019486687078658835249629288573965049442154273973477195346788212280616586215277781784855559798784), (⟨6, by decide⟩, 15498962011169897061495451672458472104574749133514905451690358719800756478596157585406523819803589558090219421940141568237857449167744187641243414838652001277802584681103694495744), (⟨7, by decide⟩, 10674806823583029651377996419710737632207854492536035594516699149282652670664097419222235930546843982362752799269555347017869241970433772182233529162213999128778060902649865175040)]
  | 7 => [(⟨0, by decide⟩, 11187210323055327569064312094830581968366653216621189203932084467028573662733985948703171081868602049647270706693914597444566953962641198569995267975076830903854484923036467200), (⟨1, by decide⟩, -4570926297509855668382347435769905815357961573524781902758927572638315040467869734224026948610867900706148806480483541745491778285856767104289188349492530254428294409128184381440), (⟨2, by decide⟩, -5428778568564381191323933829674425563780472221796109412369971322092138746741727025523043326208296624552371061500719655188270654414483057174274088028538878954014227309325126205440), (⟨3, by decide⟩, 4960990563657169961062820966415091403333587717819482850345414193130875623007175077150811264274526332144263032687439622406139958163794382615688694851637318079832667748831581962240), (⟨4, by decide⟩, -9031214698010596633990335479434658883554919720898571593941707094156406691356256669891929972053682887423079878474954266314330259023255896842044464474488293447460246953616474112000), (⟨5, by decide⟩, -10835826321689429767338224985243812113824474596813817992099996793926281409565915133706005827542994570885750279897043228261206043335952324471588013806910643022125292308063458426880), (⟨6, by decide⟩, 10674806823583029651377996419710737632207854492536035594516699149282652670664097419222235930546843982362752799269555347017869241970433772182233529162213999128778060902649865175040), (⟨7, by decide⟩, 8512672487095107742414331352435611881619386507518503901698568271985027356396604820665314511673203010783840025146136680904228917399706205644156283851778110784402494739775467028480)]
  | _ => []

def planar_4_16KVH : SparseIntMatrix 10 10 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 24201121144521534001637724784353215820149625013537777330250867492725159011598203062363093826150025251991085380120377614030599201467103160910778444275438340795998838600044475147187066433785084297625), (⟨1, by decide⟩, 64592422659269885988926357934906651527250041992045360225799731413970223324252901323372460158697777576487742406564431113422762891269342152945631457259988551305531421234039942602192620138667297597900), (⟨2, by decide⟩, 17754767605402159725707757335280778129859444016716157096701261970333539517803902063627718302810608833145308931917297370400428586609833966622129487418138461604529163264307597431028149336731179087450), (⟨3, by decide⟩, 7161740524931563459176911757970896337094991870779622685243929939252245690233036133357435069035858014473394672159972711614437586534959258026010399027620199624480879199676210230677177380145819058100), (⟨4, by decide⟩, 36231280682532187567090049556915744360771504543609700943263658202510564662569747878462137070284316887644671651824819727902839926342894099967465732808305913690632060669681236236555440285392221316300), (⟨5, by decide⟩, 23823286200549053614502712881266753229799994932090998719053236946237609856537677121007118022601251256730073182906751031060439234214762463802036698353289694195115660598769184969861820359172517664500), (⟨6, by decide⟩, 37642712977611135146241408907373672879529049191280351160137078768040615445910941067346123582208244242355991565297915873036691643633117707122588589256007191922945773951863853833441177893343251932250), (⟨7, by decide⟩, 8639714288236757847447039676049665798538898140662072779792054670746295281266061234221302401923444023243047245441531727456502659270893754197410755082062635603811980356661470851270336130200551724450)]
  | 1 => [(⟨0, by decide⟩, 64592422659269885988926357934906651527250041992045360225799731413970223324252901323372460158697777576487742406564431113422762891269342152945631457259988551305531421234039942602192620138667297597900), (⟨1, by decide⟩, 24551739924905721379890101355176999333222855638090218930462348059911196455122885376323630391115466487627346405801852255307613387847201779377539100535882260374913579339407880172500995253546548168132880), (⟨2, by decide⟩, 24939035692301294822230522521432768247993665157735517627342932143395590810210600815651429946442802462678134269204401447005027016795523294339590097521754478815455800416903979489176270613167670201387640), (⟨3, by decide⟩, -22866875240248542946438560869445592764967607458932352236668511421057168523847450844324506138290272873452806966843816042529667213869069960961389669471273458577026545970799380603534839851740826304849680), (⟨4, by decide⟩, -19135573495186362238256791532537695596190193460245615050409324087664721454332087937448216936551181423243832896449714933375772138565874205729317731268112193870901932617445186956274634173461921886425840), (⟨5, by decide⟩, 16700157148501163459156437333370414365940026100496182483882334683786018167918453434026183015009594928005892720919296265934217372610821420950560091884357175310776158555589120259434049116365743902242800), (⟨6, by decide⟩, 4287040465700229388897231000404399415713537231829883200176355713979945663418505065146375781878772962236713920250919330297618538083162231692290614096666315852949274496367568512660721540339815781921400), (⟨7, by decide⟩, -11345320987667891309982635801442981869217257095594706819715528976765079387684225142949436024105685485012243680016828701147835441523727613791616586339926126394979899592066413249878860087395835489368360)]
  | 2 => [(⟨0, by decide⟩, 17754767605402159725707757335280778129859444016716157096701261970333539517803902063627718302810608833145308931917297370400428586609833966622129487418138461604529163264307597431028149336731179087450), (⟨1, by decide⟩, 24939035692301294822230522521432768247993665157735517627342932143395590810210600815651429946442802462678134269204401447005027016795523294339590097521754478815455800416903979489176270613167670201387640), (⟨2, by decide⟩, 27711755691658077782679414348228596299878602287211060552137725416597714159553695979072110331180007578430697950676589716717857876235360402193000514976566605434167306755349792619363945139692942931780420), (⟨3, by decide⟩, -23422813964385791154128323210529441781854952166225261200218659025375174663774862420301001640206428084533615161265749924967033663382837316247850167508019912297210015207381462974685200006559358496562040), (⟨4, by decide⟩, -18609473745376474315016644464756933255529561988043656869954882569464842737535170885872372190238504740220627201794676344609407553305671319703094841279024279830540861998325279041840836740948929671792520), (⟨5, by decide⟩, 20363406639602909478339813422484947252373525325244373819091694169814853770901636352299939963008780545359684600521858549811494952064722282424516248176507527530564106367518728416118950947267411162203400), (⟨6, by decide⟩, 3214300088284925247135153709887671132021581988957076069017320320107162207298146474919173180515836283979672907161470636775340994487992279745243287424672792715981558681361241922694188839776343462309700), (⟨7, by decide⟩, -13634089286520880216325814264117163282772719003421666883158055556269909646379536003559165461810198195153914079178760280634695798488847239913346052382011431460376381691902866868303985609038676360249580)]
  | 3 => [(⟨0, by decide⟩, 7161740524931563459176911757970896337094991870779622685243929939252245690233036133357435069035858014473394672159972711614437586534959258026010399027620199624480879199676210230677177380145819058100), (⟨1, by decide⟩, -22866875240248542946438560869445592764967607458932352236668511421057168523847450844324506138290272873452806966843816042529667213869069960961389669471273458577026545970799380603534839851740826304849680), (⟨2, by decide⟩, -23422813964385791154128323210529441781854952166225261200218659025375174663774862420301001640206428084533615161265749924967033663382837316247850167508019912297210015207381462974685200006559358496562040), (⟨3, by decide⟩, 22943416752501306830893714920726281199350749900559439844234928802841907189067543830732458404496172505204015940921637440498859404923186080763991279637470071345312380601425662258795563978829976282334480), (⟨4, by decide⟩, 21492546337043880540124164068961332488346644779973297224264138297477636055277988299632064119458047304549236259171374099581245770316571307821616037286626615039454206148144575895881880020582577862784240), (⟨5, by decide⟩, -14929418443389383971969241512939945092354206307720041649839498439165604064580237944712402362141535116881093087329053841143788121778397631347071082734747105130090462934395627388425071753898216934242800), (⟨6, by decide⟩, -3592468929172248511959283013411992619467348753559300114485876842449787491903080780637207358979033583406568517426295655006993613988784727784768680472617337456105413616946547785891159215114541740737400), (⟨7, by decide⟩, 11540512032870841629126506427471726573083768677128945831255529436221853555660335599591873643588166485050737839172930145934516420947892905059392233263170848408290124269317926770091044927012462160081960)]
  | 4 => [(⟨0, by decide⟩, 36231280682532187567090049556915744360771504543609700943263658202510564662569747878462137070284316887644671651824819727902839926342894099967465732808305913690632060669681236236555440285392221316300), (⟨1, by decide⟩, -19135573495186362238256791532537695596190193460245615050409324087664721454332087937448216936551181423243832896449714933375772138565874205729317731268112193870901932617445186956274634173461921886425840), (⟨2, by decide⟩, -18609473745376474315016644464756933255529561988043656869954882569464842737535170885872372190238504740220627201794676344609407553305671319703094841279024279830540861998325279041840836740948929671792520), (⟨3, by decide⟩, 21492546337043880540124164068961332488346644779973297224264138297477636055277988299632064119458047304549236259171374099581245770316571307821616037286626615039454206148144575895881880020582577862784240), (⟨4, by decide⟩, 56562617691331991870872607421698653120961652932137768249492207120729576853972161988754880020898471635175543589494297988120605833415908937594025938737165008688989070256836276214595171167239701043663120), (⟨5, by decide⟩, 5264751530857156380891429510896265275582927083184257582193816618324554254662136458492628255765031467268875700163327489993830749083894147077422643080547912868423143534000619101956442440628781970543600), (⟨6, by decide⟩, -22739588664103478666473426759662212484030264044183279188191438248923416350774958131021103222207377492562491654919349526932861559065287425366024167312156848337896737462118790132431864268738447962808200), (⟨7, by decide⟩, 2653787837785426672022667970381531890805031782827782079029271853019048755326959941319954080437282061298521793212533217362151891917674454939507386047514701227239342569457430859825541899961639738379480)]
  | 5 => [(⟨0, by decide⟩, 23823286200549053614502712881266753229799994932090998719053236946237609856537677121007118022601251256730073182906751031060439234214762463802036698353289694195115660598769184969861820359172517664500), (⟨1, by decide⟩, 16700157148501163459156437333370414365940026100496182483882334683786018167918453434026183015009594928005892720919296265934217372610821420950560091884357175310776158555589120259434049116365743902242800), (⟨2, by decide⟩, 20363406639602909478339813422484947252373525325244373819091694169814853770901636352299939963008780545359684600521858549811494952064722282424516248176507527530564106367518728416118950947267411162203400), (⟨3, by decide⟩, -14929418443389383971969241512939945092354206307720041649839498439165604064580237944712402362141535116881093087329053841143788121778397631347071082734747105130090462934395627388425071753898216934242800), (⟨4, by decide⟩, 5264751530857156380891429510896265275582927083184257582193816618324554254662136458492628255765031467268875700163327489993830749083894147077422643080547912868423143534000619101956442440628781970543600), (⟨5, by decide⟩, 25548144317602986480557199183214002109193005450770269965889418765420291295101048559209594881600553706794452675011723509131748385832925320142518974654678052546321377370309000687175028046359448196618000), (⟨6, by decide⟩, -6725777323150749362663925457167485902110148993443680834328645126621377215630109649809942942641868032099280244697468356709697987183620836230027835728788117260170225626845617136251024299046522307339000), (⟨7, by decide⟩, -15018222273929469259474216674192283805095059560456944692995974227156297012691285501384631515294447712657578421176466882911883852169409968934642076002996748984087356273210660613562664305200276973408600)]
  | 6 => [(⟨0, by decide⟩, 37642712977611135146241408907373672879529049191280351160137078768040615445910941067346123582208244242355991565297915873036691643633117707122588589256007191922945773951863853833441177893343251932250), (⟨1, by decide⟩, 4287040465700229388897231000404399415713537231829883200176355713979945663418505065146375781878772962236713920250919330297618538083162231692290614096666315852949274496367568512660721540339815781921400), (⟨2, by decide⟩, 3214300088284925247135153709887671132021581988957076069017320320107162207298146474919173180515836283979672907161470636775340994487992279745243287424672792715981558681361241922694188839776343462309700), (⟨3, by decide⟩, -3592468929172248511959283013411992619467348753559300114485876842449787491903080780637207358979033583406568517426295655006993613988784727784768680472617337456105413616946547785891159215114541740737400), (⟨4, by decide⟩, -22739588664103478666473426759662212484030264044183279188191438248923416350774958131021103222207377492562491654919349526932861559065287425366024167312156848337896737462118790132431864268738447962808200), (⟨5, by decide⟩, -6725777323150749362663925457167485902110148993443680834328645126621377215630109649809942942641868032099280244697468356709697987183620836230027835728788117260170225626845617136251024299046522307339000), (⟨6, by decide⟩, 17582661281878688275693276061020338597249524378166122624733058579523071361411601305259878239265794923517228384363405746173499317323330546988434686235526371657577054009618367305712641570153436618226500), (⟨7, by decide⟩, 5266568706240899710333650787242034927296297298569201396884355137322546939287859994317967931987030615297034428327352169634143518133423197590783035324009152224112768997599914730561415165360393389095700)]
  | 7 => [(⟨0, by decide⟩, 8639714288236757847447039676049665798538898140662072779792054670746295281266061234221302401923444023243047245441531727456502659270893754197410755082062635603811980356661470851270336130200551724450), (⟨1, by decide⟩, -11345320987667891309982635801442981869217257095594706819715528976765079387684225142949436024105685485012243680016828701147835441523727613791616586339926126394979899592066413249878860087395835489368360), (⟨2, by decide⟩, -13634089286520880216325814264117163282772719003421666883158055556269909646379536003559165461810198195153914079178760280634695798488847239913346052382011431460376381691902866868303985609038676360249580), (⟨3, by decide⟩, 11540512032870841629126506427471726573083768677128945831255529436221853555660335599591873643588166485050737839172930145934516420947892905059392233263170848408290124269317926770091044927012462160081960), (⟨4, by decide⟩, 2653787837785426672022667970381531890805031782827782079029271853019048755326959941319954080437282061298521793212533217362151891917674454939507386047514701227239342569457430859825541899961639738379480), (⟨5, by decide⟩, -15018222273929469259474216674192283805095059560456944692995974227156297012691285501384631515294447712657578421176466882911883852169409968934642076002996748984087356273210660613562664305200276973408600), (⟨6, by decide⟩, 5266568706240899710333650787242034927296297298569201396884355137322546939287859994317967931987030615297034428327352169634143518133423197590783035324009152224112768997599914730561415165360393389095700), (⟨7, by decide⟩, 11612373417644729425150165938023729280051049278192749814031314637525133603880715147519237531613583152618285540558601172601782028884323348510942490901354556256262141215909486546082001710576991773616420)]
  | _ => []

def planar_4_16U : Matrix (Fin 10) (Fin 2) ℚ := sparseRatScaledMatrix planar_4_16KD planar_4_16KU
def planar_4_16L : Matrix (Fin 2) (Fin 10) ℚ := sparseRatMatrix planar_4_16KL

def planar_4_16AV : Matrix (Fin 10) (Fin 10) ℚ :=
  ((planar_4_16AD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_16KD planar_4_16KVA

theorem planar_4_16A_kernel_check : SparseScaledFrameCheck planar_4_16KD planar_4_16AM planar_4_16KU planar_4_16KL planar_4_16KVA := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_16A_kernel_frame : HasKernelFrame planar_4_16A planar_4_16U planar_4_16L planar_4_16AV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_16KD≠0) planar_4_16A_kernel_check).scale_matrix
    (by norm_num [planar_4_16AD])

theorem planar_4_16A_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_16A.map (Rat.castHom ℂ)).mulVecLin)=2 :=
  kernelFrame_finrank planar_4_16A_kernel_frame.ratCast

def planar_4_16HV : Matrix (Fin 10) (Fin 10) ℚ :=
  ((planar_4_16HD : ℚ)⁻¹)⁻¹ • sparseRatScaledMatrix planar_4_16KD planar_4_16KVH

theorem planar_4_16H_kernel_check : SparseScaledFrameCheck planar_4_16KD planar_4_16HM planar_4_16KU planar_4_16KL planar_4_16KVH := by
  unfold SparseScaledFrameCheck
  decide +kernel

theorem planar_4_16H_kernel_frame : HasKernelFrame planar_4_16H planar_4_16U planar_4_16L planar_4_16HV :=
  (sparseScaledFrameCheck_sound (by decide : planar_4_16KD≠0) planar_4_16H_kernel_check).scale_matrix
    (by norm_num [planar_4_16HD])

theorem planar_4_16H_kernel_finrank : Module.finrank ℂ (LinearMap.ker (planar_4_16H.map (Rat.castHom ℂ)).mulVecLin)=2 :=
  kernelFrame_finrank planar_4_16H_kernel_frame.ratCast

theorem planar_4_16_same_kernel (v : Fin 10 → ℂ) :
    (planar_4_16A.map (Rat.castHom ℂ)) *ᵥ v=0 ↔ (planar_4_16H.map (Rat.castHom ℂ)) *ᵥ v=0 :=
  kernelFrame_same_kernel planar_4_16A_kernel_frame.ratCast planar_4_16H_kernel_frame.ratCast v

def planar_4_16WS : SparseIntMatrix 10 8 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 1)]
  | 1 => [(⟨1, by decide⟩, 1)]
  | 2 => [(⟨2, by decide⟩, 1)]
  | 3 => [(⟨3, by decide⟩, 1)]
  | 4 => [(⟨4, by decide⟩, 1)]
  | 5 => [(⟨5, by decide⟩, 1)]
  | 6 => [(⟨6, by decide⟩, 1)]
  | 7 => [(⟨7, by decide⟩, 1)]
  | _ => []

def planar_4_16RS : SparseIntMatrix 8 10 := fun i =>
  match i.val with
  | 0 => [(⟨0, by decide⟩, 15)]
  | 1 => [(⟨1, by decide⟩, 15), (⟨8, by decide⟩, 15), (⟨9, by decide⟩, -18)]
  | 2 => [(⟨2, by decide⟩, 15), (⟨8, by decide⟩, 15), (⟨9, by decide⟩, -15)]
  | 3 => [(⟨3, by decide⟩, 15), (⟨8, by decide⟩, -15), (⟨9, by decide⟩, 18)]
  | 4 => [(⟨4, by decide⟩, 15), (⟨8, by decide⟩, -25), (⟨9, by decide⟩, 46)]
  | 5 => [(⟨5, by decide⟩, 15), (⟨9, by decide⟩, 18)]
  | 6 => [(⟨6, by decide⟩, 15), (⟨8, by decide⟩, 10), (⟨9, by decide⟩, -31)]
  | 7 => [(⟨7, by decide⟩, 15), (⟨8, by decide⟩, 15), (⟨9, by decide⟩, -51)]
  | _ => []

def planar_4_16W : Matrix (Fin 10) (Fin 8) ℚ := sparseRatMatrix planar_4_16WS
def planar_4_16R : Matrix (Fin 8) (Fin 10) ℚ := sparseRatScaledMatrix 15 planar_4_16RS

theorem planar_4_16_complement : HasComplement planar_4_16U planar_4_16L planar_4_16W planar_4_16R := by
  unfold HasComplement
  decide +kernel

theorem planar_4_16A_active_posDef :
    ((planar_4_16W.map (Rat.castHom ℂ))ᴴ * (planar_4_16A.map (Rat.castHom ℂ)) * (planar_4_16W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_16A_kernel_frame.ratCast planar_4_16A_posSemidef _ _
    ((planar_4_16_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_16_complement.map (Rat.castHom ℂ)).2.2)

theorem planar_4_16H_active_posDef :
    ((planar_4_16W.map (Rat.castHom ℂ))ᴴ * (planar_4_16H.map (Rat.castHom ℂ)) * (planar_4_16W.map (Rat.castHom ℂ))).PosDef :=
  kernelFrame_complement_posDef planar_4_16H_kernel_frame.ratCast planar_4_16H_posSemidef _ _
    ((planar_4_16_complement.map (Rat.castHom ℂ)).2.1) ((planar_4_16_complement.map (Rat.castHom ℂ)).2.2)

end BosonicLaughlin

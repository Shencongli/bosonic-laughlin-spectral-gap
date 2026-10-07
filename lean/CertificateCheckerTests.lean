import BosonicLaughlin.SparseGramCertificate
open BosonicLaughlin

/- Regression checks: corrupting a coefficient or a transpose must fail;
an algebraic Gram equality with a negative weight is not a PSD witness. -/
private def unitRow : SparseIntMatrix 1 1 := fun _ => [(0,1)]
private def doubleRow : SparseIntMatrix 1 1 := fun _ => [(0,2)]
private def emptyRow : SparseIntMatrix 1 1 := fun _ => []

example : ¬SparseGramCheck 1 doubleRow unitRow unitRow (fun _ => 1) := by
  unfold SparseGramCheck
  decide +kernel
example : ¬SparseGramCheck 1 unitRow unitRow emptyRow (fun _ => 1) := by
  unfold SparseGramCheck
  decide +kernel
example : SparseGramCheck (-1) unitRow unitRow unitRow (fun _ => -1) ∧
    ¬(0 < (-1 : ℤ)) ∧ ¬(∀ i : Fin 1, 0 ≤ (fun _ : Fin 1 => (-1 : ℤ)) i) := by
  unfold SparseGramCheck
  decide +kernel

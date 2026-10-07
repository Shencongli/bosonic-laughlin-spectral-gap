import BosonicLaughlin.KernelFrames
import Mathlib.Data.Int.Basic

/-!
Sparse integer rows with a proved exact matrix interpretation. Multiplication
only visits stored entries, and insertion combines equal column indices and
removes zero coefficients. No ordering assumption on the input rows is needed
for the interpretation theorems.
-/
namespace BosonicLaughlin
open Finset
open scoped Matrix

abbrev SparseIntRow (n : ℕ) := List (Fin n × ℤ)
abbrev SparseIntMatrix (m n : ℕ) := Fin m → SparseIntRow n

def sparseIntRowEval {n : ℕ} : SparseIntRow n → Fin n → ℤ
  | [], _ => 0
  | (k,a)::r, j => (if k=j then a else 0) + sparseIntRowEval r j

def sparseIntInsert {n : ℕ} (j : Fin n) (a : ℤ) : SparseIntRow n → SparseIntRow n
  | [] => if a=0 then [] else [(j,a)]
  | (k,b)::r => if j=k then
      if a+b=0 then r else (k,a+b)::r
    else (k,b)::sparseIntInsert j a r

def sparseIntRowAdd {n : ℕ} (r s : SparseIntRow n) : SparseIntRow n :=
  r.foldr (fun p t => sparseIntInsert p.1 p.2 t) s

def sparseIntRowScale {n : ℕ} (a : ℤ) (r : SparseIntRow n) : SparseIntRow n :=
  r.map (fun p => (p.1,a*p.2))

def sparseIntMulRow {m n : ℕ} (r : SparseIntRow m) (B : SparseIntMatrix m n) :
    SparseIntRow n := r.foldr (fun p s => sparseIntRowAdd (sparseIntRowScale p.2 (B p.1)) s) []

def sparseIntToMatrix {m n : ℕ} (A : SparseIntMatrix m n) : Matrix (Fin m) (Fin n) ℤ :=
  fun i j => sparseIntRowEval (A i) j

theorem sparseIntInsert_eval {n : ℕ} (j : Fin n) (a : ℤ) (r : SparseIntRow n) (t : Fin n) :
    sparseIntRowEval (sparseIntInsert j a r) t =
      (if j=t then a else 0) + sparseIntRowEval r t := by
  induction r with
  | nil => by_cases ha : a=0 <;> simp [sparseIntInsert, sparseIntRowEval, ha]
  | cons p r ih =>
    rcases p with ⟨k,b⟩
    by_cases hjk : j=k
    · subst k
      by_cases hz : a+b=0 <;> by_cases hjt : j=t <;>
        simp [sparseIntInsert, sparseIntRowEval, hz, hjt] <;> omega
    · by_cases hjt : j=t <;> by_cases hkt : k=t <;>
        simp_all [sparseIntInsert, sparseIntRowEval] <;> omega

theorem sparseIntRowAdd_eval {n : ℕ} (r s : SparseIntRow n) (j : Fin n) :
    sparseIntRowEval (sparseIntRowAdd r s) j = sparseIntRowEval r j + sparseIntRowEval s j := by
  induction r with
  | nil => simp [sparseIntRowAdd, sparseIntRowEval]
  | cons p r ih =>
    rcases p with ⟨k,a⟩
    simp only [sparseIntRowAdd, List.foldr_cons, sparseIntInsert_eval, sparseIntRowEval]
    rw [show sparseIntRowEval (List.foldr (fun p t => sparseIntInsert p.1 p.2 t) s r) j =
      sparseIntRowEval r j + sparseIntRowEval s j from ih]
    omega

theorem sparseIntRowScale_eval {n : ℕ} (a : ℤ) (r : SparseIntRow n) (j : Fin n) :
    sparseIntRowEval (sparseIntRowScale a r) j = a * sparseIntRowEval r j := by
  induction r with
  | nil => simp [sparseIntRowScale, sparseIntRowEval]
  | cons p r ih =>
    rcases p with ⟨k,b⟩
    simp only [sparseIntRowScale, List.map_cons, sparseIntRowEval]
    rw [show sparseIntRowEval (List.map (fun p => (p.1,a*p.2)) r) j =
      a * sparseIntRowEval r j from ih]
    split_ifs <;> ring

theorem sparseIntMulRow_eval {m n : ℕ} (r : SparseIntRow m) (B : SparseIntMatrix m n)
    (j : Fin n) : sparseIntRowEval (sparseIntMulRow r B) j =
      ∑ k : Fin m, sparseIntRowEval r k * sparseIntRowEval (B k) j := by
  induction r with
  | nil => simp [sparseIntMulRow, sparseIntRowEval]
  | cons p r ih =>
    rcases p with ⟨k,a⟩
    simp only [sparseIntMulRow, List.foldr_cons, sparseIntRowAdd_eval, sparseIntRowScale_eval]
    rw [show sparseIntRowEval (List.foldr
      (fun p s => sparseIntRowAdd (sparseIntRowScale p.2 (B p.1)) s) [] r) j =
        ∑ l : Fin m, sparseIntRowEval r l * sparseIntRowEval (B l) j from ih]
    simp [sparseIntRowEval, add_mul, Finset.sum_add_distrib, ite_mul]

theorem sparseIntMulRow_matrix {m n k : ℕ} (A : SparseIntMatrix m n)
    (B : SparseIntMatrix n k) (i : Fin m) (j : Fin k) :
    sparseIntRowEval (sparseIntMulRow (A i) B) j = (sparseIntToMatrix A * sparseIntToMatrix B) i j :=
  sparseIntMulRow_eval (A i) B j

theorem sparseInt_single_eval {n : ℕ} (i j : Fin n) (a : ℤ) :
    sparseIntRowEval [(i,a)] j = (a • (1 : Matrix (Fin n) (Fin n) ℤ)) i j := by
  simp [sparseIntRowEval, Matrix.one_apply, smul_eq_mul, mul_ite]

end BosonicLaughlin

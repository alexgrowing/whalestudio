import Mathlib

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Matrix

variable {O : Type} [CommRing O]

def el {n : ℕ} (b a : Fin n) (c : O) : Matrix (Fin n) (Fin n) O := 1 + Matrix.single b a c

def Gen (O : Type) [CommRing O] (n : ℕ) : Submonoid (Matrix (Fin n) (Fin n) O) :=
  Submonoid.closure {g | ∃ (b a : Fin n) (c : O), g = el b a c}

def bord {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : Matrix (Fin (m+1)) (Fin (m+1)) O :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (M i)))

@[simp] theorem bord_zero_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : bord M 0 0 = 1 := by
  simp [bord]
@[simp] theorem bord_zero_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) O) (j : Fin m) :
    bord M 0 j.succ = 0 := by
  simp [bord]
@[simp] theorem bord_succ_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) O) (i : Fin m) :
    bord M i.succ 0 = 0 := by
  simp [bord]
@[simp] theorem bord_succ_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) O) (i j : Fin m) :
    bord M i.succ j.succ = M i j := by
  simp [bord]

@[simp] theorem zero_eq_succ_iff {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := iff_false_intro (fun h => Fin.succ_ne_zero k h.symm)

def colS {m : ℕ} (f : Fin m → O) : Matrix (Fin (m+1)) (Fin (m+1)) O :=
  1 + ∑ i, Matrix.single i.succ 0 (f i)

def rowS {m : ℕ} (g : Fin m → O) : Matrix (Fin (m+1)) (Fin (m+1)) O :=
  1 + ∑ j, Matrix.single 0 j.succ (g j)

@[simp] theorem colS_apply {m : ℕ} (f : Fin m → O) (i j : Fin (m+1)) :
    colS f i j = (1 : Matrix (Fin (m+1)) (Fin (m+1)) O) i j +
      Fin.cases 0 (fun k => if j = 0 then f k else 0) i := by
  simp only [colS, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply]
  congr 1
  induction i using Fin.cases with
  | zero => simp
  | succ i => by_cases hj : j = 0 <;> simp [hj, eq_comm]

@[simp] theorem rowS_apply {m : ℕ} (g : Fin m → O) (i j : Fin (m+1)) :
    rowS g i j = (1 : Matrix (Fin (m+1)) (Fin (m+1)) O) i j +
      Fin.cases 0 (fun k => if i = 0 then g k else 0) j := by
  simp only [rowS, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply]
  congr 1
  induction j using Fin.cases with
  | zero => simp
  | succ j => by_cases hi : i = 0 <;> simp [hi, eq_comm]

variable [IsLocalRing O]

end Formalism.L2.GlobalTheoryTheory.ColValS

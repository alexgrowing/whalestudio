import Mathlib
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace PI.UnitaryGroupMassFormula.GaugeFrame

open Matrix Formalism.UG

section Gen

variable {S : Type} [CommRing S] (τ : S →+* S)

variable {m : ℕ}

def low (K : Matrix (Fin (m + 1)) (Fin (m + 1)) S) : Matrix (Fin m) (Fin m) S :=
  K.submatrix Fin.succ Fin.succ

def blk (c : S) (A : Matrix (Fin m) (Fin m) S) : Matrix (Fin (m + 1)) (Fin (m + 1)) S :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases c (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

@[simp] theorem low_apply (K : Matrix (Fin (m + 1)) (Fin (m + 1)) S) (i j : Fin m) :
    low K i j = K i.succ j.succ := rfl

@[simp] theorem blk_zero_zero (c : S) (A : Matrix (Fin m) (Fin m) S) : blk c A 0 0 = c := by
  simp [blk]

@[simp] theorem blk_zero_succ (c : S) (A : Matrix (Fin m) (Fin m) S) (j : Fin m) :
    blk c A 0 j.succ = 0 := by
  simp [blk]

@[simp] theorem blk_succ_zero (c : S) (A : Matrix (Fin m) (Fin m) S) (i : Fin m) :
    blk c A i.succ 0 = 0 := by
  simp [blk]

@[simp] theorem blk_succ_succ (c : S) (A : Matrix (Fin m) (Fin m) S) (i j : Fin m) :
    blk c A i.succ j.succ = A i j := by
  simp [blk]

end Gen

end PI.UnitaryGroupMassFormula.GaugeFrame

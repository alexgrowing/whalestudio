import Mathlib

noncomputable section

open Matrix

namespace PositivityTheory.KB.PsiBlockMatrix

variable (R : Type) [CommRing R]

def ee (q n : ℕ) : Fin n × Fin q ≃ Fin (q * n) := (Equiv.prodComm _ _).trans finProdFinEquiv

def blkM (q n : ℕ) : (Fin q → Matrix (Fin n) (Fin n) R) →* Matrix (Fin (q * n)) (Fin (q * n)) R where
  toFun a := Matrix.reindex (ee q n) (ee q n) (Matrix.blockDiagonal a)
  map_one' := by simp
  map_mul' a b := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
    rfl

def blk (q n : ℕ) : (Fin q → GL (Fin n) R) →* GL (Fin (q * n)) R :=
  (Units.map (blkM R q n)).comp MulEquiv.piUnits.symm.toMonoidHom

end PositivityTheory.KB.PsiBlockMatrix

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf

noncomputable section

namespace GlobalTheory.SchurExt

section LowerUnipotent

variable {R : Type} [CommRing R] {m r : ℕ}

def lowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R :=
  unblk (Matrix.fromBlocks 1 0 Y 1)

def conjLowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R :=
  lowUni Y * k * lowUni (-Y)

end LowerUnipotent

end GlobalTheory.SchurExt

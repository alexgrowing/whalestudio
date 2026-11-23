import Mathlib

noncomputable section
namespace GlobalTheory.DblSiegel

def lagCols {R : Type} [Zero R] {d d₁ : ℕ} (x : Fin d → R) (ι : Matrix (Fin d) (Fin d₁) R) :
    Matrix (Fin d ⊕ Fin d) (Fin 2 ⊕ Fin d₁) R :=
  Matrix.fromCols (Matrix.of fun r k => ![Sum.elim x 0, Sum.elim 0 x] k r) (Matrix.fromRows ι ι)

end GlobalTheory.DblSiegel

import Mathlib
import Formalism.GradedWeylDivisibility.StatementE

noncomputable section

namespace GlobalTheory.Mem.Gelf

open MvPolynomial

def rowE (R : Type) [CommRing R] (r n : ℕ) :
    Matrix (Fin r) (Fin r) (Module.End R (MvPolynomial (Fin r × Fin n) R)) :=
  Matrix.of fun a b => ∑ s : Fin n,
    (LinearMap.mulLeft R (X (a, s) : MvPolynomial (Fin r × Fin n) R)).comp (pderiv (R := R) (b, s)).toLinearMap

def GlRel {A : Type} [Ring A] {N : ℕ} (E : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

def gelfA {R : Type} [CommRing R] {N : ℕ} (μ : Fin N → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun a b => if a = b then μ a + ((N - 1 - a.val : ℕ) : R) else if a < b then -1 else 0

def gelfC {R : Type} [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) : R :=
  ∑ a, ∑ b, (gelfA μ ^ k) a b

end GlobalTheory.Mem.Gelf

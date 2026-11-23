import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.DivIndU

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

noncomputable def diagGL {n : ℕ} (x : Fin n → L) (hx : ∀ i, x i ≠ 0) : GL (Fin n) L :=
  ⟨Matrix.diagonal x, Matrix.diagonal fun i => (x i)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hx i),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hx i)⟩

end GlobalTheory.DivIndU

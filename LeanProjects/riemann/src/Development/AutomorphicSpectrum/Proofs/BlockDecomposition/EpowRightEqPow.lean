import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient

namespace GlobalTheory.CompanionTheory.PairMult

section Powers

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem epowLeft_eq_pow (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    PositivityTheory.RgBcC.RealD.epow E m a b =
      ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [PositivityTheory.RgBcC.RealD.epow, Matrix.one_apply]
  | succ m ih =>
    simp only [PositivityTheory.RgBcC.RealD.epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem epowRight_eq_pow (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    Formalism.REAL.epow E m a b =
      ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ m ih =>
    simp only [Formalism.REAL.epow, pow_succ, Matrix.mul_apply, Matrix.of_apply, ih]

theorem etr_eq_gelA (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) :
    Formalism.REAL.etr E m = PositivityTheory.RgBcC.RealD.gelA E m := by
  simp only [Formalism.REAL.etr, PositivityTheory.RgBcC.RealD.gelA, epowLeft_eq_pow, epowRight_eq_pow]

end Powers

end GlobalTheory.CompanionTheory.PairMult

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports

noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.KZ

def sgC (c : ℕ) (x : Fin 2 → ℚ) (z : ℂ) : ℂ := GlobalTheory.Sieg.sg c x (UpperHalfPlane.ofComplex z)

open Classical in

def siegel {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) : T.K :=
  if h : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero) then h.choose else 0

end GlobalTheory.KZ

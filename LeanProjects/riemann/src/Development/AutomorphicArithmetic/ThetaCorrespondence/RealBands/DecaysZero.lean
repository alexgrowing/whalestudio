import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

noncomputable section

open Formalism.REAL Formalism.MainNotions.S

namespace UpperTheory.Lit.Cusp

def wt {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : ℝ := (1 + Real.sqrt (hs (umat g))) ^ (2 * n ^ 2 + 1)

def Decays {n : ℕ} {ε : Fin n → Bool} (f : UJ ε → ℂ) : Prop := ∃ C : ℝ, ∀ g, ‖f g‖ * wt g ≤ C

end UpperTheory.Lit.Cusp

end

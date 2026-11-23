import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory

theorem haarLie_isHaarOn_Nset : ∀ (k r : ℕ) (κ : ENNReal), 0 < κ → κ < ⊤ →
    IsHaarOn (Nset k r) (haarLie (Nset k r) κ) :=
  fun k r κ h0 h1 => Formalism.MainNotions.BridgeCSB.haarLieN k r κ h0.ne' h1.ne

end GlobalTheory

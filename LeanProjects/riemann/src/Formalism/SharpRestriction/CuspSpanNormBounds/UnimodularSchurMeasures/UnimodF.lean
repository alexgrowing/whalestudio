import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def RepA (X : CData) : Prop :=
  (∀ g h, X.R (g * h) = X.R g ∘L X.R h) ∧ X.R 1 = 1 ∧ (∀ g (F : X.L2), ‖X.R g F‖ = ‖F‖) ∧
    ∀ F : X.L2, Continuous fun g => X.R g F

def UnimodF (X : CData) : Prop := X.μf.IsMulRightInvariant

end Formalism.MainNotions.LeviCoordinates

end

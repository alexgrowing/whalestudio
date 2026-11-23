import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

def GenericGermInjective.Statement : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (E : X.Modules), IsVectorBundle E →
    ∀ (U : X.Opens) (hU : genericPoint X ∈ U),
      Function.Injective (E.presheaf.germ U (genericPoint X) hU)

end GroundTheory.Heights₂.Heights.Model

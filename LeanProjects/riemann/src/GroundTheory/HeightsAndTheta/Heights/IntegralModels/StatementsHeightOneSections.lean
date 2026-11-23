import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

def HeightOneSections.Statement : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], IsNormalScheme X →
    ∀ (E : X.Modules), IsVectorBundle E →
    ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (v : E.presheaf.stalk (genericPoint X)),
      (∀ x : X, x ∈ U → ringKrullDim (X.presheaf.stalk x) = 1 → v ∈ genericImage E x) →
      ∃ s : Γ(E, U), E.presheaf.germ U (genericPoint X) hU s = v

end GroundTheory.Heights₂.Heights.Model

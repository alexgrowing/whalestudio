import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridge
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem IntNumIsFieldIntersection.full : IntNumIsFieldIntersection.Statement.{u} :=
  IntNumIsFieldIntersection.of_intNumBase_cutRational FieldNumbers.IntNumBase.full
    FieldNumbers.CutRational.full

end GroundTheory.Heights₂.Heights.NumbersDVR

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.KernelsRest
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def KernelsCut.Statement : Prop :=
  SymplecticReduction.Statement ∧ SiegelCoordinates.Statement ∧ FirstCoordinateBound.Statement ∧
    GaussianSum.Statement ∧ ThetaBound.Statement ∧ WeakMatrixArithmetic.Statement ∧
    OrthogonalLines.Statement ∧ LineOfLargeDegree.Statement ∧ ShortVectors.Statement ∧
    RestTerm.Statement ∧ RestTermSharp.Statement ∧ AlternantRowRule.Statement ∧
    AlternantPush.Statement ∧ FrobeniusRectangleBound.Statement

end GroundTheory.Heights₂.Heights

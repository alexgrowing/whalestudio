import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PTorsionEquidistribution
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PThirdDifferenceConstant
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PBoundedHomogeneousZero
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PSupOfOrthonormalSum
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PSlopeParameterChoice
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PMonomialNormLowerBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

theorem TorsionEquidistribution.full : TorsionEquidistribution.Statement :=
  TorsionEquidistribution.proof

theorem ThirdDifferenceConstant.full : ThirdDifferenceConstant.Statement.{u} :=
  ThirdDifferenceConstant.proof

theorem BoundedHomogeneousZero.full : BoundedHomogeneousZero.Statement.{u} :=
  BoundedHomogeneousZero.proof

theorem SupOfOrthonormalSum.full : SupOfOrthonormalSum.Statement.{u, v} :=
  SupOfOrthonormalSum.proof

theorem SlopeParameterChoice.full : SlopeParameterChoice.Statement :=
  SlopeParameterChoice.proof

theorem MonomialNormLowerBound.full : MonomialNormLowerBound.Statement :=
  MonomialNormLowerBound.proof

end GroundTheory.Heights₂.Heights

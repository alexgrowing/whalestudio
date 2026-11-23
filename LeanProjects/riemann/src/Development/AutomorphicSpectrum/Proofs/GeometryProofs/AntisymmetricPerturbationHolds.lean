import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymPerturbation
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymStability
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymDivisible

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem antisymPerturbation_holds : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement :=
  @GroundTheory.Heights₂.Heights.AntisymPerturbation.proof
    (@GroundTheory.Heights₂.Heights.AntisymStability.proof GroundTheory.Heights₂.Heights.AntisymDivisible.proof)

end GlobalTheory.CompanionTheory.Ar.Link

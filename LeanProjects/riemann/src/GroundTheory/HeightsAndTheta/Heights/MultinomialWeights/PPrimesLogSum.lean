import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PPrimeLogSum
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.ImportsBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.TheoremB

namespace PrimesLogSum

theorem proof (h : NineStatements.PrimeLogSum.Statement) : IndefiniteRowSideFullHecke.TheoremB.PrimesLogSum.Statement :=
  IndefiniteRowSideFullHecke.TheoremB.PrimesLogSum.equiv.mp h

theorem full : IndefiniteRowSideFullHecke.TheoremB.PrimesLogSum.Statement :=
  proof NineStatements.PrimeLogSum.full

theorem fullNat : NineStatements.PrimeLogSum.Statement :=
  NineStatements.PrimeLogSum.full

end PrimesLogSum

end GroundTheory.Heights₂.Heights.TheoremB

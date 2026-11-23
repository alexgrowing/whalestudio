import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETrunc
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETruncMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETruncTail
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEScale
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEEnergy
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEWeight
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormSecIntegrable

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.AnalyticLimit in

theorem lemmaETailMass : GroundTheory.Heights₂.Heights.AnalyticLimit.LemmaETailMass.Statement :=
  LemmaETailMass.proof LemmaETrunc.proof LemmaETruncMass.proof
    (LemmaETruncTail.proof LemmaEScale.proof LemmaEEnergy.proof LemmaEWeight.proof
      LogNormSecIntegrable.proof)

end GlobalTheory.CompanionTheory.Ar.Giv

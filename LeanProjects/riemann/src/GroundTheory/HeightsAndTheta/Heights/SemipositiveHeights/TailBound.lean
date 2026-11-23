import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.OfListTailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailLogOfMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMono
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMonoRaise
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMonoDens
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLocDensContOnOpen
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PMIntegrableOfDensLe
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PMIntMonoOfDensLe
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegSection
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegYoDense
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegRCont
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PChartCont
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdEqHolo
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PHyperplaneDivisible
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PCoordDivDivisible
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdDivides
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdTransition
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdCocycle
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormHolo
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdPartition
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PIndicatorSmooth
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PNormSqSmooth
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdWeight
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdMetric
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdSectionProps
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdNormCont
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBddOnInner
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdComparison
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open GroundTheory.Heights₂.Heights.AnalyticLimit

theorem ListMono.full : ListMono.Statement :=
  ListMono.proof ListMonoRaise.proof ListMonoDens.proof LocDensContOnOpen.proof
    MIntegrableOfDensLe.proof MIntMonoOfDensLe.proof

theorem RegSection.full : RegSection.Statement :=
  RegSection.proof RegYoDense.proof RegRCont.proof
    (BdMetric.proof ChartCont.proof
      (BdTransition.proof RegYoDense.proof BdEqHolo.proof
        (BdDivides.proof (CoordDivDivisible.proof HyperplaneDivisible.proof)))
      (BdCocycle.proof RegYoDense.proof BdEqHolo.proof)
      (LogNormHolo.proof ChartCont.proof)
      (BdWeight.proof BdPartition.proof IndicatorSmooth.proof NormSqSmooth.proof))
    (BdSectionProps.proof BdEqHolo.proof)
    (BdNormCont.proof ChartCont.proof BdEqHolo.proof)
    (BdComparison.proof ChartCont.proof BddOnInner.proof)

theorem TailShift.full : TailShift.Statement := TailShift.proof

theorem LemmaETailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : LemmaETailLog.Statement :=
  LemmaETailLog.proof h TailLogOfMass.proof

theorem ListTailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : ListTailLog.Statement :=
  ListTailLog.of_lemmaE (LemmaETailLog.of_lemmaETailMass h) ListMono.full RegSection.full
    TailShift.full

theorem TailBound.of_lemmaETailMass (h : LemmaETailMass.Statement) : TailBound.Statement :=
  TailBound.of_listTailLog (ListTailLog.of_lemmaETailMass h)

end GroundTheory.Heights₂.Heights.ForSecondHalf

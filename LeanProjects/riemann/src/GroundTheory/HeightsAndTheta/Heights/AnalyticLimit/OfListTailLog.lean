import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Assembly
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListProductMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListTailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListTailLogSmooth
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PProductBounds
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassStep
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplace
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassError
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PWeightCocycle
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PPolynomialInWeights
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Imports
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PPropertyF
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem GreenMassStep.full : GreenMassStep.Statement := GreenMassStep.proof

theorem GreenMassReplace.full : GreenMassReplace.Statement := GreenMassReplace.proof

theorem GreenMassError.full : GreenMassError.Statement := GreenMassError.proof

theorem UniformIntegrability.full : UniformIntegrability.Statement :=
  UniformIntegrability.of_greenMass GreenMassStep.full GreenMassReplace.full GreenMassError.full

theorem WeightCocycle.full : WeightCocycle.Statement := WeightCocycle.proof

theorem PolynomialInWeights.full : PolynomialInWeights.Statement := PolynomialInWeights.proof

theorem Convergence.full : Convergence.Statement := Convergence.proof WeightCocycle.full

theorem CoefficientLimit.full : CoefficientLimit.Statement :=
  CoefficientLimit.proof WeightCocycle.full PolynomialInWeights.full

theorem ArgumentConvergenceC2.full : ArgumentConvergenceC2.Statement := ArgumentConvergenceC2.proof

theorem PropertyF.full : PropertyF.Statement := PropertyF.proof GluedLocal.full ArgumentConvergenceC2.full

theorem ListProductMass.full : ListProductMass.Statement := ListProductMass.proof

theorem ListTailLog.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLog.Statement :=
  ListTailLog.proof hE hM hC hS

theorem TailBound.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : TailBound.Statement :=
  TailBound.of_listTailLog (ListTailLog.of_lemmaE hE hM hC hS)

theorem ListTailLogSmooth.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLogSmooth.Statement :=
  ListTailLogSmooth.proof (ListTailLog.of_lemmaE hE hM hC hS)

theorem ProductBounds.of_listTailLog (h : ListTailLog.Statement) : ProductBounds.Statement :=
  ProductBounds.proof ListProductMass.full (ListTailLogSmooth.proof h)

theorem ProductBounds.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ProductBounds.Statement :=
  ProductBounds.of_listTailLog (ListTailLog.of_lemmaE hE hM hC hS)

theorem SystemIndependence.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : SystemIndependence.Statement :=
  SystemIndependence.of_productBounds (ProductBounds.of_lemmaE hE hM hC hS)

end GroundTheory.Heights₂.Heights.AnalyticLimit

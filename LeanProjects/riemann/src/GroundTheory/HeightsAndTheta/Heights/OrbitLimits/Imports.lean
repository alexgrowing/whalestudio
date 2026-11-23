import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFStep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFSecRed
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreBij
import GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
import GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
import GroundTheory.HeightsAndTheta.Heights.Intersections.MixedDiscEqZeroOfMulVec
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZIff
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsRest
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
import GroundTheory.HeightsAndTheta.Heights.Intersections.PullWMemFibre
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsSheetPullW
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

theorem PF.of_found
    (hInt : PtsIntegrableStatement) (hIm : ImageArithStatement) (hFD : FibreDimStatement)
    (hCM : ContractMixedStatement) (hCMF : ContractMixedFieldStatement)
    (hRes : ResExistsStatement)
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι')
    (hPD : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjDegStatement F ι ι')
    (hMult : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι)
    (hDivPush : ArithmeticIntersectionDivisorPushforward.Statement) (hPullPush : pullbackPushforward_holds.Statement)
    (hPullCount : PullbackDegreeCount.Statement) (hFDZ : FibreDimensionZero.Statement)
    (hVDA : VerticalDegreeAfterAdjoining.Statement) (hFM : PFFibreMult.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFStatement := by
  have hRank : pointFormRank_holds.Statement := pointFormRank_holds.proof RatioAlgDep.proof
  have hP0 : PushforwardProjectivePoint.Statement :=
    PushforwardProjectivePoint.proof hIm (pointForm_holds.proof hRank pointFormEuler_holds.proof) (ProjectivePointVertical.proof hGeo hEU hPC)
  have hCyc : ArithmeticIntersectionCycle.Statement :=
    ArithmeticIntersectionCycle.proof (ArithmeticIntersectionHorizontal.proof divSuppArith hIm hP0)
      (ArithmeticIntersectionVertical.proof hGeo hEU hPC hPD (VerticalDegree.proof hFDZ ChartRankAdjoin.proof hVDA))
      hDivPush GenericPointExists.proof hEU
  have hAI3 : PushforwardArithIntersection.Statement :=
    PushforwardArithIntersection.proof arithVarZero (RatR.proof hInt) hCyc
      (ArithmeticIntersectionIntegral.proof hInt (IntersectionWithSection.proof hRes hPullPush hPullCount pullbackDensity_holds.proof))
  have hStep : PFStep.Statement :=
    PFStep.proof (PFSecRed.proof hMult hFD) (PFVert.proof hGeo hEU hCMF) (PFIntZero.proof hRank)
      PFHoriz.proof (PFFibreSum.proof hFD PFFibreBij.proof hFM) hIm hCM
  exact PushforwardProjLineFlag.proof hAI3 hStep

end GroundTheory.Heights₂.Heights.Targets

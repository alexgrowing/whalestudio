import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFStep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFSecRed
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreBij
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreMult
import GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Multilin
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixed
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Contract
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv.ProjF

open GroundTheory.Heights₂.Heights

theorem pfIntZero : Inter.PFIntZero.Statement :=
  Inter.PFIntZero.proof (Inter.pointFormRank_holds.proof Inter.RatioAlgDep.proof)

theorem pfVert : Inter.PFVert.Statement :=
  Inter.PFVert.proof (by intros; exact geoNumStatement _) (by intros; exact Targets.ExistsUnique.full _ _)
    Targets.contractMixedField

theorem contractMixed : ContractMixedStatement :=
  Targets.ContractMixed.of_found imageArith Targets.Contract.pulledBackForms_topDensity_vanish
    (Inter.ProjectivePointVertical.proof (by intros; exact geoNumStatement _) (by intros; exact Targets.ExistsUnique.full _ _)
      (by intros; exact Targets.ProjContract.full _ _ _ _ _))
    pfIntZero pfVert

theorem pfStep : Inter.PFStep.Statement :=
  Inter.PFStep.proof (Inter.PFSecRed.proof (by intros; exact Targets.Multilin.full _ _) GlobalTheory.CompanionTheory.Ar.Giv.fibreDim) pfVert pfIntZero
    Inter.PFHoriz.proof (Inter.PFFibreSum.proof GlobalTheory.CompanionTheory.Ar.Giv.fibreDim Inter.PFFibreBij.proof Inter.PFFibreMult.proof)
    imageArith contractMixed

theorem projFormula : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFStatement := fun h =>
  Inter.PushforwardProjLineFlag.proof (GlobalTheory.T.generic_degree_of_arith_system h) pfStep

end GlobalTheory.CompanionTheory.Ar.Giv.ProjF

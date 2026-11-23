import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFCoord
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GenDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.Intersections.PullWMemFibre
import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.SemilocResidueDegOfFibreIncomp
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FibreIncomp
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRC3ResidualContractionComponent
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim

namespace GlobalTheory.CompanionTheory.Ar.Pub

open GroundTheory.Heights₂.Heights

theorem genDeg_of_resExists (hE : ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement := by
  have hPts : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement :=
    GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists hE
  have hFI : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement :=
    GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncomp.full
  have hFD : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement := GlobalTheory.CompanionTheory.Ar.Giv.fibreDim
  have hSec : GroundTheory.Heights₂.Heights.Inter.IntersectionWithSection.Statement :=
    GroundTheory.Heights₂.Heights.Inter.IntersectionWithSection.proof hE GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.full
      (GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount.of_remaining
        GroundTheory.Heights₂.Heights.AutoClose.chart_norm_count hFD)
      GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.full
  have hCyc : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.Statement :=
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.of_remaining GroundTheory.Heights₂.Heights.ForSecondHalf.projDeg_all hFI
      (GroundTheory.Heights₂.Heights.ForSecondHalf.semilocMaxIdeals_of_fibreIncomp hFI)
      (GroundTheory.Heights₂.Heights.ForSecondHalf.semilocResidueDeg_of_fibreIncomp hFI hFD) hFD
  exact GroundTheory.Heights₂.Heights.Targets.GenDeg.of_pts hPts hSec hCyc

theorem pfCoord_of_genDeg (hGD : ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement := by
  exact GroundTheory.Heights₂.Heights.Targets.PFCoord.of_found hGD
    (fun F _ K _ ι _ => GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full F ι)
    GroundTheory.Heights₂.Heights.Targets.genFibreExists GlobalTheory.CompanionTheory.Ar.Giv.fibreDim
    GroundTheory.Heights₂.Heights.Inter.Closed.Targets.CoordFibreDeg

theorem genDeg_and_pfCoord :
    ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement →
      ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement ∧ ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement := by
  intro hE
  exact ⟨genDeg_of_resExists hE, pfCoord_of_genDeg (genDeg_of_resExists hE)⟩

end GlobalTheory.CompanionTheory.Ar.Pub

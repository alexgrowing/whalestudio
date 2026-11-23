import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FirstPointNeSecondPoint
import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Assembly
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial MeasureTheory Topology Set
open GroundTheory.Heights₂.Heights.CP
open scoped Manifold ContDiff

noncomputable section

namespace ComplexProjectiveLineResolution

def liftV : CP 1 → Fin 2 → ℂ := by
  classical
  exact (chartDomain 0).piecewise (fun q ↦ chartVec 0 (chartCoord 0 q)) (fun _ ↦ Pi.single 1 1)

def lift (q : CP 1) : P1.J2 → ℂ := fun p ↦ liftV q p.2

def reidx : (Fin 2 → ℂ) →L[ℂ] (P1.J2 → ℂ) :=
  ContinuousLinearMap.pi fun p ↦ ContinuousLinearMap.proj p.2

end ComplexProjectiveLineResolution

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

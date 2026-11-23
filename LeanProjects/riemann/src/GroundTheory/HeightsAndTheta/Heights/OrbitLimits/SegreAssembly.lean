import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDimBound
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartFiniteIrrel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreComponent
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreDivisor
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Positivity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

universe u v w

theorem SegreComponent.full : SegreComponent.Statement.{u, v, w} :=
  SegreComponent.proof ChartDimBound.proof ChartFiniteIrrel.proof

theorem SegreDivisor.full : SegreDivisor.Statement.{u, v, w} :=
  SegreDivisor.proof SegreComponent.full

theorem Positivity.full {K : Type u} [Fintype K] (F : Type w) [Field F] (ι : K → Type v)
    [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.PositivityStatement F ι :=
  Positivity.of_found SegreDivisor.full F ι

end GroundTheory.Heights₂.Heights.Targets

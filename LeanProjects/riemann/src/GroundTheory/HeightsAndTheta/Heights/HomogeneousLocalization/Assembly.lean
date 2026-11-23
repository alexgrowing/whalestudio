import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.Assembly
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSCoord
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSIndex
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSValue
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSContinuousFrame
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSNormConj
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PPNFlat
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PPNReduced
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSFullSupport
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSConjInvariant
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PPolySections
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PMonomialBasis
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PSupMonomial
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.IntegralMonoInnerEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MeasureTheory NumberField
  GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

theorem FSCoord.full : FSCoord.Statement.{u} := FSCoord.proof

theorem FSIndex.full : FSIndex.Statement.{u} := FSIndex.proof FSCoord.full

theorem FSValue.full : FSValue.Statement.{u} := FSValue.proof FSCoord.full

theorem FSContinuousFrame.full : FSContinuousFrame.Statement.{u} :=
  FSContinuousFrame.proof FSIndex.full ComplexMetric.RegularContinuous.full

theorem FSNormConj.full : FSNormConj.Statement.{u} := FSNormConj.proof FSIndex.full

theorem PNFlat.full : PNFlat.Statement.{u} := PNFlat.proof

theorem PNReduced.full : PNReduced.Statement.{u} := PNReduced.proof

theorem FSFullSupport.full : FSFullSupport.Statement := FSFullSupport.proof

theorem FSConjInvariant.full : FSConjInvariant.Statement := FSConjInvariant.proof

theorem PolySections.full : PolySections.Statement.{u} := PolySections.proof

theorem MonomialBasis.full : MonomialBasis.Statement.{u} := MonomialBasis.proof PolySections.full

theorem SupMonomial.full : SupMonomial.Statement := SupMonomial.proof FSValue.full

theorem L2MonomialOrthogonality.full : L2MonomialOrthogonality.Statement := L2MonomialOrthogonality.proof FSCoord.full FSIndex.full

end SectionsLatticeFS

namespace ProjScheme

open SectionsLatticeFS

def fsBundleFull {A : Type u} [CommRing A] {N : ℕ} (n : ℕ) : (self A N).HermitianLineBundle :=
  fsBundle FSContinuousFrame.full FSNormConj.full n

def fsPointMeasuresFull (K : Type) [Field K] [NumberField K] (N : ℕ) : (self (𝓞 K) N).PointMeasures :=
  fsPointMeasures K N FSFullSupport.full FSConjInvariant.full

example : (self (𝓞 ℚ) 1).HermitianLineBundle := fsBundleFull 1

example : (self (𝓞 ℚ) 1).PointMeasures := fsPointMeasuresFull ℚ 1

end ProjScheme

end

end GroundTheory.Heights₂.Heights

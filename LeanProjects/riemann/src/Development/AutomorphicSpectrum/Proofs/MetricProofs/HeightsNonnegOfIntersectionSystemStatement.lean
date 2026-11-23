import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightsNonnegOfIntersectionSystem
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heights_nonneg_of_intersection_system : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (II : IntersectionSystem) (q : ℕ) (w : Fin q → Ω), IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A → (∀ j, w j ∈ chartLat y A.a 1) → KH.GeneratesOn y A.a w → (∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) → HeightsNonneg II (mCoordIdeal y) A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.heightsNonneg_of_smallGenerators | exact GlobalTheory.CompanionTheory.Ar.Giv.heightsNonneg_of_smallGenerators | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.heightsNonneg_of_smallGenerators <;> assumption)

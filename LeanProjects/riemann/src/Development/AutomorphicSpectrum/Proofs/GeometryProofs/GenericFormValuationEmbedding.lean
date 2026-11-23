import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SectionInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import Development.WeilBound.CoreStatements.RationalSupMetrics.ExistsFieldHomOnOpen

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem exists_form_embedding_hasVal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω], Birational y → IsRelevant (mCoordIdeal y) → ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → aeval z h ≠ 0 → ∃ φ : F →+* 𝕜, ∀ θ : F, HasVal y 0 (algebraMap F Ω θ) z (φ θ) :=
  @MultiProjectiveCoordinates.exists_field_hom_on_open

end GlobalTheory.CompanionTheory.Ar.Small

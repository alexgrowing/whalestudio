import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFormValuationEmbedding
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SectionInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_form_valuation_embedding : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω], Birational y → IsRelevant (mCoordIdeal y) → ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → aeval z h ≠ 0 → ∃ φ : F →+* 𝕜, ∀ θ : F, HasVal y 0 (algebraMap F Ω θ) z (φ θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.exists_form_embedding_hasVal | exact GlobalTheory.CompanionTheory.Ar.Small.exists_form_embedding_hasVal | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.exists_form_embedding_hasVal <;> assumption)

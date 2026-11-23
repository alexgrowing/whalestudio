import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SectionInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import Development.WeilBound.CoreStatements.RationalSupMetrics.MhbNeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem MultiProjectiveCoordinates.exists_field_hom_on_open : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω], Birational y → IsRelevant (mCoordIdeal y) → ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → aeval z h ≠ 0 → ∃ φ : F →+* 𝕜, ∀ θ : F, HasVal y 0 (algebraMap F Ω θ) z (φ θ) := by
  intro K _ ι _ Ω _ y F _ _ _ hbir _
  obtain ⟨ω, -, hω⟩ := MultiProjectiveCoordinates.Val.exists_prim F
  obtain ⟨d, g, h, hg, hh, n, e⟩ := hbir (algebraMap F Ω ω)
  refine ⟨h, ⟨⟨d, hh⟩, fun hm => n ((MultiProjectiveCoordinates.Val.mem_iff y hh).1 hm)⟩, ?_⟩
  intro 𝕜 _ _ z hz hn
  have hx : MultiProjectiveCoordinates.Val.V y z (algebraMap F Ω ω) (aeval z g / aeval z h) :=
    ⟨d, g, h, hg, hh, e, hn, by rw [div_mul_cancel₀ _ hn]⟩
  obtain ⟨φ, hφ⟩ := MultiProjectiveCoordinates.Val.exists_hom hz.2 hω hx
  exact ⟨φ, fun θ => (hφ θ).hasVal⟩

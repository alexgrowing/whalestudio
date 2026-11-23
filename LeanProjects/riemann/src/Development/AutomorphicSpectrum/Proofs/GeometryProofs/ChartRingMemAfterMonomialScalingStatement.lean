import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingMemAfterMonomialScaling
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ring_mem_after_monomial_scaling : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (s t : ∀ k, J k), mseg y s ≠ 0 → mseg y t ≠ 0 → ∀ a ∈ chartRing o (mseg y) s, ∃ n : ℕ, (mseg y s / mseg y t) ^ n * a ∈ chartRing o (mseg y) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg | exact GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg <;> assumption)

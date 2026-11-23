import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.WeilBound.CoreStatements.RationalSupMetrics.IsFormOffMul

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem isFormOff_mul_of_arith : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (u v : MRing ι), IsArithVar (mCoordIdeal y) d → IsFormOff (mCoordIdeal y) u → IsFormOff (mCoordIdeal y) v → IsFormOff (mCoordIdeal y) (u * v) := by
  exact @MultiProjectiveCoordinates.isFormOff_mul

end GlobalTheory.CompanionTheory.Ar.Small

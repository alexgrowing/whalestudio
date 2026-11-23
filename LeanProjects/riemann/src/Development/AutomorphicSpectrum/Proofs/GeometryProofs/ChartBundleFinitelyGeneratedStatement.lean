import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleFinitelyGenerated
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_finitely_generated : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)) (c : ι), x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg | exact GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg | (intros; apply GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg <;> assumption)

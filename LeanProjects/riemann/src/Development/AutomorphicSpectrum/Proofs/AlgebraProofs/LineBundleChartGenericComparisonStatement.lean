import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineBundleChartGenericComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_chart_generic_comparison : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (A T Am : ChartBundle O (mseg x) 1 Ω) (u : Ω) (a : K → ℤ) (m : ℤ), u ≠ 0 → IsLine O x u a A.lat → IsLine O x 1 0 T.lat → SameGeneric O x A T → IsLine O x (u ^ m) (m • a) Am.lat → SameGeneric O x Am T ∧ ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d 1 Am T k L Q = m ^ k * ck O x d 1 A T k L Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CkLinePow.main | exact GlobalTheory.CompanionTheory.Ar.CkLinePow.main | (intros; apply GlobalTheory.CompanionTheory.Ar.CkLinePow.main <;> assumption)

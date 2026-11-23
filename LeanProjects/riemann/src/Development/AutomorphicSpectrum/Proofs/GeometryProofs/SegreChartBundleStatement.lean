import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segre_chart_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (W : ChartBundle ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) r E) (L : Lat ξ E), CoordTie ℤ ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) → L.IsVB r ⊤ → L.IsChartOf (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) W.lat → ∀ (c : (k : K) → J k) (f : Ω) (b : Fin r → E), GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y c ≠ 0 → f ∈ chartRing ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c → f ≠ 0 → (GroundTheory.Heights₂.Heights.LowerBoundFree.IsFrameOver y W c f b ↔ ∀ p : Cpt ξ, InChart ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c p → unitAt ξ p f → L.IsFrameAt b p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt | exact GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt | (intros; apply GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valAt_iff_value_at : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), genPt ξ ⤳ centre z → CoordsAt ξ y z w → ∀ (a : Ω) (v : ℂ), ValAt ξ z a v ↔ GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y a w v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords | exact GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsProductRefinement
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_product_refinement : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (s : κ' → Ω), CoordTie o ξ x → (∀ p : Cpt ξ, ∃ i, InChart ξ s i p) → [Finite κ] → [Finite κ'] → ∃ n : ℕ, CoordTie o ξ fun q : (Fin n → κ) × κ × κ' => (∏ a, x (q.1 a)) * x q.2.1 * s q.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coordTie_add_block | exact GlobalTheory.CompanionTheory.Ar.coordTie_add_block | (intros; apply GlobalTheory.CompanionTheory.Ar.coordTie_add_block <;> assumption)

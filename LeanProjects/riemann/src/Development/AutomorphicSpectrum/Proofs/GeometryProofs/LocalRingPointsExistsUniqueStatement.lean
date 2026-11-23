import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_ring_points_existsUnique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ w : (Σ k, J k) → R, (∀ k, ∃ c, IsUnit (w ⟨k, c⟩)) → (∀ g ∈ mCoordIdeal y, MvPolynomial.aeval w g = 0) → ∃! z : Spec (CommRingCat.of R) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w) ∧ (∀ z : Spec (CommRingCat.of R) ⟶ X, genPt ξ ⤳ centre z → ∃ w, CoordsAt ξ y z w) ∧ ∀ (z : Spec (CommRingCat.of R) ⟶ X) w, genPt ξ ⤳ centre z → CoordsAt ξ y z w → (∀ g ∈ mCoordIdeal y, MvPolynomial.aeval w g = 0) ∧ ∀ w', CoordsAt ξ y z w' ↔ ∃ a : K → Rˣ, w' = fun p => (a p.1 : R) * w p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.tie_points | exact GlobalTheory.CompanionTheory.Ar.tie_points | (intros; apply GlobalTheory.CompanionTheory.Ar.tie_points <;> assumption)

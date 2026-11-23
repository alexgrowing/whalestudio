import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConjugatePointSameCentre
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_point_same_centre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), centre (spMap (starRingEnd ℂ) ≫ z) = centre z ∧ (CoordsAt ξ y z w → CoordsAt ξ y (spMap (starRingEnd ℂ) ≫ z) (conjVec w)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj | exact GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj <;> assumption)

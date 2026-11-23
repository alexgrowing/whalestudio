import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicCoordsOfGenericPoint
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_coords_of_generic_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → DifferentiableOn ℂ w B → (∀ u ∈ B, CoordsAt ξ y (p u) (w u)) → IsHolTo B p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family | exact GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family | (intros; apply GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family <;> assumption)

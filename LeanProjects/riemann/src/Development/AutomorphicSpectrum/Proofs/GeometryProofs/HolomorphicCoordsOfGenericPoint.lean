import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartFamilyOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PeriodsHol

theorem isHolTo_of_coordsAt_family : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → DifferentiableOn ℂ w B → (∀ u ∈ B, CoordsAt ξ y (p u) (w u)) → IsHolTo B p := by
  intro X Ω _ ξ K _ J _ y htie hall n B w p hB hw hco
  exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol.isHolTo_of_coordsAt htie hall hB
    (fun q => (differentiableOn_pi.1 hw) q) hco

end GlobalTheory.CompanionTheory.Ar.PeriodsHol

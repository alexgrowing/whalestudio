import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenSecond
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_second : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (R S : Type) [CommRing R] [Nontrivial R] [CommRing S] (f : R →+* S) (d r : ℕ) (B : Germ.FB R d (𝓞 E)) (B₂ : Germ.FB S d (𝓞 E)) (x : Fin r → (Fin d → R) × (Fin d → R)), IsMapOf f B B₂ → IsHBasis B x → IsHBasis B₂ (fun j => vmap f (x j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map <;> assumption)

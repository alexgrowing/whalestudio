import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenFirst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_first : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B B₂ : Germ.FB R d O) (C C₂ : Germ.FB S d O) (φ ψ : Germ.Pt R 1 d) (lam : Germ.PS R 2 d), IsMapOf f B C → IsMapOf f B₂ C₂ → IsIso B B₂ φ ψ lam → IsIso C C₂ (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i)) (MvPowerSeries.map f lam) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isIso_map | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isIso_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isIso_map <;> assumption)

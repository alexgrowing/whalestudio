import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPushAlongMap
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_push_along_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (V : Type) [AddCommGroup V] [Module R V] (M : LieModel t'.G x V), ∃ Mf : LieModel t.G (x ≫ f) V, ∀ e, (Mf.pt e).left = (M.pt e).left ≫ m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SabLie.lieModel_of_sabMap | exact GlobalTheory.CompanionTheory.Ar.SabLie.lieModel_of_sabMap | (intros; apply GlobalTheory.CompanionTheory.Ar.SabLie.lieModel_of_sabMap <;> assumption)

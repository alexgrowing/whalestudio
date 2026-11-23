import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIff
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_inner_product_map_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (z : Spec (CommRingCat.of ℂ) ⟶ X') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ), v.left = v'.left ≫ m.φ → w.left = w'.left ≫ m.φ → (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_tripleMap_iff | exact GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_tripleMap_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_tripleMap_iff <;> assumption)

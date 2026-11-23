import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory

theorem etale_of_comp_etale_of_smoothOfRelativeDimension :
    ∀ (X Y Z S : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z) (sX : X ⟶ S) (sY : Y ⟶ S) (d : ℕ),
      h ≫ sY = sX → SmoothOfRelativeDimension d sX → SmoothOfRelativeDimension d sY →
      Etale (h ≫ f) → Etale h := by
  intro X Y Z S h f sX sY d hs hX hY he
  subst hs
  haveI : FormallyUnramified (h ≫ f) := inferInstance
  haveI : FormallyUnramified h := FormallyUnramified.of_comp h f
  exact etale_of_formallyUnramified_of_smoothOfRelativeDimension h sY d hY hX

end GlobalTheory

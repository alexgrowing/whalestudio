import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfCompEtaleSameRelativeDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_comp_etale_sameRelativeDimension : ∀ (X Y Z S : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z) (sX : X ⟶ S) (sY : Y ⟶ S) (d : ℕ), h ≫ sY = sX → SmoothOfRelativeDimension d sX → SmoothOfRelativeDimension d sY → Etale (h ≫ f) → Etale h := by
  first | (exact @GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension) | (exact GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension) | (intros; apply GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension  <;> assumption)

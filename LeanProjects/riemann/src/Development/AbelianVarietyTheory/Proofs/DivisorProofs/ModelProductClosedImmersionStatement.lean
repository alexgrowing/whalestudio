import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelProductClosedImmersion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_product_closed_immersion : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B₁ B₂ : GlobalTheory.Vert.Model O) (f₁ : GlobalTheory.Vert.Model.Hom B₁ B) (f₂ : GlobalTheory.Vert.Model.Hom B₂ B), ∃ (Z : GlobalTheory.Vert.Model O) (h₁ : GlobalTheory.Vert.Model.Hom Z B₁) (h₂ : GlobalTheory.Vert.Model.Hom Z B₂) (w : h₁.f ≫ f₁.f = h₂.f ≫ f₂.f), IsClosedImmersion (pullback.lift h₁.f h₂.f w) := by
  first | exact @GlobalTheory.ModelClosure.exists_model_closedImmersion_pullback | exact GlobalTheory.ModelClosure.exists_model_closedImmersion_pullback | (intros; apply GlobalTheory.ModelClosure.exists_model_closedImmersion_pullback <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeDimClosedImmersionProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_dim_closed_immersion_product : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B₁ B₂ Z : GlobalTheory.Vert.Model O) (f₁ : GlobalTheory.Vert.Model.Hom B₁ B) (f₂ : GlobalTheory.Vert.Model.Hom B₂ B) (h₁ : GlobalTheory.Vert.Model.Hom Z B₁) (h₂ : GlobalTheory.Vert.Model.Hom Z B₂) (w : h₁.f ≫ f₁.f = h₂.f ≫ f₂.f), IsClosedImmersion (pullback.lift h₁.f h₂.f w) → Z.relDim + B.relDim ≤ B₁.relDim + B₂.relDim := by
  first | exact @GlobalTheory.Vert.Model.relDim_add_le_of_isClosedImmersion | exact GlobalTheory.Vert.Model.relDim_add_le_of_isClosedImmersion | (intros; apply GlobalTheory.Vert.Model.relDim_add_le_of_isClosedImmersion <;> assumption)

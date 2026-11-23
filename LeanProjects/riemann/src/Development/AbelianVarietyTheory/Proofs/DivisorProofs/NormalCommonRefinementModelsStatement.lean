import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalCommonRefinementModels
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_common_refinement_models : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B B₁ B₂ : GlobalTheory.Vert.Model O) (f₁ : GlobalTheory.Vert.Model.Hom B₁ B) (f₂ : GlobalTheory.Vert.Model.Hom B₂ B), f₁.relDim = 0 → f₂.relDim = 0 → ∃ (B₃ : GlobalTheory.Vert.Model O) (h₁ : GlobalTheory.Vert.Model.Hom B₃ B₁) (h₂ : GlobalTheory.Vert.Model.Hom B₃ B₂), GlobalTheory.IsNormalScheme B₃.X ∧ h₁.relDim = 0 ∧ h₂.relDim = 0 ∧ h₁.f ≫ f₁.f = h₂.f ≫ f₂.f := by
  first | exact @GlobalTheory.DomThird.exists_normal_dominating | exact GlobalTheory.DomThird.exists_normal_dominating | (intros; apply GlobalTheory.DomThird.exists_normal_dominating <;> assumption)

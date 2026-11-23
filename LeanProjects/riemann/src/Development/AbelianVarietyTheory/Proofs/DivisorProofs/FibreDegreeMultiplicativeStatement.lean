import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDegreeMultiplicative
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_degree_multiplicative : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B₁ B₂ B₃ : GlobalTheory.Vert.Model O) (g : GlobalTheory.Vert.Model.Hom B₃ B₂) (f : GlobalTheory.Vert.Model.Hom B₂ B₁), g.relDim = 0 → f.relDim = 0 → (g.comp f).fibreDeg 1 = g.fibreDeg 1 * f.fibreDeg 1 := by
  first | exact @GlobalTheory.Vert.Model.Hom.fibreDeg_one_comp | exact GlobalTheory.Vert.Model.Hom.fibreDeg_one_comp | (intros; apply GlobalTheory.Vert.Model.Hom.fibreDeg_one_comp <;> assumption)

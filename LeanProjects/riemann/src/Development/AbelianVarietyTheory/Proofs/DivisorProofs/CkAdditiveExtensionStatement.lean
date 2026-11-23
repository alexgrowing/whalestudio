import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkAdditiveExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ck_additive_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P₁ P₂ P₃ : Pres B), IsExt P₁.mod P₂.mod P₃.mod → ∀ k : ℕ, P₂.ck p k = P₁.ck p k + P₃.ck p k := by
  first | exact @GlobalTheory.MixedLocalChains.ExtAdd.ck_add_of_isExt | exact GlobalTheory.MixedLocalChains.ExtAdd.ck_add_of_isExt | (intros; apply GlobalTheory.MixedLocalChains.ExtAdd.ck_add_of_isExt <;> assumption)

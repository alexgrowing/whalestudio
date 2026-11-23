import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalizationRelativeDimZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalization_relative_dim_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (Z : GlobalTheory.Vert.Model O), ∃ (Z' : GlobalTheory.Vert.Model O) (n : GlobalTheory.Vert.Model.Hom Z' Z), GlobalTheory.IsNormalScheme Z'.X ∧ n.relDim = 0 := by
  first | exact @GlobalTheory.Vert.Model.exists_normal_hom | exact GlobalTheory.Vert.Model.exists_normal_hom | (intros; apply GlobalTheory.Vert.Model.exists_normal_hom <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeDimZeroFibreDegree
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_dim_zero_fibre_degree : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), f.relDim = 0 → 0 < Module.finrank f.fnField Γ(f.genFibre, ⊤) ∧ f.fibreDeg 1 = (Module.finrank f.fnField Γ(f.genFibre, ⊤) : ℚ) := by
  first | exact @GlobalTheory.Vert.Model.Hom.fibreDeg_one_of_relDim_eq_zero | exact GlobalTheory.Vert.Model.Hom.fibreDeg_one_of_relDim_eq_zero | (intros; apply GlobalTheory.Vert.Model.Hom.fibreDeg_one_of_relDim_eq_zero <;> assumption)

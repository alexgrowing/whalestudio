import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsomorphismPullbackComp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_isomorphism_pullback_comp : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z Z₁ Z₂ : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom Z₁ Z) (g : GlobalTheory.Vert.Model.Hom Z₂ Z₁) (E E' : Z.X.Modules) (φ : Z.GenIso E E'), ((φ.pull f.comp_str).pull g.comp_str).hom ≫ Z₂.genRes.map ((Scheme.Modules.pullbackComp g.f f.f).app E').hom = Z₂.genRes.map ((Scheme.Modules.pullbackComp g.f f.f).app E).hom ≫ (φ.pull (g.comp f).comp_str).hom := by
  first | exact @GlobalTheory.Vert.Model.GenIso.pull_pull_comp_hom | exact GlobalTheory.Vert.Model.GenIso.pull_pull_comp_hom | (intros; apply GlobalTheory.Vert.Model.GenIso.pull_pull_comp_hom <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairCompositionExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_composition_exists : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z Z₁ Z₂ : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom Z₁ Z) (g : GlobalTheory.Vert.Model.Hom Z₂ Z₁) (E E' E'' : Z.X.Modules) (φ : Z.GenIso E E') (φ' : Z.GenIso E' E'') (N : ℕ) (P : GlobalTheory.Vert.Model.FlagPair ((φ.pull f.comp_str).pull g.comp_str) N) (Q : GlobalTheory.Vert.Model.FlagPair ((φ'.pull f.comp_str).pull g.comp_str) N), Q.fl = P.fl' → ∃ (P₁ : GlobalTheory.Vert.Model.FlagPair (φ.pull (g.comp f).comp_str) N) (Q₁ : GlobalTheory.Vert.Model.FlagPair (φ'.pull (g.comp f).comp_str) N), Q₁.fl = P₁.fl' := by
  first | exact @GlobalTheory.Vert.Model.FlagPair.exists_chain_pull_comp | exact GlobalTheory.Vert.Model.FlagPair.exists_chain_pull_comp | (intros; apply GlobalTheory.Vert.Model.FlagPair.exists_chain_pull_comp <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullbackComposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_pullback_composition : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z Z₁ Z₂ : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom Z₁ Z) (g : GlobalTheory.Vert.Model.Hom Z₂ Z₁) (E E' : Z.X.Modules) (φ : Z.GenIso E E') (N : ℕ), GlobalTheory.Vert.Model.FlagPair ((φ.pull f.comp_str).pull g.comp_str) N → Nonempty (GlobalTheory.Vert.Model.FlagPair (φ.pull (g.comp f).comp_str) N) := by
  first | exact @GlobalTheory.Vert.Model.FlagPair.nonempty_pull_comp | exact GlobalTheory.Vert.Model.FlagPair.nonempty_pull_comp | (intros; apply GlobalTheory.Vert.Model.FlagPair.nonempty_pull_comp <;> assumption)

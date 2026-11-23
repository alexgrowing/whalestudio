import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullDivisorClass
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowup
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_pull_divisor_class : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z Z₁ : GlobalTheory.Vert.Model O) (f : Z₁.X ⟶ Z.X) (hf : f ≫ Z.str = Z₁.str) (E E' : Z.X.Modules) (φ : Z.GenIso E E') (N : ℕ) (P : GlobalTheory.Vert.Model.FlagPair φ N) (i : Fin N), ((GlobalTheory.FlagPairExists.pairPull hf P).div i).cls = GlobalTheory.Vert.Model.vPull hf ((P.div i).cls) := by
  first | exact @GlobalTheory.FlagPairExists.cls_div_pairPull | exact GlobalTheory.FlagPairExists.cls_div_pairPull | (intros; apply GlobalTheory.FlagPairExists.cls_div_pairPull <;> assumption)

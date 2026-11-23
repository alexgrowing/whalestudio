import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullback
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

theorem GlobalTheory.FlagPairExists.cls_div_pairPull : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z Z₁ : GlobalTheory.Vert.Model O) (f : Z₁.X ⟶ Z.X) (hf : f ≫ Z.str = Z₁.str) (E E' : Z.X.Modules) (φ : Z.GenIso E E') (N : ℕ) (P : GlobalTheory.Vert.Model.FlagPair φ N) (i : Fin N), ((GlobalTheory.FlagPairExists.pairPull hf P).div i).cls = GlobalTheory.Vert.Model.vPull hf ((P.div i).cls) := by
  intro O _ _ _ Z Z₁ f hf E E' φ N P i
  exact GlobalTheory.Vert.FlagPairPull.cls_div_pairPull hf P i

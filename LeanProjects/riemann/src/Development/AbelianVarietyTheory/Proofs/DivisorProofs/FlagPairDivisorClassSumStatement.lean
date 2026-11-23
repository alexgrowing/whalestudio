import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairDivisorClassSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeSymmetric
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_divisor_class_sum : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O) (W W' : B.X.Modules) (ψ : B.GenIso W W') (R : GlobalTheory.Vert.Model.FlagPair ψ 2), (R.div 0).cls + (R.div 1).cls = (ψ.div R.fl.isVB_self R.fl'.isVB_self).cls := by
  first | exact @GlobalTheory.Vert.Model.FlagPair.cls_div_add_rank_two | exact GlobalTheory.Vert.Model.FlagPair.cls_div_add_rank_two | (intros; apply GlobalTheory.Vert.Model.FlagPair.cls_div_add_rank_two <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairSameStepsPointEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_same_steps_point_eq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P P' : GlobalTheory.Vert.Model.FlagPair φ r) (i : Fin r), P.fl.SameStep P'.fl i.castSucc → P.fl.SameStep P'.fl i.succ → P.fl'.SameStep P'.fl' i.castSucc → P.fl'.SameStep P'.fl' i.succ → (P.toFPair p).x i = (P'.toFPair p).x i ∧ (P.toFPair p).x' i = (P'.toFPair p).x' i ∧ (P.toFPair p).Dv i = (P'.toFPair p).Dv i := by
  first | exact @GlobalTheory.Vert.FlagSame.toFPair_eq_of_sameStep | exact GlobalTheory.Vert.FlagSame.toFPair_eq_of_sameStep | (intros; apply GlobalTheory.Vert.FlagSame.toFPair_eq_of_sameStep <;> assumption)

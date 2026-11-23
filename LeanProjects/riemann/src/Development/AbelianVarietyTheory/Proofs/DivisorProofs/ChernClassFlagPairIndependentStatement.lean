import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassFlagPairIndependent
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_class_flag_pair_independent : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → (∀ (W W' : B.X.Modules) (ψ : B.GenIso W W') (R R' : GlobalTheory.Vert.Model.FlagPair ψ 2) (k : ℕ) (Q : PicSym B.X), ck (R.toFPair p) k Q = ck (R'.toFPair p) k Q) → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P P' : GlobalTheory.Vert.Model.FlagPair φ r), GlobalTheory.Vert.Model.FlagPair.Adj P P' → ∀ (k : ℕ) (Q : PicSym B.X), ck (P.toFPair p) k Q = ck (P'.toFPair p) k Q := by
  first | exact @GlobalTheory.AdjRankTwo.ck_eq_of_adj | exact GlobalTheory.AdjRankTwo.ck_eq_of_adj | (intros; apply GlobalTheory.AdjRankTwo.ck_eq_of_adj <;> assumption)

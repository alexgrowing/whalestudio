import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkFlagPairIndependent
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ck_flag_pair_independent : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r k : ℕ) (P P' : GlobalTheory.Vert.Model.FlagPair φ r) (Q : PicSym B.X), ck (P.toFPair p) k Q = ck (P'.toFPair p) k Q := by
  first | exact @GlobalTheory.FlagIndep.ck_eq_of_flagPair | exact GlobalTheory.FlagIndep.ck_eq_of_flagPair | (intros; apply GlobalTheory.FlagIndep.ck_eq_of_flagPair <;> assumption)

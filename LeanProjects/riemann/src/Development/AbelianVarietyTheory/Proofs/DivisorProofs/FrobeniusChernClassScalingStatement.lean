import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusChernClassScaling
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_chern_class_scaling : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (R R' : Pres B) (g : Γ(B.X, ⊤)), IsRootOfP p g p → R.r = 1 → Kills g R.mod → IsFrob p R.mod R'.mod → ∀ k : ℕ, R'.ck p k = ((p : ℚ) ^ k) • R.ck p k := by
  first | exact @GlobalTheory.FrobRankOne.ck_frob_rankOne | exact GlobalTheory.FrobRankOne.ck_frob_rankOne | (intros; apply GlobalTheory.FrobRankOne.ck_frob_rankOne <;> assumption)

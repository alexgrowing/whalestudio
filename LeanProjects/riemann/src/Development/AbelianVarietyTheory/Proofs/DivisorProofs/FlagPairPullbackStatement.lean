import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_pullback : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B B₁ : GlobalTheory.Vert.Model O) (h : B₁.X ⟶ B.X) (hh : h ≫ B.str = B₁.str) (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P : GlobalTheory.Vert.Model.FlagPair φ r), ∃ P₁ : GlobalTheory.Vert.Model.FlagPair (φ.pull hh) r, ∀ i, (P₁.toFPair p).x i = smallPull h ((P.toFPair p).x i) ∧ (P₁.toFPair p).x' i = smallPull h ((P.toFPair p).x' i) ∧ (P₁.toFPair p).Dv i = GlobalTheory.Vert.Model.vPullQ hh ((P.toFPair p).Dv i) := by
  first | exact @GlobalTheory.Vert.FlagPairPull.exists_flagPair_pull | exact GlobalTheory.Vert.FlagPairPull.exists_flagPair_pull | (intros; apply GlobalTheory.Vert.FlagPairPull.exists_flagPair_pull <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullbackComposite
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_pullback_composite : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B B₁ B₂ : GlobalTheory.Vert.Model O) (f : B₁.X ⟶ B.X) (hf : f ≫ B.str = B₁.str) (h : B₂.X ⟶ B₁.X) (hh : h ≫ B₁.str = B₂.str) (c : B₂.X ⟶ B.X) (hc : c ≫ B.str = B₂.str), h ≫ f = c → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P : GlobalTheory.Vert.Model.FlagPair ((φ.pull hf).pull hh) r), ∃ P' : GlobalTheory.Vert.Model.FlagPair (φ.pull hc) r, ∀ i, (P'.toFPair p).x i = (P.toFPair p).x i ∧ (P'.toFPair p).x' i = (P.toFPair p).x' i ∧ (P'.toFPair p).Dv i = (P.toFPair p).Dv i := by
  first | exact @GlobalTheory.Vert.Model.FlagPair.exists_pull_comp | exact GlobalTheory.Vert.Model.FlagPair.exists_pull_comp | (intros; apply GlobalTheory.Vert.Model.FlagPair.exists_pull_comp <;> assumption)

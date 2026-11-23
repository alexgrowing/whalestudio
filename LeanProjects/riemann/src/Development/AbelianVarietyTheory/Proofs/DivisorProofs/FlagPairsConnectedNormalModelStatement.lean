import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairsConnectedNormalModel
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pairs_connected_normal_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P P' : GlobalTheory.Vert.Model.FlagPair φ r), ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (m : ℕ) (g : Fin (m + 1) → GlobalTheory.Vert.Model.FlagPair (φ.pull f.comp_str) r), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ 0 < f.fibreDeg 1 ∧ (∀ (k : ℕ) (Q : PicSym B.X), ck ((g 0).toFPair p) k (picSymPull f.f Q) = f.fibreDeg 1 * ck (P.toFPair p) k Q) ∧ (∀ (k : ℕ) (Q : PicSym B.X), ck ((g (Fin.last m)).toFPair p) k (picSymPull f.f Q) = f.fibreDeg 1 * ck (P'.toFPair p) k Q) ∧ ∀ j : Fin m, GlobalTheory.Vert.Model.FlagPair.Adj (g j.castSucc) (g j.succ) := by
  first | exact @GlobalTheory.FlagPairChain.exists_chain_flagPair | exact GlobalTheory.FlagPairChain.exists_chain_flagPair | (intros; apply GlobalTheory.FlagPairChain.exists_chain_flagPair <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairsConnectedNormalModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassFlagPairIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassFlagPairRankTwoStatement

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.FlagIndep

theorem ck_eq_of_flagPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r k : ℕ) (P P' : GlobalTheory.Vert.Model.FlagPair φ r) (Q : PicSym B.X), ck (P.toFPair p) k Q = ck (P'.toFPair p) k Q := by
  intro O _ _ _ p _ _ _ B hB E E' φ r k P P' Q
  obtain ⟨B', f, m, g, hB', hf0, hpos, h0, hlast, hadj⟩ := GlobalTheory.T.flag_pairs_connected_normal_model O p B hB E E' φ r P P'
  have hstep : ∀ j : Fin (m + 1), ck ((g j).toFPair p) k (picSymPull f.f Q) =
      ck ((g 0).toFPair p) k (picSymPull f.f Q) := by
    intro j
    induction j using Fin.induction with
    | zero => rfl
    | succ j ih =>
      rw [← ih]
      exact (GlobalTheory.T.chern_class_flag_pair_independent O p B' hB' (GlobalTheory.T.chern_class_flag_pair_rank_two O p B' hB') _ _ _ r _ _ (hadj j) k _).symm
  have h := (h0 k Q).symm.trans ((hstep (Fin.last m)).symm.trans (hlast k Q))
  exact mul_left_cancel₀ hpos.ne' h

end GlobalTheory.FlagIndep

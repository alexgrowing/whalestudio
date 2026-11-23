import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairChernExchangeIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairDivisorClassSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairCapDegDifferenceZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairDivisorCapDegVanishStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.FlagRankTwo

theorem ck_flagPair_rank_two : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (W W' : B.X.Modules) (ψ : B.GenIso W W') (R R' : GlobalTheory.Vert.Model.FlagPair ψ 2) (k : ℕ) (Q : PicSym B.X), ck (R.toFPair p) k Q = ck (R'.toFPair p) k Q := by
  intro O _ _ _ p _ _ _ B hB W W' ψ R R' k Q
  refine GlobalTheory.T.flag_pair_chern_exchange_identity (B.toITh p) (R.toFPair p) (R'.toFPair p) k Q
    (fun E E' a => GlobalTheory.VertComm.capDeg_vp_comm O p B hB E E' a) ?_ ?_
    (fun D y => GlobalTheory.T.flag_pair_capDeg_difference_zero O p B hB W W' ψ R R' D y)
    (fun y => GlobalTheory.T.flag_pair_divisor_capDeg_vanish O p B hB W W' ψ R R' y)
  · have h3 := congrArg firstChernPic (R.fl.cls_det.symm.trans R'.fl.cls_det)
    simp only [Fin.sum_univ_two, map_add, firstChernPic_class] at h3
    exact h3
  · change GlobalTheory.Vert.Model.toQ (R.div 0).cls + GlobalTheory.Vert.Model.toQ (R.div 1).cls =
      GlobalTheory.Vert.Model.toQ (R'.div 0).cls + GlobalTheory.Vert.Model.toQ (R'.div 1).cls
    rw [← map_add, ← map_add, GlobalTheory.T.flag_pair_divisor_class_sum O B W W' ψ R, GlobalTheory.T.flag_pair_divisor_class_sum O B W W' ψ R']

end GlobalTheory.FlagRankTwo

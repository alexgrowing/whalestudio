import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairChernExchangeIdentity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BracketIndepOfCofactors
open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.DV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_chern_exchange_identity : ∀ (Z : ITh) (P P' : FPair Z 2) (k : ℕ) (Q : Z.Ch), (∀ (E E' : Z.VDiv) (a : Z.Ch), Z.capDeg E (Z.cD E' * a) = Z.capDeg E' (Z.cD E * a)) → Z.c1 (P.x 0) + Z.c1 (P.x 1) = Z.c1 (P'.x 0) + Z.c1 (P'.x 1) → P.Dv 0 + P.Dv 1 = P'.Dv 0 + P'.Dv 1 → (∀ (D : Z.VDiv) (y : Z.Ch), Z.capDeg D ((Z.c1 (P'.x' 1) - Z.c1 (P.x' 0)) * (Z.c1 (P.x' 0) - Z.c1 (P'.x' 0)) * y) = 0) → (∀ y : Z.Ch, Z.capDeg (P.Dv 1 - P'.Dv 0) ((Z.c1 (P.x 0) - Z.c1 (P'.x 0)) * y) + Z.capDeg (P.Dv 0 - P'.Dv 0) ((Z.c1 (P'.x' 1) - Z.c1 (P.x' 0)) * y) = 0) → ck P k Q = ck P' k Q := by
  first | exact @GlobalTheory.FlagRankTwo.ck_eq_of_rank_two | exact GlobalTheory.FlagRankTwo.ck_eq_of_rank_two | (intros; apply GlobalTheory.FlagRankTwo.ck_eq_of_rank_two <;> assumption)

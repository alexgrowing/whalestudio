import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPointsOfEqualChains
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_points_of_equal_chains : GlobalTheory.ChainPts.EqChainSt → GlobalTheory.ChainPts.ChainPtsSt := by
  first | exact @GlobalTheory.ChainParts.chainPtsSt_of_eqChainSt | exact GlobalTheory.ChainParts.chainPtsSt_of_eqChainSt | (intros; apply GlobalTheory.ChainParts.chainPtsSt_of_eqChainSt <;> assumption)

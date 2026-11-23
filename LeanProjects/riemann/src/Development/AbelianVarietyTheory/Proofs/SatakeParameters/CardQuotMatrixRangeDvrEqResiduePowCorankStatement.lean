import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardQuotMatrixRangeDvrEqResiduePowCorank
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EsymmInvMulEsymmCard
open GlobalTheory.LatHecke GlobalTheory.SatakeInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_quot_matrix_range_dvr_eq_residue_pow_corank : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (A : Matrix (Fin r) (Fin r) O), IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤ LinearMap.range A.mulVecLin → Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) = qRes O ^ (r - (A.map (IsLocalRing.residue O)).rank) := by
  first | exact @GlobalTheory.IdxRank.card_quot_range | exact GlobalTheory.IdxRank.card_quot_range | (intros; apply GlobalTheory.IdxRank.card_quot_range <;> assumption)

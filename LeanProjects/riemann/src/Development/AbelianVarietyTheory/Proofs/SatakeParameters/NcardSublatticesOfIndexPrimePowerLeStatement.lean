import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NcardSublatticesOfIndexPrimePowerLe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
open GlobalTheory.LatHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_sublatticesOfIndexPrimePower_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (n : ℕ) (L : Lat O K r), ((subIdx n L).ncard : ℝ) ≤ ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n := by
  first | exact @GlobalTheory.SubIdxCount.ncard_subIdx_le | exact GlobalTheory.SubIdxCount.ncard_subIdx_le | (intros; apply GlobalTheory.SubIdxCount.ncard_subIdx_le <;> assumption)

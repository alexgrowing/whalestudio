import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumAlternatingCardElementarySublatticesAbove
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
open GlobalTheory.LatHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_alternating_card_elementarySublattices_above : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (n : ℕ) (L M : Lat O K r), 1 ≤ n → M ∈ subIdx n L → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * (({M' | M' ∈ subElem k L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) = 0 := by
  first | exact @GlobalTheory.LatHecke.sum_alt_card_subElem_ge | exact GlobalTheory.LatHecke.sum_alt_card_subElem_ge | (intros; apply GlobalTheory.LatHecke.sum_alt_card_subElem_ge <;> assumption)

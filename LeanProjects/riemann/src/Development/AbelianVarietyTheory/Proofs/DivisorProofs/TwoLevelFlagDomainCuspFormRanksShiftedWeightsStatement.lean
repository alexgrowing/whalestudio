import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeights
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelFlagDomain_cuspForm_ranks_shifted_weights : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), LevelHyp (sub M ⊥) → 0 < M.p0 → M.p0 < r → ∀ (ka : Wt M.Ψ r) (T : ℕ), ArchOn M ka T → sOf M ≤ T → Ranks M ka (sOf M) ((M.dimY : ℝ) * (M.dimY + 6) / T) 2 := by
  first | exact @GlobalTheory.ShareRanks.ranks | exact GlobalTheory.ShareRanks.ranks | (intros; apply GlobalTheory.ShareRanks.ranks <;> assumption)

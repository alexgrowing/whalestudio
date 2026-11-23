import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotallySplitRationalPrimeOfSplitsCompletely
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotallySplitRationalPrime_of_splitsCompletely : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), SplitsCompletely E g → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g := by
  first | exact @GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely | exact GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely | (intros; apply GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely <;> assumption)

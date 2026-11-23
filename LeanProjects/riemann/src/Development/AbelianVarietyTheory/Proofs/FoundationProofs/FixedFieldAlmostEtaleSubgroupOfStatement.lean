import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleSubgroupOf
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFieldAlmostEtale_subgroupOf : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (U H : Subgroup G), AlmostSep v U → AlmostSep v (U.subgroupOf H) := by
  first | exact @GlobalTheory.AlmostEt.almostSep_subgroupOf | exact GlobalTheory.AlmostEt.almostSep_subgroupOf | (intros; apply GlobalTheory.AlmostEt.almostSep_subgroupOf <;> assumption)

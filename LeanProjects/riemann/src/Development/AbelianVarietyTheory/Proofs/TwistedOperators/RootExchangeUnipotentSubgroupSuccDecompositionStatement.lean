import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentSubgroupSuccDecomposition
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchangeUnipotentSubgroup_succ_decomposition : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), ∀ g ∈ N k n c (p + 1), ∃ g₁ ∈ N k n c p ⊓ N k n c (p + 1), ∃ u : n → k, g = g₁ * rowE c p u := by
  first | exact @GlobalTheory.RootEx.RadicalDecomp.succ_decomp | exact GlobalTheory.RootEx.RadicalDecomp.succ_decomp | (intros; apply GlobalTheory.RootEx.RadicalDecomp.succ_decomp <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRootInvolutionParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_root_involution_parabolic : ∀ {k : ℕ} (W : Finset (SV k)), IsPar W → ∃ f : SV k → SV k, ∀ u, u ∉ W → IsPar (insert u W) →
  f u ∉ W ∧ f u ≠ u ∧ IsPar (insert (f u) W) ∧ vec u + vec (f u) ∈ aP W ∧ f (f u) = u := by
  first | exact @GlobalTheory.ChamberFlip.chain_flip | exact GlobalTheory.ChamberFlip.chain_flip | (intros; apply GlobalTheory.ChamberFlip.chain_flip <;> assumption)

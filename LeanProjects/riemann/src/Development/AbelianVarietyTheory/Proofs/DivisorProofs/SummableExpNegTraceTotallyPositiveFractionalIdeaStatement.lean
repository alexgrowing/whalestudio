import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegTraceTotallyPositiveFractionalIdea
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_exp_neg_trace_totallyPositive_fractionalIdeal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) (δ : ℝ), 0 < δ → Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
  first | exact @GlobalTheory.LatExpSum.summable_exp_neg_trace | exact GlobalTheory.LatExpSum.summable_exp_neg_trace | (intros; apply GlobalTheory.LatExpSum.summable_exp_neg_trace <;> assumption)

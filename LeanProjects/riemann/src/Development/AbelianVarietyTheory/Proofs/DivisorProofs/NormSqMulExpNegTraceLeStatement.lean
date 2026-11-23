import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqMulExpNegTraceLe
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sq_mul_exp_neg_trace_le' : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : ℝ), 0 < δ → ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) → |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤ C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) := by
  first | exact @GlobalTheory.norm_sq_mul_exp_neg_trace_le | exact GlobalTheory.norm_sq_mul_exp_neg_trace_le | (intros; apply GlobalTheory.norm_sq_mul_exp_neg_trace_le <;> assumption)

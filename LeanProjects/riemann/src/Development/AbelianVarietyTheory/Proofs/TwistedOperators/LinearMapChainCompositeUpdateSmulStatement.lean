import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateSmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
open GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearMapChainComposite_update_smul : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (c : ℂ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (c • A)) n = c • chainTo (Function.update k j₀ A) n := by
  first | exact @GlobalTheory.ChainSmul.chainTo_update_smul | exact GlobalTheory.ChainSmul.chainTo_update_smul | (intros; apply GlobalTheory.ChainSmul.chainTo_update_smul <;> assumption)

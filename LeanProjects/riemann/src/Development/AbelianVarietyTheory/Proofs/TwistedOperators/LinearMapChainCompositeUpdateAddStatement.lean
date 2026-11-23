import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateAdd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
open GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearMapChainComposite_update_add : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (A B : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (A + B)) n = chainTo (Function.update k j₀ A) n + chainTo (Function.update k j₀ B) n := by
  first | exact @GlobalTheory.chainTo_update_add | exact GlobalTheory.chainTo_update_add | (intros; apply GlobalTheory.chainTo_update_add <;> assumption)

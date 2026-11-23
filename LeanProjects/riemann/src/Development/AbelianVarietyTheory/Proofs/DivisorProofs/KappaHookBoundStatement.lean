import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaHookBound
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_hook_bound : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (u : ι → Fin N → ℝ) (Q : ι → ℕ → MvPolynomial (ι × Fin N) ℝ) (g U : ℝ) (τ τ' : ι) (i : Fin N) (k : ℕ), 0 < g → (∀ τ a b, a ≠ b → u τ a ≠ u τ b) → IsDecomp u Q → 2 ≤ k → k ≤ N → (∀ a b, u τ a - u τ b ≤ U) → (∀ a, a ≠ i → g ≤ |u τ' i - u τ' a|) → |kap u k (X (τ', i) ^ (k - 1)) (Q τ k)| ≤ 2 ^ (k - 1) / (k.factorial : ℝ) * U * ((N : ℝ) * (1 + U / g)) ^ (k - 1) := by
  first | exact @GlobalTheory.KapBound.abs_kap_le | exact GlobalTheory.KapBound.abs_kap_le | (intros; apply GlobalTheory.KapBound.abs_kap_le <;> assumption)

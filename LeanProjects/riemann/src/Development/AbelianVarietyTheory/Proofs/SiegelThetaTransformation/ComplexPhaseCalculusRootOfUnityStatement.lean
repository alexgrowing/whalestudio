import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComplexPhaseCalculusRootOfUnity
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_phase_calculus_rootOfUnity : (∀ a b : ℂ, Ph a → Ph b → Ph (a * b)) ∧ (∀ a : ℂ, Ph a → Ph (conj a) ∧ Ph a⁻¹) ∧ (∀ t : ℝ, Ph (t : ℂ)) ∧ (∀ a : ℂ, IsMu a → Ph a ∧ ‖a‖ = 1) ∧ (∀ a : ℂ, Ph a → ‖a‖ = 1 → IsMu a) ∧ (∀ a b : ℂ, IsMu a → IsMu b → IsMu (a * b) ∧ IsMu a⁻¹ ∧ IsMu (conj a)) ∧ (∀ (a : ℂ) (k : ℕ), 0 < k → (IsMu (a ^ k) → IsMu a) ∧ (Ph (a ^ k) → Ph a)) ∧ (∀ q : ℚ, IsMu (cexp (π * I * (q : ℂ)))) ∧ ∀ a b : ℂ, b ≠ 0 → Ph b → Ph (a * b) → Ph a := by
  first | exact @GlobalTheory.Phase.Calc.calculus | exact GlobalTheory.Phase.Calc.calculus | (intros; apply GlobalTheory.Phase.Calc.calculus <;> assumption)

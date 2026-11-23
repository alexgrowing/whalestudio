import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementMulPos
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateGramSymm
open GlobalTheory.CasimirOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralCasimirElement_mul_pos : ∀ {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ), (∀ a b, s (a * b) = s b * s a) → (∀ a, s (s a) = a) → (∀ a b, φ (a * b) = φ (b * a)) → (∀ a, φ (s a) = φ a) → (∀ a, a ≠ 0 → 0 < φ (s a * a)) → ∀ u, u ≠ 0 → 0 < φ (s (casimir (⇑x) s φ * u) * u) := by
  first | (exact @GlobalTheory.CasimirOrder.casimir_mul_pos) | (exact GlobalTheory.CasimirOrder.casimir_mul_pos) | (intros; apply GlobalTheory.CasimirOrder.casimir_mul_pos  <;> assumption)

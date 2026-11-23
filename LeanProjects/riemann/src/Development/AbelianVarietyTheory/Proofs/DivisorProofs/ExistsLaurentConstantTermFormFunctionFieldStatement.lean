import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentConstantTermFormFunctionField
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_laurentConstantTermForm_functionField : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∃ ρ : F →ₗ[k] k, IsRes k x ρ := by
  first | (exact @GlobalTheory.exists_isRes) | (exact GlobalTheory.exists_isRes) | (intros; apply GlobalTheory.exists_isRes <;> assumption)

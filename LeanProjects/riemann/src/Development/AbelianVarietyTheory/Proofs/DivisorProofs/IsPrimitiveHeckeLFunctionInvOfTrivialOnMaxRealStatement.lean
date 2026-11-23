import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxReal
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveHeckeLFunction_inv_of_trivialOnMaxReal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (Λ : ℂ → ℂ), TrivOnF χ → IsHeckeL χ Λ → IsHeckeL χ⁻¹ Λ := by
  first | exact @GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF | exact GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF | (intros; apply GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF <;> assumption)

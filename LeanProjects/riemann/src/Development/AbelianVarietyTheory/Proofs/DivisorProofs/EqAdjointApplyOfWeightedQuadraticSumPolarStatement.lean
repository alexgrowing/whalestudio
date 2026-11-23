import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdjointApplyOfWeightedQuadraticSumPolar
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_adjoint_apply_of_weightedQuadraticSum_polar : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (X₀ : Type) [AddCommGroup X₀] (β : LinearMap.BilinForm ℤ X₀), (∀ a b, β a b = β b a) → (∀ a, a ≠ 0 → 0 < β a a) → ∀ (E E' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * E' = E.transpose * (W + W.transpose) → ∀ z z' : Fin 8 → X₀, (∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + z) - qW W β (fun a => ∑ b, E a b • y b) - qW W β z = qW W β (y + z') - qW W β y - qW W β z') → z' = fun a => ∑ b, E' a b • z b := by
  first | exact @GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar | exact GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar | (intros; apply GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar <;> assumption)

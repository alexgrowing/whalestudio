import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicIntegralLeFundamentalDomain
import Mathlib
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_integral_le_fundamental_domain : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (F : (Fin g → ℂ) → ℝ) (Fd U : Set (Fin g → ℂ)), Continuous F → (∀ (l : Λ) z, F (z + l) = F z) → IsAddFundamentalDomain Λ Fd volume → MeasurableSet U → (∀ u ∈ U, ∀ v ∈ U, u - v ∈ Λ → u = v) → ∫⁻ w in U, ENNReal.ofReal (F w) ≤ ∫⁻ z in Fd, ENNReal.ofReal (F z) := by
  first | exact @GlobalTheory.lintegral_le_of_injects_fundamentalDomain | exact GlobalTheory.lintegral_le_of_injects_fundamentalDomain | (intros; apply GlobalTheory.lintegral_le_of_injects_fundamentalDomain <;> assumption)

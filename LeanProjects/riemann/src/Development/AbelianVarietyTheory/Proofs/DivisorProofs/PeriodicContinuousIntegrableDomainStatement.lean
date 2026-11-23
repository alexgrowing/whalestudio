import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicContinuousIntegrableDomain
import Mathlib
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_continuous_integrable_domain : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (F : (Fin g → ℂ) → ℝ) (Fd : Set (Fin g → ℂ)), Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Continuous F → (∀ (l : Λ) z, F (z + l) = F z) → IsAddFundamentalDomain Λ Fd volume → IntegrableOn F Fd volume := by
  first | exact @GlobalTheory.integrableOn_fundamentalDomain_of_periodic | exact GlobalTheory.integrableOn_fundamentalDomain_of_periodic | (intros; apply GlobalTheory.integrableOn_fundamentalDomain_of_periodic <;> assumption)

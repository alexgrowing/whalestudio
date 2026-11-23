import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarOfCommuteSchrodingerOperators
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_of_commute_schrodingerOperators : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l), (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(S f₁) = rhoFun w ⇑(S f)) → ∃ c : ℂ, ∀ f, S f = c • f := by
  first | exact @GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun | exact GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun | (intros; apply GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun <;> assumption)

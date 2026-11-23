import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzUnitaryIntertwinerScalar
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_unitary_intertwiner_scalar : GlobalTheory.FunPr.Hypotheses₂ → ∀ (l : Type) [Fintype l] (U : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
    (∀ (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(U h₁) = GlobalTheory.RealWeil.rhoFun w ⇑(U h)) →
    (∀ h : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, U h = a • h := by
  first | exact @GlobalTheory.RealWeil.SchurSchwartz.schur_schwartz | exact GlobalTheory.RealWeil.SchurSchwartz.schur_schwartz | (intros; apply GlobalTheory.RealWeil.SchurSchwartz.schur_schwartz <;> assumption)

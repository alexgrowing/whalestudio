import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReQuad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorNormInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodQuadraticFormsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFormFderivComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFlatOfQuadraticDerivativeStatement

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.ThetaMet
open scoped Real ContDiff

namespace GlobalTheory.ThetaMet

theorem isMetric_chernIsFlat : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ →
    IsMetric B τ (stdLat g) (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2))
      (fun P : Pt E g => Real.exp (-2 * π * ((fun i => (P.2 i).im) ⬝ᵥ
        ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im)))) ∧
    ChernIsFlat B τ (fun P : Pt E g => Real.exp (-2 * π * ((fun i => (P.2 i).im) ⬝ᵥ
      ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im)))) := by
  intro g E _ _ _ B τ hτ
  obtain ⟨hf, hq, hr⟩ := GlobalTheory.T.period_quadratic_forms_smooth hτ
  refine ⟨⟨?_, fun P _ => Real.exp_pos _, fun l _ P hP => ?_⟩,
    GlobalTheory.T.chern_flat_of_quadratic_derivative hτ hf hq hr (GlobalTheory.T.quadratic_form_fderiv_complex hτ)⟩
  · exact Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hq)
  · exact GlobalTheory.T.theta_factor_norm_invariance (τ P.1) (hτ.2.2 P.1 hP.1) l P.2

end GlobalTheory.ThetaMet

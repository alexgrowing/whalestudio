import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceFormImaginaryPart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_trace_form_imaginary_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (t₁ : E) (ρ : ℝ), (∀ i, φ i t₁ = -Complex.I * ((ρ / 2 : ℝ) : ℂ)) →
    ∀ (a : FR E) (x y : E), ((Algebra.trace ℚ E ((a : E) * t₁ * x * bar y) : ℚ) : ℝ) =
      (∑ j, (φ (e j) (a : E) * (ρ : ℂ)) * φ (e j) x * starRingEnd ℂ (φ (e j) y)).im := by
  first | exact @GlobalTheory.trace_riemannForm_eq_im | exact GlobalTheory.trace_riemannForm_eq_im | (intros; apply GlobalTheory.trace_riemannForm_eq_im <;> assumption)

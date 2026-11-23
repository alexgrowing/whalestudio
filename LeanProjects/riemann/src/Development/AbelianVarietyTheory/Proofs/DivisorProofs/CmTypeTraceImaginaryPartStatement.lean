import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeTraceImaginaryPart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
open NumberField GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_trace_imaginary_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (h : I → ℝ) (mu : E), (∀ z : E, ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) = ∑ i, h i * (φ i z).im) →
    ∀ i, 2 * Complex.I * φ i mu = (h i : ℂ) := by
  first | exact @GlobalTheory.cmType_trace_im_coeff | exact GlobalTheory.cmType_trace_im_coeff | (intros; apply GlobalTheory.cmType_trace_im_coeff <;> assumption)

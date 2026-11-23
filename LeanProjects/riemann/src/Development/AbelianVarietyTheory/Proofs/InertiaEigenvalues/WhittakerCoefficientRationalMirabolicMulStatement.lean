import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), Continuous f → (∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ g, f (ratGL E a γ * g) = f g) → ∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) (g : GA E a), coefF ψ (m + 1) ξ f (ratGL E a γ * g) = coefF ψ (m + 1) (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) f g := by
  first | exact @GlobalTheory.CuspGeneric.coefF_ratGL_mul | exact GlobalTheory.CuspGeneric.coefF_ratGL_mul | (intros; apply GlobalTheory.CuspGeneric.coefF_ratGL_mul <;> assumption)

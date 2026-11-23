import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionThetaMatrixCoeffRationalTranslat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierInversion_thetaMatrixCoeff_rationalTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∀ w x : WO S T, Summable (fun γ : ratL T S => ‖thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀)‖) → ∑' γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) * heisO ψ S T ((γ : WO S T) + w) f₀ x = f x * star (heisO ψ S T w f₀ x) * heisO ψ S T w f₀ x := by
  first | exact @GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate | exact GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate | (intros; apply GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate <;> assumption)

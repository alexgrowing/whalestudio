import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqSetIntegralTsumRationalTranslates
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_setIntegral_tsum_rationalTranslates : ∀ (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratMx D m n) 𝓕 μ → ∀ c : Mx D m n → ℂ, Integrable c μ → (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun a : Matrix (Fin m) (Fin n) D.host.E => ‖c (y + a.map (incA D))‖) ∧ ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' a : Matrix (Fin m) (Fin n) D.host.E, c (y + a.map (incA D)) ∂μ := by
  first | exact @GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum | exact GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum | (intros; apply GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum <;> assumption)

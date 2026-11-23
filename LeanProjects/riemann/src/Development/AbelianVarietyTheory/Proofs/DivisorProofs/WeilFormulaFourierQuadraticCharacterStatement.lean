import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFormulaFourierQuadraticCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_fourier_quadratic_character : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ (f g : X → ℂ) (s : X → X) (γ : ℂ), Continuous f → Continuous s → (∀ y u, f y * e y u = g u * f (y + s u)) → HasGauss μ f γ → ∀ φ ∈ SB X, ∀ x, four μ e (fun y => f y * four μ e φ y) x = γ * ∫ z, g (x + z) * φ z ∂μ := by
  first | exact @GlobalTheory.KSp.WeilFormula.weil_formula | exact GlobalTheory.KSp.WeilFormula.weil_formula | (intros; apply GlobalTheory.KSp.WeilFormula.weil_formula <;> assumption)

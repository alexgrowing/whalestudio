import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzValuedIntegralLinear
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_valued_integral_linear : ∀ {D₁ D₂ Ω₁ Ω₂ : Type} [NormedAddCommGroup D₁] [NormedSpace ℝ D₁] [NormedAddCommGroup D₂] [NormedSpace ℝ D₂]
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (m₁ : Measure Ω₁) (m₂ : Measure Ω₂) [IsFiniteMeasure m₁] [SFinite m₂]
    (G : SchwartzMap D₁ ℂ → Ω₁ → Ω₂ → SchwartzMap D₂ ℂ),
    (∀ (a b : ℂ) (f f' : SchwartzMap D₁ ℂ) k l, G (a • f + b • f') k l = a • G f k l + b • G f' k l) →
    (∀ f (n : ℕ) (y : D₂), StronglyMeasurable (Function.uncurry fun k l => iteratedFDeriv ℝ n (⇑(G f k l)) y)) →
    (∀ a n : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (w : Ω₂ → ℝ), Integrable w m₂ ∧
      ∀ f k l, SchwartzMap.seminorm ℂ a n (G f k l) ≤ C * w l * (s.sup (schwartzSeminormFamily ℂ D₁ ℂ)) f) →
    ∃ T : SchwartzMap D₁ ℂ →L[ℂ] SchwartzMap D₂ ℂ, ∀ f, ⇑(T f) = fun y => ∫ k, ∫ l, G f k l y ∂m₂ ∂m₁ := by
  first | exact @GlobalTheory.ParamSchwartz.iteratedIntegral_clm | exact GlobalTheory.ParamSchwartz.iteratedIntegral_clm | (intros; apply GlobalTheory.ParamSchwartz.iteratedIntegral_clm <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslateTaylorSecondOrder
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_translate_taylor_second_order : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : 𝓢(X, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ a : X, ‖a‖ ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f - LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) ≤ C * ‖a‖ ^ 2 := by
  first | exact @GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le | exact GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le | (intros; apply GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le <;> assumption)

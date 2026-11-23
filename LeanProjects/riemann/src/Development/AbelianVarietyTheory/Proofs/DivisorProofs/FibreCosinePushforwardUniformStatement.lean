import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCosinePushforwardUniform
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_cosine_pushforward_uniform : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → ∀ J : Set ℝ, MeasurableSet J →
    ∫⁻ x : ℂ, J.indicator (fun _ => (1 : ENNReal)) (GlobalTheory.FibCos.cos G x) * ENNReal.ofReal (GlobalTheory.FibCos.fs G x) =
      volume (J ∩ Set.Icc (0 : ℝ) 1) := by
  first | exact @GlobalTheory.FibCos.lintegral_indicator_cos_mul_fs | exact GlobalTheory.FibCos.lintegral_indicator_cos_mul_fs | (intros; apply GlobalTheory.FibCos.lintegral_indicator_cos_mul_fs <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapInfiniteGLHaarMeasureMulLeft
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_infiniteGLHaarMeasure_mul_left : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (γ : MatInf E j), 0 < detNorm E j γ → (haarGL E j).map (fun g => γ * g) = haarGL E j := by
  first | exact @GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq | exact GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq | (intros; apply GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanTraceFormDualLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineLatticeClassMean_traceFormDualLattice : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ F : Submodule ℤ (VecInf E j) → ENNReal, (∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => F (latAt E j Λ g)) g)) → latMean E j (fun L => F (dualAt E j L)) = latMean E j F := by
  first | exact @GlobalTheory.MeanDual.latMean_dualAt | exact GlobalTheory.MeanDual.latMean_dualAt | (intros; apply GlobalTheory.MeanDual.latMean_dualAt <;> assumption)

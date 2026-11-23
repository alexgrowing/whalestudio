import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeTraceDualAndTraceDualTraceDual
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_traceDual_and_traceDual_traceDual : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsLattice E Λ → Submodule.IsLattice E (trDual E j Λ) ∧ trDual E j (trDual E j Λ) = Λ := by
  first | exact @GlobalTheory.MeanDual.Alg.isLattice_trDual_and_trDual_trDual | exact GlobalTheory.MeanDual.Alg.isLattice_trDual_and_trDual_trDual | (intros; apply GlobalTheory.MeanDual.Alg.isLattice_trDual_and_trDual_trDual <;> assumption)

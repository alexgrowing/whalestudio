import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLatticeStabiliserRealGroupMulMem
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagLatticeStabiliserRealGroup_mul_mem : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), ∀ x ∈ flagGroup I xf S, ∀ y ∈ flagGroup I xf S, x * y ∈ flagGroup I xf S := by
  first | exact @GlobalTheory.FlagStabMul.flagGroup_mul | exact GlobalTheory.FlagStabMul.flagGroup_mul | (intros; apply GlobalTheory.FlagStabMul.flagGroup_mul <;> assumption)

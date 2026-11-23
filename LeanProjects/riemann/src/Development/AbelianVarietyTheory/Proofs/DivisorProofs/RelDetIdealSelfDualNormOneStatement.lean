import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDetIdealSelfDualNormOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relDetIdeal_selfDual_normOne : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), StandardLatticesGL3.SD D L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  first | exact @GlobalTheory.SelfDualDetNorm.detId_normOne | exact GlobalTheory.SelfDualDetNorm.detId_normOne | (intros; apply GlobalTheory.SelfDualDetNorm.detId_normOne <;> assumption)

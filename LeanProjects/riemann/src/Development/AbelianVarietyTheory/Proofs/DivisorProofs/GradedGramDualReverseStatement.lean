import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedGramDualReverse
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open Matrix GlobalTheory.HermFrame GlobalTheory.GradedNorm GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_gram_dual_reverse : ∀ {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ), M.PosDef → ∀ k : Fin q, (GlobalTheory.HermFrame.gradedGram (GlobalTheory.CurvInterp.dualRev Mᵀ) k () ()).re = (GlobalTheory.GradedNorm.grSq M (Fin.rev k))⁻¹ := by
  first | exact @GlobalTheory.DualRevGraded.gradedGram_dualRev_re | exact GlobalTheory.DualRevGraded.gradedGram_dualRev_re | (intros; apply GlobalTheory.DualRevGraded.gradedGram_dualRev_re <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowGrassmannBlockCurvatureSupertraceZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero : ∀ {n p q : ℕ} (e : Fin p × Fin q → Fin n) (k : ℕ), 1 ≤ k → ((GlobalTheory.GrassModel.blockPoly e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace + ((-GlobalTheory.GrassModel.blockPolyBar e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace = 0 := by
  first | exact @GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | exact GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | (intros; apply GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTraceGramBlockMatrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_trace_gram_block_eq_pow_mul_norm_det : ∀ {E E' : Type} [Field E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] {d n : ℕ} (w : Module.Basis (Fin d) E E') (H : Matrix (Fin n) (Fin n) E') (v : Fin d → E'), (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1)).det = (Matrix.of fun k l => Algebra.trace E E' (w k * v l)).det ^ n * Algebra.norm E H.det := by
  first | exact @GlobalTheory.det_traceGram_blockMatrix | exact GlobalTheory.det_traceGram_blockMatrix | (intros; apply GlobalTheory.det_traceGram_blockMatrix <;> assumption)

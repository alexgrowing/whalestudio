import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceSkewHermitianMulHermitianOrthonormalBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.re_trace_skewHermitian_mul_hermitianOrthonormalBasis : ∀ (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length), (trace (kB ε i * pB ε b)).re = 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB | exact GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB | (intros; apply GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB <;> assumption)

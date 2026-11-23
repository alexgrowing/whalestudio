import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SkewHermitianOrthonormalBasisTraceOrthonormal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianOrthonormalBasis_trace_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length), (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal | exact GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal | (intros; apply GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal <;> assumption)

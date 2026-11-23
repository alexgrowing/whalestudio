import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetRationalMatrixTwoSidedMulEqProdEmbeddings
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_rationalMatrixTwoSidedMul_eq_prod_embeddings : ∀ (D : D7) (N N' : ℕ) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), LinearMap.det (mulV D M' M) = ∏ τ, embT D τ M'.det ^ N * embT D τ M.det ^ N' := by
  first | exact @GlobalTheory.TwoSidedDet.det_mulV | exact GlobalTheory.TwoSidedDet.det_mulV | (intros; apply GlobalTheory.TwoSidedDet.det_mulV <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace' : ∀ (F : Type) [Field F] [Finite F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F) (f : F[X]) (y : AlgebraicClosure F), Irreducible f → aeval y f = 0 → Module.finrank F (LinearMap.ker (aeval (Matrix.toLin' M) f)) = f.natDegree * Module.finrank (AlgebraicClosure F) (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)))) y) := by
  first | exact @GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace | exact GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace | (intros; apply GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace <;> assumption)

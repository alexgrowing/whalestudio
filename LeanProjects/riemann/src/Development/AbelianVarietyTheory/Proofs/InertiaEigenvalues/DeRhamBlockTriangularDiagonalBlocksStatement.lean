import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamBlockTriangularDiagonalBlocks
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_blockTriangular_diagonal_blocks : SubQuot := by
  first | exact @GlobalTheory.PMon.subQuot | exact GlobalTheory.PMon.subQuot | (intros; apply GlobalTheory.PMon.subQuot <;> assumption)

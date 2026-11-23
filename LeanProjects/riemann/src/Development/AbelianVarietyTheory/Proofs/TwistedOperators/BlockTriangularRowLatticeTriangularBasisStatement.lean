import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularRowLatticeTriangularBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockTriangular_row_lattice_triangular_basis : SpanEq := by
  first | exact @GlobalTheory.InertZeta.RowSpan.spanEq_holds | exact GlobalTheory.InertZeta.RowSpan.spanEq_holds | (intros; apply GlobalTheory.InertZeta.RowSpan.spanEq_holds <;> assumption)

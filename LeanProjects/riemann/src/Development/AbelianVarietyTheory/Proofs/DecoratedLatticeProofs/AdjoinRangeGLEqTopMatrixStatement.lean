import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdjoinRangeGLEqTopMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_range_GL_eq_top_matrix : ∀ (R : Type) [CommRing R] (n : ℕ), Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ) = ⊤ := by
  first | exact @GlobalTheory.adjoin_range_GL_eq_top | exact GlobalTheory.adjoin_range_GL_eq_top | (intros; apply GlobalTheory.adjoin_range_GL_eq_top <;> assumption)

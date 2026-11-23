import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixFamilyDegreeLeRankMulLineBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixFamilyDegree_le_rank_mul_line_bound : ∀ (r : ℕ) (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ g : Place k F → Matrix (Fin r) (Fin r) F, admitted g → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ r * b := by
  first | exact @GlobalTheory.Nef.deg_le_rank_mul_of_linesLE | exact GlobalTheory.Nef.deg_le_rank_mul_of_linesLE | (intros; apply GlobalTheory.Nef.deg_le_rank_mul_of_linesLE <;> assumption)

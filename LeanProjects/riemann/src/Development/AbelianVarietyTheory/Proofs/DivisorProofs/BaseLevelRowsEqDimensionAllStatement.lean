import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelRowsEqDimensionAll
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_level_rows_eq_dimension_all : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Part D O c), BaseRankDimension D O c b := by
  first | exact @GlobalTheory.Fc.Ind.base_level_rows_eq_dimension | exact GlobalTheory.Fc.Ind.base_level_rows_eq_dimension | (intros; apply GlobalTheory.Fc.Ind.base_level_rows_eq_dimension <;> assumption)

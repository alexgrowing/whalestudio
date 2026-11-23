import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormParametersEqNatStepGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnNormParameters_eq_natStepGap : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) → GlobalTheory.ColumnNormCompare.numDatumOfParameters D L = ofRecord D L Del h0 := by
  first | exact @GlobalTheory.ColumnNormCompare.numRec_eq_ofRecord | exact GlobalTheory.ColumnNormCompare.numRec_eq_ofRecord | (intros; apply GlobalTheory.ColumnNormCompare.numRec_eq_ofRecord <;> assumption)

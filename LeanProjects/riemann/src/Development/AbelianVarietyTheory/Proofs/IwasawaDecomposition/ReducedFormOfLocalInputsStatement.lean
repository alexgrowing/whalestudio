import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputs
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_form_of_local_inputs : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → GlobalTheory.NRows.Rows D → SumRepresentations.ReducedMultiplicityStatement D := by
  first | exact @GlobalTheory.PtSt.reducedMultiplicity_of_rows | exact GlobalTheory.PtSt.reducedMultiplicity_of_rows | (intros; apply GlobalTheory.PtSt.reducedMultiplicity_of_rows <;> assumption)

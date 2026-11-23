import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PageEstimateStatement
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.page_estimate_statement : PageSt := by
  first | exact @GlobalTheory.BigOn.pageSt | exact GlobalTheory.BigOn.pageSt | (intros; apply GlobalTheory.BigOn.pageSt <;> assumption)

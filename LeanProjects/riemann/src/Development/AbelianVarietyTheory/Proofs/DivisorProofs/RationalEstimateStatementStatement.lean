import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEstimateStatement
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_estimate_statement : RatSt := by
  first | exact @GlobalTheory.BigOn.ratSt | exact GlobalTheory.BigOn.ratSt | (intros; apply GlobalTheory.BigOn.ratSt <;> assumption)

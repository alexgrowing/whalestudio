import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivityFromAllEstimates
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjectivity_from_all_estimates : RunsSt → RatSt → GeoSt → (AtRec fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) → TwistSt → ShareSt → BadSt → ExpSt → PageSt → OntoX := by
  first | exact @GlobalTheory.BigOn.OntoPath.onto_path | exact GlobalTheory.BigOn.OntoPath.onto_path | (intros; apply GlobalTheory.BigOn.OntoPath.onto_path <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OnWithOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivityFromAllEstimatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunsEstimateStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEstimateStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFromPageEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankAtPlacesFromComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximumEstimateStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonOffTypePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PageEstimateStatementStatement

set_option autoImplicit false

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn

theorem ontoX_of_twist_shares_exp : ExportSt → TwistSt → ShareSt → BadSt → ExpSt → OntoX := by
  intro _ hT hS hB hE
  have hP : PageSt := GlobalTheory.T.page_estimate_statement
  have hG : GeoSt := GlobalTheory.T.geometric_from_page_estimate hP
  exact GlobalTheory.T.surjectivity_from_all_estimates GlobalTheory.T.runs_estimate_statement GlobalTheory.T.rational_estimate_statement hG (GlobalTheory.T.rank_at_places_from_comparison GlobalTheory.T.maximum_estimate_statement hG GlobalTheory.T.comparison_off_type_places) hT hS hB hE hP

end GlobalTheory.BigOn

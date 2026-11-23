import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OntoXOfTwistSharesExp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageStStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoStOfPageStStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoPathStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRunsAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtremalVectorsSplitPartStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankAtPlacesRecStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MaxStStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompareOffOwnAtRunsStatement

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn
theorem ontoX_of_twist_shares_exp_alt : _root_.GlobalTheory.BigOn.ExportedStatement → _root_.GlobalTheory.BigOn.TwistStatement' → _root_.GlobalTheory.BigOn.ShareStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement → _root_.GlobalTheory.BigOn.ExponentStatement → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  intro _ hT hS hB hE
  have hP : _root_.GlobalTheory.BigOn.PageStatement := _root_.GlobalTheory.T.page_estimate_statement'
  have hG : _root_.GlobalTheory.BigOn.GeometricStatement' := _root_.GlobalTheory.T.geoSt_of_pageSt' hP
  exact _root_.GlobalTheory.T.onto_x_of_all_estimates _root_.GlobalTheory.T.runs_estimate_statement' _root_.GlobalTheory.T.rational_estimate_statement' hG (_root_.GlobalTheory.T.rank_at_twisted_places_of_max_geo _root_.GlobalTheory.T.maximum_estimate_statement' hG _root_.GlobalTheory.T.bigOn_comparison_at_twisted_places) hT hS hB hE hP
end GlobalTheory.BigOn
end

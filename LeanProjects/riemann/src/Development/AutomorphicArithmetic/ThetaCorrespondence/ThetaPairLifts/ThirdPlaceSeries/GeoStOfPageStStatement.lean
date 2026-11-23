import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFromPageEstimateStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoStOfPageSt

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geoSt_of_pageSt' : _root_.GlobalTheory.BigOn.PageStatement → _root_.GlobalTheory.BigOn.GeometricStatement' := by
  first | exact @_root_.GlobalTheory.BigOn.geoSt_of_pageSt_alt | exact _root_.GlobalTheory.BigOn.geoSt_of_pageSt_alt | (intros; apply _root_.GlobalTheory.BigOn.geoSt_of_pageSt_alt <;> assumption)
end

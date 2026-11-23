import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAllStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jump_closed_forall_d7 : ∀ D : D7, _root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D := by
  first | exact @_root_.GlobalTheory.JumpStatement.holds_all_alt | exact _root_.GlobalTheory.JumpStatement.holds_all_alt | (intros; apply _root_.GlobalTheory.JumpStatement.holds_all_alt <;> assumption)
end

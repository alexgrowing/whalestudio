import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAll
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.statement_J_all : ∀ D : D7, AdmissibleParameterJ.JumpBoundClosedForm D := by
  first | exact @GlobalTheory.JumpStatement.holds_all | exact GlobalTheory.JumpStatement.holds_all | (intros; apply GlobalTheory.JumpStatement.holds_all <;> assumption)

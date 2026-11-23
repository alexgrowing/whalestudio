import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2PairOfAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG2_pair_of_admissible : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → AdmissibleParameterJ.DeRhamFamilyAway D ∧ AdmissibleParameterJ.DeRhamFamilyTypePrimes D := by
  first | exact @GlobalTheory.PointRepAboveL.main | exact GlobalTheory.PointRepAboveL.main | (intros; apply GlobalTheory.PointRepAboveL.main <;> assumption)
